from __future__ import annotations
import argparse
from dataclasses import asdict, dataclass
import json
from pathlib import Path
import shutil
import tempfile
from time import time
from uuid import uuid4

from .agda_interact import AgdaProcess
from .file_graph import solve_order
from .guards import DivergenceGuard
from .goal_index import GoalIndex
from .learning import TraceLearning, goal_shape
from .memory import rss_mb
from .rewrite_db import RewriteDB
from .search_policy import policy_for_goal
from .scheduler import ResourceVector, choose_strategy
from .utils import append_jsonl
from .zkperf_live import LiveZKPerfRun

@dataclass(frozen=True)
class Goal:
    goal_id: int
    goal_type: str
    order: int
    source: dict[str, object] | None = None

class AutoProver:
    """Coordinator for one-file or project-scoped scaffold runs.

    Constraints:
    - candidate generation and ranking are advisory only.
    - acceptance requires deterministic replay through Agda.

    Current limitation:
    - promotion targeting is exact for currently parseable goal/hole surfaces,
      but still depends on the current Agda goal-list parser contract.
    """

    def __init__(
        self,
        file_path: str,
        project_root: str | None = None,
        *,
        trace_path: str | None = None,
        run_id: str | None = None,
        zkperf_run: LiveZKPerfRun | None = None,
    ):
        self.file_path = file_path
        self.project_root = project_root
        self.run_id = run_id or uuid4().hex
        self.trace_path = trace_path or f"data/traces/{self.run_id}.jsonl"
        self.zkperf_run = zkperf_run
        self.agda = AgdaProcess(file_path, observer=self._observe_process if self.zkperf_run else None)
        self.guard = DivergenceGuard()
        self.goal_index = GoalIndex()
        if self.project_root:
            self.goal_index.rebuild_from_project(self.project_root)
        self.goal_index.load()
        self.rewrite_db = RewriteDB()
        self.rewrite_db.load()
        self.learning = TraceLearning()
        self.learning.load()
        self.recent: list[str] = []

    def _trace(self, row: dict[str, object]) -> None:
        payload = {"run_id": self.run_id, **row}
        payload.setdefault("rss_mb", rss_mb())
        append_jsonl(self.trace_path, payload)
        if self.zkperf_run is not None:
            self.zkperf_run.record_event(payload)

    def _observe_process(self, row: dict[str, object]) -> None:
        self._trace(row)

    def _iotcm(self, body: str, *, indirect: bool) -> str:
        mode = "Indirect" if indirect else "Direct"
        return f'IOTCM "{self.file_path}" None {mode} {body}'

    def _json_messages(self, lines: list[str]) -> list[dict[str, object]]:
        messages: list[dict[str, object]] = []
        for line in lines:
            if not line.startswith("{"):
                continue
            try:
                payload = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(payload, dict):
                messages.append(payload)
        return messages

    def _error_reason(self, lines: list[str]) -> str:
        for message in self._json_messages(lines):
            if message.get("kind") != "DisplayInfo":
                continue
            info = message.get("info")
            if not isinstance(info, dict):
                continue
            if info.get("kind") == "Error":
                error = info.get("error")
                if isinstance(error, dict):
                    text = error.get("message")
                    if isinstance(text, str) and text:
                        return text
                return "Agda interaction error"
        return "Agda interaction error"

    def _parse_goals(self, lines: list[str]) -> list[Goal]:
        for message in self._json_messages(lines):
            if message.get("kind") != "DisplayInfo":
                continue
            info = message.get("info")
            if not isinstance(info, dict) or info.get("kind") != "AllGoalsWarnings":
                continue
            visible_goals = info.get("visibleGoals")
            if not isinstance(visible_goals, list):
                return []
            parsed: list[Goal] = []
            for idx, visible_goal in enumerate(visible_goals):
                if not isinstance(visible_goal, dict) or visible_goal.get("kind") != "OfType":
                    continue
                constraint_obj = visible_goal.get("constraintObj")
                goal_type = visible_goal.get("type")
                if not isinstance(constraint_obj, dict) or not isinstance(goal_type, str):
                    continue
                goal_id = constraint_obj.get("id")
                if not isinstance(goal_id, int):
                    continue
                source = self._goal_source_from_json(constraint_obj, idx)
                parsed.append(
                    Goal(
                        goal_id=goal_id,
                        goal_type=goal_type.strip(),
                        order=idx,
                        source=source,
                    )
                )
            return parsed
        return []

    def _escape_expr(self, expr: str) -> str:
        return expr.replace("\\", "\\\\").replace('"', '\\"')

    def _goal_source_from_json(self, constraint_obj: dict[str, object], order: int) -> dict[str, object] | None:
        ranges = constraint_obj.get("range")
        if not isinstance(ranges, list) or not ranges:
            return None
        interval = ranges[0]
        if not isinstance(interval, dict):
            return None
        start = interval.get("start")
        end = interval.get("end")
        if not isinstance(start, dict) or not isinstance(end, dict):
            return None
        start_pos = start.get("pos")
        end_pos = end.get("pos")
        line = start.get("line")
        col = start.get("col")
        if not all(isinstance(value, int) for value in [start_pos, end_pos, line, col]):
            return None
        return {
            "goal_id": constraint_obj.get("id"),
            "goal_order": order,
            "span_start": start_pos - 1,
            "span_end": end_pos - 1,
            "line": line,
            "column": col,
        }

    def _replace_goal_text(self, goal: Goal, expr: str) -> tuple[bool, dict[str, object] | None]:
        if goal.source is None:
            return False, None
        path = Path(self.file_path)
        text = path.read_text(encoding="utf-8")
        target = dict(goal.source)
        start = target.get("span_start")
        end = target.get("span_end")
        if not isinstance(start, int) or not isinstance(end, int):
            return False, None
        if start < 0 or end < start or end > len(text):
            return False, None
        target["source_text"] = text[start:end]
        updated = text[:start] + expr + text[end:]
        path.write_text(updated, encoding="utf-8")
        return True, target

    def _target_goal_transition(
        self,
        target_goal_id: int,
        before_goals: list[Goal],
        after_goals: list[Goal],
    ) -> dict[str, object]:
        before_ids = {goal.goal_id for goal in before_goals}
        after_ids = {goal.goal_id for goal in after_goals}
        before_types = {goal.goal_id: goal.goal_type for goal in before_goals}
        after_types = {goal.goal_id: goal.goal_type for goal in after_goals}
        target_present_before = target_goal_id in before_ids
        target_present_after = target_goal_id in after_ids
        return {
            "target_goal_present_before": target_present_before,
            "target_goal_present_after": target_present_after,
            "target_goal_removed": target_present_before and not target_present_after,
            "target_goal_type_before": before_types.get(target_goal_id),
            "target_goal_type_after": after_types.get(target_goal_id),
        }

    def _restart_process(self) -> None:
        self.agda.close()
        self.agda = AgdaProcess(self.file_path)

    def load_file(self) -> list[str]:
        """Load the current file into Agda interaction mode."""
        cmd = self._iotcm(f'(Cmd_load "{self.file_path}" [])', indirect=True)
        lines = self.agda.send_and_collect(cmd, timeout=0.4)
        self._trace({
            "event": "load",
            "file": self.file_path,
            "message_count": len(lines),
        })
        if self._error_reason(lines) != "Agda interaction error":
            raise RuntimeError(self._error_reason(lines))
        return lines

    def extract_goals(self) -> list[Goal]:
        """Extract live unsolved goal types from the current interaction state.

        Postcondition:
        - returns visible goals from Agda's structured JSON interaction output.
        - returns an empty list for solved files.
        """
        lines = self.load_file()
        goals = self._parse_goals(lines)
        self._trace({
            "event": "goals_visible",
            "file": self.file_path,
            "goal_count": len(goals),
            "goal_ids": [goal.goal_id for goal in goals],
        })
        return goals

    def rank_goals(self, goals: list[Goal]) -> list[Goal]:
        return sorted(goals, key=lambda goal: self._estimate_state(goal.goal_type).potential(), reverse=True)

    def _estimate_state(self, goal_type: str) -> ResourceVector:
        gt = goal_type.lower()
        n = 2 if ("=" in gt or "≡" in gt) else 1
        u = 2 if "∀" in gt or "->" in gt else 1
        m = 1
        i = 0
        r = 0
        d = 1 if "case" in gt else 0
        return ResourceVector(n=n, u=u, m=m, i=i, r=r, d=d)

    def generate_candidates(self, goal_type: str, strategy_name: str) -> list[str]:
        policy = policy_for_goal(goal_type)
        rewrites = self.rewrite_db.match(goal_type)
        lemmas = self.goal_index.retrieve(goal_type)
        candidates: list[str] = []

        if strategy_name == "intro":
            candidates.append("λ x → ?")
        elif strategy_name == "rewrite":
            candidates.extend([f"rewrite {r['tag']}" for r in rewrites if r.get("tag")])
            candidates.extend([f"{lemma['name']}" for lemma in lemmas[:3]])
        elif strategy_name == "apply":
            candidates.extend([f"{lemma['name']} ?" for lemma in lemmas[:5]])
        elif strategy_name == "constructor":
            candidates.extend(["zero", "suc ?"])
        elif strategy_name == "trivial":
            candidates.extend(["refl", "?"])
        else:
            candidates.append("?")

        deduped = []
        seen = set()
        for c in candidates:
            if c not in seen:
                seen.add(c)
                deduped.append(c)
        learned = self.learning.rank_candidates(
            strategy_name,
            goal_type,
            deduped[: policy.max_candidates],
        )
        return learned[: policy.max_candidates]

    def try_candidate(
        self,
        expr: str,
        goal: Goal,
        current_goals: list[Goal],
        strategy_name: str,
    ) -> tuple[bool, list[str], dict[str, object] | None]:
        start = time()
        original_text = Path(self.file_path).read_text(encoding="utf-8")
        replay_lines: list[str] = []
        after_goal_count: int | None = None
        after_goal_ids: list[int] | None = None
        transition: dict[str, object] | None = None
        target_source: dict[str, object] | None = None
        source_mutated = False
        process_restarted = False
        give_cmd = self._iotcm(
            f'(Cmd_give WithoutForce {goal.goal_id} noRange "{self._escape_expr(expr)}")',
            indirect=True,
        )
        self._trace({
            "event": "candidate_proposed",
            "file": self.file_path,
            "expr": expr,
            "goal_type": goal.goal_type,
            "goal_id": goal.goal_id,
            "goal_shape": goal_shape(goal.goal_type),
            "strategy": strategy_name,
            "before_goal_count": len(current_goals),
        })
        lines = self.agda.send_and_collect(give_cmd, timeout=0.3)
        outcome = "rejected"
        ok = False
        reason = "candidate_rejected"
        error_reason = self._error_reason(lines)
        if error_reason != "Agda interaction error":
            reason = error_reason
        else:
            source_mutated, target_source = self._replace_goal_text(goal, expr)
            if not source_mutated:
                reason = "promotion_target_unavailable"
            else:
                self._trace({
                    "event": "candidate_replay",
                    "file": self.file_path,
                    "expr": expr,
                    "goal_id": goal.goal_id,
                    "strategy": strategy_name,
                    "source_mutated": source_mutated,
                })
                try:
                    self._restart_process()
                    process_restarted = True
                    replay_goals = self.extract_goals()
                    after_goal_count = len(replay_goals)
                    after_goal_ids = [replay_goal.goal_id for replay_goal in replay_goals]
                    transition = self._target_goal_transition(goal.goal_id, current_goals, replay_goals)
                    replay_lines = [f"REPLAY goals={after_goal_count}"]
                    if bool(transition["target_goal_removed"]):
                        ok = True
                        outcome = "accepted"
                        reason = "replayed"
                    else:
                        reason = "target_goal_not_resolved_after_replay"
                except RuntimeError as exc:
                    reason = str(exc)
        if not ok:
            if source_mutated:
                Path(self.file_path).write_text(original_text, encoding="utf-8")
                if not process_restarted:
                    self._restart_process()
                    process_restarted = True
            elif self.agda.proc.poll() is not None:
                self._restart_process()
                process_restarted = True
        self._trace({
            "event": "candidate_attempt",
            "expr": expr,
            "goal_type": goal.goal_type,
            "goal_id": goal.goal_id,
            "goal_shape": goal_shape(goal.goal_type),
            "strategy": strategy_name,
            "outcome": outcome,
            "reason": reason,
            "ok": ok,
            "before_goal_ids": [current_goal.goal_id for current_goal in current_goals],
            "after_goal_ids": after_goal_ids,
            "before_goal_count": len(current_goals),
            "after_goal_count": after_goal_count,
            "target_goal_removed": None if transition is None else transition["target_goal_removed"],
            "target_goal_present_before": None if transition is None else transition["target_goal_present_before"],
            "target_goal_present_after": None if transition is None else transition["target_goal_present_after"],
            "target_goal_type_before": None if transition is None else transition["target_goal_type_before"],
            "target_goal_type_after": None if transition is None else transition["target_goal_type_after"],
            "target_goal_source": target_source,
            "source_mutated": source_mutated,
            "process_restarted": process_restarted,
            "elapsed_ms": int((time() - start) * 1000),
        })
        self.learning.record_attempt(strategy_name, goal.goal_type, expr, ok)
        return ok, lines + replay_lines, target_source

    def solve(self, max_steps: int = 50) -> bool:
        try:
            for step in range(max_steps):
                try:
                    goals = self.extract_goals()
                except RuntimeError as exc:
                    self._trace({
                        "event": "interaction_error",
                        "file": self.file_path,
                        "step": step,
                        "reason": str(exc),
                    })
                    return False
                if not goals:
                    self._trace({"event": "solved", "step": step})
                    return True

                ranked_goals = self.rank_goals(goals)
                goal = ranked_goals[0]
                state = self._estimate_state(goal.goal_type)
                decision = self.guard.check(goal.goal_type, state, self.recent)
                if decision.stop:
                    self._trace({
                        "event": "guard_stop",
                        "goal": goal.goal_type,
                        "reason": decision.reason,
                        "state": asdict(state),
                    })
                    return False

                strategy = choose_strategy(goal.goal_type, state)
                candidates = self.generate_candidates(goal.goal_type, strategy.name)
                policy = policy_for_goal(goal.goal_type)

                self._trace({
                    "event": "step",
                    "step": step,
                    "goal": goal.goal_type,
                    "goal_id": goal.goal_id,
                    "goal_count": len(goals),
                    "goal_class": policy.goal_class,
                    "state": asdict(state),
                    "strategy": strategy.name,
                    "candidate_count": len(candidates),
                    "policy_max_candidates": policy.max_candidates,
                })

                for candidate in candidates:
                    ok, _, accepted_source = self.try_candidate(candidate, goal, goals, strategy.name)
                    if ok:
                        self.recent.append(strategy.name)
                        self._trace({
                            "event": "accepted",
                            "goal": goal.goal_type,
                            "goal_id": goal.goal_id,
                            "goal_order": goal.order,
                            "target_goal_source": accepted_source,
                            "strategy": strategy.name,
                            "candidate": candidate,
                        })
                        break

            return False
        finally:
            self.learning.flush()


def trace_event(trace_path: str, run_id: str, row: dict[str, object]) -> None:
    payload = {"run_id": run_id, **row}
    payload.setdefault("rss_mb", rss_mb())
    append_jsonl(trace_path, payload)

def _copytree_filtered(source_root: Path, shadow_root: Path) -> None:
    ignored_name = shadow_root.parent.name

    def _ignore(dirpath: str, names: list[str]) -> set[str]:
        ignored: set[str] = set()
        if Path(dirpath).resolve() == source_root.resolve() and ignored_name in names:
            ignored.add(ignored_name)
        return ignored

    shutil.copytree(source_root, shadow_root, dirs_exist_ok=True, ignore=_ignore)

def _shadow_copy_for_file(file_path: str) -> tuple[tempfile.TemporaryDirectory[str], Path]:
    source_path = Path(file_path).resolve()
    shadow_dir = tempfile.TemporaryDirectory(prefix="agda_delta_file_")
    shadow_root = Path(shadow_dir.name) / source_path.parent.name
    shadow_root.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source_path, shadow_root / source_path.name)
    for sibling in source_path.parent.iterdir():
        if sibling == source_path or not sibling.is_file():
            continue
        if sibling.suffix in {".agda", ".lagda", ".lagda.md", ".agda-lib"}:
            shutil.copy2(sibling, shadow_root / sibling.name)
    return shadow_dir, shadow_root / source_path.name


def solve_project(
    project_root: str,
    max_steps: int,
    *,
    trace_path: str | None = None,
    run_id: str | None = None,
    zkperf_dir: str | None = None,
) -> bool:
    """Run the scaffold across a project tree.

    Postcondition:
    - returns `True` only if every discovered file run returns success.
    """
    source_root = Path(project_root).resolve()
    project_run_id = run_id or uuid4().hex
    project_trace_path = trace_path or f"data/traces/{project_run_id}.jsonl"
    project_zkperf_dir = zkperf_dir or f"data/zkperf/{project_run_id}"
    zkperf_run = LiveZKPerfRun(
        run_id=project_run_id,
        target=str(source_root),
        mode="project",
        output_dir=project_zkperf_dir,
        external_trace_path=project_trace_path,
    )
    ordered_files: list[Path] = []
    try:
        ordered_files = solve_order(str(source_root))
    except FileNotFoundError as exc:
        payload = {
            "event": "project_scan_error",
            "project_root": project_root,
            "reason": str(exc),
        }
        trace_event(project_trace_path, project_run_id, payload)
        zkperf_run.record_event({"run_id": project_run_id, **payload})
        zkperf_run.finalize(solved=False, extra_manifest={"file_count": 0})
        return False
    shadow_dir = tempfile.TemporaryDirectory(prefix="agda_delta_project_")
    shadow_root = Path(shadow_dir.name) / source_root.name
    _copytree_filtered(source_root, shadow_root)
    payload = {
        "event": "project_scan",
        "project_root": project_root,
        "file_count": len(ordered_files),
    }
    trace_event(project_trace_path, project_run_id, payload)
    zkperf_run.record_event({"run_id": project_run_id, **payload})
    overall = True
    try:
        for path in ordered_files:
            shadow_path = shadow_root / path.relative_to(source_root)
            prover = AutoProver(
                str(shadow_path),
                project_root=str(shadow_root),
                trace_path=project_trace_path,
                run_id=project_run_id,
                zkperf_run=zkperf_run,
            )
            solved = prover.solve(max_steps=max_steps)
            file_payload = {
                "event": "file_result",
                "file": str(path),
                "shadow_file": str(shadow_path),
                "ok": solved,
            }
            trace_event(project_trace_path, project_run_id, file_payload)
            zkperf_run.record_event({"run_id": project_run_id, **file_payload})
            overall = overall and solved
            prover.agda.close()
        project_payload = {
            "event": "project_result",
            "project_root": project_root,
            "file_count": len(ordered_files),
            "ok": overall,
        }
        trace_event(project_trace_path, project_run_id, project_payload)
        zkperf_run.record_event({"run_id": project_run_id, **project_payload})
        return overall
    finally:
        shadow_dir.cleanup()
        zkperf_run.finalize(solved=overall, extra_manifest={"file_count": len(ordered_files)})

def solve_file(
    file_path: str,
    max_steps: int,
    *,
    trace_path: str | None = None,
    run_id: str | None = None,
    zkperf_dir: str | None = None,
) -> bool:
    file_run_id = run_id or uuid4().hex
    file_trace_path = trace_path or f"data/traces/{file_run_id}.jsonl"
    file_zkperf_dir = zkperf_dir or f"data/zkperf/{file_run_id}"
    zkperf_run = LiveZKPerfRun(
        run_id=file_run_id,
        target=file_path,
        mode="file",
        output_dir=file_zkperf_dir,
        external_trace_path=file_trace_path,
    )
    shadow_dir, shadow_file = _shadow_copy_for_file(file_path)
    solved = False
    try:
        prover = AutoProver(
            str(shadow_file),
            trace_path=file_trace_path,
            run_id=file_run_id,
            zkperf_run=zkperf_run,
        )
        solved = prover.solve(max_steps=max_steps)
        file_payload = {
            "event": "file_result",
            "file": str(Path(file_path).resolve()),
            "shadow_file": str(shadow_file),
            "ok": solved,
        }
        trace_event(file_trace_path, file_run_id, file_payload)
        zkperf_run.record_event({"run_id": file_run_id, **file_payload})
        prover.agda.close()
        return solved
    finally:
        zkperf_run.finalize(solved=solved)
        shadow_dir.cleanup()

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("file", nargs="?", help="Path to Agda file")
    parser.add_argument("--project", help="Path to a project root with .agda files")
    parser.add_argument("--steps", type=int, default=50)
    parser.add_argument("--trace-path", help="Optional JSONL path for this run's trace output")
    parser.add_argument("--zkperf-dir", help="Optional live zkperf bundle directory for this run")
    args = parser.parse_args()
    run_id = uuid4().hex

    if args.project:
        solved = solve_project(
            args.project,
            max_steps=args.steps,
            trace_path=args.trace_path,
            run_id=run_id,
            zkperf_dir=args.zkperf_dir,
        )
    else:
        if not args.file:
            parser.error("provide FILE or --project")
        solved = solve_file(
            args.file,
            max_steps=args.steps,
            trace_path=args.trace_path,
            run_id=run_id,
            zkperf_dir=args.zkperf_dir,
        )
    print("solved" if solved else "stopped")

if __name__ == "__main__":
    main()
