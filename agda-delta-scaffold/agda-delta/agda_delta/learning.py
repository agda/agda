from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
import json
from typing import Any, Iterable

DEFAULT_LEARNING_PATH = "data/learning-model.json"
DEFAULT_LEGACY_TRACE_PATH = "data/traces.jsonl"
DEFAULT_MAX_CANDIDATES_PER_FAMILY = 256


def goal_shape(goal_type: str) -> str:
    gt = goal_type.lower()
    if "->" in gt or "∀" in gt or "pi" in gt:
        return "intro"
    if "=" in gt or "≡" in gt:
        return "equality"
    if any(tok in gt for tok in ["nat", "vec", "list", "maybe"]):
        return "data"
    return "generic"


@dataclass
class CandidateStats:
    success: int = 0
    failure: int = 0

    def score(self) -> tuple[int, int]:
        return (self.success - self.failure, self.success)


class TraceLearning:
    def __init__(
        self,
        path: str | Path = DEFAULT_LEARNING_PATH,
        *,
        legacy_trace_path: str | Path = DEFAULT_LEGACY_TRACE_PATH,
        max_candidates_per_family: int = DEFAULT_MAX_CANDIDATES_PER_FAMILY,
    ):
        self.path = Path(path)
        self.legacy_trace_path = Path(legacy_trace_path)
        self.max_candidates_per_family = max_candidates_per_family
        self.candidate_stats: dict[tuple[str, str, str], CandidateStats] = defaultdict(CandidateStats)
        self.strategy_stats: dict[tuple[str, str], CandidateStats] = defaultdict(CandidateStats)
        self._dirty = False

    def load(self) -> None:
        """Load advisory ranking history from the compressed learner model.

        Preconditions:
        - missing files are allowed.

        Postconditions:
        - malformed rows are ignored.
        - caller can always rank candidates from an empty model.
        """
        self.candidate_stats.clear()
        self.strategy_stats.clear()
        self._dirty = False
        if self.path.exists():
            self._load_model()
            return

        raw_sources = list(self._raw_trace_sources())
        if raw_sources:
            for source in raw_sources:
                self._load_from_raw(self._raw_rows(source))
            self.save()

    def _raw_trace_sources(self) -> list[Path]:
        sources: set[Path] = set()
        if self.legacy_trace_path.exists():
            sources.add(self.legacy_trace_path)
        trace_root = self.legacy_trace_path.parent
        if trace_root.exists() and trace_root.is_dir():
            for file in trace_root.glob("*.jsonl"):
                sources.add(file)
        return sorted(sources)

    def _raw_rows(self, trace_file: Path) -> Iterable[dict[str, Any]]:
        with trace_file.open("r", encoding="utf-8") as handle:
            for line in handle:
                line = line.strip()
                if not line:
                    continue
                try:
                    payload = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if not isinstance(payload, dict):
                    continue
                if payload.get("event") != "candidate_attempt":
                    continue
                yield payload

    def _normalize_row(self, row: dict[str, Any]) -> tuple[str, str, str] | None:
        strategy = row.get("strategy")
        shape = row.get("goal_shape")
        candidate = row.get("expr")
        if not isinstance(strategy, str) or not isinstance(shape, str) or not isinstance(candidate, str):
            return None
        return strategy, shape, candidate

    def _load_from_raw(self, rows: Iterable[dict[str, Any]]) -> None:
        for row in rows:
            parsed = self._normalize_row(row)
            if parsed is None:
                continue
            strategy, shape, candidate = parsed
            candidate_bucket = self.candidate_stats[(strategy, shape, candidate)]
            family_bucket = self.strategy_stats[(strategy, shape)]
            if row.get("ok"):
                candidate_bucket.success += 1
                family_bucket.success += 1
            else:
                candidate_bucket.failure += 1
                family_bucket.failure += 1
        self._prune_candidates()

    def _load_model(self) -> None:
        with self.path.open("r", encoding="utf-8") as handle:
            payload = json.load(handle)
        if not isinstance(payload, dict):
            return

        raw_candidate_stats = payload.get("candidate_stats")
        if isinstance(raw_candidate_stats, list):
            for row in raw_candidate_stats:
                if not isinstance(row, dict):
                    continue
                strategy = row.get("strategy")
                shape = row.get("shape")
                candidate = row.get("candidate")
                success = row.get("success")
                failure = row.get("failure")
                if (
                    not isinstance(strategy, str)
                    or not isinstance(shape, str)
                    or not isinstance(candidate, str)
                    or not isinstance(success, int)
                    or not isinstance(failure, int)
                ):
                    continue
                self.candidate_stats[(strategy, shape, candidate)] = CandidateStats(
                    success=success,
                    failure=failure,
                )

        raw_strategy_stats = payload.get("strategy_stats")
        if isinstance(raw_strategy_stats, list):
            for row in raw_strategy_stats:
                if not isinstance(row, dict):
                    continue
                strategy = row.get("strategy")
                shape = row.get("shape")
                success = row.get("success")
                failure = row.get("failure")
                if (
                    not isinstance(strategy, str)
                    or not isinstance(shape, str)
                    or not isinstance(success, int)
                    or not isinstance(failure, int)
                ):
                    continue
                self.strategy_stats[(strategy, shape)] = CandidateStats(
                    success=success,
                    failure=failure,
                )

        self._prune_candidates()

    def _prune_candidates(self) -> None:
        if self.max_candidates_per_family <= 0:
            return

        families = list(self.candidate_stats.keys())
        tracked = {(strategy, shape) for strategy, shape, _ in families}
        for strategy, shape in tracked:
            members = [
                (candidate, stats)
                for (s, sh, candidate), stats in self.candidate_stats.items()
                if s == strategy and sh == shape
            ]
            if len(members) <= self.max_candidates_per_family:
                continue
            members.sort(
                key=lambda item: (
                    item[1].score()[0],
                    item[1].score()[1],
                    item[0],
                ),
                reverse=True,
            )
            for candidate, _ in members[self.max_candidates_per_family :]:
                del self.candidate_stats[(strategy, shape, candidate)]

    def save(self) -> None:
        """Persist compressed learner state."""
        if self.max_candidates_per_family > 0:
            self._prune_candidates()
        self.path.parent.mkdir(parents=True, exist_ok=True)
        serialized_candidates: list[dict[str, Any]] = []
        for (strategy, shape, candidate), stats in self.candidate_stats.items():
            serialized_candidates.append(
                {
                    "strategy": strategy,
                    "shape": shape,
                    "candidate": candidate,
                    "success": stats.success,
                    "failure": stats.failure,
                }
            )
        serialized_strategy: list[dict[str, Any]] = []
        for (strategy, shape), stats in self.strategy_stats.items():
            serialized_strategy.append(
                {
                    "strategy": strategy,
                    "shape": shape,
                    "success": stats.success,
                    "failure": stats.failure,
                }
            )

        payload = {
            "version": 1,
            "candidate_stats": serialized_candidates,
            "strategy_stats": serialized_strategy,
        }
        tmp_path = self.path.with_suffix(".tmp")
        with tmp_path.open("w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
        tmp_path.replace(self.path)
        self._dirty = False

    def record_attempt(self, strategy: str, goal_type: str, candidate: str, ok: bool) -> None:
        """Record one candidate attempt into compressed state."""
        if not strategy or not goal_type or not candidate:
            return
        shape = goal_shape(goal_type)
        candidate_bucket = self.candidate_stats[(strategy, shape, candidate)]
        strategy_bucket = self.strategy_stats[(strategy, shape)]
        if ok:
            candidate_bucket.success += 1
            strategy_bucket.success += 1
        else:
            candidate_bucket.failure += 1
            strategy_bucket.failure += 1
        self._dirty = True

    def flush(self) -> None:
        if self._dirty:
            self.save()

    def rank_candidates(self, strategy: str, goal_type: str, candidates: list[str]) -> list[str]:
        """Return a deterministic candidate order.

        Invariants:
        - ranking is advisory only.
        - cold-start ordering falls back to a stable lexical tie-breaker.
        """
        shape = goal_shape(goal_type)

        def sort_key(candidate: str) -> tuple[int, int, int, str]:
            candidate_bucket = self.candidate_stats[(strategy, shape, candidate)]
            family_bucket = self.strategy_stats[(strategy, shape)]
            return (
                candidate_bucket.score()[0],
                candidate_bucket.score()[1],
                family_bucket.score()[0],
                candidate,
            )

        return sorted(candidates, key=sort_key, reverse=True)
