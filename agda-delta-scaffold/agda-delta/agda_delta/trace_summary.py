from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path


def _load_rows(path: Path) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            payload = json.loads(line)
            if isinstance(payload, dict):
                rows.append(payload)
    return rows


def _summarize_run(rows: list[dict[str, object]]) -> dict[str, object]:
    run_id = rows[0].get("run_id") if rows else None
    events = Counter()
    candidate_outcomes = Counter()
    candidate_reasons = Counter()
    accepted_candidates = Counter()
    goals = Counter()
    stopped = False
    solved = False

    for row in rows:
        event = row.get("event")
        if isinstance(event, str):
            events[event] += 1
        if event == "candidate_attempt":
            outcome = row.get("outcome")
            if isinstance(outcome, str):
                candidate_outcomes[outcome] += 1
            reason = row.get("reason")
            if isinstance(reason, str):
                candidate_reasons[reason] += 1
            goal_class = row.get("goal_shape")
            if isinstance(goal_class, str):
                goals[goal_class] += 1
        if event == "accepted":
            candidate = row.get("candidate")
            if isinstance(candidate, str):
                accepted_candidates[candidate] += 1
        if event == "solved":
            solved = True
        if event in {"guard_stop", "interaction_error"}:
            stopped = True

    if rows and not solved:
        stopped = True

    return {
        "run_id": run_id,
        "events": dict(events),
        "candidate_outcomes": dict(candidate_outcomes),
        "candidate_reasons_top": candidate_reasons.most_common(3),
        "accepted_candidates_top": accepted_candidates.most_common(3),
        "goal_shapes": dict(goals),
        "status": "solved" if solved else "stopped" if stopped else "unknown",
    }


def summarize_paths(paths: list[Path]) -> list[dict[str, object]]:
    summaries: list[dict[str, object]] = []
    for path in paths:
        rows = _load_rows(path)
        summary = _summarize_run(rows)
        summary["path"] = str(path)
        summaries.append(summary)
    return summaries


def print_summary(summaries: list[dict[str, object]]) -> None:
    for summary in summaries:
        print(f"path: {summary['path']}")
        print(f"run_id: {summary['run_id']}")
        print(f"status: {summary['status']}")
        print(f"events: {summary['events']}")
        print(f"candidate_outcomes: {summary['candidate_outcomes']}")
        print(f"candidate_reasons_top: {summary['candidate_reasons_top']}")
        print(f"accepted_candidates_top: {summary['accepted_candidates_top']}")
        print(f"goal_shapes: {summary['goal_shapes']}")
        print()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("paths", nargs="+", help="Trace JSONL paths")
    args = parser.parse_args()
    summaries = summarize_paths([Path(path) for path in args.paths])
    print_summary(summaries)


if __name__ == "__main__":
    main()
