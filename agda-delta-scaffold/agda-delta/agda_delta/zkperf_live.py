from __future__ import annotations

import importlib.util
import json
import os
import shutil
from pathlib import Path
from typing import Any

from .utils import append_jsonl


REGISTER_LABELS = [
    "idx",
    "log10(period+1)",
    "log10(ts_gap+1)",
    "pid",
    "tid",
    "cpu_mode",
]


def _default_zkperf_root() -> Path:
    return Path(__file__).resolve().parents[4] / "zkperf"


def _load_module(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec is not None and spec.loader is not None
    spec.loader.exec_module(module)
    return module


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


class LiveZKPerfRun:
    """Live zkperf-style witness sink for one agda-delta CLI run."""

    def __init__(
        self,
        *,
        run_id: str,
        target: str,
        mode: str,
        output_dir: str | Path,
        external_trace_path: str | Path | None = None,
        zkperf_root: str | Path | None = None,
    ) -> None:
        self.run_id = run_id
        self.target = str(Path(target).resolve())
        self.mode = mode
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.external_trace_path = Path(external_trace_path).resolve() if external_trace_path else None
        self.zkperf_root = Path(zkperf_root) if zkperf_root else _default_zkperf_root()
        self.agda_trace_path = self.output_dir / "agda_trace.jsonl"
        self.bundle_trace_path = self.output_dir / "trace.jsonl"
        self.sample_trace_path = self.output_dir / "zkperf_sample_trace.json"
        self.source_path = self.output_dir / "source.json"
        self.machine_witness_path = self.output_dir / "agda_machine_witness.json"
        self.compact_path = self.output_dir / "compact.json"
        self.roundtrip_path = self.output_dir / "roundtrip.json"
        self.stats_path = self.output_dir / "stats.json"
        self.manifest_path = self.output_dir / "manifest.json"
        self._annotations: list[dict[str, Any]] = []
        self._rss_samples_mb: list[float] = []
        self._rss_budget_mb = self._load_rss_budget_mb()
        self._timestamp = 0
        self._step = 0
        self._file_slots: dict[str, int] = {}
        self._strategy_slots: dict[str, int] = {}

    def _slot(self, table: dict[str, int], key: str) -> int:
        if key not in table:
            table[key] = len(table) + 1
        return table[key]

    def _load_rss_budget_mb(self) -> float | None:
        raw = os.environ.get("AGDA_DELTA_RSS_MB_BUDGET")
        if raw is None:
            return None
        try:
            value = float(raw)
        except ValueError:
            return None
        if value <= 0:
            return None
        return round(value, 2)

    def _transition(self, row: dict[str, Any]) -> str:
        event = str(row.get("event", "unknown"))
        if event == "candidate_attempt":
            outcome = row.get("outcome")
            if isinstance(outcome, str):
                return f"{event}:{outcome}"
        return event

    def _cpu_mode(self, row: dict[str, Any]) -> str:
        if row.get("event") in {"accepted", "solved"}:
            return "User"
        if row.get("outcome") == "accepted" or row.get("ok") is True:
            return "User"
        return "Kernel"

    def _int_field(self, row: dict[str, Any], *names: str) -> int:
        for name in names:
            value = row.get(name)
            if isinstance(value, bool):
                continue
            if isinstance(value, int):
                return value
        return 0

    def _goal_count(self, row: dict[str, Any]) -> int:
        return self._int_field(row, "after_goal_count", "before_goal_count", "goal_count", "file_count")

    def _machine_state(self, row: dict[str, Any], transition: str) -> dict[str, Any]:
        file_value = row.get("file") or row.get("shadow_file") or row.get("project_root") or self.target
        return {
            "file": str(file_value),
            "goal_id": row.get("goal_id"),
            "goal_count": self._goal_count(row),
            "strategy": row.get("strategy"),
            "goal_class": row.get("goal_class") or row.get("goal_shape"),
            "candidate_class": row.get("goal_shape"),
            "source_mutated": row.get("source_mutated"),
            "process_restarted": row.get("process_restarted"),
            "accepted_boundary_crossed": row.get("ok") is True or row.get("event") in {"accepted", "solved"},
            "phase": transition,
        }

    def record_event(self, row: dict[str, Any]) -> None:
        payload = dict(row)
        append_jsonl(self.agda_trace_path, payload)
        rss_mb = payload.get("rss_mb")
        if isinstance(rss_mb, (int, float)):
            self._rss_samples_mb.append(round(float(rss_mb), 2))

        transition = self._transition(payload)
        period = max(
            1,
            self._int_field(
                payload,
                "elapsed_ms",
                "goal_count",
                "candidate_count",
                "before_goal_count",
                "after_goal_count",
                "file_count",
                "step",
            ),
        )
        self._timestamp += period
        self._step += 1
        machine_state = self._machine_state(payload, transition)
        file_slot = self._slot(self._file_slots, machine_state["file"])
        strategy_slot = self._slot(
            self._strategy_slots,
            str(machine_state["strategy"] or payload.get("event") or "unknown"),
        )
        accepted_flag = 1 if machine_state["accepted_boundary_crossed"] else 0
        self._annotations.append(
            {
                "step": self._step,
                "timestamp": self._timestamp,
                "period": period,
                "transition": transition,
                "cpu_mode": self._cpu_mode(payload),
                "cid": f"{self.run_id}:{self._step}:{transition}",
                "next_state": [
                    self._step,
                    machine_state["goal_count"],
                    accepted_flag,
                    file_slot,
                    strategy_slot,
                ],
                "machine_state": machine_state,
            }
        )

    def finalize(self, *, solved: bool, extra_manifest: dict[str, Any] | None = None) -> None:
        source_dir = str(Path(self.target).parent) if self.mode == "file" else self.target
        shard_family_counts = {
            "sample": len(self._annotations),
            "mmap": 0,
            "other": 0,
            "schema": 0,
        }
        codec = _load_module(
            self.zkperf_root / "scripts" / "compact-sample-trace.py",
            "zkperf_compact_sample_trace_live",
        )
        events: list[str] = []
        event_to_index: dict[str, int] = {}
        rows: list[dict[str, Any]] = []
        for annotation in self._annotations:
            transition = str(annotation["transition"])
            event_index = event_to_index.setdefault(transition, len(events))
            if event_index == len(events):
                events.append(transition)
            next_state = annotation["next_state"]
            rows.append(
                {
                    "step": int(annotation["step"]),
                    "event_idx": event_index,
                    "timestamp": int(annotation["timestamp"]),
                    "period": int(annotation["period"]),
                    "pid": int(next_state[3]),
                    "tid": int(next_state[4]),
                    "cpu_mode": str(annotation["cpu_mode"]),
                    "cid": annotation["cid"],
                }
            )
        compact_payload = {
            "trace_kind": "sample_trace_compact/v1",
            "source_trace_kind": "sample_trace",
            "source_dir": source_dir,
            "artifact": self.target,
            "template_set": "agda_delta:live_witness_v1",
            "shard_family_counts": shard_family_counts,
            "events": events,
            "rows": rows,
        }
        source_payload = codec.decode_trace(compact_payload)
        _write_json(self.sample_trace_path, source_payload)
        _write_json(self.source_path, source_payload)
        _write_json(
            self.machine_witness_path,
            {
                "trace_kind": "agda_delta_machine_witness/v1",
                "run_id": self.run_id,
                "mode": self.mode,
                "target": self.target,
                "state_machine_schema": "agda_delta/live_machine_v1",
                "steps": len(self._annotations),
                "step_annotations": [
                    {
                        "step": annotation["step"],
                        "timestamp": annotation["timestamp"],
                        "transition": annotation["transition"],
                        "cid": annotation["cid"],
                        "machine_state": annotation["machine_state"],
                    }
                    for annotation in self._annotations
                ],
            },
        )

        _write_json(self.compact_path, compact_payload)
        roundtrip_payload = codec.decode_trace(compact_payload)
        _write_json(self.roundtrip_path, roundtrip_payload)
        stats_payload = codec.compression_stats(self.sample_trace_path, self.compact_path, self.roundtrip_path)
        if self._rss_samples_mb:
            rss_peak = max(self._rss_samples_mb)
            rss_final = self._rss_samples_mb[-1]
            rss_budget_exceeded = (
                self._rss_budget_mb is not None and rss_peak > self._rss_budget_mb
            )
            stats_payload.update(
                {
                    "rss_mb_min": min(self._rss_samples_mb),
                    "rss_mb_max": rss_peak,
                    "rss_mb_avg": round(sum(self._rss_samples_mb) / len(self._rss_samples_mb), 2),
                    "rss_mb_final": rss_final,
                    "rss_sample_count": len(self._rss_samples_mb),
                    "rss_budget_mb": self._rss_budget_mb,
                    "rss_budget_exceeded": rss_budget_exceeded,
                }
            )
        _write_json(self.stats_path, stats_payload)

        if self.external_trace_path and self.external_trace_path.exists():
            if self.external_trace_path.resolve() != self.bundle_trace_path.resolve():
                shutil.copy2(self.external_trace_path, self.bundle_trace_path)
        elif not self.bundle_trace_path.exists():
            self.bundle_trace_path.write_text("", encoding="utf-8")

        manifest = {
            "run_id": self.run_id,
            "mode": self.mode,
            "target": self.target,
            "solved": solved,
            "event_count": len(self._annotations),
            "live_emitted": True,
            "state_machine_schema": "agda_delta/live_machine_v1",
            "agda_trace_path": self.agda_trace_path.name,
            "trace_path": self.bundle_trace_path.name,
            "zkperf_sample_trace_path": self.sample_trace_path.name,
            "source_path": self.source_path.name,
            "machine_witness_path": self.machine_witness_path.name,
            "compact_path": self.compact_path.name,
            "roundtrip_path": self.roundtrip_path.name,
            "stats_path": self.stats_path.name,
        }
        if self._rss_samples_mb:
            rss_peak = max(self._rss_samples_mb)
            rss_final = self._rss_samples_mb[-1]
            rss_budget_exceeded = (
                self._rss_budget_mb is not None and rss_peak > self._rss_budget_mb
            )
            manifest.update(
                {
                    "rss_mb_peak": rss_peak,
                    "rss_mb_final": rss_final,
                    "rss_sample_count": len(self._rss_samples_mb),
                    "rss_budget_mb": self._rss_budget_mb,
                    "rss_budget_exceeded": rss_budget_exceeded,
                }
            )
        if extra_manifest:
            manifest.update(extra_manifest)
        _write_json(self.manifest_path, manifest)
