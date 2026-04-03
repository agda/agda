#!/usr/bin/env python3
"""Run the bounded dashi_agda zkperf window in one command."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
AGDA_ROOT = ROOT.parents[2]
DASHI_ROOT = AGDA_ROOT / "dashi_agda"
EXPORTER = ROOT / "scripts" / "export-zkperf-agda.py"
QUEUE_EMITTER = DASHI_ROOT / "scripts" / "generate_layer2_long_compute_queue.py"
QUEUE_RENDERER = DASHI_ROOT / "scripts" / "render_layer2_batch_commands.py"


def _run_json(cmd: list[str], *, cwd: Path, timeout_s: float) -> dict[str, object]:
    completed = subprocess.run(
        cmd,
        cwd=str(cwd),
        check=True,
        capture_output=True,
        text=True,
        timeout=timeout_s,
    )
    return json.loads(completed.stdout)


def _run_text(cmd: list[str], *, cwd: Path, timeout_s: float) -> str:
    completed = subprocess.run(
        cmd,
        cwd=str(cwd),
        check=True,
        capture_output=True,
        text=True,
        timeout=timeout_s,
    )
    return completed.stdout


def _slug(path: Path) -> str:
    parts = list(path.with_suffix("").parts)
    if len(parts) >= 2:
        parts = parts[-2:]
    return "-".join(parts).replace(" ", "-")


def _step_timeout(remaining_s: float, reserve_s: float, cap_s: float) -> float:
    usable = max(1.0, remaining_s - reserve_s)
    return max(1.0, min(cap_s, usable))


def main() -> None:
    parser = argparse.ArgumentParser(description="Run the bounded dashi_agda zkperf target window.")
    parser.add_argument("--budget-seconds", type=float, default=300.0)
    parser.add_argument("--steps", type=int, default=1)
    parser.add_argument("--hf-repo", default="introspector/zkperf")
    parser.add_argument("--out-dir", type=Path, default=ROOT / "out" / "dashi-zkperf-window")
    parser.add_argument("--queue-jobs", type=int, default=4)
    parser.add_argument("--skip-hf", action="store_true")
    parser.add_argument("--render-first-pair", action="store_true")
    args = parser.parse_args()

    out_dir = args.out_dir.resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    queue_dir = out_dir / "layer2-queue"
    queue_script = queue_dir / "first.sh"

    targets = [
        ("Layer2FiniteSearchShell", DASHI_ROOT / "Ontology/Hecke/Layer2FiniteSearchShell.agda"),
        ("KernelMonoid", DASHI_ROOT / "Kernel/Monoid.agda"),
        ("SaturatedInvariantRefinementStatus", DASHI_ROOT / "Ontology/Hecke/SaturatedInvariantRefinementStatus.agda"),
        ("VerificationPrelude", DASHI_ROOT / "Verification/Prelude.agda"),
    ]

    started = time.monotonic()
    records: list[dict[str, object]] = []

    for index, (label, target) in enumerate(targets, start=1):
        elapsed = time.monotonic() - started
        remaining = args.budget_seconds - elapsed
        reserve = 10.0 if index < len(targets) else 20.0
        timeout_s = _step_timeout(remaining, reserve, 75.0)
        if remaining <= reserve:
            records.append(
                {
                    "step": label,
                    "kind": "export",
                    "target": str(target),
                    "status": "skipped_budget",
                    "elapsed_s": round(elapsed, 3),
                    "remaining_s": round(max(0.0, remaining), 3),
                }
            )
            continue

        bundle_dir = out_dir / _slug(target)
        cmd = [
            sys.executable,
            str(EXPORTER),
            str(target),
            "--steps",
            str(args.steps),
            "--output-dir",
            str(bundle_dir),
        ]
        if not args.skip_hf:
            cmd.extend(["--hf-repo", args.hf_repo])

        step_start = time.monotonic()
        status = "ok"
        payload: dict[str, object] | None = None
        error: str | None = None
        try:
            payload = _run_json(cmd, cwd=ROOT, timeout_s=timeout_s)
        except subprocess.TimeoutExpired:
            status = "timed_out"
            error = f"timed out after {timeout_s:.1f}s"
        except subprocess.CalledProcessError as exc:
            status = "failed"
            error = exc.stderr.strip() or exc.stdout.strip() or str(exc)

        record: dict[str, object] = {
            "step": label,
            "kind": "export",
            "target": str(target),
            "status": status,
            "timeout_s": round(timeout_s, 3),
            "duration_s": round(time.monotonic() - step_start, 3),
        }
        if payload is not None:
            record["bundle_dir"] = payload.get("bundle_dir")
            record["default_hf_path"] = payload.get("default_hf_path")
            record["stats"] = payload.get("stats")
            if "hf" in payload:
                record["hf"] = payload["hf"]
        if error:
            record["error"] = error
        records.append(record)

    elapsed = time.monotonic() - started
    remaining = args.budget_seconds - elapsed
    if remaining > 5.0:
        queue_timeout = _step_timeout(remaining, 0.0, 30.0)
        step_start = time.monotonic()
        status = "ok"
        error = None
        try:
            _run_text(
                [
                    sys.executable,
                    str(QUEUE_EMITTER),
                    "--include-commands",
                    "--parallel",
                    "-j",
                    str(args.queue_jobs),
                    "--write-batch-files",
                    str(queue_dir),
                ],
                cwd=DASHI_ROOT,
                timeout_s=queue_timeout,
            )
            if args.render_first_pair:
                _run_text(
                    [
                        sys.executable,
                        str(QUEUE_RENDERER),
                        str(queue_dir / "offline-heavy-by-pair" / "first.json"),
                        "--format",
                        "script",
                        "--out",
                        str(queue_script),
                    ],
                    cwd=DASHI_ROOT,
                    timeout_s=min(10.0, queue_timeout),
                )
        except subprocess.TimeoutExpired:
            status = "timed_out"
            error = f"timed out after {queue_timeout:.1f}s"
        except subprocess.CalledProcessError as exc:
            status = "failed"
            error = exc.stderr.strip() or exc.stdout.strip() or str(exc)

        record = {
            "step": "Layer2QueueGeneration",
            "kind": "queue",
            "status": status,
            "timeout_s": round(queue_timeout, 3),
            "duration_s": round(time.monotonic() - step_start, 3),
            "queue_dir": str(queue_dir),
        }
        if args.render_first_pair and status == "ok":
            record["first_pair_script"] = str(queue_script)
        if error:
            record["error"] = error
        records.append(record)
    else:
        records.append(
            {
                "step": "Layer2QueueGeneration",
                "kind": "queue",
                "status": "skipped_budget",
                "queue_dir": str(queue_dir),
            }
        )

    summary = {
        "budget_seconds": args.budget_seconds,
        "steps": args.steps,
        "hf_repo": None if args.skip_hf else args.hf_repo,
        "out_dir": str(out_dir),
        "total_duration_s": round(time.monotonic() - started, 3),
        "records": records,
    }
    summary_path = out_dir / "window-summary.json"
    summary_path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
