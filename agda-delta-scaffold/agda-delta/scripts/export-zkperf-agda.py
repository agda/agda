#!/usr/bin/env python3
"""Run agda-delta and return the live-emitted zkperf witness bundle."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from uuid import uuid4


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agda_delta.autoprove import solve_file, solve_project


def _default_zkperf_root() -> Path:
    return Path(__file__).resolve().parents[4] / "zkperf"


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, payload: dict[str, object]) -> None:
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _stable_hf_label(file: str | None, project: str | None) -> str:
    if project:
        root = Path(project).resolve()
        return f"project-{root.name}"
    assert file is not None
    target = Path(file).resolve()
    parent = target.parent.name
    stem = target.stem
    return f"file-{parent}-{stem}"


def main() -> None:
    parser = argparse.ArgumentParser(description="Export agda-delta runs as live zkperf witness bundles.")
    parser.add_argument("file", nargs="?", help="Path to Agda file")
    parser.add_argument("--project", help="Path to a project root with .agda files")
    parser.add_argument("--steps", type=int, default=50)
    parser.add_argument("--output-dir", type=Path, help="Output bundle directory")
    parser.add_argument("--zkperf-root", type=Path, default=_default_zkperf_root())
    parser.add_argument("--hf-repo", help="Optional HF dataset repo, for example introspector/zkperf")
    parser.add_argument("--hf-path", help="Optional path inside the HF dataset")
    args = parser.parse_args()

    if bool(args.file) == bool(args.project):
        parser.error("provide exactly one of FILE or --project")

    run_id = uuid4().hex
    target_label = args.project or args.file
    assert target_label is not None
    safe_label = Path(target_label).stem if args.file else Path(target_label).name
    output_dir = args.output_dir or (ROOT / "out" / f"zkperf-agda-{safe_label}-{run_id[:8]}")
    output_dir.mkdir(parents=True, exist_ok=True)

    solved = (
        solve_project(
            args.project,
            max_steps=args.steps,
            trace_path=str(output_dir / "trace.jsonl"),
            run_id=run_id,
            zkperf_dir=str(output_dir),
        )
        if args.project
        else solve_file(
            args.file,
            max_steps=args.steps,
            trace_path=str(output_dir / "trace.jsonl"),
            run_id=run_id,
            zkperf_dir=str(output_dir),
        )
    )

    manifest = _load_json(output_dir / "manifest.json")
    stats_payload = _load_json(output_dir / "stats.json")
    default_hf_path = f"runs/agda/{_stable_hf_label(args.file, args.project)}-{run_id}"
    manifest["solved"] = solved
    manifest["steps"] = args.steps
    manifest["default_hf_path"] = default_hf_path
    _write_json(output_dir / "manifest.json", manifest)

    result: dict[str, object] = {
        "bundle_dir": str(output_dir),
        "manifest": manifest,
        "stats": stats_payload,
        "default_hf_path": default_hf_path,
    }

    if args.hf_repo:
        publisher = args.zkperf_root / "scripts" / "publish-agda-zkperf-bundle.py"
        path_in_repo = args.hf_path or default_hf_path
        upload = subprocess.run(
            [
                sys.executable,
                str(publisher),
                str(output_dir),
                "--repo",
                args.hf_repo,
                "--path-in-repo",
                path_in_repo,
            ],
            check=True,
            capture_output=True,
            text=True,
        )
        result["hf"] = json.loads(upload.stdout)

    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
