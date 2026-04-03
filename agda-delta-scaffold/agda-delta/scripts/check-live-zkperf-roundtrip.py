#!/usr/bin/env python3
"""Run a bounded live zkperf export and fail unless the bundle round-trips exactly."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
EXPORTER = ROOT / "scripts" / "export-zkperf-agda.py"


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def main() -> None:
    parser = argparse.ArgumentParser(description="Check that a live agda-delta zkperf bundle round-trips exactly.")
    parser.add_argument(
        "--file",
        default=str(ROOT / "testdata" / "span" / "SpanTarget.agda"),
        help="Agda file to export",
    )
    parser.add_argument("--steps", type=int, default=2)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=ROOT / "out" / "check-live-zkperf-roundtrip",
        help="Bundle output directory",
    )
    args = parser.parse_args()

    proc = subprocess.run(
        [
            sys.executable,
            str(EXPORTER),
            str(Path(args.file).resolve()),
            "--steps",
            str(args.steps),
            "--output-dir",
            str(args.output_dir),
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    result = json.loads(proc.stdout)
    stats = result["stats"]
    if stats.get("roundtrip_equal") is not True:
        raise SystemExit("live zkperf bundle failed exact round-trip check")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
