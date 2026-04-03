# agda-delta

Incremental Agda experimentation scaffold with:
- deterministic acceptance boundary
- Δ-cone scheduler
- divergence/cycle guards
- goal index
- rewrite DB
- autonomous prover loop
- project-level file graph traversal
- multi-goal prioritisation
- deterministic learning from trace history

## Prioritized roadmap
- Emit live `zkperf` witness artifacts from the runtime path rather than reconstructing them after the run.
- Harden interaction lifecycle and failure signaling.
- Add dedicated multi-hole regression fixtures for promotion targeting.
- Preserve deterministic project traversal and advisory trace-learning semantics.
- Keep constraints and contracts explicit on canonical surfaces.

Details live in [`ROADMAP.md`](ROADMAP.md).

## Constraints
- Learned/neural components are advisory only.
- Agda remains the deterministic truth/acceptance engine.
- Proposal -> replay -> promote boundary must be preserved.
- Trace learning may reorder candidates, but it may not promote results on its own.

## Contracts

### Invariants
- Agda is the sole acceptance boundary.
- `solve_project` uses all-files-success semantics.
- Project traversal and candidate ordering are deterministic for fixed source and trace inputs.
- Guard stops must be explainable from recorded state.

### Preconditions
- `agda` is installed and supports `--interaction-json`.
- `--project` points to an existing root containing `.agda` files.
- `data/` is writable when trace or index persistence is active.
- Goal parsing depends on the current Agda JSON interaction payload shape.

### Postconditions
- Runs emit trace data sufficient to explain project/file outcomes.
- Each CLI run writes to its own trace file by default, or to an explicit `--trace-path` when supplied.
- Each CLI run also emits a run-scoped live witness bundle with codec-stable `zkperf_sample_trace.json`, plus `agda_trace.jsonl`, `agda_machine_witness.json`, `compact.json`, `roundtrip.json`, `stats.json`, and `manifest.json`.
- `stats.json` and `manifest.json` expose stable run-level RSS summaries derived from emitted trace rows.
- Optional environment budget `AGDA_DELTA_RSS_MB_BUDGET` marks bundle-level memory nonconformance through `rss_budget_mb` and `rss_budget_exceeded`.
- Interaction startup failure is surfaced explicitly.
- Ranking remains deterministic under cold-start or sparse trace history.
- Promotion targets the selected goal identity, not a heuristic-first hole position.
- Accepted promotion requires disappearance of the targeted goal id after replay.
- Accepted and replayed attempts carry goal ranges sourced from Agda's interaction metadata.
- The scaffold may stop without promotion, but it must not silently cross the acceptance boundary.

## Current implementation status
- `autoprove.py` supports single-file runs and `--project` traversal.
- `file_graph.py` scans `.agda` files and solves them in import/dependency order.
- `goal_index.py` can rebuild a lemma index from a whole project tree.
- `learning.py` ranks candidates from prior trace outcomes using deterministic sorting.
- `trace_summary.py` summarizes isolated run traces for operator review.
- `scripts/export-zkperf-agda.py` is a thin wrapper over the live runtime witness bundle and can hand that bundle off to the sibling `zkperf` HF publisher.
- `scripts/export-zkperf-agda.py` derives stable HF dataset paths from the target plus `run_id` when no explicit HF path is supplied.
- `scripts/check-live-zkperf-roundtrip.py` is the narrow regression gate for the live `zkperf` bundle contract.
- The refine/replay path replays real `Cmd_give` commands through Agda and promotes only on replay-confirmed state change in a shadow workspace.
- Promotion now targets the selected goal identity through Agda's native JSON goal/range metadata.
- Trace records carry before/after goal-id sets and restart/mutation facts for accepted and rejected replay attempts.
- Trace records are run-scoped through `run_id` and isolated trace paths.
- Live witness bundles keep the `zkperf` sample-trace surface codec-stable and write richer Agda-specific state-machine annotations to `agda_machine_witness.json`.
- Live witness bundles also summarize memory telemetry at bundle level through RSS fields in `stats.json` and `manifest.json`.
- When `AGDA_DELTA_RSS_MB_BUDGET` is set, live witness bundles also expose whether peak RSS exceeded that threshold.
- HF publication refuses bundles whose `zkperf` sample trace does not round-trip exactly.

## Architecture
- Whole-system metasystem view: [`docs/architecture/agda-delta-metasystem.puml`](docs/architecture/agda-delta-metasystem.puml)
- Canonical control flow:
  - `file_graph.py` orders project files
  - `autoprove.py` orchestrates solve steps
  - `scheduler.py`, `guards.py`, `goal_index.py`, `rewrite_db.py`, and `learning.py` advise candidate choice
  - `agda_interact.py` is the deterministic interaction boundary
  - `zkperf_live.py` projects the live runtime stream into `zkperf`-style witness artifacts

## Run
```bash
python -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
python -m agda_delta.autoprove examples/Test.agda
python -m agda_delta.autoprove --project examples
python -m agda_delta.autoprove testdata/span/SpanTarget.agda --trace-path data/manual-span-target.jsonl
python -m agda_delta.autoprove testdata/span/SpanTarget.agda --zkperf-dir out/live-span-target
python -m agda_delta.trace_summary data/manual-span-target.jsonl
python3 scripts/export-zkperf-agda.py testdata/span/SpanTarget.agda --output-dir out/zkperf-span-target
python3 scripts/export-zkperf-agda.py testdata/span/SpanTarget.agda --hf-repo introspector/zkperf
python3 scripts/check-live-zkperf-roundtrip.py
```
