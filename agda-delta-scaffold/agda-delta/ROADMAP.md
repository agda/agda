# agda-delta prioritized roadmap

## Current priority order

1. Add richer goal/span attribution beyond the current goal-list parser contract.
2. Harden interaction lifecycle and failure signaling.
3. Add dedicated multi-hole regression fixtures for promotion targeting.
4. Preserve deterministic project traversal and trace-learning semantics.
5. Make constraints, invariants, preconditions, and postconditions explicit on canonical surfaces.

## Constraints

- Learned ranking is advisory only.
- Agda is the only acceptance boundary.
- Project traversal and candidate ranking must be deterministic for fixed inputs and fixed trace data.
- Guard stops must be explainable from recorded state.

## Invariants

- Proposal -> replay -> promote remains a strict one-way boundary.
- `solve_project` uses all-files-success semantics: one file failure makes the project result fail.
- `solve_order` is stable for a fixed project tree and falls back deterministically when cycles remain.
- Empty trace history must not destabilize candidate ranking.

## Preconditions

- `agda` must be installed and support `--interaction-json`.
- Project mode requires an existing root containing at least one `.agda` file.
- Trace and index files must be writable if persistence is enabled.
- Goal extraction assumes Agda emits JSON interaction responses matching the current payload contract.

## Postconditions

- Every run records enough trace data to explain the project/file outcome.
- Every run writes trace data to an isolated per-run sink unless an explicit trace path is requested.
- Isolated trace files can be summarized without manual JSONL inspection.
- Every run emits a live witness bundle with canonical `agda_trace.jsonl` and codec-stable `zkperf_sample_trace.json` surfaces, plus compact/reconstruction stats and an Agda-specific machine-witness sidecar.
- Every run emits stable run-level RSS summaries in `stats.json` and `manifest.json`, derived from emitted trace rows.
- When `AGDA_DELTA_RSS_MB_BUDGET` is set, every run also records whether peak RSS crossed the configured budget.
- HF publication must fail closed when `roundtrip_equal` is not exact.
- A narrow regression command must exist for the live bundle contract so exact round-trip drift is caught before publish.
- Failure to start or keep the interaction process alive is surfaced as an explicit runtime failure.
- Project scans either return a deterministic ordered file list or fail explicitly on missing inputs.
- Ranking returns a deterministic order even when no history exists.
- Promotion is tied to the selected goal identity and fails explicitly when goal metadata is unavailable.
- Accepted replay removes the targeted goal id from the post-replay goal set.

## Deferred work

- Broader protocol coverage beyond the current load/give/replay loop.
- Hole-bearing examples and protocol-focused regression tests.
- Richer goal parsing and more complete Agda interaction protocol support.
