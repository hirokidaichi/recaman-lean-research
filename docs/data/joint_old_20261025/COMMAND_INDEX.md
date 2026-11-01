# Commands and evidence index — 2026-10-25

All commands ran from repository root. No stage/commit/push. CPU and journal elapsed are separate.

## Predeclared protocols

- [BARRIER_ONE_PROTOCOL.json](BARRIER_ONE_PROTOCOL.json): H-20261025-05
- [BARRIER_PROTOCOL.json](BARRIER_PROTOCOL.json): H-20261025-02
- [CONTEXT_PROTOCOL.json](CONTEXT_PROTOCOL.json): H-20261025-03
- [DAG_BENCH_PROTOCOL.json](DAG_BENCH_PROTOCOL.json): H-20261025-04
- [DAG_FULL_PROTOCOL.json](DAG_FULL_PROTOCOL.json): H-20261025-04
- [LAYER_FULL_PROTOCOL.json](LAYER_FULL_PROTOCOL.json): H-20261025-10
- [LAYER_PROTOCOL.json](LAYER_PROTOCOL.json): H-20261025-10
- [LINEAR_BENCH_PROTOCOL.json](LINEAR_BENCH_PROTOCOL.json): H-20261025-07
- [LINEAR_FULL_PROTOCOL.json](LINEAR_FULL_PROTOCOL.json): H-20261025-07
- [PROTOCOL.json](PROTOCOL.json): H-20261025-01
- [PRUNED_BENCH_PROTOCOL.json](PRUNED_BENCH_PROTOCOL.json): H-20261025-09
- [PRUNED_FULL_PROTOCOL.json](PRUNED_FULL_PROTOCOL.json): H-20261025-09

## Actual guarded validation jobs

- `dag-bench-checked`: `lake env lean -j1 docs/data/joint_old_20261025/dag_bench.lean`; started 2026-10-25T06:33:34.336390+09:00; wall cap 90s, process CPU cap 90s, RSS cap 4194304KiB.
  - exit 0, reason `completed`, wall 72.52162424987182s; [dag-bench-checked-result.json](dag-bench-checked-result.json), [dag-bench-checked.log](dag-bench-checked.log).
- `dag-bench-single`: `lake env lean -j1 docs/data/joint_old_20261025/dag_bench.lean`; started 2026-10-25T06:31:24.887744+09:00; wall cap 90s, process CPU cap 90s, RSS cap 4194304KiB.
  - exit 1, reason `completed`, wall 73.01704470906407s; [dag-bench-single-result.json](dag-bench-single-result.json), [dag-bench-single.log](dag-bench-single.log).
- `dag-bench`: `lake env lean docs/data/joint_old_20261025/dag_bench.lean`; started 2026-10-25T06:29:59.259187+09:00; wall cap 90s, process CPU cap 90s, RSS cap 4194304KiB.
  - exit 152, reason `completed`, wall 14.590276666916907s; [dag-bench-result.json](dag-bench-result.json), [dag-bench.log](dag-bench.log).
- `dag-fast-bench`: `lake env lean -j1 docs/data/joint_old_20261025/dag_fast_bench.lean`; started 2026-10-25T06:52:13.056359+09:00; wall cap 90s, process CPU cap 90s, RSS cap 4194304KiB.
  - exit 0, reason `completed`, wall 31.239813207881525s; [dag-fast-bench-result.json](dag-fast-bench-result.json), [dag-fast-bench.log](dag-fast-bench.log).
- `dag-fast-full`: `lake build Recaman.FourEventData`; started 2026-10-25T06:54:48.910990+09:00; wall cap 2400s, process CPU cap 2400s, RSS cap 4194304KiB.
  - exit -15, reason `process exited -15`, wall 1208.8436721670441s; [dag-fast-full-result.json](dag-fast-full-result.json), [dag-fast-full.log](dag-fast-full.log).
- `dag-full`: `lake build Recaman.FourEventData`; started 2026-10-25T06:38:07.283623+09:00; wall cap 3600s, process CPU cap 3600s, RSS cap 4194304KiB.
  - exit -15, reason `completed`, wall 966.5154822499026s; [dag-full-result.json](dag-full-result.json), [dag-full.log](dag-full.log).
- `dag-layer-bench`: `lake build Recaman.FourEventLayer8`; started 2026-10-25T07:29:07.418022+09:00; wall cap 90s, process CPU cap 90s, RSS cap 4194304KiB.
  - exit 0, reason `completed`, wall 4.869996624998748s; [dag-layer-bench-result.json](dag-layer-bench-result.json), [dag-layer-bench.log](dag-layer-bench.log).
- `dag-layer-full`: `lake build Recaman.FourEventData`; started 2026-10-25T07:30:35.526420+09:00; wall cap 900s, process CPU cap 900s, RSS cap 4194304KiB.
  - Final outcome: fixed07:45 deadline, exit-15, wall864.548117s, peak3701456KiB; [dag-layer-full-result.json](dag-layer-full-result.json). Initial certificate not supplied.
- `dag-pruned-bench-checked`: `lake env lean -j1 docs/data/joint_old_20261025/dag_pruned_bench.lean`; started 2026-10-25T07:13:26.432130+09:00; wall cap 90s, process CPU cap 90s, RSS cap 4194304KiB.
  - exit 0, reason `completed`, wall 15.076177707873285s; [dag-pruned-bench-checked-result.json](dag-pruned-bench-checked-result.json), [dag-pruned-bench-checked.log](dag-pruned-bench-checked.log).
- `dag-pruned-bench`: `lake env lean -j1 docs/data/joint_old_20261025/dag_pruned_bench.lean`; started 2026-10-25T07:12:16.573152+09:00; wall cap 90s, process CPU cap 90s, RSS cap 4194304KiB.
  - exit 1, reason `process exited 1`, wall 0.5425764580722898s; [dag-pruned-bench-result.json](dag-pruned-bench-result.json), [dag-pruned-bench.log](dag-pruned-bench.log).
- `dag-pruned-full`: `lake build Recaman.FourEventData`; started 2026-10-25T07:15:47.772685+09:00; wall cap 1200s, process CPU cap 1200s, RSS cap 4194304KiB.
  - exit -15, reason `RSS cap`, wall 560.9207523339428s; [dag-pruned-full-result.json](dag-pruned-full-result.json), [dag-pruned-full.log](dag-pruned-full.log).

## Verification entry points

`python3 scripts/harness_gate.py --lint-module <each new module>`: [final-module-lints.json](final-module-lints.json).
`python3 scripts/harness_gate.py --audit-template E-401/E-402/E-404/E-406/E-407`: literal signatures/reviewer answers in docs/statement_audits.
`python3 docs/data/joint_old_20261025/generate_layers.py --check`: deterministic source/graph comparison; not a kernel proof.
`./scripts/check.sh`: early [check-barrier-2.log](check-barrier-2.log), successful final result is [final-check-2.log](final-check-2.log); final-check.log records the corrected frontier-reference failure.
`make brief`: final-brief.log after latest frontier synchronization.

## Interpretation

Same numeric input graph is reused, never called fresh holdout. Independent graph/future/gap controls are named in each protocol.
Cancelled time files are incomplete. run_guard process CPU cap is not aggregate process-group enforcement.
Final source preservation, outcome, confirmed time and next action are in DAILY and final manifest.
