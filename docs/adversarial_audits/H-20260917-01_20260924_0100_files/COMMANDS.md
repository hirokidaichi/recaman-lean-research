# Independent command ledger

Common cwd: `/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`.
All times JST on 2026-09-24. stdout, stderr, and numeric exit files are in this directory.

| Time | Shell argv | Timeout | Exit | stdout/stderr |
|---|---|---:|---:|---|
| 01:05 | `python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean` | short command; no shell timeout | 0 | `vacuity.stdout`, `vacuity.stderr` |
| 01:05 | `python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean` | short command; no shell timeout | 0 | `lint.stdout`, `lint.stderr` |
| 01:05 | `timeout 120 ./scripts/check.sh` | 120s | 0 | `check.stdout`, `check.stderr` |
| 01:06 | `python3 /tmp/recaman-weekly-audit-20260924-0100-sol/independent_controls.py` | fixed examples; no shell timeout | 0 | `independent_controls.stdout`, `independent_controls.stderr` |
| 01:10 | `timeout 120 python3 -c 'from experiments.issue73_20260910.two_ss.classify_and_charge import periodic_scan; r=periodic_scan(16,64); print(next(x for x in r["collisions"] if x[0]=="ss2_oldest_collision"))'` | 120s | 0 | `e133_replay.stdout`, `e133_replay.stderr` |
| 01:11 | `timeout 120 python3 /tmp/recaman-weekly-audit-20260924-0100-sol/independent_controls.py` | 120s | 0 | `independent_controls.v2.stdout`, `independent_controls.v2.stderr` |
| 01:13 | `timeout 120 python3 /tmp/recaman-weekly-audit-20260924-0100-sol/independent_controls.v1.reconstructed.py` | 120s | 0 | `independent_controls.v1.reconstructed.replay.stdout`, `.stderr` |
| 01:14 | `timeout 120 sh -c 'cd docs/data/issue73_20260924/slot0100 && sha256sum -c SHA256SUMS'` | 120s | 0 | `writer_manifest_verify.stdout`, `.stderr` (52/52 OK) |
| 01:14 | final HEAD/hash/status/process snapshot | short command; no shell timeout | 0 | `final_state.stdout`, `.stderr` |
| 01:14 | byte comparison of each full-card proposal with `original + LF + live_ready append` | short command; no shell timeout | 0 | `full_composition.stdout`, `.stderr` |

The target Lean source SHA was recorded in `shorttight.sha256`. New helper v1/v2 SHA was recorded
before each run in `independent_controls.pre.sha256` and `independent_controls.v2.pre.sha256`.
The E-133 existing source SHA was recorded before replay in `e133_source.pre.sha256`.

The v1 source was not retained before the v2 edit. It was reconstructed afterward from the exact
source displayed in the preceding tool output. Its SHA matches the v1 pre-run SHA, and its replay
stdout matches the original v1 stdout byte-for-byte. See `AUDIT_REPORT.md` for the non-erasure note.
