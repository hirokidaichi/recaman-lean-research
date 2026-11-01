# 01:30 command and source record

- CWD: `/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research` (`cwd.txt`).
- Revision: `08c08565c743f39350c9b959e1df7d30aa1cae5d` (`revision.txt`); dirty worktree captured in `git_status.txt`. No stage or commit.
- Source snapshot: `ShortTightDonorAvoidance.snapshot.lean`, SHA `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`.
- Prior reproducibility script: `donor_without_minimality.snapshot.py`, SHA `ab7fa5f91bd5d31776a9ba32adc41709c1bafae218b9ac550df39521f8563499`.
- New regression source: `recheck.py`; `recheck_v1.py`, `recheck_v2.py` are **post hoc reconstructed** source versions, not source files preserved at their original execution time. SHA values in `SHA256SUMS` after freeze. No random seed; all 2048 length-11 words are enumerated exactly, with no cap. Historical p13/14 cycles are exhaustive for those periods, not fresh holdout.

| Command / argv (all in CWD) | stdout | stderr | Exit | Bound |
| --- | --- | --- | ---: | --- |
| `python3 docs/data/issue73_20260923/slot0130/recheck_v1.py` | `recheck_v1.stdout` | `recheck_v1.stderr` | 1, incorrect prefix3 expectation | immediate |
| `python3 docs/data/issue73_20260923/slot0130/recheck_v2.py` | `recheck_v2.stdout` | `recheck_v2.stderr` | 1, incorrect phase0 expectation | immediate |
| `python3 docs/data/issue73_20260923/slot0130/recheck.py` | `recheck.jsonl` | `recheck_final.stderr` | 0 | immediate |
| `python3 -u experiments/issue73_20260920/donor_without_minimality.py --mode local` | `old_local.jsonl` | `old_local.stderr` | 0 | immediate |
| `python3 -u experiments/issue73_20260920/donor_without_minimality.py --mode holdout` | `old_holdout.jsonl` | `old_holdout.stderr` | 0 | completed before freeze |
| `python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean` | `vacuity.log` | combined into same log | 0 | immediate |
| `python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean` | `lint.log` | combined into same log | 0 | immediate |
| `lake env lean docs/data/issue73_20260923/slot0130/diagnostic.lean` | `diagnostic.stdout` | `diagnostic.stderr` | 0 | immediate |
| `./scripts/check.sh` | `check.stdout` | `check.stderr` | 0 | deadline monitored, completed before freeze |
| `python3 docs/data/issue73_20260923/slot0130/recheck.py` after `recheck_pre_run.sha256` capture | `recheck_final_verified.jsonl` | `recheck_final_verified.stderr` | 0 | immediate |

The first checker invocation was originally on `recheck.py` at the v1 content;
its unmodified original stderr is `recheck.stderr`. The second was originally
on `recheck.py` at the v2 content; its unmodified original stderr is
`recheck_after_fix.stderr`. **The exact source files were not captured before
those original runs.** The versioned source files are reconstructed from the
final version by restoring the old assertion lines and reproduce the failures
in `recheck_v1.stderr` and `recheck_v2.stderr`. Treat the absent original
pre-run source SHA as a provenance limitation. Both are checker bugs, not
repairs of the mathematical statement. For the final checker, the pre-run SHA
is `0d929f6cc065a90aef2acdd9f8cd2b7db782535cd079ca226c7ef9d6abc5e176`
in `recheck_pre_run.sha256`; the exact argv is in the last table row, exit 0,
and raw output in `recheck_final_verified.jsonl` and `.stderr`. The previous daytime Lean 2-bit failure is
archived in `docs/data/issue73_20260920/daytime/build_nonminimal_local.log`.

`cmp` between prior and rerun local JSONL and between prior and rerun p13/14
JSONL exited 0 (byte equality). The newer output is a reproducibility check
of consumed known data. No new holdout, new global exploration or new Lean
research theorem was performed.

All operations were monitored against the 01:50 prohibition and 01:55 hard
end. The commands were complete before freeze; no OS-level timeout wrapper
was needed for these observed short runs. Diagnostic `#check` and `#print
axioms` in `diagnostic.lean` are read-only declarations, not new theorems.
