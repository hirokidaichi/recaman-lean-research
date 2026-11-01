# Exact execution record

- CWD for every command: `/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`
- HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`
- Initial, pre-append H-04 card SHA-256: `21a41d3f06948dd97cfabbcb1df880e0a86679694c79cf3aa2cb1dd85840668e`
- Target Lean SHA-256: `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`
- Parameters: known literal `SAAASSSASASASAAA`, `p=16`, `u0=15`, `B=[3]`, `lag 3=3`, inclusive full-supply cutoff `16*(16+1)=272`; no seed and no holdout.

The final run's exact argument arrays, timeout seconds, start/elapsed times,
exit codes, timeout flags, and stream hashes are in `commands.json`. Complete
stdout and stderr bytes are in each named `*.stdout` / `*.stderr` file. The
runner source is `run_checks.py`; this paragraph is an index, not a substitute
for those raw files. All seven final-run commands exited 0 without timeout:

| Name | Command | Result |
|---|---|---|
| literal | `python3 -u docs/data/issue73_20260923/slot0100/check_literal.py` | one witness; 16/16 full-U Hall subsets |
| statement_audit | `python3 -u docs/data/issue73_20260923/slot0100/audit_signatures.py` | source quote exact; existing E-360 G5 Q exact |
| vacuity | `python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean` | 0/21 flagged, module-wide |
| lint | `python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean` | 20/21 substantive, module-wide; one unrelated wrapper |
| target_build | `lake build Recaman.ShortTightDonorAvoidance` | 110 jobs successful |
| symbol | `lake env lean docs/data/issue73_20260923/slot0100/symbol_check.lean` | Q/literal/trueOldest signatures; literal axioms `[propext, Quot.sound]` |
| full_check | `./scripts/check.sh` | 392 jobs; 2572 declarations within allowed axioms |

`run_metadata.json` fixes the post-append uncommitted source hashes used in
the final run. The initial card hash above preserves the pre-append version.
This session performed two earlier successful runner executions while adding
the diagnostic symbol and statement audit steps. Their outputs were superseded
by this final complete run; there was no failed experimental version. The
recorded exact streams and `commands.json` correspond to the final run.
