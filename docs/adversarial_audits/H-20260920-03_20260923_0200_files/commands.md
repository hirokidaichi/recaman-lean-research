# Independent H-03 audit command record

- cwd: `/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`
- HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`
- Seed: none; exhaustive deterministic enumeration. No cap was reached in completed runs.
- The frozen repo source, card, and original experiment are in `frozen/` with SHA-256 values in `audit_report.md`. All generated source SHA-256 values below were recorded before execution and remained unchanged.
- Every command below redirected stdout and stderr to `runs/<name>.stdout` and `runs/<name>.stderr`. Output/stderr are retained even for the interrupted command.

| Name | Exact argv before redirection | Source SHA-256 | Timeout | Exit |
|---|---|---|---:|---:|
| independent_p1_12_p15 | `gtimeout 90s python3 -u /tmp/recaman-audit-20260923-0200-sol/independent_prefix_check.py --periods 1 2 3 4 5 6 7 8 9 10 11 12 15` | `b35c09ec1b8bb345a6abafe515a23832f52c13f4e4d761afe1bfcdaae39bd236` | 90s | 0 |
| controls | `gtimeout 10s python3 -u /tmp/recaman-audit-20260923-0200-sol/prefix_controls.py` | `21ba33bcaeb9419b26ec12de791d05e3d27c70189c3ee47bdfd5ed79d56b4847` | 10s | 0 |
| literal_eval | `gtimeout 60s lake env lean /tmp/recaman-audit-20260923-0200-sol/prefix_literal_eval.lean` | `6194f9a1ff5e64e518dbdb041385376614d0064e9886f72094a5419a2c0935d3` | 60s | 0 |
| diagnostic | `gtimeout 90s lake env lean /tmp/recaman-audit-20260923-0200-sol/prefix_diagnostic.lean` | `43d1a40faaef9032be8854b8789ef1e4ec3415197de54da1edc26714aa7d0217` | 90s | 0 |
| vacuity | `gtimeout 90s python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean` | script `9047ec7d616cf490e91c19d048072e3a799e58884b173aa4cac9a1202dd3a6ac`, target `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85` | 90s | 0 |
| lint | `gtimeout 90s python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean` | script `e07f50f2696a28ffc441ff2d99675bd8d8b4389ea0717a88833259adc6ca1107`, target same | 90s | 0 |
| check | `gtimeout 180s ./scripts/check.sh` | script `38a5f90fa92a9a73fb54a69ffda5e34095c7bfe4fd6c70674f11148b1a26e536`, target same | 180s | 0 |
| writer_p4_control | `gtimeout 10s python3 -c 'import sys; sys.path.insert(0,"/tmp/recaman-audit-20260923-0200-sol"); from independent_prefix_check import p2,window,neighborhood; c=tuple(x=="A" for x in "AAAS"); print(len(c),c[2],p2(window(c,2,3)),p2(window(c,2,4)),sorted(neighborhood(c,[(2,3)])),sorted(neighborhood(c,[(2,4)])))'` | independent checker hash above | 10s | 0 |
| writer_p9_control | `gtimeout 10s python3 -c 'import sys; sys.path.insert(0,"/tmp/recaman-audit-20260923-0200-sol"); from independent_prefix_check import p2,window,neighborhood; c=tuple(x=="A" for x in "ASAAASASS"); print(len(c),c[4],p2(window(c,4,3)),p2(window(c,4,7)),sorted(neighborhood(c,[(4,3)])),sorted(neighborhood(c,[(4,7)])))'` | independent checker hash above | 10s | 0 |
| independent_p13_14_16_17 | `gtimeout 90s python3 -u /tmp/recaman-audit-20260923-0200-sol/independent_prefix_check.py --periods 13 14 16 17` | checker hash above | 90s | 0; unplanned exploratory raw, not accepted evidence |
| independent_p18_19 | `gtimeout 90s python3 -u /tmp/recaman-audit-20260923-0200-sol/independent_prefix_check.py --periods 18 19` | checker hash above | 90s | 130, interrupted on parent instruction before a period result; no inference |

The original writer replay and comparison commands, including original source and raw file hashes, are independently documented in `docs/data/issue73_20260923/slot0200/commands.md`. I read and verified that packet rather than rerunning the same writer commands. The writer's `SHA256SUMS` returned 25/25 OK on final inspection; its final proposed-card SHA is in `audit_report.md`.
