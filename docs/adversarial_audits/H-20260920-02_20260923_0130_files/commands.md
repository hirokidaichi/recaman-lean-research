# Independent audit command record (JST, 2026-09-23)

- CWD for repository commands: `/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`.
- Repository HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`; dirty worktree was left untouched.
- Target source SHA-256: `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`.
- Original card SHA-256: `cf7cd47ff31d451d8d242e80373fb15a95666308ed30149b33b46b45722dce02`.
- All scripts below enumerate deterministic finite sets or verify fixed literals. Seed: none. Cap: none except stated period maximum or timeout. Periods 13/14 are already consumed historical data, not a fresh holdout.
- Raw stdout/stderr is in the named `.raw.*`, `.stdout`, and `.stderr` files. This document is a command record, not a replacement for those streams.

| Approx. JST from raw-file mtime | Exact argv (all `timeout` values are wall-clock caps) | Exit | Raw output |
| --- | --- | ---: | --- |
| 01:35:26 | `timeout 180s python3 -u /tmp/recaman-audit-20260923-0130-sol/independent_check.py --maxp 14` | 0 | `independent_check.raw.jsonl`, `independent_check.stderr` |
| 01:35:52 | `timeout 90s python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean` | 0 | `vacuity.raw.log` |
| 01:35:52 | `timeout 90s python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean` | 0 | `lint.raw.log` |
| 01:35:52-01:36:02 | `timeout 180s ./scripts/check.sh` | 0 | `check.raw.log` |
| 01:36:47 | `timeout 60s python3 -u /tmp/recaman-audit-20260923-0130-sol/controls.py` | 0 | `controls.raw.jsonl`, `controls.stderr` |
| 01:37:13 | `timeout 60s lake env lean /tmp/recaman-audit-20260923-0130-sol/diagnostic.lean` | 0 | `diagnostic.raw.log` |
| 01:37:38 | `timeout 30s python3 -u /tmp/recaman-audit-20260923-0130-sol/integer_clocks.py` | 0 | `integer_clocks.raw.jsonl`, `integer_clocks.stderr` |
| 01:38:15 | `timeout 30s python3 -u docs/data/issue73_20260923/slot0130/recheck.py` | 0 | `writer_recheck.raw.jsonl`, `writer_recheck.stderr` |
| 01:38:15 | `timeout 30s python3 -u docs/data/issue73_20260923/slot0130/recheck_v1.py` | 1, expected failed assertion | `writer_recheck_v1_reproduced.stdout`, `.stderr` |
| 01:38:15 | `timeout 30s python3 -u docs/data/issue73_20260923/slot0130/recheck_v2.py` | 1, expected failed assertion | `writer_recheck_v2_reproduced.stdout`, `.stderr` |
| 01:39:40 | `timeout 30s python3 -u /tmp/recaman-audit-20260923-0130-sol/shortcut_collisions.py` | 0 | `shortcut_collisions.raw.jsonl`, `.stderr` |
| 01:40:50 | `timeout 30s python3 -u /tmp/recaman-audit-20260923-0130-sol/verify_weak_tightness.py` | 0 | `verify_weak_tightness.raw.jsonl`, `.stderr` |
| 01:40:02 | `shasum -a 256 -c docs/data/issue73_20260923/slot0130/SHA256SUMS` (first freeze) | 0 | `writer_manifest_verify.raw.log` |
| 01:41:37 | `shasum -a 256 -c docs/data/issue73_20260923/slot0130/SHA256SUMS` (post-verdict version) | 0 | `writer_manifest_v2_verify.raw.log` |
| 01:42:43 | `shasum -a 256 -c docs/data/issue73_20260923/slot0130/SHA256SUMS` (final linked card) | 0 | `writer_manifest_final_verify.raw.log` |

The independent finite script source was hashed before its first execution:
`independent_check.py` SHA-256 `58a53a271a599826d27042e19e3a237d08220c85fe2b1ce6b39a436d17665aae`.
Other pre-execution source hashes: `controls.py` `0402f3a181633f49de58454910900b4d676d5834e069670fe4c9d87a3e16579d`,
`integer_clocks.py` `fbf58c27b39a2b0ed39a7a981d0580b051888c10670b0af5db4b049771d98cd1`,
`shortcut_collisions.py` `f0fdbe6197578287cdde9e16b152a648af112df2c360f6ad325aa51e497309f6`,
`verify_weak_tightness.py` `a15f431b8f408348088606df4f765ec61f41fb30b383ad79bfbc541f52aa3915`.

The final writer `recheck.py` has a packet pre-run hash `0d929f6cc065a90aef2acdd9f8cd2b7db782535cd079ca226c7ef9d6abc5e176`; my rerun stdout is byte-identical to `recheck_final_verified.jsonl` (`cmp -s`, exit 0). Reconstructed v1/v2 reproduce the archived failure text byte-for-byte, but their original execution-time sources and SHA values were not captured. `cmp -s` of live vs writer snapshot Lean source, prior vs writer snapshot Python source, and prior vs writer-copy local and period13/14 raw data all exited 0. The first writer manifest had 35 entries, all verified, SHA-256 `6681150d21a035864f488d705f5980ce5c62a37ecf2146491a73c9271aefc0e8`; the next 37-entry version also verified, SHA-256 `2f451af5ab93993020571e8e529d132dbe9fbaf0d0608dcb5afc10104b1dd642`. The final linked-card version had 39 entries, all verified, manifest SHA-256 `f1cbb7d2f1cf6914646352531cbc9443b94ed519dfeca798e59e49b6ad338203`; final card SHA-256 `6bdbd25143c166bad26cffb6441fc8ff2baf31c767838cd8a0b5139eaeefa5a1`.
