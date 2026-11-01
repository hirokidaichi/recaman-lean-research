# Reproduction commands

All commands ran from the repository root on the frozen working tree.

```text
timeout 120 python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean
exit 0; raw log: report_vacuity.raw.log

timeout 120 python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean
exit 0; raw log: harness_lint.raw.log

timeout 600 ./scripts/check.sh
exit 1; raw log: check.raw.log
reason: module is outside the Recaman root closure: Recaman.SS2OldestPattern

timeout 420 lake env lean Recaman/ShortTightDonorAvoidance.lean
exit 0; raw log: core_lean.raw.log

timeout 180 lake build Recaman.ShortTightDonorAvoidance
exit 0; 110 jobs; raw log: core_lake_build.raw.log
post-build source hashes: source_hashes_after_build.raw.log; all three match MANIFEST.md
This dependency-aware target build is not a replacement for the failed full check.

timeout 480 lake env lean Recaman/Audit.lean
exit 0; raw log: audit_lean.raw.log

timeout 60 python3 -u experiments/issue73_20260920/short_owner_future.py
exit 0; raw log: short_owner_future.raw.log

timeout 90 python3 -u experiments/issue73_20260920/baseline_q_w.py 11
exit 0; raw log: baseline_q_w_p11.raw.log
```

No p=32/33 holdout was rerun. Its already-used daytime outputs are only hash-frozen in the
manifest. The failed full check was not repaired or rerun because the blocking module is explicitly
outside this slot's review and edit authority.
