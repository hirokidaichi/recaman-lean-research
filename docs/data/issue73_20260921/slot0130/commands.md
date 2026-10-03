# Commands and outcomes

All commands ran from the repository root on 2026-09-21 JST with bounded execution.

```text
date '+%Y-%m-%d %H:%M:%S %Z'
start: 2026-09-21 01:33:37 JST

git rev-parse HEAD
08c08565c743f39350c9b959e1df7d30aa1cae5d

bash scripts/check_module_architecture.sh
before edit: exit 1 in the preserved 01:00 log, SS2OldestPattern outside root closure
after edit: exit 0, root reaches 389/389 and 110 import contracts pass

timeout 600 ./scripts/check.sh
exit 0; check_after_root_import.raw.log
392 build jobs; 2572 audited declarations; final pass line present

timeout 600 ./scripts/check.sh
exit 0; check_after_e359_sync.raw.log
fresh run after the prose-only E-359 audit synchronization; 392 jobs and 2572 audit reports pass

timeout 600 ./scripts/check.sh
exit 0; check_after_e359_sync_and_provenance.raw.log
fresh run after the reviewer-required E-359 sync provenance note; same 392/2572 pass

timeout 120 python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean
exit 0; report_vacuity.raw.log; 0/21 flagged

timeout 120 python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean
exit 0; harness_lint.raw.log; 20/21 substantive

line-by-line comparison of core_signatures_verbatim.txt against file:line source
exit 0; statement_comparison.raw.log; all 82 lines exact

python3 scripts/harness_gate.py --audit-template E-999
exit 1; expected precondition failure: ID absent from EVIDENCE_REGISTRY.tsv
```

No p32/33 holdout, p<=11 census, proper-U probe, or mathematical checker was rerun. No staging or
commit was performed.
