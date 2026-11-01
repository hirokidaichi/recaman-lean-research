# Post-apply verification

Status: **PASS at 2026-09-24 02:43:29 JST**.

Required checks:

1. Live weekly report equals `source/candidates/proposed_weekly_report_full.final.md`.
2. Live main card equals `source/candidates/proposed_main_card_full.final.md`.
3. Live handoff equals `source/candidates/proposed_handoff_full.final.md`.
4. HEAD and frozen Lean/registry/frontier/proof-map hashes remain unchanged.
5. Automation remains `PAUSED`; process inspection records only current control/audit work, with no
   research computation left running.

The parent applied all three approved full files. Independent `cmp` returned 0 for all three and the
live SHA-256 values are weekly `6bbd269b...04048ac`, main card `0fd675d8...746fc8e7`, and handoff
`7a312654...d634b8fa`. HEAD remains `08c08565...ca1cae5d`; frozen Lean, registry, protected claims,
frontier, and proof-map hashes are unchanged. Exact stdout/stderr/exit and the prehashed fixed command
are in `raw/postapply.*`, `raw/postapply_time.stdout`, and `source/postapply_check.sh`.

The final targeted process output contains only the checking shell and its `rg`, not a research
computation. The writer reports completed. Root and this auditor remain active only to archive and close;
their eventual termination is left to the parent record rather than predicted here.
