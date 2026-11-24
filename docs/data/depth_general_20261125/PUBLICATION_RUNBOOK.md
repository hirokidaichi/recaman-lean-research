# Nov25 finalized snapshot publication

This is a concrete execution plan, NOT proof that publication or120minutes is complete. Only owned docs/evidence are staged. Normal origin/main push, enabled .githooks, individual authorized RECAMAN_ALLOW_BURST=1 on the validated snapshot commit. No new Lean or gate/workflow changes. Preserve foreign Nov07 journal and every frozen prior-day byte.

All commands below run in `/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`. Execute each DEPENDENT command only AFTER observing the previous success; do not repeat H04's shell-continued-after-freeze-failure mistake.

1. Actual clock/checkpoint to handoff at/after07:45; no new math. All20math+5guard workers already have wait4 completion receipts. Confirm exact metadata/owned paths/CI scope before stop.
2. Target REAL journal stop07:57:20 (advanced from07:58:20 after reviewing the two enabled-hook commits, two normal pushes/remote checks and bounded CI reads), before08:00:
   `python3 scripts/research_session.py stop --session b0dc7157-d226-442b-9e58-e4de75cf1b6a --note <actual reason>`.
   A late unconfirmed clock jump must be recovered as GAP, not credited by an ordinary stop. Do not rerun start or alter historical journals.
3. `python3 docs/data/depth_general_20261125/finalize_work.py` writes exact closed-journal values/phase allocation/cards/frontier/tracker/final brief. Waiting13.202 excluded; no post-stop publication time added.
4. `python3 docs/data/depth_general_20261125/audit_snapshot.py --final` verifies all155 frozen prior-day paths, foreign hash, exact new rows/current paper/source/card/receipt versions, AST/text/ownership, and finalized journal. It writes explicit OWNED_PATHS and reviewed SHA256 content. No math/Lean rerun.
5. `python3 docs/data/depth_general_20261125/publish_snapshot.py` verifies remote/HEAD/hooks/empty index, adds ONLY explicit paths, checks staged content and every stage0 blob, commits with daily snapshot flag and normal-pushes exact SHA. Rechecks ls-remote equality. Saves snapshot SHA/push proof.
6. `python3 docs/data/depth_general_20261125/observe_ci.py` reads actual PUSH workflow/check runs for that SHA. The connected workflow wrapper is PR-only, so this bounded read uses gh. Baseline CI's lost-runner failure is separate; a new run is not called successful while pending/unobserved.
7. `python3 docs/data/depth_general_20261125/publish_receipt.py` commits ONLY DAILY and exact publication/CI receipts, normal-pushes final SHA and confirms ls-remote. Self-SHA/status are written outside repo to `/tmp/recaman-20261125-final-publication.json`/`.log` and reported in chat.
8. If deadline permits, read final SHA CI once; otherwise explicitly unconfirmed. Final Japanese daily report contains work time/shortfall, evidence/scopes, local/general/streak/next, failures, DAILY/journal links, both SHAs/branch/remote/CI/unsaved targets. Exactly one heartbeat NOTIFY block, then required memory citation.

Every publication subprocess has a wall/deadline margin and kills only its own group on timeout. If a step fails, preserve local results/commit and exact error; no force, no empty retry commit, no hook bypass, no publication after08:00. Remote updates must not be overwritten. Current preflight fetched origin/main equals baseline SHA, so no merge is needed; if it advances, stop the automatic publisher and review/integrate safely within the remaining authorized window, or record the preserved unpublished snapshot for the next window.

The earlier stop target reserves concrete publication margin; it is not a confirmed stop or120-minute completion. The exact final journal will record the resulting shortfall, excluding waiting/start delay and all post-stop publication time. Do not keep a work interval open during the commits merely to claim120 minutes.
