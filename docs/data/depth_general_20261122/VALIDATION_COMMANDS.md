# Recorded validation and publication commands

Run from the repository root. These are provenance records, not instructions to restart completed mathematical searches or STOPPED Lean jobs. Exact worker argv and resource limits are in their launch/result receipts; protocol files freeze the proposed predicates and discovery/parameter-control split before launch.

Static validation completed successfully and is recorded in `validation-*.json` and matching logs:

```text
bash scripts/check_module_architecture.sh
bash scripts/check_research_registry.sh
python3 viewer/gen_manifest.py --check
make brief
```

The registry check retains G1-G5, protected labels and static G6 definition locks. No new adopted Lean file exists, so these results do not claim a new full Lean build. The fresh finite certificate's failed command, its scratch source hash and complete diagnostics are in `local-m4-attempt1-result.json` and its log. No retry was made, and the quarantined `.lean.txt` was never renamed into the library.

Owned-source and final-journal audit:

```text
python3 docs/data/depth_general_20261122/validate_snapshot.py
python3 scripts/research_session.py stop --session 45f3710c-fdb7-4f12-9cb5-4071951492ef --note <actual completion reason>
python3 docs/data/depth_general_20261122/finalize_work.py
python3 docs/data/depth_general_20261122/validate_snapshot.py --final
```

The finalizer is single-use and requires a stopped journal. Its later execution is recorded by the finalized summary; a command shown here is not proof it ran. Checkpoints belong to the same parent session and are not independent daily cycles.

After07:45 and only after final validation, `publish_snapshot.py` uses the explicit allowlist, verifies an empty foreign index, preserves the11/07 journal hash, checks unchanged origin/main, stages only owned paths and runs enabled hooks. The user-approved `RECAMAN_ALLOW_BURST=1` is set only for that individual snapshot commit command. It pushes the resulting exact commit SHA normally, never force-pushes, and checks `git ls-remote origin refs/heads/main`.

Hosted CI is read after the verified push. Prefer the connected GitHub GET tool for the exact snapshot SHA's workflow/check collections; `observe_ci.py` provides a bounded read-only `gh api` fallback. An empty response, pending run or read error is recorded explicitly and never promoted to success. `publish_receipt.py` saves the observed snapshot receipt in one further docs-only commit and normal push; its own SHA and final remote comparison go to `/tmp/recaman-20261122-final-publication.json` and chat.

No `git add -A`, `git add .`, force push, hook disabling, protected edit, old-day time backfill, or failed Lean adoption is authorized by these records.
