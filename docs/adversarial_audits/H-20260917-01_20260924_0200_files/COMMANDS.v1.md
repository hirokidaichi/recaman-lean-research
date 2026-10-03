# Commands v1

- Auditor cwd: `/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`
- Audit output: `/tmp/recaman-weekly-audit-20260924-0200-sol`
- Start clock: `2026-09-24 02:03:58 JST (+0900)`
- HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`
- Repository mode: read-only. No stage, commit, gate edit, protected-claim edit, or research-source edit.

Read-only commands used before this record are the `date`, `pwd`, `git rev-parse HEAD`,
`git status --short`, `wc -l`, `cat`, `sed -n`, `rg -n`, `find`, `tail`, and `ps` calls described
in `AUDIT_REPORT.v1.md`. Their direct terminal output informed the audit; the decisive raw checks
below are separately persisted.

Planned persisted checks:

1. `python3 source/inventory_check.py`
   - cwd: audit directory
   - timeout: 30 seconds
   - stdout/stderr/exit: `raw/inventory_check.*`
   - source prehash: `prehash/INVENTORY_CHECK_PRE_RUN.sha256`
2. `shasum -a 256 -c prehash/REPO_TARGETS.sha256`
   - cwd: repository root
   - timeout: 30 seconds
   - stdout/stderr/exit: `raw/repo_targets_verify.*`
3. Prior audit manifest verification, without rerunning their mathematical/Lean commands:
   - `shasum -a 256 -c SHA256SUMS` in each archived 01:00/01:30 audit directory
   - timeout: 30 seconds each
   - outputs: `raw/prior_0100_manifest.*`, `raw/prior_0130_manifest.*`

Lean validation policy: no Lean command is newly run in this inventory slot. The current source
hashes are compared with the hashes audited in the 01:00/01:30 packets. Their saved results were:
`report_vacuity.py --all` 0/21 and 0/13, lint 20/21 and 13/13, and `./scripts/check.sh`
exit 0 with 392 jobs and 2,572 declarations. These are prior same-source results, not current runs.
