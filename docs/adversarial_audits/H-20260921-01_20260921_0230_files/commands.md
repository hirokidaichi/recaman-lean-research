# Independent audit commands

Workdir: `/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research`

- `{ date '+%Y-%m-%d %H:%M:%S %Z (%z)'; git rev-parse HEAD; git status --short;
  shasum -a 256 Recaman/ShortTightDonorAvoidance.lean Recaman/OwnerFamilyLagEleven.lean
  Recaman/PeriodicOwnerFamilyLagEleven.lean docs/EVIDENCE_REGISTRY.tsv
  docs/PROTECTED_CLAIMS.tsv docs/HYPOTHESIS_CARD_2026-09-21_SHORT_SUPPLY_DONOR_DELETION.md
  docs/data/issue73_20260921/slot0230/candidate_packet.md
  docs/data/issue73_20260921/slot0230/statement_audit_draft.md
  docs/data/issue73_20260921/slot0230/control_replay.py
  docs/data/issue73_20260921/slot0230/HYPOTHESIS_CARD_2026-09-21_SHORT_SUPPLY_DONOR_DELETION.PROVED_LEAN.proposed.md
  docs/data/issue73_20260921/slot0230/raw/control_replay.stdout.log
  docs/data/issue73_20260921/slot0230/raw/full_check.combined.log; }`
  Timeout: tool default 10 seconds. Exit: 0. Raw: `source_state.raw.log`.
- `sed -n '363,391p' Recaman/ShortTightDonorAvoidance.lean`
  Timeout: tool default 10 seconds. Exit: 0. Raw: `target_signature.repo_snapshot.raw.log`.
- `timeout 45s python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean`
  Exit: 0. Raw: `vacuity.raw.log`.
- `timeout 45s python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean`
  Exit: 0. Raw: `lint.raw.log`.
- `timeout 120s lake env lean Recaman/ShortTightDonorAvoidance.lean`
  Exit: 0; wall time 18.94 seconds. Raw: `lean.raw.log`.
- `timeout 20s python3 /tmp/recaman-audit-20260921-0230-sol/deletion_checker.py`
  Exit: 0. Final raw: `deletion_checker.v2.raw.log`. The earlier successful, less explicit
  output is retained in `deletion_checker.raw.log` / `deletion_checker.v1.raw.log`.
- `timeout 150s ./scripts/check.sh`
  Exit: 0; wall time 6.6 seconds. Raw: `full_check.raw.log`.

The fixed checker uses no seed and no discovery or holdout range. Its only finite scan is the
declared inclusive minimal-lag scan `1 <= d <= p(p+1)` on the named fixed words.
