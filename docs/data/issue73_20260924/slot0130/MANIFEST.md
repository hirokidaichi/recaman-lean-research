# Slot 01:30 manifest

Writer started at `2026-09-24 01:32:23 JST`, HEAD
`08c08565c743f39350c9b959e1df7d30aa1cae5d`; originals were captured after that start.
Final packet freeze recorded at `2026-09-24 01:41:51 JST`. This directory is a draft-and-evidence packet.
It makes no live-document change and no new research claim. Independent joint-audit disposition is
recorded by the parent under `docs/adversarial_audits/H-20260920-02_20260924_0130.md`.

## Primary drafts

- `candidate_packet.md`: bounded question, acceptance/stop, claim ledger, adversarial checks, provenance.
- `weekly_report_append_draft.md`: section intended for live weekly report after approval.
- `proposed_weekly_report_full.md`: full weekly text with the opening scope paragraph corrected and append included.
- `proposed_h02_card_append.md`, `proposed_h03_card_append.md`, `proposed_h04_card_append.md`,
  `proposed_h05_card_append.md`: short live-card additions with links resolved relative to `docs/`.
- `proposed_h02_card_full.md`, `proposed_h03_card_full.md`, `proposed_h04_card_full.md`,
  `proposed_h05_card_full.md`: frozen original plus approved-form append candidate.
- `verbatim_signature_audit.md`: exact source signatures and direction/meaning audit.
- `REVIEW_STATUS.md`: independent re-audit result and the exact approved primary hashes.

## Frozen originals

- `original_h02_card_at_freeze.md`
- `original_h03_card_at_freeze.md`
- `original_h04_card_at_freeze.md`
- `original_h05_card_at_freeze.md`
- `original_weekly_report_at_freeze.md`

Each frozen original compared byte-identical to its live source at writer validation time.

## Provenance and validation

- `SOURCE_SHA256SUMS`: target Lean, live cards/report/handoff, 9/23 parent audits and independent reports.
- `commands.md`: writer-side read and validation command record, including commands explicitly not run.
- `SHA256SUMS`: relative integrity list for every packet file except itself.
- `raw/start_state.txt`: clock, cwd, HEAD, ownership boundary.
- `raw/provenance_scope.txt`: writer versus independent joint-auditor execution boundary.
- `raw/source_signature_excerpts.txt`: direct source excerpts.
- `raw/archive_verdict_excerpts.txt`: direct independent-archive verdict excerpts.
- `raw/writer_validation.txt`: compact validation result.

## Preserved superseded drafts

- `raw/*before_parent_wording.md`: version before the parent's first wording corrections.
- `raw/*before_auditor_correction.md`: version before the independent auditor's three corrections.
- `raw/card_drafts.before_live_heading_correction.md`: eight card append/full drafts before final live heading wording.

Superseded files are provenance only and must not be applied.

## Scope boundary

No new Lean, search, range extension, result registration, evidence promotion, status change, stage or commit.
No live card, live weekly report, handoff, registry, frontier, proof map, root, Audit, protected claim or gate was edited
by the writer. The writer did not rerun computational or Lean gates; current-slot independent-auditor runs are separate.
