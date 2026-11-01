# Slot 0100 evidence manifest

This directory is the writer-owned 2026-09-24 01:00 JST weekly-audit packet. It contains no new
research Lean, registry change, promotion, live-card edit, exploration, or holdout.

## Drafts

- `candidate_packet.md`: bounded question, exact scope, evidence, limits, and next decision.
- `weekly_report_section_draft.md`: proposed established-results section for the weekly report.
- `proposed_main_card_append.md`: un-applied append proposal for H-20260917-01.
- `proposed_deletion_card_append.md`: un-applied append proposal for H-20260921-01.
- `proposed_main_card_append_live_ready.md`: append-only main-card text whose application remains
  conditional on the parent-confirmed independent audit.
- `proposed_deletion_card_append_live_ready.md`: append-only deletion-card text under the same
  application condition.
- `proposed_main_card_full_live_ready.md`: frozen original main card plus the corrected append,
  ready for post-application byte comparison.
- `proposed_deletion_card_full_live_ready.md`: frozen original deletion card plus the corrected
  append, ready for post-application byte comparison.
- `verbatim_statement_audit.md`: exact signatures and bidirectional semantic audit.
- `commands.md`: commands, outputs, omissions, and correction history.

## Frozen inputs

- `original_main_card_at_freeze.md`: byte copy of the live main card at entry.
- `original_deletion_card_at_freeze.md`: byte copy of the live deletion card at entry.
- `raw/ShortTightDonorAvoidance.source_snapshot.lean`: byte copy of the frozen target source.
- `raw/E-360.statement_audit_snapshot.md`: byte copy of the official G5.
- `raw/E-360.registration_audit_snapshot.md`: byte copy of the registration audit.
- `raw/deletion_audit_snapshot.md`: byte copy of the restricted-corollary audit.
- `raw/relevant_registry_rows.tsv`: exact registry rows E-069/E-133/E-240/E-345/E-360.
- `raw/original_*`: inherited original signature/control/hash logs, copied without alteration.

## Current raw checks

- `raw/precheck_identity.log`: timestamp, HEAD, and pre-check identities.
- `raw/current_verbatim_source_excerpt.log`: direct source excerpt for W/Q/deletion.
- `raw/current_ownerfamily_definition.log`: direct four-field definition excerpt.
- `raw/current_audit_prints.log`: direct Audit inclusion excerpt.
- `raw/{vacuity,lint,full_check}.{command,stdout,stderr}.log`: unedited check records.
- `raw/candidate_packet.before_parent_correction.md`: preserved first packet wording before the
  status-scope clarification.
- `raw/proposed_*before_link_correction.md`: preserved first live-ready fragments before correcting
  links from packet-relative to their eventual `docs/` card location.
- `raw/before_independent_correction/`: the complete affected draft set before narrowing the
  periodic-construction wording and spelling out the E-351 premises.
- `raw/final_identity_and_status.log`: final source identities, card `cmp`, status, and whitespace
  check results.

`SHA256SUMS` hashes every other file in this directory recursively and excludes itself.
