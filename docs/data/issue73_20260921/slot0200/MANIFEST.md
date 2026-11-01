# Slot 0200 registration bundle

## Live-application payload

- `EVIDENCE_REGISTRY.proposed.tsv` -> `docs/EVIDENCE_REGISTRY.tsv`
- `E-360.live-ready.md` -> `docs/statement_audits/E-360.md`
- `HYPOTHESIS_CARD_2026-09-17_SHORT_TIGHT_DONOR_AVOIDANCE.proposed.md` -> Q card
- `HYPOTHESIS_CARD_2026-09-20_SHORT_OWNER_FUTURE.proposed.md` -> W card
- `CURRENT_FRONTIER.proposed.md` -> current frontier
- `PROOF_MAP.proposed.md` -> proof map
- `RESEARCH_HANDOFF_2026-09-21_SOL.proposed.md` -> handoff

The live payload changes no Lean source, gate, protected label, or central claim. The G5 says
application is pending and does not pre-assert success. Parent authorization and a post-application
independent hash/gate/full-check review remain required.

## Evidence and history

- `scope.md`, `commands.md`, `protocol_record.md`, `revision_notes.md`
- `raw/`: exact writer exits and outputs for source status, G1-G5, protected, lint, vacuity,
  audit-template, and full check
- `preapply_*`: complete input snapshots for cards, registry, frontier, proof map, and handoff
- `rejected_v1_2symbol_*`: exact rejected two-symbol metadata drafts
- `proposed_*_append.md` and `proposed_card_handoff_updates.md`: reviewable minimal append/diff text

`SHA256SUMS` is slot-relative and covers every bundle file other than itself.
