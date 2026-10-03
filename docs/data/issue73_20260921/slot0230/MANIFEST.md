# Slot 0230 manifest

- Time window: 2026-09-21 02:32-02:50 JST
- Writer: `/root/sol_20260921_deletion0230`
- Independent auditor: `/root/sol_20260921_deletion_audit0230`
- Question: semantic status of existing
  `Recaman.ShortTightDonorAvoidance.short_supply_donor_deletion`
- Frozen source SHA-256:
  `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`
- HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`

## Conclusion

The exact theorem is meaningful and nonvacuous when all members of `U` satisfy the minimal
lag-3/7/11 hypotheses. It is not conclusion-assuming or vacuous. Its proof is a direct corollary of
E-360 Q, short Hall, and existing tight/slack deletion lemmas, so it supplies no new mathematical
input and merits no new registry row or E-number. It does not cover an unrestricted complete all-lag
supply set, general T6, lag 15 or larger members, positive drift, completeness provenance, or actual
orbits.

The independent auditor approved final proposed card status `PROVED-LEAN` at SHA-256
`c138c3ca29fe0971ac0b6d41480c8ebf0d790202267883a4c2a9805b937d43bb`, based on the exact existing
`Recaman/Audit.lean:2701` theorem and the semantic audit. The parent then authorized applying exactly
that approved version to the live card; its post-application hash is the same `c138c3...`.

## Files

- `candidate_packet.md`: conclusion, exact scope, dependency reduction, controls, interpretation.
- `statement_audit_draft.md`: verbatim target signature and G5-style audit.
- `control_replay.py`: exact fixed-control replay; no discovery or holdout search.
- `HYPOTHESIS_CARD_2026-09-21_SHORT_SUPPLY_DONOR_DELETION.PROVED_LEAN.proposed.md`: independently
  approved full replacement proposal for the live card.
- `HYPOTHESIS_CARD_2026-09-21_SHORT_SUPPLY_DONOR_DELETION.preapply.md`: exact initial
  `CONJECTURED` live card preserved before authorized application.
- `MANIFEST.preapply.md`, `SHA256SUMS.preapply`: pre-application packet inventories preserved.
- `correction_notes.md`: provenance corrections and final application record.
- `raw/target_signature.log`: verbatim source lines 360-391.
- `raw/target_signature.ascii_rejected.log`: preserved initial incorrectly labeled ASCII artifact.
- `raw/control_replay.command.log`, `raw/control_replay.stdout.log`: reproducible fixed controls.
- `raw/control_examples.summary.log`: hand-edited control digest, explicitly not raw.
- `raw/vacuity.log`, `raw/lint.log`: heuristic gate output.
- `raw/full_check.command.log`, `raw/full_check.combined.log`: fresh complete check capture.
- `raw/full_check.summary.log`: preserved initial incorrectly labeled excerpt, now marked summary.
- `raw/source_hash_status.log`: entry hashes and dirty-tree notice.
- `commands.md`: command list.

The live card created and then parent-authorized for promotion in this slot is
`docs/HYPOTHESIS_CARD_2026-09-21_SHORT_SUPPLY_DONOR_DELETION.md`. No existing Q/W card, registry,
frontier, proof map, Lean file, Audit file, gate, or protected claim was changed in this slot.

## Verification

- `python3 scripts/report_vacuity.py --all Recaman/ShortTightDonorAvoidance.lean`: exit 0, 0/21
  flagged; heuristic only.
- `python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean`: exit 0;
  candidate called substantive; heuristic only.
- Target source versus `raw/target_signature.log`: diff exit 0.
- Target source signature versus `statement_audit_draft.md`: diff exit 0.
- `control_replay.py` versus frozen stdout: diff exit 0.
- `timeout 180s ./scripts/check.sh`: exit 0 in 6.389 seconds; 392 jobs; 2,572 audited declarations.

## Strongest evidence

- Exact proof inspection shows only two branches: tight uses Q plus
  `deleted_hall_of_not_mem`; non-tight uses short Hall plus `deleted_hall_of_slack`.
- p8 donor-containing `U=[3,7]`, `B=[3]` and `B=[3,7]` actually remove phase 0 from
  `{0,1,4}` and retain Hall, proving deletion is not always a no-op.
- Dropping `ssCount=2` fails on the fixed p12 SS3 control: deleting phase 4 leaves two neighbors for
  three tight members.

## Failed attempts and corrections

- The first target raw converted Unicode to ASCII while claiming verbatim provenance. It was rejected,
  preserved, and replaced by source-exact output.
- The first full-check file omitted middle lines. It was relabeled summary and replaced by a fresh
  complete combined capture.
- The first fixed-control log omitted the inline source. It was relabeled summary and replaced by a
  complete replay source, source hash, command metadata, and raw stdout.
- An overbroad statement about every complete supply set was corrected: complete U is covered when all
  members are short, but unrestricted complete all-lag U is not.

## Remaining uncertainty and next decision

The general all-lag deletion problem remains open. Historical daytime independent-audit absence and
the missing first slot0100 checker source/raw are not repaired by this packet. The approved card
application is complete. No new registry row, proof-map claim, or research branch should be opened
from this corollary.
