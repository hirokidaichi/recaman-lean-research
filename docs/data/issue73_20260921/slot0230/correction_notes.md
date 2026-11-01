# Slot 0230 correction and application notes

## Provenance corrections

1. The first target raw normalized Unicode to ASCII while claiming verbatim output. The erroneous
   text is preserved in `raw/target_signature.ascii_rejected.log`; the final target raw is exact.
2. The first full-check file retained only selected terminal lines while being labeled raw. It is
   preserved as `raw/full_check.summary.log`; the fresh complete capture is
   `raw/full_check.combined.log`.
3. The first fixed-control log omitted the inline source. It is preserved as
   `raw/control_examples.summary.log`; replay source, hash, metadata, and stdout are frozen separately.
4. The first interpretation text was overbroad. A complete U is covered if all members meet the short
   hypotheses; an unrestricted complete all-lag U is not covered.

## Independent decision

The independent auditor approved the exact restricted theorem and final card wording at frozen source
SHA-256 `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`. The final card label is
`PROVED-LEAN` because the exact theorem is checked at `Recaman/Audit.lean:2701`. It remains a direct
corollary with no new registry row, E-number, or mathematical input. The official audit record is
`docs/adversarial_audits/H-20260921-01_20260921_0230.md`.

## Authorized application

- Initial live card hash: `24b36a8230275636575e82921dc3be94bc60862c20c020823d9fd2ed8711fac1`.
- Approved proposal hash: `c138c3ca29fe0971ac0b6d41480c8ebf0d790202267883a4c2a9805b937d43bb`.
- Applied live card hash: `c138c3ca29fe0971ac0b6d41480c8ebf0d790202267883a4c2a9805b937d43bb`.
- Proposal versus live card: `diff -u` exit 0.
- Applied scope: only `docs/HYPOTHESIS_CARD_2026-09-21_SHORT_SUPPLY_DONOR_DELETION.md`.
