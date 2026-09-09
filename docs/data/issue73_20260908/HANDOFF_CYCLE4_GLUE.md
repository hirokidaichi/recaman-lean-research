# Handoff: issue #73 cycle 4, lag-11 Lean glue (union count still open)

Conclusion first: `|U11min| ≤ |D|` is `PROVED-LEAN` for every period
(`u11Count_le_subtractionCount`). `|U7 ∪ U11min| ≤ |D|` (E-080) is still
`PROVED-PAPER`. This fire did not close the union.

## Hypothesis-card status

H-20260908-05: union count `CONJECTURED`; φ11 injection `PROVED-LEAN`.

## What was proved in Lean this fire

- `phi11Phase_inj`: min-lag-11 phases inject on `Z/pZ` (wrap reduces to
  `timeClash_same_time`).
- `phi11Phase_is_sub`: images are subtraction phases.
- `u11Count_le_subtractionCount`: `|U11min| ≤ |D|`, all-period.
- `phi7Phase_is_sub`: U7 charges land on S.
- `u7_pairwise_timeClash7`: the three U7 window types clash at charges
  3,5,7 (finite `decide`; clashes lie in forced signs).

## What remains for E-080

1. Glue `timeClash7` onto actual 7-sign windows → `phi7Phase_inj`.
2. `u7Blocked` ⇒ `im φ7 ∩ im φ11 = ∅`.
3. `suppliedCount + u11Count ≤ subtractionCount`.

## Files changed

`Recaman/LagElevenPeriodic.lean`, `Recaman/Audit.lean`,
`docs/MODULE_IMPORT_CONTRACTS.tsv`, cards, `SESSION_STATE.md`, this handoff.

No `sorry`. `recaman-visualizer/` untouched.

## Commands

`./scripts/check.sh` PASS.

## Remaining uncertainty

`|U11min| ≤ |D|` does not imply E-071 and is not the union bound.
Different U7 classes still need the 7-window glue, not just the kernel
`decide`.

## Next decision

Finish `phi7Phase_inj` + disjoint images, then audit the sum as E-080
`PROVED-LEAN`. Do not run lag-19.
