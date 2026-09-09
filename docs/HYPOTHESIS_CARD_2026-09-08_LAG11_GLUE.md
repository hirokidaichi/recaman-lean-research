# Hypothesis card: Lean glue of the lag-11 injection onto periodic words

- ID: `H-20260908-05`
- Owner: root
- Created: 2026-09-08
- Status: `PROVED-LEAN` (`suppliedCount_add_u11Count_le_subtractionCount`)
- Research branch: issue #73, remaining Lean edge of E-079 / E-080
- Base revision: `8b07f93fbbb17352c091cabaa333fc366a66c04f`

## One bounded question

For every `e : ℤ → Bool` of period `p > 0` (true = addition), write U7 for
addition phases with some P2 lag `d ≤ 7` and U11min for those whose least P2
lag is exactly 11. Prove in Lean, with a semantic bridge from the actual
preceding 11 signs,

```text
|U7 ∪ U11min| ≤ |D|.
```

This is the intended statement of E-080, not a finite-period census and not
another L-bit automaton vector. It is strictly stronger than E-071.

## Why it would matter

- Frontier obligation: E-079 is a kernel on 17 combinatorial windows; the
  count on actual periodic words is still paper. Glue discharges that edge.
- Does not prove E-067/E-070 (E-086 still leaves lag ≥ 19).

## Provenance and dependencies

- `Recaman.ShortPeriodicSupply.P2`, `periodic_capacity`.
- Kernel: `Recaman.LagElevenSupply` (E-079).
- Paper: `docs/data/issue73_20260908/lag11/injection_proof.md` (E-080).
- Same-time clash (not the offset-index `clash` of E-079) is the injectivity
  obstruction; both happen to hold on the 17×17 assignment, but glue uses
  same-time overlap.

## Falsification plan

- Control: `SSSSAAAASAAA` has a lag-11 A that is not U7.
- Wrong collision distance `i−j` already failed on `SSSASSAAAASSAAA`.
- Same-time clash vs E-079 `clash`: 272/272 agree on this assignment
  (`COMPUTED` pre-check). Glue still quotes same-time geometry.
- Stop if the 17 types do not exhaust min-lag-11 11-bit masks, or if some
  type-charge is not locally U7-blocked on an actual window.

## Acceptance

`PROVED-LEAN`: `|U7 ∪ U11min| ≤ |D|` for every period, audited, no
`sorry`/`native_decide`. Semantic audit: the map is recovered from the
actual 11 signs, not an opaque matching oracle.

## Decision

- Continue / formalize / refute / stop: the count is Lean. Stop this glue
  unit. Do not enumerate lag-19 types. E-067/E-070 remain open.
- Reopen only if: a semantic gap appears in the Z-to-circle reduction, or a
  d-independent charge for all lags is proposed.
