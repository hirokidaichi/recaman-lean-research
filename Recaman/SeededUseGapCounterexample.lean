import Recaman.Basic

namespace Recaman

/-! # A seeded counterexample to the local square-root-six use-gap claim

The recurring-candidate burst theorem forces at least three additions after
a use clock; it does not force the fourth step to be a subtraction.  This
finite exact `Basic.step` continuation records the resulting semantic gap.

At absolute clock `m = 120`, candidate `c = 10` is entered by a legal
subtraction.  The continuation then takes eleven additions followed by ten
subtractions, returning to candidate `10` at clock `n = 141`.  Every
intermediate candidate is strictly above its clock, so these are consecutive
low-candidate clocks.  The next use also begins with three additions.  Yet

```text
(n - m)^2 = 21^2 = 441 < 720 = 6m.
```

The seed is deliberately not claimed reachable from `initial`.  Its role is
to falsify any derivation of the `sqrt (6m)` gap from local floor, burst, and
exact greedy-step assumptions alone.  A canonical or genuinely global
self-supply hypothesis would have to be stated separately.
-/

/-- Finite history used immediately before the legal entry at clock `120`.
It preloads the blockers for the eleven-addition run and the successor demand
at the second use clock. -/
def seededUseGapBaseSeen : List Nat :=
  [251, 10, 130, 251, 373, 496, 620, 745, 871, 998, 1126, 1255, 151, 0]

/-- Seeded state immediately before absolute clock `120`. -/
def seededUseGapPreState : State :=
  ⟨251, seededUseGapBaseSeen⟩

/-- Exact greedy continuation after entering the first use clock.  Local
time `t` corresponds to absolute time `120 + t`. -/
def seededUseGapState : Nat → State
  | 0 => step 120 seededUseGapPreState
  | t + 1 => step (121 + t) (seededUseGapState t)

/-- The finite continuation satisfies the complete local counterexample
payload: legal entry, equal endpoint candidates, no intervening low candidate,
the first use's long addition run followed by legal subtractions, a three-step
burst at the second use, and failure of the proposed square-root-six bound. -/
theorem seededUseGap_local_counterexample :
    CanSubtract 120 seededUseGapPreState ∧
    (seededUseGapState 0).value - 121 = 10 ∧
    (seededUseGapState 21).value - 142 = 10 ∧
    (∀ i : Fin 20,
      120 + (i.1 + 1) <
        (seededUseGapState (i.1 + 1)).value - (121 + (i.1 + 1))) ∧
    (∀ i : Fin 11,
      ¬ CanSubtract (121 + i.1) (seededUseGapState i.1)) ∧
    (∀ i : Fin 10,
      CanSubtract (132 + i.1) (seededUseGapState (11 + i.1))) ∧
    (∀ i : Fin 3,
      ¬ CanSubtract (142 + i.1) (seededUseGapState (21 + i.1))) ∧
    21 * 21 < 6 * 120 := by
  decide

end Recaman
