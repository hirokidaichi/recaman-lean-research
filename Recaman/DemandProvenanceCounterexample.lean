import Recaman.History

namespace Recaman

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-! # Canonical witnesses for supplied-demand provenance

A *low supplied use* is a state clock `m` whose step `m + 1` is a forced
addition with positive candidate `a m - (m + 1) ≤ m`, and whose exposed
successor demand `a m - 1` is already in history.  This is the rigid
successor demand `c + m` of the recurring-candidate burst, written without
any recurrence hypothesis, so it can be evaluated on the canonical prefix.

The two kernel-checked facts below record that the canonical prefix
satisfies neither birth contraction frozen by `H-20260902-02`:

* the demand `6` of the low supplied use at clock `5` is born by the
  truncated addition `a 3 = 3 + 3`, whose candidate is zero, so `6 ≤ 2 * 3`;
* the demand `151` of the low supplied use at clock `112` is born by the
  legal subtraction at clock `110`, which is near-diagonal: `151 ≤ 2 * 110`.

These certify only facts about the canonical prefix.  They assert nothing
about an eventual corridor, where the late addition birth of a rigid demand
is contracted by `corridor_recurringCandidate_late_demand_birth`.
-/

private theorem firstAt_6_3_demandProvenance : FirstAt a 6 3 := by
  constructor
  · decide
  · intro earlier hearlier hvalue
    have hnot : 6 ∉ valuesThrough 2 := by decide
    exact hnot (mem_valuesThrough_iff.mpr
      ⟨earlier, by omega, hvalue⟩)

private theorem firstAt_151_110_demandProvenance : FirstAt a 151 110 := by
  constructor
  · decide
  · intro earlier hearlier hvalue
    have hnot : 151 ∉ valuesThrough 109 := by decide
    exact hnot (mem_valuesThrough_iff.mpr
      ⟨earlier, by omega, hvalue⟩)

/-- The low supplied use at clock `5` (candidate `1`, forced addition at
clock `6`) demands `6`, which was born by the truncated addition at clock
`3` whose candidate was `0`.  Hence the birth clock `3` satisfies
`6 ≤ 2 * 3`: the corridor-only addition contraction does not hold on the
canonical prefix. -/
theorem truncatedBirth_suppliedDemand_counterexample :
    FirstAt a 6 3 ∧
      a 2 = 3 ∧
      nextSubtractionCandidate 2 = 0 ∧
      ¬ CanSubtract 3 (stateAt 2) ∧
      a 3 = 6 ∧
      a 5 = 7 ∧
      6 < a 5 ∧
      nextSubtractionCandidate 5 = 1 ∧
      nextSubtractionCandidate 5 ≤ 5 ∧
      ¬ CanSubtract 6 (stateAt 5) ∧
      a 5 - 1 = 6 ∧
      6 ∈ valuesThrough 5 ∧
      6 ≤ 2 * 3 := by
  refine ⟨firstAt_6_3_demandProvenance, ?_⟩
  decide

/-- The low supplied use at clock `112` (candidate `39`, forced addition at
clock `113`) demands `151`, which was born by the legal subtraction at
clock `110`.  The birth is near-diagonal, `151 ≤ 2 * 110`, so the
subtraction channel of a supplied demand is not half-clock contracted on
the canonical prefix. -/
theorem nearDiagonalBirth_suppliedDemand_counterexample :
    FirstAt a 151 110 ∧
      a 109 = 261 ∧
      CanSubtract 110 (stateAt 109) ∧
      a 110 = 151 ∧
      a 112 = 152 ∧
      113 < a 112 ∧
      nextSubtractionCandidate 112 = 39 ∧
      nextSubtractionCandidate 112 ≤ 112 ∧
      ¬ CanSubtract 113 (stateAt 112) ∧
      a 112 - 1 = 151 ∧
      151 ∈ valuesThrough 112 ∧
      151 ≤ 2 * 110 := by
  refine ⟨firstAt_151_110_demandProvenance, ?_⟩
  decide

end Recaman
