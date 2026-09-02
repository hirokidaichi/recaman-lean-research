import Recaman.History

namespace Recaman

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-! # Exact standard-prefix counterexamples for supply ancestry

These finite kernel checks certify only facts about the canonical Recamán
prefix.  In particular, they do not assert that any of the displayed states
belongs to an eventual high-candidate corridor.
-/

private theorem firstAt_42_20_supplyAncestry : FirstAt a 42 20 := by
  constructor
  · decide
  · intro earlier hearlier hvalue
    have hnot : 42 ∉ valuesThrough 19 := by decide
    exact hnot (mem_valuesThrough_iff.mpr
      ⟨earlier, by omega, hvalue⟩)

private theorem firstAt_151_110_supplyAncestry : FirstAt a 151 110 := by
  constructor
  · decide
  · intro earlier hearlier hvalue
    have hnot : 151 ∉ valuesThrough 109 := by decide
    exact hnot (mem_valuesThrough_iff.mpr
      ⟨earlier, by omega, hvalue⟩)

private theorem firstAt_135_126_supplyAncestry : FirstAt a 135 126 := by
  constructor
  · decide
  · intro earlier hearlier hvalue
    have hnot : 135 ∉ valuesThrough 125 := by decide
    exact hnot (mem_valuesThrough_iff.mpr
      ⟨earlier, by omega, hvalue⟩)

/-- Value `42` is first born by the legal subtraction at clock `20`, but is
later exposed as a positive, history-blocked candidate at state `35`.  Thus
following the forced use back to its birth reverses the forcedness premise. -/
theorem subtractionBorn_42_forcedReuse_counterexample :
    FirstAt a 42 20 ∧
      a 19 = 62 ∧
      CanSubtract 20 (stateAt 19) ∧
      nextSubtractionCandidate 19 = 42 ∧
      a 19 - 20 = 42 ∧
      a 20 = 42 ∧
      a 35 = 78 ∧
      0 < nextSubtractionCandidate 35 ∧
      36 < a 35 ∧
      nextSubtractionCandidate 35 = 42 ∧
      ¬ CanSubtract 36 (stateAt 35) := by
  refine ⟨firstAt_42_20_supplyAncestry, ?_⟩
  decide

/-- The distinct subtraction-born values `151` and `135` have the same
predecessor orbit value `261`, at subtraction clocks `110` and `126`.
Both values are later exposed as positive, history-blocked candidates. -/
theorem subtractionBorn_sharedParent_counterexample :
    FirstAt a 151 110 ∧
      FirstAt a 135 126 ∧
      151 ≠ 135 ∧
      a 109 = 261 ∧
      CanSubtract 110 (stateAt 109) ∧
      nextSubtractionCandidate 109 = 151 ∧
      a 109 = 151 + 110 ∧
      a 110 = 151 ∧
      a 125 = 261 ∧
      CanSubtract 126 (stateAt 125) ∧
      nextSubtractionCandidate 125 = 135 ∧
      a 125 = 135 + 126 ∧
      a 126 = 135 ∧
      a 109 = a 125 ∧
      a 113 = 265 ∧
      0 < nextSubtractionCandidate 113 ∧
      114 < a 113 ∧
      nextSubtractionCandidate 113 = 151 ∧
      ¬ CanSubtract 114 (stateAt 113) ∧
      a 133 = 269 ∧
      0 < nextSubtractionCandidate 133 ∧
      134 < a 133 ∧
      nextSubtractionCandidate 133 = 135 ∧
      ¬ CanSubtract 134 (stateAt 133) := by
  refine ⟨firstAt_151_110_supplyAncestry,
    firstAt_135_126_supplyAncestry, ?_⟩
  decide

end Recaman
