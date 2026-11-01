import Recaman.EventualHighCandidateLedger
import Recaman.DebtAddition

namespace Recaman

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-! # Causal reuse of positive forced-addition candidates

A positive failed subtraction candidate always has an earlier first
occurrence, even when the forced-addition output is not fresh.  Reusing one
candidate at different clocks produces distinct output *values*, but those
outputs need not be first occurrences.  Thus the only unconditional charge
is to the use clock itself.
-/

/-- A positive forced-addition candidate has a canonical earlier first
occurrence.  No freshness assumption on the addition output is needed. -/
theorem forcedAddition_positive_candidate_has_earlier_firstAt
    {n : Nat}
    (hforced : ¬ CanSubtract (n + 1) (stateAt n))
    (hpositive : n + 1 < a n) :
    ∃ candidate firstTime,
      candidate = a n - (n + 1) ∧
      0 < candidate ∧
      FirstAt a candidate firstTime ∧
      firstTime < n + 1 := by
  have hstatePositive : n + 1 < (stateAt n).value := by
    simpa [a] using hpositive
  rcases (not_canSubtract_iff_nonpositive_or_seen.mp hforced) with
    hnonpositive | hseen
  · exact False.elim (hnonpositive hstatePositive)
  · have hseenActual : a n - (n + 1) ∈ valuesThrough n := by
      simpa [a, valuesThrough] using hseen
    rcases history_member_has_firstAt hseenActual with
      ⟨firstTime, htime, hfirst⟩
    exact ⟨a n - (n + 1), firstTime, rfl, by omega,
      hfirst, Nat.lt_succ_of_le htime⟩

/-- After a positive forced use of candidate `candidate` at clock `n+1`,
the candidate exposed at the very next clock is `candidate + n`.  In
particular, except for the degenerate first clock, the same candidate cannot
be used on two consecutive clocks. -/
theorem nextCandidate_after_positive_forcedAddition
    {n candidate : Nat}
    (hpositive : n + 1 < a n)
    (hcandidate : nextSubtractionCandidate n = candidate)
    (hforced : ¬ CanSubtract (n + 1) (stateAt n)) :
    nextSubtractionCandidate (n + 1) = candidate + n := by
  have hstep := a_succ_of_not_canSubtract hforced
  simp only [nextSubtractionCandidate] at hcandidate ⊢
  rw [hstep]
  omega

/-- Uses of the same positive candidate at two different clocks have
strictly ordered forced-addition output values.  This is an injection into
raw output values, not into fresh occurrences. -/
theorem forcedAddition_same_candidate_outputs_strict
    {first second candidate : Nat}
    (htime : first < second)
    (hfirstPositive : first + 1 < a first)
    (hsecondPositive : second + 1 < a second)
    (hfirstCandidate : a first - (first + 1) = candidate)
    (hsecondCandidate : a second - (second + 1) = candidate)
    (hfirstForced : ¬ CanSubtract (first + 1) (stateAt first))
    (hsecondForced : ¬ CanSubtract (second + 1) (stateAt second)) :
    a (first + 1) < a (second + 1) := by
  have hfirstStep := a_succ_of_not_canSubtract hfirstForced
  have hsecondStep := a_succ_of_not_canSubtract hsecondForced
  omega

private theorem firstAt_285_169 : FirstAt a 285 169 := by
  constructor
  · decide
  · intro earlier hearlier hvalue
    have hnot : 285 ∉ valuesThrough 168 := by decide
    exact hnot (mem_valuesThrough_iff.mpr
      ⟨earlier, by omega, hvalue⟩)

/-- Exact standard-prefix counterexample to both one-use charging and fresh
output charging.  While target `19` is still missing, candidate `285` forces
addition at clocks `173` and `1325`.  The second output is `2935`, but that
value already occurred at time `1313`. -/
theorem highCandidate_forcedReuse_and_nonfreshOutput_counterexample :
    FirstAt a 285 169 ∧
      19 ∉ valuesThrough 1325 ∧
      19 < nextSubtractionCandidate 172 ∧
      nextSubtractionCandidate 172 = 285 ∧
      ¬ CanSubtract 173 (stateAt 172) ∧
      19 < nextSubtractionCandidate 1324 ∧
      nextSubtractionCandidate 1324 = 285 ∧
      ¬ CanSubtract 1325 (stateAt 1324) ∧
      a 173 = 631 ∧
      a 1313 = 2935 ∧
      a 1325 = 2935 := by
  refine ⟨firstAt_285_169, ?_⟩
  decide

/-- Distinct high candidates can also collide at the same forced-addition
output.  While `4` is missing, clocks `101` and `113` use candidates `63`
and `39`, respectively, but both land on `265`. -/
theorem highCandidate_distinctCandidates_sameOutput_counterexample :
    4 ∉ valuesThrough 113 ∧
      4 < nextSubtractionCandidate 100 ∧
      nextSubtractionCandidate 100 = 63 ∧
      ¬ CanSubtract 101 (stateAt 100) ∧
      4 < nextSubtractionCandidate 112 ∧
      nextSubtractionCandidate 112 = 39 ∧
      ¬ CanSubtract 113 (stateAt 112) ∧
      a 101 = 265 ∧
      a 113 = 265 := by
  decide

end Recaman
