import Recaman.LandingSurfaces

namespace Recaman

theorem firstAt_seven : FirstAt a 7 5 := by
  constructor
  · decide
  · intro u hu hvalue
    have hcases : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 := by
      omega
    rcases hcases with h | h | h | h | h
    · subst u
      have hne : a 0 ≠ 7 := by decide
      exact hne hvalue
    · subst u
      have hne : a 1 ≠ 7 := by decide
      exact hne hvalue
    · subst u
      have hne : a 2 ≠ 7 := by decide
      exact hne hvalue
    · subst u
      have hne : a 3 ≠ 7 := by decide
      exact hne hvalue
    · subst u
      have hne : a 4 ≠ 7 := by decide
      exact hne hvalue

theorem firstAt_three : FirstAt a 3 2 := by
  constructor
  · decide
  · intro u hu hvalue
    have hcases : u = 0 ∨ u = 1 := by omega
    rcases hcases with h | h
    · subst u
      have hne : a 0 ≠ 3 := by decide
      exact hne hvalue
    · subst u
      have hne : a 1 ≠ 3 := by decide
      exact hne hvalue

/-- The first small concrete instance of the actual-blocker bridge:
a₅=7 and step 6 is blocked by the previously seen value 1. -/
theorem actualBlocker_at_five : ActualBlocker 5 7 0 1 := by
  constructor
  · exact firstAt_seven
  · constructor
    · decide
    · intro i hi
      omega
  · decide
  · decide
  · decide

example : 1 < 7 ∧ ∃ fy, FirstAt a 1 fy ∧ fy < 5 :=
  actualBlocker_at_five.doubleDescent

/-- The target equation predicts 7-6=1, but 1 was already seen.  Therefore
the target attempt returns the concrete blocker rather than a new landing. -/
theorem targetAttempt_seven_to_one : TargetOutcome 5 7 1 1 := by
  apply targetDescent_dichotomy firstAt_seven
  · decide
  · unfold TargetEquation
    decide

theorem targetAttempt_seven_to_one_is_blocked :
    ∃ length y, length < 1 ∧ ActualBlocker 5 7 length y := by
  cases targetAttempt_seven_to_one with
  | lands _ hlanding =>
      have hnot : a (5 + 1) ≠ 1 := by decide
      exact False.elim (hnot hlanding)
  | blocked length y hbefore blocker =>
      exact ⟨length, y, hbefore, blocker⟩

/-- The naive direct-target criterion is already too strong at a₂=3:
there is no k with 1 + 2k + U(k) = 3. -/
theorem no_targetEquation_three_to_one (k : Nat) :
    ¬ TargetEquation 2 3 1 k := by
  intro hequation
  cases k with
  | zero =>
      simp [TargetEquation, descentDrop, upperTri] at hequation
  | succ k =>
      unfold TargetEquation descentDrop at hequation
      simp [upperTri, Nat.succ_mul] at hequation
      omega

theorem not_targetResolvable_one : ¬ TargetResolvable 1 := by
  intro hresolve
  rcases hresolve 3 2 firstAt_three (by omega) with ⟨k, hequation⟩
  exact no_targetEquation_three_to_one k hequation

/-- Coordinate trace of the smallest direct-target counterexample.
At time 2 it is regular (q,r,G)=(1,1,0); forced addition moves to
(2,0,-3), the next one-borrow subtraction moves to (0,2,2), and one
more forced addition reaches the target surface (1,2,1). -/
theorem smallestCounterexample_coordinateTrace :
    CoordinatesAt 2 1 1 ∧ potential 1 1 = 0 ∧
    CoordinatesAt 3 2 0 ∧ potential 2 0 = -3 ∧
    CoordinatesAt 4 0 2 ∧ potential 0 2 = 2 ∧
    CoordinatesAt 5 1 2 ∧ potential 1 2 = 1 := by
  have hcoord2 : CoordinatesAt 2 1 1 := by
    unfold CoordinatesAt
    constructor <;> decide
  have hnot3 : ¬ CanSubtract 3 (stateAt 2) := by decide
  have hadd := coordinates_add_regular hcoord2 (by omega) hnot3
  have hcan4 : CanSubtract 4 (stateAt 3) := by decide
  have hsub := coordinates_sub_borrow hadd.1
    (by omega) (by omega) (by omega) hcan4
  have hnot5 : ¬ CanSubtract 5 (stateAt 4) := by decide
  have hadd2 := coordinates_add_regular hsub.1 (by omega) hnot5
  exact ⟨hcoord2, by decide, hadd.1, by decide,
    hsub.1, by decide, hadd2.1, by decide⟩

/-- A concrete genuinely multi-borrow arithmetic state.  For `n=3`,
`q=10`, `r=1`, the corrected modulus is 4 and the unique borrow data is
`b=3`, `s=3`.  Addition gives quotient 8, while subtraction gives quotient 6. -/
theorem threeBorrow_arithmetic_example :
    BorrowData 3 10 1 3 3 ∧
      QuotRem 4 35 8 3 ∧ potential 8 3 = potential 10 1 + 21 ∧
      QuotRem 4 27 6 3 ∧ potential 6 3 = potential 10 1 + 36 := by
  constructor
  · constructor <;> decide
  constructor
  · constructor <;> decide
  constructor
  · decide
  constructor
  · constructor <;> decide
  · decide

/-- The time-four hypothesis in the abstract subtraction-negativity theorem is
sharp: this non-orbit arithmetic state at time two uses two borrows and lands
on the positive target level `G=1`.  `actual_multi_time_ge_four` excludes it
from the Recamán orbit. -/
theorem earlyMultiBorrow_subtraction_exception :
    BorrowData 2 4 0 2 2 ∧
      QuotRem 3 (8 - 3) 1 2 ∧ potential 1 2 = Int.ofNat 1 := by
  constructor
  · constructor <;> decide
  constructor
  · constructor <;> decide
  · decide

/-- A smallest warning against dropping the exact-gate intermediate-freshness
hypothesis.  At time 18 the target level `m=4` itself is fresh on `q=2,G=4`,
but the intermediate value 24 is old, so the next step adds and reaches 62. -/
theorem targetSurface_two_fresh_target_but_blocked :
    CoordinatesAt 18 2 7 ∧
      potential 2 7 = Int.ofNat 4 ∧
      4 ∉ valuesThrough 18 ∧
      gateIntermediate 18 4 ∈ valuesThrough 18 ∧
      a 19 = 62 := by
  constructor
  · unfold CoordinatesAt
    constructor <;> decide
  constructor
  · decide
  constructor
  · decide
  constructor <;> decide

end Recaman
