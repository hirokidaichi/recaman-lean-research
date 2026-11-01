import Recaman.History
import Recaman.CoordinateDynamics

namespace Recaman

/-- Failure of a subtraction has exactly the two reasons present in the
definition of `CanSubtract`: the candidate is nonpositive, or it has already
occurred.  This state-level form is useful independently of the actual orbit. -/
theorem not_canSubtract_iff_nonpositive_or_seen {stepIndex : Nat} {state : State} :
    (¬ CanSubtract stepIndex state) ↔
      (¬ stepIndex < state.value) ∨ state.value - stepIndex ∈ state.seen := by
  unfold CanSubtract
  constructor
  · intro hnot
    by_cases hpositive : stepIndex < state.value
    · by_cases hseen : state.value - stepIndex ∈ state.seen
      · exact Or.inr hseen
      · exact False.elim (hnot ⟨hpositive, hseen⟩)
    · exact Or.inl hpositive
  · rintro (hnonpositive | hseen) hcan
    · exact hnonpositive hcan.1
    · exact hcan.2 hseen

/-- If a first occurrence at time `n+1` was produced by forced addition,
then either the attempted subtraction was nonpositive, or its positive
candidate has a first occurrence at a strictly earlier time.

The candidate is also strictly below the new value.  Notice that the theorem
does not claim a lower target bound or any relation to a search anchor: those
facts are not consequences of forced addition alone. -/
theorem firstAt_forcedAddition_dichotomy {n y : Nat}
    (hfirst : FirstAt a y (n + 1))
    (hforced : ¬ CanSubtract (n + 1) (stateAt n)) :
    (¬ n + 1 < a n) ∨
      ∃ x fx,
        x = a n - (n + 1) ∧ 0 < x ∧
        FirstAt a x fx ∧ fx < n + 1 ∧ x < y := by
  by_cases hpositive : n + 1 < a n
  · right
    have hseen : (stateAt n).value - (n + 1) ∈ (stateAt n).seen := by
      have hstatePositive : n + 1 < (stateAt n).value := by
        simpa [a] using hpositive
      rcases (not_canSubtract_iff_nonpositive_or_seen.mp hforced) with
        hnonpositive | hseen
      · exact False.elim (hnonpositive hstatePositive)
      · exact hseen
    have hseenActual : a n - (n + 1) ∈ valuesThrough n := by
      simpa [a, valuesThrough] using hseen
    rcases history_member_has_firstAt hseenActual with ⟨fx, hfx, hfirstX⟩
    refine ⟨a n - (n + 1), fx, rfl, by omega, hfirstX,
      Nat.lt_succ_of_le hfx, ?_⟩
    have hadd := a_succ_of_not_canSubtract hforced
    have hy : y = a (n + 1) := hfirst.1.symm
    rw [hy, hadd]
    omega
  · exact Or.inl hpositive

/-- Positive pre-state values rule out the nonpositive branch and expose the
earlier first occurrence directly. -/
theorem firstAt_forcedAddition_extract_candidate {n y : Nat}
    (hfirst : FirstAt a y (n + 1))
    (hforced : ¬ CanSubtract (n + 1) (stateAt n))
    (hpositive : n + 1 < a n) :
    ∃ x fx,
      x = a n - (n + 1) ∧ 0 < x ∧
      FirstAt a x fx ∧ fx < n + 1 ∧ x < y := by
  rcases firstAt_forcedAddition_dichotomy hfirst hforced with
    hnonpositive | hextracted
  · exact False.elim (hnonpositive hpositive)
  · exact hextracted

/-- The target lower bound needed by debt recursion is available exactly
when it is separately known for the subtraction candidate. -/
theorem firstAt_forcedAddition_extract_candidate_above_target
    {m n y : Nat}
    (hfirst : FirstAt a y (n + 1))
    (hforced : ¬ CanSubtract (n + 1) (stateAt n))
    (hpositive : n + 1 < a n)
    (htarget : m ≤ a n - (n + 1)) :
    ∃ x fx,
      m ≤ x ∧ FirstAt a x fx ∧ fx < n + 1 ∧ x < y := by
  rcases firstAt_forcedAddition_extract_candidate hfirst hforced hpositive with
    ⟨x, fx, hx, _, hfirstX, htime, hxy⟩
  subst x
  exact ⟨a n - (n + 1), fx, htarget, hfirstX, htime, hxy⟩

/-- Likewise, exiting debt through an anchor decrease requires the separate
comparison between the candidate and the anchor. -/
theorem firstAt_forcedAddition_extract_candidate_below_anchor
    {anchor n y : Nat}
    (hfirst : FirstAt a y (n + 1))
    (hforced : ¬ CanSubtract (n + 1) (stateAt n))
    (hpositive : n + 1 < a n)
    (hanchor : a n - (n + 1) < anchor) :
    ∃ x fx,
      x < anchor ∧ FirstAt a x fx ∧ fx < n + 1 ∧ x < y := by
  rcases firstAt_forcedAddition_extract_candidate hfirst hforced hpositive with
    ⟨x, fx, hx, _, hfirstX, htime, hxy⟩
  subst x
  exact ⟨a n - (n + 1), fx, hanchor, hfirstX, htime, hxy⟩

/-- The actual step from `a 5 = 7` to the first occurrence `a 6 = 13`
shows that a target below the new value need not be below the blocked
candidate: for target `8`, the candidate is the old value `1`. -/
private theorem debtAddition_firstAt_thirteen : FirstAt a 13 6 := by
  constructor
  · decide
  · intro u hu hvalue
    have hcases :
        u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 ∨ u = 5 := by
      omega
    rcases hcases with h | h | h | h | h | h
    · subst u
      have hne : a 0 ≠ 13 := by decide
      exact hne hvalue
    · subst u
      have hne : a 1 ≠ 13 := by decide
      exact hne hvalue
    · subst u
      have hne : a 2 ≠ 13 := by decide
      exact hne hvalue
    · subst u
      have hne : a 3 ≠ 13 := by decide
      exact hne hvalue
    · subst u
      have hne : a 4 ≠ 13 := by decide
      exact hne hvalue
    · subst u
      have hne : a 5 ≠ 13 := by decide
      exact hne hvalue

theorem forcedAddition_target_bound_not_automatic :
    FirstAt a 13 6 ∧
      ¬ CanSubtract 6 (stateAt 5) ∧
      8 ≤ 13 ∧ ¬ 8 ≤ a 5 - 6 := by
  exact ⟨debtAddition_firstAt_thirteen, by decide, by decide, by decide⟩

/-- The same actual step shows that an anchor comparison is independent of
forced addition: its candidate `1` is not strictly below anchor `1`. -/
theorem forcedAddition_anchor_bound_not_automatic :
    FirstAt a 13 6 ∧
      ¬ CanSubtract 6 (stateAt 5) ∧
      ¬ a 5 - 6 < 1 := by
  exact ⟨debtAddition_firstAt_thirteen, by decide, by decide⟩

end Recaman
