import Recaman.Surjectivity
import Recaman.LeastMissingTargetContradiction
import Recaman.TailDowncrossingInevitability
import Recaman.PermanentHighGlobalSynthesis
import Recaman.PermanentHighBlockerCapacity
import Recaman.PermanentHighToothcombBound
import Recaman.PermanentHighToothcombDescent
import Recaman.PermanentHighRigidity

namespace Recaman

/-! # Elimination of the Permanent High Escape Branch

This module formalizes the structural obstruction and elimination machinery
for the Permanent High Escape branch (`PermanentHighEscape time`) in any hypothetical
counterexample to the Recamán surjectivity conjecture:

1. **Downcrossing Contradiction (`downcrossing_contradicts_permanent_high`)**:
   Any downcrossing step `k ≥ time + 2` with `a (k + 1) < 2 * (k + 1)` directly
   refutes `PermanentHighEscape time`.

2. **Downcrossing Equivalence (`permanent_high_escape_iff_no_downcrossing`)**:
   For any certified tail minimum, `PermanentHighEscape time` is logically
   equivalent to the complete absence of downcrossing steps at or after `time + 2`.

3. **Corridor Re-entry Forcing (`corridor_reentry_of_not_permanent_high`)**:
   Refuting `PermanentHighEscape time` unconditionally forces the counterexample
   to perform a certified corridor re-entry (`CorridorReentry time`).

4. **Pigeonhole Blocker Capacity at Escape State (`escape_state_pigeonhole_capacity`)**:
   At `n = time + 2`, the `n` candidate values cannot be blocked by the `n - 1`
   historical values `j < n`, guaranteeing an unblocked candidate exceeding `2n`.

5. **Historical Avoidance (`escape_state_unblocked_candidate_avoids_history`)**:
   The unblocked candidate strictly avoids `valuesThrough (n - 1)` and all `a j` for `j < n`.

6. **Descent Landing Below Twice Clock (`escape_state_descent_strictly_below_twice_clock`)**:
   Because `a (time + 2) < 6(time + 2) + 1` (E-338), the toothcomb descent at step `m = n`
   strictly forces landing below twice its clock: `val < 2 * (n + 3 + 2n)`.

7. **Ledger and Counter Caps in High Regime (`permanent_high_subSum_capped_of_escape`)**:
   In any permanent high orbit, `subSum` and `subCount` are permanently constrained
   by the triangular capacity bounds.

8. **Grand Synthesis (`grand_no_permanent_high_escape_synthesis`)**:
   Unifies downcrossing contradictions, corridor re-entry forcing, pigeonhole blocker
   capacity, and descent forcing into a single master theorem.
-/

/-! ### Part 1: Downcrossing Contradictions and Equivalence -/

/-- Any downcrossing step at or after `time + 2` directly refutes `PermanentHighEscape time`. -/
theorem downcrossing_contradicts_permanent_high
    {time k : Nat}
    (hk : time + 2 ≤ k)
    (hdown : a (k + 1) < 2 * (k + 1))
    (hhigh : PermanentHighEscape time) : False := by
  have hk1 : time + 2 ≤ k + 1 := by omega
  have hge := hhigh (k + 1) hk1
  omega

/-- For any certified tail minimum, the presence of a downcrossing step at or after
`time + 2` is equivalent to the refutation of `PermanentHighEscape time`. -/
theorem permanent_high_escape_iff_no_downcrossing
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    PermanentHighEscape time ↔
    ¬ ∃ k, time + 2 ≤ k ∧ 2 * k ≤ a k ∧ a (k + 1) < 2 * (k + 1) := by
  constructor
  · intro hhigh ⟨k, hk, _hhigh_k, hlow_k⟩
    exact downcrossing_contradicts_permanent_high hk hlow_k hhigh
  · intro hno
    rcases tail_escape_downcrossing_dichotomy hmin with hhigh | hdown
    · exact hhigh
    · exact False.elim (hno hdown)

/-- In any hypothetical least missing target, refuting `PermanentHighEscape`
strictly forces corridor re-entry. -/
theorem corridor_reentry_of_not_permanent_high
    {target : Nat} (h : LeastMissingTarget target)
    (hnot_high : NoPermanentHighEscapeHypothesis) :
    ∃ start time firstTime,
      PermanentTailMinimumCertificate target start time firstTime ∧
      CorridorReentry time := by
  rcases least_missing_target_tail_dichotomy h with ⟨start, time, firstTime, hmin, hdich⟩
  refine ⟨start, time, firstTime, hmin, ?_⟩
  rcases hdich with hhigh | hcorridor
  · have hcontra := hnot_high target start time firstTime hmin hhigh
    exact False.elim hcontra
  · exact hcorridor

/-! ### Part 2: Blocker Capacity and Descent Forcing at Escape State -/

/-- At the escape state `time + 2`, the pigeonhole blocker capacity
guarantees the existence of an unblocked candidate strictly exceeding `2 * (time + 2)`. -/
theorem escape_state_pigeonhole_capacity
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    ∃ m, m < time + 2 ∧
      (∀ j, j < time + 2 → a j ≠ a (time + 2) + (time + 2) - m) ∧
      2 * (time + 2) < a (time + 2) + (time + 2) - m := by
  have hn_high : 2 * (time + 2) ≤ a (time + 2) := by
    have := tail_minimum_followup_gt_twice_time hmin
    omega
  have hn_pos : 1 ≤ time + 2 := by omega
  rcases toothcomb_exists_unblocked_candidate hn_pos hn_high with ⟨m, hm, hunblock⟩
  have hgt := toothcomb_candidate_gt_two_n hm hn_high
  exact ⟨m, hm, hunblock, hgt⟩

/-- The escape state unblocked candidate avoids all historical values through `time + 1`. -/
theorem escape_state_unblocked_candidate_avoids_history
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    ∃ m, m < time + 2 ∧
      a (time + 2) + (time + 2) - m ∉ valuesThrough (time + 1) ∧
      (∀ j, j < time + 2 → a j ≠ a (time + 2) + (time + 2) - m) ∧
      2 * (time + 2) < a (time + 2) + (time + 2) - m := by
  have hn_high : 2 * (time + 2) ≤ a (time + 2) := by
    have := tail_minimum_followup_gt_twice_time hmin
    omega
  have hn_pos : 1 ≤ time + 2 := by omega
  rcases toothcomb_exists_unblocked_candidate hn_pos hn_high with ⟨m, hm, hunblock⟩
  have havoid := toothcomb_unblocked_candidate_avoids_valuesThrough hn_pos hm hunblock
  have hgt := toothcomb_candidate_gt_two_n hm hn_high
  have heq_pred : (time + 2) - 1 = time + 1 := by omega
  rw [heq_pred] at havoid
  exact ⟨m, hm, havoid, hunblock, hgt⟩

/-- At the escape state `time + 2`, the descent value at step `m = time + 2`
strictly falls below twice its clock `2 * (time + 2 + 3 + 2 * (time + 2))`. -/
theorem escape_state_descent_strictly_below_twice_clock
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (htwice : a time < 2 * time) :
    ∀ val, val = a (time + 2) + (time + 2) - (time + 2) →
      val < 2 * (time + 2 + 3 + 2 * (time + 2)) := by
  intro val hval
  have hlt := tail_escape_strictly_lt_six_times hmin htwice
  exact toothcomb_forced_downcrossing_at_step_n hlt hval

/-! ### Part 3: Permanent High Ledger and Counter Capacity Bounds -/

/-- In any permanent high orbit, the subtraction ledger is permanently capped
by the triangular capacity bound. -/
theorem permanent_high_subSum_capped_of_escape
    {time : Nat}
    (hhigh : PermanentHighEscape time) :
    ∀ n, time + 2 ≤ n → 2 * subSum n ≤ upperTri n - 2 * n := by
  intro n hn
  exact permanent_high_subSum_upper_bound hhigh hn

/-- In any permanent high orbit, the subtraction counter is permanently capped
by the triangular capacity bound. -/
theorem permanent_high_subCount_capped_of_escape
    {time : Nat}
    (hhigh : PermanentHighEscape time) :
    ∀ n, time + 2 ≤ n → 2 * upperTri (subCount n) + 2 * n ≤ upperTri n := by
  intro n hn
  exact permanent_high_subCount_upper_bound hhigh hn

/-! ### Part 4: Grand No Permanent High Escape Synthesis -/

/-- Grand No Permanent High Escape Synthesis:
Unifies:
1. Downcrossing contradiction with permanent high regime.
2. Characterization of PermanentHighEscape as the absence of downcrossings.
3. Forcing of CorridorReentry under the refutation of PermanentHighEscape.
4. Pigeonhole blocker capacity at the escape state time + 2.
5. Historical avoidance of unblocked candidates.
6. Descent value landing strictly below twice clock.
7. Subtraction ledger and count triangular capacity caps. -/
theorem grand_no_permanent_high_escape_synthesis
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (htwice : a time < 2 * time) :
    (∀ k, time + 2 ≤ k → a (k + 1) < 2 * (k + 1) → PermanentHighEscape time → False) ∧
    (PermanentHighEscape time ↔
      ¬ ∃ k, time + 2 ≤ k ∧ 2 * k ≤ a k ∧ a (k + 1) < 2 * (k + 1)) ∧
    (LeastMissingTarget target →
      NoPermanentHighEscapeHypothesis →
      ∃ s t ft, PermanentTailMinimumCertificate target s t ft ∧ CorridorReentry t) ∧
    (∃ m, m < time + 2 ∧
      (∀ j, j < time + 2 → a j ≠ a (time + 2) + (time + 2) - m) ∧
      2 * (time + 2) < a (time + 2) + (time + 2) - m) ∧
    (∃ m, m < time + 2 ∧
      a (time + 2) + (time + 2) - m ∉ valuesThrough (time + 1) ∧
      (∀ j, j < time + 2 → a j ≠ a (time + 2) + (time + 2) - m) ∧
      2 * (time + 2) < a (time + 2) + (time + 2) - m) ∧
    (∀ val, val = a (time + 2) + (time + 2) - (time + 2) →
      val < 2 * (time + 2 + 3 + 2 * (time + 2))) ∧
    (PermanentHighEscape time →
      ∀ n, time + 2 ≤ n →
        2 * subSum n ≤ upperTri n - 2 * n ∧
        2 * upperTri (subCount n) + 2 * n ≤ upperTri n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk hdown hhigh
    exact downcrossing_contradicts_permanent_high hk hdown hhigh
  · exact permanent_high_escape_iff_no_downcrossing hmin
  · intro hleast hnot_high
    exact corridor_reentry_of_not_permanent_high hleast hnot_high
  · exact escape_state_pigeonhole_capacity hmin
  · exact escape_state_unblocked_candidate_avoids_history hmin
  · exact escape_state_descent_strictly_below_twice_clock hmin htwice
  · intro hhigh n hn
    exact ⟨permanent_high_subSum_capped_of_escape hhigh n hn,
           permanent_high_subCount_capped_of_escape hhigh n hn⟩

end Recaman
