import Recaman.ActualDescent

namespace Recaman

/-- The arithmetic condition saying that k consecutive subtraction steps from
value v at time f would land on the positive target m. -/
def TargetEquation (f v m k : Nat) : Prop :=
  m + descentDrop f k = v

/-- The complete result of a finite target-directed descent attempt. -/
inductive TargetOutcome (f v m k : Nat) : Prop where
  | lands
      (run : DescentRun f v k)
      (landing : a (f + k) = m)
  | blocked
      (length y : Nat)
      (before_target : length < k)
      (blocker : ActualBlocker f v length y)

theorem DescentRun.extend {f v length : Nat}
    (run : DescentRun f v length)
    (hcan : CanSubtract (f + length + 1) (stateAt (f + length))) :
    DescentRun f v (length + 1) := by
  constructor
  · exact run.start_value
  · intro i hi
    have hile : i ≤ length := Nat.le_of_lt_succ hi
    rcases Nat.eq_or_lt_of_le hile with heq | hlt
    · subst i
      exact hcan
    · exact run.subtracts i hlt

theorem descentDrop_strict (f : Nat) {i j : Nat} (hij : i < j) :
    descentDrop f i < descentDrop f j := by
  have hstep : descentDrop f i < descentDrop f (i + 1) := by
    rw [descentDrop_succ]
    exact Nat.lt_add_of_pos_right (by omega)
  have htail : descentDrop f (i + 1) ≤ descentDrop f j :=
    descentDrop_mono f (Nat.succ_le_of_lt hij)
  exact Nat.lt_of_lt_of_le hstep htail

/-- Finite target-descent dichotomy.

If the triangular-number equation predicts a positive target m after k
subtractions, then the real Recamán orbit either performs all k subtractions
and lands on m, or it has a first positive previously-seen blocker before that
landing. -/
theorem targetDescent_dichotomy {f v : Nat} (hfirst : FirstAt a v f) :
    ∀ k m, 0 < m → TargetEquation f v m k → TargetOutcome f v m k := by
  intro k
  induction k with
  | zero =>
      intro m hm hequation
      refine TargetOutcome.lands ?_ ?_
      · constructor
        · exact hfirst.1
        · intro i hi
          omega
      · unfold TargetEquation at hequation
        simp [descentDrop, upperTri] at hequation
        have hstart := hfirst.1
        simpa using (show a f = m by omega)
  | succ k ih =>
      intro m hm hequation
      let intermediate := m + (f + k + 1)
      have hintermediate : 0 < intermediate := by
        simp [intermediate]
        omega
      have hprefixEquation : TargetEquation f v intermediate k := by
        unfold TargetEquation at hequation ⊢
        have hdrop := descentDrop_succ f k
        simp only [intermediate]
        omega
      cases ih intermediate hintermediate hprefixEquation with
      | blocked length y hbefore blocker =>
          exact TargetOutcome.blocked length y (by omega) blocker
      | lands run hlanding =>
          have hpositive : f + k + 1 < a (f + k) := by
            simp only [intermediate] at hlanding
            omega
          have hcandidate : a (f + k) - (f + k + 1) = m := by
            simp only [intermediate] at hlanding
            omega
          by_cases hcan : CanSubtract (f + k + 1) (stateAt (f + k))
          · refine TargetOutcome.lands (run.extend hcan) ?_
            have hstep := a_succ_of_canSubtract hcan
            change a ((f + k) + 1) = m
            omega
          · have hpositiveState :
                f + k + 1 < (stateAt (f + k)).value := by
              simpa [a] using hpositive
            have hseenState :
                (stateAt (f + k)).value - (f + k + 1) ∈
                  (stateAt (f + k)).seen := by
              by_cases hseen :
                  (stateAt (f + k)).value - (f + k + 1) ∈
                    (stateAt (f + k)).seen
              · exact hseen
              · exact False.elim (hcan ⟨hpositiveState, hseen⟩)
            have hmseen : m ∈ valuesThrough (f + k) := by
              change m ∈ (stateAt (f + k)).seen
              rw [← hcandidate]
              exact hseenState
            have blocker : ActualBlocker f v k m := {
              first_v := hfirst
              run := run
              blocker_positive := hpositive
              blocker_candidate := hcandidate
              blocker_seen := hmseen
            }
            exact TargetOutcome.blocked k m (by omega) blocker

/-- A blocker produced during a target attempt stays at or above the target
and is strictly below the starting value.  It equals m exactly at the final
attempted step; an earlier blocker is strictly above m. -/
theorem targetBlocker_bounds {f v m k length y : Nat}
    (hequation : TargetEquation f v m k)
    (hbefore : length < k)
    (blocker : ActualBlocker f v length y) :
    m ≤ y ∧ y < v ∧
      (length + 1 = k → y = m) ∧
      (length + 1 < k → m < y) := by
  have hblocker := blocker.blocker_eq_drop
  have hdropLe : descentDrop f (length + 1) ≤ descentDrop f k :=
    descentDrop_mono f (Nat.succ_le_of_lt hbefore)
  have hylt : y < v := blocker.doubleDescent.1
  unfold TargetEquation at hequation
  constructor
  · omega
  · refine ⟨hylt, ?_, ?_⟩
    · intro heq
      subst k
      omega
    · intro hstrict
      have hdropLt : descentDrop f (length + 1) < descentDrop f k :=
        descentDrop_strict f hstrict
      omega

/-- User-facing corollary: a valid target attempt either reaches m or exposes
a blocker whose value and first-occurrence time both descend. -/
theorem targetDescent_lands_or_doubleDescent {f v m k : Nat}
    (hfirst : FirstAt a v f) (hm : 0 < m)
    (hequation : TargetEquation f v m k) :
    a (f + k) = m ∨
      ∃ length y fy,
        length < k ∧ m ≤ y ∧ y < v ∧
        FirstAt a y fy ∧ fy < f := by
  cases targetDescent_dichotomy hfirst k m hm hequation with
  | lands _ hlanding =>
      exact Or.inl hlanding
  | blocked length y hbefore blocker =>
      rcases blocker.doubleDescent with ⟨hylt, fy, hfirstY, hfy⟩
      have hmle := (targetBlocker_bounds hequation hbefore blocker).1
      exact Or.inr ⟨length, y, fy, hbefore, hmle, hylt, hfirstY, hfy⟩

end Recaman
