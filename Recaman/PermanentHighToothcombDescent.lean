import Recaman.PermanentHighCollision
import Recaman.PermanentHighRigidity
import Recaman.TailDowncrossingDichotomy
import Recaman.TailDowncrossingLedger
import Recaman.DebtInvariant

namespace Recaman

/-! # Permanent High Toothcomb Descent and `AASA` Branching Dichotomy

This module formalizes the mechanism of the Recamán **toothcomb descent** and
the branching dichotomy of `AASA` sequences in the permanent high regime:

1. **Universal Toothcomb Unit Decrement Identity**:
   Whenever step `k + 1` is an addition, the subtraction candidate at step `k + 2`
   is precisely `a k - 1`:
   `cand(k + 2) = a(k + 1) - (k + 2) = a k - 1`.
   When step `k + 2` subtracts, the value decrements by 1: `a(k + 2) = a k - 1`.

2. **The `AASA` Subtraction Candidate**:
   In any `AASA` episode starting at `n`, the subtraction candidate at step `n + 5`
   is `a(n + 4) - (n + 5) = a(n) + n - 1 = a(n + 3) - 1`.

3. **Episode Avoidance for `n ≥ 2`**:
   For any `n ≥ 2`, this candidate strictly avoids all 5 values in the episode:
   `{a n, a(n + 1), a(n + 2), a(n + 3), a(n + 4)}`.

4. **`AASAA` Requires a Prior Summit `a j ≥ 3n - 1`**:
   Because the candidate avoids the current episode, step `n + 5` can fail to subtract
   (yielding `AASAA`) ONLY IF the candidate already appeared at an earlier time
   `j ≤ n - 1`.
   In the high regime `2n ≤ a n`, this forces a historical summit:
   `∃ j ≤ n - 1, a j = a n + n - 1 ≥ 3n - 1`.

5. **Guaranteed `AASAS` Toothcomb Initiation**:
   In any segment where past values are bounded by `3n - 1` (`∀ j ≤ n - 1, a j < 3n - 1`),
   step `n + 5` is GUARANTEED to subtract:
   `CanSubtract (n + 5) (stateAt (n + 4))`.
   This forces the pattern `AASAS` and strictly prevents `AASAA` from forming.
   When it subtracts, it lands on `a(n + 5) = a(n + 3) - 1 = a n + n - 1`.

6. **Step n + 7 Candidate and Continued Toothcomb**:
   If step `n + 6` adds after `AASAS`, the candidate at step `n + 7` is:
   `a(n + 6) - (n + 7) = a(n + 5) - 1 = a n + n - 2`.
   For `n ≥ 3`, this candidate strictly avoids all 7 values in `{a n, ..., a(n + 6)}`.
-/

/-! ### Part 1: Universal Toothcomb Decrement Identity -/

/-- Universal unit decrement identity: after an addition at step `k + 1`,
the subtraction candidate at step `k + 2` is precisely `a k - 1`. -/
theorem toothcomb_unit_decrement_candidate
    {k : Nat}
    (hnot : ¬ CanSubtract (k + 1) (stateAt k)) :
    a (k + 1) - (k + 2) = a k - 1 := by
  have hstep := a_succ_of_not_canSubtract hnot
  omega

/-- When step `k + 2` can subtract after an addition at step `k + 1`,
it lands precisely on `a k - 1`. -/
theorem toothcomb_subtraction_landing_value
    {k : Nat}
    (hnot : ¬ CanSubtract (k + 1) (stateAt k))
    (hcan : CanSubtract (k + 2) (stateAt (k + 1))) :
    a (k + 2) = a k - 1 := by
  have heq : (k + 1) + 1 = k + 2 := by omega
  have hcan' : CanSubtract ((k + 1) + 1) (stateAt (k + 1)) := by
    rw [heq]
    exact hcan
  have hstep2 := a_succ_of_canSubtract hcan'
  rw [heq] at hstep2
  have hcand := toothcomb_unit_decrement_candidate hnot
  omega

/-! ### Part 2: `AASA` Subtraction Candidate and Episode Avoidance -/

/-- In any `AASA` sequence starting at `n`, the subtraction candidate at step `n + 5`
is `a n + n - 1 = a (n + 3) - 1`. -/
theorem aasa_subtraction_candidate
    {n : Nat}
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3))) :
    a (n + 4) - (n + 5) = a n + n - 1 ∧
    a (n + 3) - 1 = a n + n - 1 := by
  have hstep1 := a_succ_of_not_canSubtract hnot1
  have hstep2 := a_succ_of_not_canSubtract hnot2
  have heq2 : n + 1 + 1 = n + 2 := by omega
  rw [heq2] at hstep2
  have heq3 : (n + 2) + 1 = n + 3 := by omega
  have hcan3' : CanSubtract ((n + 2) + 1) (stateAt (n + 2)) := by
    rw [heq3]
    exact hcan3
  have hstep3 := a_succ_of_canSubtract hcan3'
  rw [heq3] at hstep3
  have hstep4 := a_succ_of_not_canSubtract hnot4
  have heq4 : n + 3 + 1 = n + 4 := by omega
  rw [heq4] at hstep4
  have hlt : n + 3 < a (n + 2) := hcan3.1
  have h1 : a (n + 4) - (n + 5) = a n + n - 1 := by omega
  have h2 : a (n + 3) - 1 = a n + n - 1 := by omega
  exact ⟨h1, h2⟩

/-- For `n ≥ 2`, the subtraction candidate `a n + n - 1` strictly differs from all
5 values in the current episode `{a n, ..., a (n + 4)}`. -/
theorem aasa_candidate_not_in_current_episode
    {n : Nat} (hn2 : 2 ≤ n)
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3))) :
    ∀ t, n ≤ t → t ≤ n + 4 → a t ≠ a n + n - 1 := by
  intro t hnt htn4
  have hstep1 := a_succ_of_not_canSubtract hnot1
  have hstep2 := a_succ_of_not_canSubtract hnot2
  have heq2 : n + 1 + 1 = n + 2 := by omega
  rw [heq2] at hstep2
  have heq3 : (n + 2) + 1 = n + 3 := by omega
  have hcan3' : CanSubtract ((n + 2) + 1) (stateAt (n + 2)) := by
    rw [heq3]
    exact hcan3
  have hstep3 := a_succ_of_canSubtract hcan3'
  rw [heq3] at hstep3
  have hstep4 := a_succ_of_not_canSubtract hnot4
  have heq4 : n + 3 + 1 = n + 4 := by omega
  rw [heq4] at hstep4
  have _hlt : n + 3 < a (n + 2) := hcan3.1
  have hcases : t = n ∨ t = n + 1 ∨ t = n + 2 ∨ t = n + 3 ∨ t = n + 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega

/-! ### Part 3: Branching Dichotomy and Summit Escalation -/

/-- In the high regime `2n ≤ a n` with `n ≥ 2`, if step `n + 5` fails to subtract
(yielding `AASAA`), the blocker must have appeared at some earlier time `j ≤ n - 1`,
forcing a historical summit `a j ≥ 3n - 1`. -/
theorem aasa_fifth_addition_requires_prior_summit
    {n : Nat} (hn_high : 2 * n ≤ a n) (hn2 : 2 ≤ n)
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hnot5 : ¬ CanSubtract (n + 5) (stateAt (n + 4))) :
    ∃ j, j ≤ n - 1 ∧ 3 * n - 1 ≤ a j ∧ a j = a n + n - 1 := by
  have ⟨hcand, _⟩ := aasa_subtraction_candidate hnot1 hnot2 hcan3 hnot4
  have heq5 : (n + 4) + 1 = n + 5 := by omega
  have hnot5' : ¬ CanSubtract ((n + 4) + 1) (stateAt (n + 4)) := by
    rw [heq5]
    exact hnot5
  have hcases := not_canSubtract_cases hnot5'
  have hstep1 := a_succ_of_not_canSubtract hnot1
  have hstep2 := a_succ_of_not_canSubtract hnot2
  have heq2 : n + 1 + 1 = n + 2 := by omega
  rw [heq2] at hstep2
  have heq3 : (n + 2) + 1 = n + 3 := by omega
  have hcan3' : CanSubtract ((n + 2) + 1) (stateAt (n + 2)) := by
    rw [heq3]
    exact hcan3
  have hstep3 := a_succ_of_canSubtract hcan3'
  rw [heq3] at hstep3
  have hstep4 := a_succ_of_not_canSubtract hnot4
  have heq4 : n + 3 + 1 = n + 4 := by omega
  rw [heq4] at hstep4
  have _hlt : n + 3 < a (n + 2) := hcan3.1
  rcases hcases with hsmall | hseen
  · omega
  · rw [hcand] at hseen
    rcases mem_valuesThrough_iff.mp hseen with ⟨j, hj, hval⟩
    have hj_lt : j ≤ n - 1 := by
      by_cases hj_ge : n ≤ j
      · have hne := aasa_candidate_not_in_current_episode hn2 hnot1 hnot2 hcan3 hnot4 j hj_ge (by omega)
        exact False.elim (hne hval)
      · omega
    have hge : 3 * n - 1 ≤ a j := by omega
    exact ⟨j, hj_lt, hge, hval⟩

/-- In any segment without a prior summit of height `3n - 1`, step `n + 5`
is GUARANTEED to subtract, forcing the pattern `AASAS` and strictly preventing `AASAA`! -/
theorem aasa_forced_subtraction_under_summit_bound
    {n : Nat} (hn_high : 2 * n ≤ a n) (hn2 : 2 ≤ n)
    (hsummit : ∀ j, j ≤ n - 1 → a j < 3 * n - 1)
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3))) :
    CanSubtract (n + 5) (stateAt (n + 4)) := by
  by_cases hcan5 : CanSubtract (n + 5) (stateAt (n + 4))
  · exact hcan5
  · rcases aasa_fifth_addition_requires_prior_summit hn_high hn2 hnot1 hnot2 hcan3 hnot4 hcan5 with ⟨j, hj, _hge, _hval⟩
    have hlt := hsummit j hj
    omega

/-- When step `n + 5` subtracts, it lands on `a (n + 5) = a (n + 3) - 1 = a n + n - 1`. -/
theorem aasa_forced_subtraction_landing_value
    {n : Nat}
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hcan5 : CanSubtract (n + 5) (stateAt (n + 4))) :
    a (n + 5) = a (n + 3) - 1 ∧ a (n + 5) = a n + n - 1 := by
  have heq5 : (n + 4) + 1 = n + 5 := by omega
  have hcan5' : CanSubtract ((n + 4) + 1) (stateAt (n + 4)) := by
    rw [heq5]
    exact hcan5
  have hstep5 := a_succ_of_canSubtract hcan5'
  rw [heq5] at hstep5
  have ⟨hcand, hrec⟩ := aasa_subtraction_candidate hnot1 hnot2 hcan3 hnot4
  have _hlt : n + 5 < a (n + 4) := hcan5.1
  have heq : a (n + 5) = a n + n - 1 := by omega
  have heq_rec : a (n + 5) = a (n + 3) - 1 := by omega
  exact ⟨heq_rec, heq⟩

/-! ### Part 4: Step n + 7 Candidate and Continued Toothcomb -/

/-- If step `n + 6` adds after `AASAS`, the subtraction candidate at step `n + 7`
is `a (n + 5) - 1 = a n + n - 2`. -/
theorem aasas_step7_subtraction_candidate
    {n : Nat}
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hcan5 : CanSubtract (n + 5) (stateAt (n + 4)))
    (hnot6 : ¬ CanSubtract (n + 6) (stateAt (n + 5))) :
    a (n + 6) - (n + 7) = a (n + 5) - 1 ∧
    a (n + 6) - (n + 7) = a n + n - 2 := by
  have ⟨_hrec, hval5⟩ := aasa_forced_subtraction_landing_value hnot1 hnot2 hcan3 hnot4 hcan5
  have heq6 : (n + 5) + 1 = n + 6 := by omega
  have hnot6' : ¬ CanSubtract ((n + 5) + 1) (stateAt (n + 5)) := by
    rw [heq6]
    exact hnot6
  have hstep6 := a_succ_of_not_canSubtract hnot6'
  rw [heq6] at hstep6
  have h1 : a (n + 6) - (n + 7) = a (n + 5) - 1 := by omega
  have h2 : a (n + 6) - (n + 7) = a n + n - 2 := by omega
  exact ⟨h1, h2⟩

/-- For `n ≥ 3`, the candidate `a n + n - 2` strictly avoids all 7 values in `{a n, ..., a (n + 6)}`. -/
theorem aasas_step7_candidate_not_in_current_episode
    {n : Nat} (hn3 : 3 ≤ n)
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hcan5 : CanSubtract (n + 5) (stateAt (n + 4)))
    (hnot6 : ¬ CanSubtract (n + 6) (stateAt (n + 5))) :
    ∀ t, n ≤ t → t ≤ n + 6 → a t ≠ a n + n - 2 := by
  intro t hnt htn6
  have hstep1 := a_succ_of_not_canSubtract hnot1
  have hstep2 := a_succ_of_not_canSubtract hnot2
  have heq2 : n + 1 + 1 = n + 2 := by omega
  rw [heq2] at hstep2
  have heq3 : (n + 2) + 1 = n + 3 := by omega
  have hcan3' : CanSubtract ((n + 2) + 1) (stateAt (n + 2)) := by
    rw [heq3]
    exact hcan3
  have hstep3 := a_succ_of_canSubtract hcan3'
  rw [heq3] at hstep3
  have hstep4 := a_succ_of_not_canSubtract hnot4
  have heq4 : n + 3 + 1 = n + 4 := by omega
  rw [heq4] at hstep4
  have ⟨_hrec, hval5⟩ := aasa_forced_subtraction_landing_value hnot1 hnot2 hcan3 hnot4 hcan5
  have heq6 : (n + 5) + 1 = n + 6 := by omega
  have hnot6' : ¬ CanSubtract ((n + 5) + 1) (stateAt (n + 5)) := by
    rw [heq6]
    exact hnot6
  have hstep6 := a_succ_of_not_canSubtract hnot6'
  rw [heq6] at hstep6
  have _hlt : n + 3 < a (n + 2) := hcan3.1
  have hcases : t = n ∨ t = n + 1 ∨ t = n + 2 ∨ t = n + 3 ∨ t = n + 4 ∨ t = n + 5 ∨ t = n + 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

/-! ### Part 5: Grand Toothcomb Branching Synthesis -/

/-- Grand synthesis theorem:
In the permanent high regime `2n ≤ a n` with `n ≥ 2`:
1. Every `AASA` sequence either:
   - Yields `AASAA`, which requires a prior historical summit `a j ≥ 3n - 1` (j ≤ n - 1),
     or
   - Yields `AASAS`, initiating the toothcomb descent landing on `a(n + 5) = a(n + 3) - 1`.
2. In the absence of a prior summit `a j ≥ 3n - 1`, the transition to `AASAS` is
   unconditionally forced, and `AASAA` is strictly impossible!
3. After `AASAS`, an addition at step `n + 6` produces the candidate `a(n + 5) - 1 = a n + n - 2`,
   continuing the toothcomb decrement by 1. -/
theorem grand_permanent_high_toothcomb_branching_synthesis
    {n : Nat} (hn_high : 2 * n ≤ a n) (hn2 : 2 ≤ n)
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3))) :
    (¬ CanSubtract (n + 5) (stateAt (n + 4)) →
       ∃ j, j ≤ n - 1 ∧ 3 * n - 1 ≤ a j ∧ a j = a n + n - 1) ∧
    ((∀ j, j ≤ n - 1 → a j < 3 * n - 1) →
       CanSubtract (n + 5) (stateAt (n + 4)) ∧
       a (n + 5) = a (n + 3) - 1 ∧
       a (n + 5) = a n + n - 1) ∧
    (∀ (_hcan5 : CanSubtract (n + 5) (stateAt (n + 4)))
       (_hnot6 : ¬ CanSubtract (n + 6) (stateAt (n + 5))),
       a (n + 6) - (n + 7) = a (n + 5) - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hnot5
    exact aasa_fifth_addition_requires_prior_summit hn_high hn2 hnot1 hnot2 hcan3 hnot4 hnot5
  · intro hsummit
    have hcan5 := aasa_forced_subtraction_under_summit_bound hn_high hn2 hsummit hnot1 hnot2 hcan3 hnot4
    have ⟨hrec, hval⟩ := aasa_forced_subtraction_landing_value hnot1 hnot2 hcan3 hnot4 hcan5
    exact ⟨hcan5, hrec, hval⟩
  · intro hcan5 hnot6
    have ⟨hcand, _⟩ := aasas_step7_subtraction_candidate hnot1 hnot2 hcan3 hnot4 hcan5 hnot6
    exact hcand

end Recaman
