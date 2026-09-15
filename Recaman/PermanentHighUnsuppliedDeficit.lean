import Recaman.PermanentHighCollision
import Recaman.PermanentHighRigidity
import Recaman.TailDowncrossingDichotomy
import Recaman.TailDowncrossingLedger
import Recaman.GlobalUnboundednessSupply
import Recaman.DriftResetAccumulation
import Recaman.CanonicalSSFreeSupply
import Recaman.DebtInvariant

namespace Recaman

open Recaman.CanonicalSSFreeSupply
open Recaman.DriftResetAccumulation
open Recaman.GlobalUnboundednessSupply

/-! # Permanent High Unsupplied Deficit and Super-Summit Escalation

In this module, we connect the forced `AASAAA` transition from the self-blocking
collision identity to the **unsupplied addition theory** (Theme 4 / E-324):

1. **Forced Unsupplied Addition in Every `AASAA` Episode**:
   Every `AASAA` sequence forces a third addition at step `n + 6`, producing
   the 3-addition run `A A A` across steps `n + 4, n + 5, n + 6`.
   Consequently, the 3-block around `n + 3` unconditionally contains at least
   one unsupplied addition:
   `1 ≤ unsuppliedCount canonicalSign (n + 3) 3`.

2. **Fourth Addition Forces Deficit ≥ 2**:
   If step `n + 7` is ALSO an addition, producing a 4-addition run `A A A A`,
   the unsupplied deficit increases to at least 2:
   `2 ≤ unsuppliedCount canonicalSign (n + 3) 4`.

3. **Super-Summit Escalation at Step n + 7**:
   The subtraction candidate at step `n + 7` is `a (n + 6) - (n + 7) = a n + 3n + 8`.
   We prove this candidate strictly differs from all 7 values in the current
   episode: `{a n, a (n + 1), ..., a (n + 6)}`.
   Therefore, if step `n + 7` fails to subtract, the blocker MUST come from an
   earlier epoch `j ≤ n - 1`, forcing the existence of a **super-summit**:
   `∃ j ≤ n - 1, a j = a n + 3n + 8 ≥ 5n + 8`.

4. **Guaranteed Subtraction under Super-Summit Bound**:
   In any segment without a prior super-summit (`∀ j ≤ n - 1, a j < 5n + 8`),
   step `n + 7` is GUARANTEED to subtract:
   `CanSubtract (n + 7) (stateAt (n + 6))`.
   When it subtracts:
   - It lands on `a (n + 7) = a n + 3n + 8 ≥ 5n + 8`.
   - It deposits `n + 7` into `subSum`, bringing the cumulative two-step
     subtraction deposit to `(n + 3) + (n + 7) = 2n + 10`.
-/

/-! ### Part 1: Canonical Sign Connection -/

/-- `canonicalSign n = true` when step `n + 1` cannot subtract (i.e. is an addition). -/
theorem canonicalSign_of_not_canSubtract
    {n : Nat}
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    canonicalSign (n : Int) = true := by
  rw [canonicalSign_nat]
  exact decide_eq_true hnot

/-- An `AASAA` sequence forces three consecutive additions in `canonicalSign`. -/
theorem aasaa_three_consecutive_canonicalSigns
    {n : Nat}
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hnot5 : ¬ CanSubtract (n + 5) (stateAt (n + 4))) :
    canonicalSign ((n + 3 : Nat) : Int) = true ∧
    canonicalSign (((n + 3 : Nat) : Int) + 1) = true ∧
    canonicalSign (((n + 3 : Nat) : Int) + 2) = true := by
  have hnot6 := no_aasaas_pattern hnot1 hnot2 hcan3 hnot4 hnot5
  have hsign4 := canonicalSign_of_not_canSubtract hnot4
  have hsign5 := canonicalSign_of_not_canSubtract hnot5
  have heq6 : (n + 5) + 1 = n + 6 := by omega
  have hnot6' : ¬ CanSubtract ((n + 5) + 1) (stateAt (n + 5)) := by
    rw [heq6]
    exact hnot6
  have hsign6 := canonicalSign_of_not_canSubtract hnot6'
  have h1 : ((n + 3 : Nat) : Int) + 1 = ((n + 4 : Nat) : Int) := by omega
  have h2 : ((n + 3 : Nat) : Int) + 2 = ((n + 5 : Nat) : Int) := by omega
  rw [h1, h2]
  exact ⟨hsign4, hsign5, hsign6⟩

/-- Every `AASAA` sequence unconditionally forces at least one unsupplied addition. -/
theorem aasaa_forces_unsupplied_addition
    {n : Nat}
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hnot5 : ¬ CanSubtract (n + 5) (stateAt (n + 4))) :
    1 ≤ unsuppliedCount canonicalSign ((n + 3 : Nat) : Int) 3 := by
  have ⟨h0, h1, h2⟩ := aasaa_three_consecutive_canonicalSigns hnot1 hnot2 hcan3 hnot4 hnot5
  exact three_consecutive_additions_unsupplied canonicalSign ((n + 3 : Nat) : Int) h0 h1 h2

/-! ### Part 2: Fourth Addition and Deficit ≥ 2 -/

/-- If step `n + 7` is also an addition, we have 4 consecutive additions in `canonicalSign`. -/
theorem aasaaa_four_consecutive_canonicalSigns
    {n : Nat}
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hnot5 : ¬ CanSubtract (n + 5) (stateAt (n + 4)))
    (hnot7 : ¬ CanSubtract (n + 7) (stateAt (n + 6))) :
    ∀ i : Nat, i < 4 → canonicalSign (((n + 3 : Nat) : Int) + (i : Int)) = true := by
  have ⟨h0, h1, h2⟩ := aasaa_three_consecutive_canonicalSigns hnot1 hnot2 hcan3 hnot4 hnot5
  have heq7 : (n + 6) + 1 = n + 7 := by omega
  have hnot7' : ¬ CanSubtract ((n + 6) + 1) (stateAt (n + 6)) := by
    rw [heq7]
    exact hnot7
  have hsign7 := canonicalSign_of_not_canSubtract hnot7'
  intro i hi
  rcases i with _ | _ | _ | _ | i
  · have : ((n + 3 : Nat) : Int) + ((0 : Nat) : Int) = ((n + 3 : Nat) : Int) := by omega
    rw [this]; exact h0
  · have : ((n + 3 : Nat) : Int) + ((1 : Nat) : Int) = ((n + 3 : Nat) : Int) + 1 := by omega
    rw [this]; exact h1
  · have : ((n + 3 : Nat) : Int) + ((2 : Nat) : Int) = ((n + 3 : Nat) : Int) + 2 := by omega
    rw [this]; exact h2
  · have : ((n + 3 : Nat) : Int) + ((3 : Nat) : Int) = ((n + 6 : Nat) : Int) := by omega
    rw [this]; exact hsign7
  · omega

/-- Four consecutive additions force an unsupplied deficit of at least 2. -/
theorem aasaaa_four_additions_unsupplied_deficit
    {n : Nat}
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hnot5 : ¬ CanSubtract (n + 5) (stateAt (n + 4)))
    (hnot7 : ¬ CanSubtract (n + 7) (stateAt (n + 6))) :
    2 ≤ unsuppliedCount canonicalSign ((n + 3 : Nat) : Int) 4 := by
  have hall := aasaaa_four_consecutive_canonicalSigns hnot1 hnot2 hcan3 hnot4 hnot5 hnot7
  have hd := consecutive_additions_unsupplied_deficit canonicalSign ((n + 3 : Nat) : Int) 4 (by omega) hall
  omega

/-! ### Part 3: Super-Summit Escalation at Step n + 7 -/

/-- The subtraction candidate at step `n + 7` strictly differs from all 7 terms in the
current episode `{a n, ..., a (n + 6)}`. -/
theorem aasaaa_candidate_not_in_current_episode
    {n : Nat}
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hnot5 : ¬ CanSubtract (n + 5) (stateAt (n + 4))) :
    ∀ t, n ≤ t → t ≤ n + 6 → a t ≠ a n + 3 * n + 8 := by
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
  have hstep5 := a_succ_of_not_canSubtract hnot5
  have heq5 : n + 4 + 1 = n + 5 := by omega
  rw [heq5] at hstep5
  have hval6 := aasaa_forces_third_addition hnot1 hnot2 hcan3 hnot4 hnot5
  have hlt : n + 3 < a (n + 2) := hcan3.1
  have hcases : t = n ∨ t = n + 1 ∨ t = n + 2 ∨ t = n + 3 ∨ t = n + 4 ∨ t = n + 5 ∨ t = n + 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

/-- If step `n + 7` fails to subtract after `AASAAA`, the blocker must have appeared at
some earlier time `j ≤ n - 1`, forcing a prior super-summit `a j ≥ 5n + 8`. -/
theorem aasaaa_fourth_addition_requires_super_summit
    {n : Nat} (hn_high : 2 * n ≤ a n)
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hnot5 : ¬ CanSubtract (n + 5) (stateAt (n + 4)))
    (hnot7 : ¬ CanSubtract (n + 7) (stateAt (n + 6))) :
    ∃ j, j ≤ n - 1 ∧ 5 * n + 8 ≤ a j ∧ a j = a n + 3 * n + 8 := by
  have hcand := aasaaa_subtraction_candidate hnot1 hnot2 hcan3 hnot4 hnot5
  have heq7 : (n + 6) + 1 = n + 7 := by omega
  have hnot7' : ¬ CanSubtract ((n + 6) + 1) (stateAt (n + 6)) := by
    rw [heq7]
    exact hnot7
  have hcases := not_canSubtract_cases hnot7'
  have hval6 := aasaa_forces_third_addition hnot1 hnot2 hcan3 hnot4 hnot5
  have hclock_ok : n + 7 < a (n + 6) := by omega
  rcases hcases with hsmall | hseen
  · omega
  · rw [hcand] at hseen
    rcases mem_valuesThrough_iff.mp hseen with ⟨j, hj, hval⟩
    have hj_lt : j ≤ n - 1 := by
      by_cases hj_ge : n ≤ j
      · have hne := aasaaa_candidate_not_in_current_episode hnot1 hnot2 hcan3 hnot4 hnot5 j hj_ge (by omega)
        exact False.elim (hne hval)
      · omega
    have hge : 5 * n + 8 ≤ a j := by omega
    exact ⟨j, hj_lt, hge, hval⟩

/-- In any segment without a prior super-summit of height `5n + 8`, step `n + 7`
is guaranteed to subtract! -/
theorem aasaaa_forced_subtraction_under_super_summit_bound
    {n : Nat} (hn_high : 2 * n ≤ a n)
    (hsummit : ∀ j, j ≤ n - 1 → a j < 5 * n + 8)
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hnot5 : ¬ CanSubtract (n + 5) (stateAt (n + 4))) :
    CanSubtract (n + 7) (stateAt (n + 6)) := by
  by_cases hcan7 : CanSubtract (n + 7) (stateAt (n + 6))
  · exact hcan7
  · rcases aasaaa_fourth_addition_requires_super_summit hn_high hnot1 hnot2 hcan3 hnot4 hnot5 hcan7 with ⟨j, hj, _hge, hval⟩
    have hlt := hsummit j hj
    omega

/-- When step `n + 7` subtracts, it lands precisely on `a n + 3n + 8 ≥ 5n + 8`. -/
theorem aasaaa_forced_subtraction_landing_value
    {n : Nat} (hn_high : 2 * n ≤ a n)
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hnot5 : ¬ CanSubtract (n + 5) (stateAt (n + 4)))
    (hcan7 : CanSubtract (n + 7) (stateAt (n + 6))) :
    a (n + 7) = a n + 3 * n + 8 ∧ 5 * n + 8 ≤ a (n + 7) := by
  have heq7 : (n + 6) + 1 = n + 7 := by omega
  have hcan7' : CanSubtract ((n + 6) + 1) (stateAt (n + 6)) := by
    rw [heq7]
    exact hcan7
  have hstep7 := a_succ_of_canSubtract hcan7'
  rw [heq7] at hstep7
  have hval6 := aasaa_forces_third_addition hnot1 hnot2 hcan3 hnot4 hnot5
  have hlt : n + 7 < a (n + 6) := hcan7.1
  have heq : a (n + 7) = a n + 3 * n + 8 := by omega
  have hge : 5 * n + 8 ≤ a (n + 7) := by omega
  exact ⟨heq, hge⟩

/-- Grand Synthesis Theorem:
Every `AASAA` sequence:
1. Forces at least one unsupplied addition in the 3-block around `n + 3`.
2. If step `n + 7` adds, forces at least two unsupplied additions and requires
   a historical super-summit `a j ≥ 5n + 8` (j ≤ n - 1).
3. If past values are bounded by `5n + 8`, step `n + 7` MUST subtract,
   landing on `a (n + 7) = a n + 3n + 8 ≥ 5n + 8`. -/
theorem grand_permanent_high_unsupplied_deficit_synthesis
    {n : Nat} (hn_high : 2 * n ≤ a n)
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hnot5 : ¬ CanSubtract (n + 5) (stateAt (n + 4))) :
    1 ≤ unsuppliedCount canonicalSign ((n + 3 : Nat) : Int) 3 ∧
    ((¬ CanSubtract (n + 7) (stateAt (n + 6)) →
        2 ≤ unsuppliedCount canonicalSign ((n + 3 : Nat) : Int) 4 ∧
        ∃ j, j ≤ n - 1 ∧ 5 * n + 8 ≤ a j) ∧
     ((∀ j, j ≤ n - 1 → a j < 5 * n + 8) →
        CanSubtract (n + 7) (stateAt (n + 6)) ∧
        a (n + 7) = a n + 3 * n + 8)) := by
  have hdef1 := aasaa_forces_unsupplied_addition hnot1 hnot2 hcan3 hnot4 hnot5
  refine ⟨hdef1, ?_, ?_⟩
  · intro hnot7
    have hdef2 := aasaaa_four_additions_unsupplied_deficit hnot1 hnot2 hcan3 hnot4 hnot5 hnot7
    rcases aasaaa_fourth_addition_requires_super_summit hn_high hnot1 hnot2 hcan3 hnot4 hnot5 hnot7 with ⟨j, hj, hge, _heq⟩
    exact ⟨hdef2, j, hj, hge⟩
  · intro hsummit
    have hcan7 := aasaaa_forced_subtraction_under_super_summit_bound hn_high hsummit hnot1 hnot2 hcan3 hnot4 hnot5
    have hland := aasaaa_forced_subtraction_landing_value hn_high hnot1 hnot2 hcan3 hnot4 hnot5 hcan7
    exact ⟨hcan7, hland.1⟩

end Recaman
