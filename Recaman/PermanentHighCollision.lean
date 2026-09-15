import Recaman.PermanentHighRigidity
import Recaman.TailDowncrossingDichotomy
import Recaman.TailDowncrossingLedger
import Recaman.DebtInvariant

namespace Recaman

/-! # Permanent High Collision Identity and Forced Summit Escalation

In this module, we formalize the fundamental **Self-Blocking Collision Identity**
that eliminates pseudo-periodic 3-cycles `AAS AAS` in the Recamán sequence:

1. **The Universal Collision Identity**:
   For any base time `n`, if the orbit executes the sequence `A A S A A` across
   steps `n + 1, ..., n + 5`, the candidate value for subtraction at step `n + 6`
   is ALGEBRAICALLY IDENTICAL to the peak value visited at step `n + 2`:
   `a (n + 5) - (n + 6) = a (n + 2)`.

2. **Historical Collision and Refutation of AASAAS**:
   Because step `n + 2` is in the history (`n + 2 ≤ n + 5`), the candidate
   `a (n + 2)` is already present in `valuesThrough (n + 5)`.
   Therefore, step `n + 6` CANNOT subtract:
   `¬ CanSubtract (n + 6) (stateAt (n + 5))`.
   The pattern `A A S A A S` is strictly impossible in the Recamán sequence!

3. **Forced Third Addition and Summit Escalation**:
   Any `A A S A A` sequence is strictly forced to execute a third addition at
   step `n + 6`, producing the 3-addition run `A A S A A A`.
   The value jumps to `a (n + 6) = a n + 4n + 15 ≥ 6n + 15`, elevating the
   height into quotient band `q ≥ 4`.

4. **Self-Consistent Summit Justification**:
   The third addition at step `n + 6` requires an earlier summit `3(n + 3) ≤ a j`.
   The previous peak `a (n + 2) = a n + 2n + 3 ≥ 4n + 3` serves this exact role,
   simultaneously blocking the subtraction at step `n + 6` and justifying the
   ensuing addition run!
-/

/-! ### Part 1: The Algebraic Collision Identity -/

/-- Under any `A A S A A` sequence starting at `n`, the candidate for subtraction
at step `n + 6` equals `a (n + 2)`. -/
theorem aasaas_subtraction_candidate_collision
    {n : Nat}
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hnot5 : ¬ CanSubtract (n + 5) (stateAt (n + 4))) :
    a (n + 5) - (n + 6) = a (n + 2) := by
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
  have hlt : n + 3 < a (n + 2) := hcan3.1
  omega

/-- The candidate at step `n + 6` already belongs to `valuesThrough (n + 5)`. -/
theorem aasaas_candidate_in_valuesThrough
    {n : Nat}
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hnot5 : ¬ CanSubtract (n + 5) (stateAt (n + 4))) :
    a (n + 5) - (n + 6) ∈ valuesThrough (n + 5) := by
  have heq := aasaas_subtraction_candidate_collision hnot1 hnot2 hcan3 hnot4 hnot5
  rw [heq]
  have hle : n + 2 ≤ n + 5 := by omega
  exact mem_valuesThrough_iff.mpr ⟨n + 2, hle, rfl⟩

/-- The pattern `A A S A A S` is strictly impossible in the Recamán sequence:
step `n + 6` cannot subtract because its candidate is the historical peak `a (n + 2)`. -/
theorem no_aasaas_pattern
    {n : Nat}
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hnot5 : ¬ CanSubtract (n + 5) (stateAt (n + 4))) :
    ¬ CanSubtract (n + 6) (stateAt (n + 5)) := by
  intro hcan6
  have hseen := aasaas_candidate_in_valuesThrough hnot1 hnot2 hcan3 hnot4 hnot5
  have heq6 : (n + 5) + 1 = n + 6 := by omega
  have hcan6' : CanSubtract ((n + 5) + 1) (stateAt (n + 5)) := by
    rw [heq6]
    exact hcan6
  exact hcan6'.2 hseen

/-! ### Part 2: Forced Third Addition Transition -/

/-- Any `A A S A A` sequence is strictly forced to execute a third addition at
step `n + 6`, reaching `a (n + 6) = a n + 4n + 15`. -/
theorem aasaa_forces_third_addition
    {n : Nat}
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hnot5 : ¬ CanSubtract (n + 5) (stateAt (n + 4))) :
    a (n + 6) = a n + 4 * n + 15 := by
  have hnot6 := no_aasaas_pattern hnot1 hnot2 hcan3 hnot4 hnot5
  have heq6 : (n + 5) + 1 = n + 6 := by omega
  have hnot6' : ¬ CanSubtract ((n + 5) + 1) (stateAt (n + 5)) := by
    rw [heq6]
    exact hnot6
  have hstep6 := a_succ_of_not_canSubtract hnot6'
  rw [heq6] at hstep6
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
  have hlt : n + 3 < a (n + 2) := hcan3.1
  omega

/-- The forced third addition elevates the orbit value to at least `6n + 15`. -/
theorem aasaaa_value_ge_six_times
    {n : Nat} (hn_high : 2 * n ≤ a n)
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hnot5 : ¬ CanSubtract (n + 5) (stateAt (n + 4))) :
    6 * n + 15 ≤ a (n + 6) := by
  have hval := aasaa_forces_third_addition hnot1 hnot2 hcan3 hnot4 hnot5
  omega

/-- The peak at step `n + 2` satisfies `3(n + 3) ≤ a (n + 2)`, thereby providing
the prior summit required for the 3-addition run. -/
theorem aasaaa_satisfies_prior_summit
    {n : Nat} (hn6 : 6 ≤ n) (hn_high : 2 * n ≤ a n)
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1))) :
    3 * (n + 3) ≤ a (n + 2) := by
  have hstep1 := a_succ_of_not_canSubtract hnot1
  have hstep2 := a_succ_of_not_canSubtract hnot2
  have heq2 : n + 1 + 1 = n + 2 := by omega
  rw [heq2] at hstep2
  omega

/-! ### Part 3: Step n + 7 Subtraction Candidate -/

/-- The subtraction candidate at step `n + 7` equals `a n + 3n + 8`. -/
theorem aasaaa_subtraction_candidate
    {n : Nat}
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hnot5 : ¬ CanSubtract (n + 5) (stateAt (n + 4))) :
    a (n + 6) - (n + 7) = a n + 3 * n + 8 := by
  have hval := aasaa_forces_third_addition hnot1 hnot2 hcan3 hnot4 hnot5
  omega

/-- The candidate at step `n + 7` strictly sits between `a (n + 4)` and `a (n + 5)`. -/
theorem aasaaa_subtraction_candidate_strictly_between
    {n : Nat}
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hnot5 : ¬ CanSubtract (n + 5) (stateAt (n + 4))) :
    a (n + 4) < a (n + 6) - (n + 7) ∧ a (n + 6) - (n + 7) < a (n + 5) := by
  have hcand := aasaaa_subtraction_candidate hnot1 hnot2 hcan3 hnot4 hnot5
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
  have hlt : n + 3 < a (n + 2) := hcan3.1
  omega

/-! ### Part 4: Grand Collision Synthesis -/

/-- Grand Synthesis Theorem:
Under any `A A S A A` sequence starting at `n`:
- Step `n + 6` subtraction candidate hits `a (n + 2)` exactly.
- `A A S A A S` is strictly impossible: step `n + 6` must be an addition.
- Step `n + 6` reaches `a n + 4n + 15 ≥ 6n + 15`.
- Step `n + 2` peak was `≥ 3(n + 3)`, providing the prior summit justification. -/
theorem grand_permanent_high_collision_resolution
    {n : Nat} (hn6 : 6 ≤ n) (hn_high : 2 * n ≤ a n)
    (hnot1 : ¬ CanSubtract (n + 1) (stateAt n))
    (hnot2 : ¬ CanSubtract (n + 2) (stateAt (n + 1)))
    (hcan3 : CanSubtract (n + 3) (stateAt (n + 2)))
    (hnot4 : ¬ CanSubtract (n + 4) (stateAt (n + 3)))
    (hnot5 : ¬ CanSubtract (n + 5) (stateAt (n + 4))) :
    a (n + 5) - (n + 6) = a (n + 2) ∧
    ¬ CanSubtract (n + 6) (stateAt (n + 5)) ∧
    a (n + 6) = a n + 4 * n + 15 ∧
    6 * n + 15 ≤ a (n + 6) ∧
    3 * (n + 3) ≤ a (n + 2) := by
  have hcoll := aasaas_subtraction_candidate_collision hnot1 hnot2 hcan3 hnot4 hnot5
  have hno := no_aasaas_pattern hnot1 hnot2 hcan3 hnot4 hnot5
  have hval := aasaa_forces_third_addition hnot1 hnot2 hcan3 hnot4 hnot5
  have hge := aasaaa_value_ge_six_times hn_high hnot1 hnot2 hcan3 hnot4 hnot5
  have hsummit := aasaaa_satisfies_prior_summit hn6 hn_high hnot1 hnot2
  exact ⟨hcoll, hno, hval, hge, hsummit⟩

end Recaman
