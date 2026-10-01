import Recaman.OrbitBounds
import Recaman.Basic
import Recaman.History
import Recaman.DebtInvariant
import Recaman.ActualDescent

namespace Recaman

/-! # Permanent High Internal Blocker and Pre-Horizon Immunity

This module formalizes the structural obstruction governing historical blockers
in the Recamán permanent high regime (`2n ≤ a n`):

1. **Candidate Height Lower Bound (`candidate_subtraction_lower_bound`)**:
   In any high regime state `2n ≤ a n`, the subtraction candidate strictly
   satisfies:
   `n - 1 ≤ a n - (n + 1)`.

2. **Pre-Horizon Ceiling (`pre_horizon_value_le_upperTri`)**:
   For any horizon `H` and any pre-horizon time `j < H`, the value is bounded
   by the triangular number:
   `a j ≤ upperTri H`.

3. **Pre-Horizon Blocker Immunity (`pre_horizon_blocker_impossible`)**:
   For any `n ≥ upperTri H + 2` in the high regime, the subtraction candidate
   strictly exceeds the triangular ceiling:
   `upperTri H < a n - (n + 1)`.
   Consequently, NO pre-horizon state `j < H` can EVER block step `n + 1`:
   `∀ j < H, a j ≠ a n - (n + 1)`.

4. **Pre-Horizon History Avoidance (`pre_horizon_valuesThrough_avoidance`)**:
   For `1 ≤ H`, the candidate strictly avoids the pre-horizon history list:
   `a n - (n + 1) ∉ valuesThrough (H - 1)`.

5. **Internal Blocker Forcing (`not_canSubtract_forces_tail_blocker`)**:
   Whenever step `n + 1` cannot subtract (`¬ CanSubtract (n + 1) (stateAt n)`),
   the blocker is mathematically FORCED to come from the high tail itself:
   `∃ j, H ≤ j ∧ j ≤ n ∧ a j = a n - (n + 1)`.

6. **Recent State Exclusion (`tail_blocker_not_current`, `tail_blocker_not_previous`, `tail_blocker_not_two_back`)**:
   The internal blocker can NEVER be the current state `n`, the previous state `n - 1`,
   or the two-back state `n - 2` (for `n ≥ 3`).
   Hence, the blocker must precede the current step by at least 3 steps:
   `j ≤ n - 3`.

7. **Internal Blocker Height Elevation (`internal_blocker_forces_height_elevation`)**:
   Because the internal blocker `j ≥ H` belongs to the permanent high regime,
   its value satisfies `2j ≤ a j`. This forces an orbit height elevation:
   `2j + n + 1 ≤ a n` and in particular `2H + n + 1 ≤ a n`.

8. **Grand Synthesis (`grand_permanent_high_internal_blocker_synthesis`)**:
   Unifies pre-horizon immunity, internal blocker forcing, recent state exclusion,
   and height elevation into a single master theorem.
-/

/-- The triangular number bounds natural numbers. -/
theorem le_upperTri (n : Nat) : n ≤ upperTri n := by
  induction n with
  | zero => simp [upperTri]
  | succ n ih => simp [upperTri]

/-- In any high regime state `2n ≤ a n`, the subtraction candidate satisfies `n - 1 ≤ a n - (n + 1)`. -/
theorem candidate_subtraction_lower_bound
    {n : Nat} (hhigh : 2 * n ≤ a n) :
    n - 1 ≤ a n - (n + 1) := by
  omega

/-- For `n ≥ upperTri H + 2` in the high regime, the subtraction candidate strictly exceeds `upperTri H`. -/
theorem candidate_subtraction_gt_upperTri
    {H n : Nat} (hhigh : 2 * n ≤ a n) (hn : upperTri H + 2 ≤ n) :
    upperTri H < a n - (n + 1) := by
  have hlb := candidate_subtraction_lower_bound hhigh
  omega

/-- For any horizon `H` and any pre-horizon time `j < H`, `a j ≤ upperTri H`. -/
theorem pre_horizon_value_le_upperTri
    {H j : Nat} (hj : j < H) :
    a j ≤ upperTri H := by
  have h1 := a_le_upperTri j
  have hmono : upperTri j ≤ upperTri H := by
    apply upperTri_mono
    omega
  exact Nat.le_trans h1 hmono

/-- Pre-horizon blocker immunity: for `n ≥ upperTri H + 2` in the high regime,
no historical state `j < H` can block the subtraction candidate `a n - (n + 1)`. -/
theorem pre_horizon_blocker_impossible
    {H n j : Nat}
    (hhigh : 2 * n ≤ a n)
    (hn : upperTri H + 2 ≤ n)
    (hj : j < H) :
    a j ≠ a n - (n + 1) := by
  have hval := pre_horizon_value_le_upperTri hj
  have hcand := candidate_subtraction_gt_upperTri hhigh hn
  omega

/-- Pre-horizon history avoidance: the subtraction candidate avoids `valuesThrough (H - 1)`. -/
theorem pre_horizon_valuesThrough_avoidance
    {H n : Nat}
    (hhigh : 2 * n ≤ a n)
    (hn : upperTri H + 2 ≤ n)
    (hH : 1 ≤ H) :
    a n - (n + 1) ∉ valuesThrough (H - 1) := by
  intro hmem
  rcases mem_valuesThrough_iff.mp hmem with ⟨j, hj, heq⟩
  have hj_lt : j < H := by omega
  have hne := pre_horizon_blocker_impossible hhigh hn hj_lt
  exact hne heq

/-- If step `n + 1` cannot subtract at `n ≥ upperTri H + 2` in the high regime,
the blocker is forced to be an internal state `H ≤ j ≤ n` from the high tail itself. -/
theorem not_canSubtract_forces_tail_blocker
    {H n : Nat}
    (hhigh : 2 * n ≤ a n)
    (hn : upperTri H + 2 ≤ n)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    ∃ j, H ≤ j ∧ j ≤ n ∧ a j = a n - (n + 1) := by
  have hcases := not_canSubtract_cases hnot
  have hgt : n + 1 < a n := by omega
  rcases hcases with hsmall | hseen
  · omega
  · rcases mem_valuesThrough_iff.mp hseen with ⟨j, hj, hval⟩
    by_cases hjH : j < H
    · have hne := pre_horizon_blocker_impossible hhigh hn hjH
      exact False.elim (hne hval)
    · exact ⟨j, by omega, hj, hval⟩

/-- The current state `a n` cannot block the subtraction candidate `a n - (n + 1)`. -/
theorem tail_blocker_not_current
    {n : Nat} (hn : 1 ≤ n) (hhigh : 2 * n ≤ a n) :
    a n ≠ a n - (n + 1) := by
  omega

/-- The previous state `a (n - 1)` cannot block the subtraction candidate `a n - (n + 1)`. -/
theorem tail_blocker_not_previous
    {n : Nat} (hn : 1 ≤ n) (hhigh : 2 * n ≤ a n) :
    a (n - 1) ≠ a n - (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hcases : a (m + 1) = a m - (m + 1) ∨ a (m + 1) = a m + (m + 1) := by
    rw [recurrence]
    split
    · left; rfl
    · right; rfl
  have : (m + 1) - 1 = m := by omega
  rw [this]
  rcases hcases with hsub | hadd
  · omega
  · omega

/-- For `n ≥ 3`, the two-back state `a (n - 2)` cannot block `a n - (n + 1)`. -/
theorem tail_blocker_not_two_back
    {n : Nat} (hn : 3 ≤ n) (hhigh : 2 * n ≤ a n) :
    a (n - 2) ≠ a n - (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : 1 ≤ m := by omega
  have hcases1 : a (m + 1) = a m - (m + 1) ∨ a (m + 1) = a m + (m + 1) := by
    rw [recurrence]
    split
    · left; rfl
    · right; rfl
  have hcases2 : a (m + 2) = a (m + 1) - (m + 2) ∨ a (m + 2) = a (m + 1) + (m + 2) := by
    have hrec := recurrence (m + 1)
    have heq : (m + 1) + 1 = m + 2 := by omega
    rw [heq] at hrec
    rw [hrec]
    split
    · left; rfl
    · right; rfl
  have : (m + 2) - 2 = m := by omega
  rw [this]
  rcases hcases1 with hsub1 | hadd1 <;> rcases hcases2 with hsub2 | hadd2
  · omega
  · omega
  · omega
  · omega

/-- Any internal blocker must strictly precede the current step by at least 3 steps: `j ≤ n - 3`. -/
theorem tail_blocker_strictly_prior_to_two_back
    {n j : Nat}
    (hn : 3 ≤ n)
    (hhigh : 2 * n ≤ a n)
    (hj : j ≤ n)
    (heq : a j = a n - (n + 1)) :
    j ≤ n - 3 := by
  by_cases hj_le : j ≤ n - 3
  · exact hj_le
  · have hcases : j = n ∨ j = n - 1 ∨ j = n - 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact False.elim (tail_blocker_not_current (by omega) hhigh heq)
    · exact False.elim (tail_blocker_not_previous (by omega) hhigh heq)
    · exact False.elim (tail_blocker_not_two_back hn hhigh heq)

/-- In any permanent high regime, an internal blocker `a j = a n - (n + 1)` forces
orbit height elevation: `2j + n + 1 ≤ a n` and `2H + n + 1 ≤ a n`. -/
theorem internal_blocker_forces_height_elevation
    {H n j : Nat}
    (hn1 : 1 ≤ n)
    (hhigh_tail : ∀ m, H ≤ m → 2 * m ≤ a m)
    (hhigh_n : 2 * n ≤ a n)
    (hjH : H ≤ j)
    (heq : a j = a n - (n + 1)) :
    2 * j + n + 1 ≤ a n ∧ 2 * H + n + 1 ≤ a n := by
  have hj_high := hhigh_tail j hjH
  have : 2 * j ≤ a n - (n + 1) := by
    rw [← heq]
    exact hj_high
  constructor
  · omega
  · omega

/-- Internal Blocker Summit Existence: at any step `n ≥ upperTri H + 2` in the permanent
high regime where subtraction is blocked, there strictly exists a blocker `H ≤ j ≤ n - 3`
in the high tail itself forcing the height elevation `2j + n + 1 ≤ a n`. -/
theorem tail_blocker_summit_existence
    {H n : Nat}
    (hhigh_tail : ∀ m, H ≤ m → 2 * m ≤ a m)
    (hn_bound : upperTri H + 2 ≤ n)
    (hn3 : 3 ≤ n)
    (hnot : ¬ CanSubtract (n + 1) (stateAt n)) :
    ∃ j, H ≤ j ∧ j ≤ n - 3 ∧
      a j = a n - (n + 1) ∧
      2 * j + n + 1 ≤ a n ∧
      2 * H + n + 1 ≤ a n := by
  have hH_le := le_upperTri H
  have hHn : H ≤ n := by omega
  have hhigh_n : 2 * n ≤ a n := hhigh_tail n hHn
  rcases not_canSubtract_forces_tail_blocker hhigh_n hn_bound hnot with ⟨j, hjH, hjn, heq⟩
  have hj_le : j ≤ n - 3 := tail_blocker_strictly_prior_to_two_back hn3 hhigh_n hjn heq
  have helev := internal_blocker_forces_height_elevation (by omega) hhigh_tail hhigh_n hjH heq
  exact ⟨j, hjH, hj_le, heq, helev.1, helev.2⟩

/-- Grand Permanent High Internal Blocker Synthesis:
Unifies:
1. Candidate lower bound `n - 1 ≤ a n - (n + 1)`
2. Pre-horizon triangular ceiling `a j ≤ upperTri H`
3. Candidate strictly exceeds `upperTri H`
4. Pre-horizon blocker immunity `∀ j < H, a j ≠ a n - (n + 1)`
5. Avoidance of `valuesThrough (H - 1)`
6. Internal tail blocker forcing for blocked subtractions
7. Blocker cannot be `n`, `n - 1`, or `n - 2`
8. Blocker must precede step by at least 3: `j ≤ n - 3`
9. Internal blocker height elevation `2j + n + 1 ≤ a n`
10. Tail blocker summit existence in the high tail -/
theorem grand_permanent_high_internal_blocker_synthesis
    {H n : Nat}
    (hhigh_tail : ∀ m, H ≤ m → 2 * m ≤ a m)
    (hn_bound : upperTri H + 2 ≤ n)
    (hn3 : 3 ≤ n) :
    (2 * n ≤ a n → n - 1 ≤ a n - (n + 1)) ∧
    (∀ j, j < H → a j ≤ upperTri H) ∧
    (2 * n ≤ a n → upperTri H < a n - (n + 1)) ∧
    (2 * n ≤ a n → ∀ j, j < H → a j ≠ a n - (n + 1)) ∧
    (1 ≤ H → 2 * n ≤ a n → a n - (n + 1) ∉ valuesThrough (H - 1)) ∧
    (¬ CanSubtract (n + 1) (stateAt n) →
      ∃ j, H ≤ j ∧ j ≤ n ∧ a j = a n - (n + 1)) ∧
    (∀ j, j ≤ n → a j = a n - (n + 1) → j ≤ n - 3) ∧
    (¬ CanSubtract (n + 1) (stateAt n) →
      ∃ j, H ≤ j ∧ j ≤ n - 3 ∧
        a j = a n - (n + 1) ∧
        2 * j + n + 1 ≤ a n ∧
        2 * H + n + 1 ≤ a n) := by
  have hH_le := le_upperTri H
  have hHn : H ≤ n := by omega
  have hhigh_n : 2 * n ≤ a n := hhigh_tail n hHn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hh
    exact candidate_subtraction_lower_bound hh
  · intro j hj
    exact pre_horizon_value_le_upperTri hj
  · intro hh
    exact candidate_subtraction_gt_upperTri hh hn_bound
  · intro hh j hj
    exact pre_horizon_blocker_impossible hh hn_bound hj
  · intro hH hh
    exact pre_horizon_valuesThrough_avoidance hh hn_bound hH
  · intro hnot
    exact not_canSubtract_forces_tail_blocker hhigh_n hn_bound hnot
  · intro j hj heq
    exact tail_blocker_strictly_prior_to_two_back hn3 hhigh_n hj heq
  · intro hnot
    exact tail_blocker_summit_existence hhigh_tail hn_bound hn3 hnot

end Recaman
