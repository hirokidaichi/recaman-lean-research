import Recaman.PermanentHighToothcombDescent
import Recaman.PermanentHighRigidity
import Recaman.TailDowncrossingDichotomy
import Recaman.TailDowncrossingLedger

namespace Recaman

/-! # Toothcomb High Regime Horizon Bound and Downcrossing Forcing

This module formalizes the quantitative horizon bound and downcrossing forcing
of the Recamán **toothcomb descent**:

1. **Toothcomb High Regime Inequality**:
   At toothcomb step `m`, the value is `a(n + 3 + 2m) = a n + n - m`.
   In order for this value to remain in the high regime `2 * time ≤ a(time)`,
   it is mathematically necessary that:
   `5 * m + n + 6 ≤ a n`.

2. **Downcrossing Forcing Beyond Horizon**:
   Whenever `a n < 5 * m + n + 6`, the toothcomb value strictly crosses below the
   high regime threshold:
   `a(n + 3 + 2m) < 2 * (n + 3 + 2m)`.
   Thus, any toothcomb that runs for more than `(a n - n - 6) / 5` steps
   is GUARANTEED to perform a downcrossing out of the permanent high regime!

3. **Strict Monotonicity and Distinctness**:
   For any indices bounded by the initial mass `m2 ≤ a n + n`:
   all toothcomb subtraction values `a n + n - m` are strictly decreasing
   and mutually distinct: `m1 < m2 → a n + n - m2 < a n + n - m1`.

4. **Addition Values Strictly Disjoint**:
   All toothcomb addition values `a n + 2n + 4 + m` are strictly greater
   than every toothcomb subtraction value:
   `a n + n - m < a n + 2n + 4 + k`.

5. **Grand Horizon Synthesis**:
   Unites the equivalence `2 * time ≤ val ↔ 5m + n + 6 ≤ a n` with the
   separation of toothcomb subtraction and addition values.
-/

/-! ### Part 1: High Regime Horizon Inequality -/

/-- Toothcomb high regime inequality: remaining at or above twice the clock
forces a linear constraint `5 * m + n + 6 ≤ a n` on the number of toothcomb steps. -/
theorem toothcomb_high_regime_inequality
    {n m : Nat} {val : Nat}
    (hval : val = a n + n - m)
    (hhigh : 2 * (n + 3 + 2 * m) ≤ val) :
    5 * m + n + 6 ≤ a n := by
  omega

/-- Downcrossing forcing: once `m` exceeds the horizon bound `a n < 5 * m + n + 6`,
the toothcomb value strictly crosses below twice the clock. -/
theorem toothcomb_exceeds_high_bound_forces_downcrossing
    {n m : Nat} {val : Nat}
    (hval : val = a n + n - m)
    (hbound : a n < 5 * m + n + 6) :
    val < 2 * (n + 3 + 2 * m) := by
  omega

/-! ### Part 2: Disjointness within Toothcomb -/

/-- Subtraction values in the toothcomb are strictly decreasing with `m`
as long as `m2 ≤ a n + n`. -/
theorem toothcomb_subtraction_values_strictly_decreasing
    (n : Nat) {m1 m2 : Nat} (hm2 : m2 ≤ a n + n) (hlt : m1 < m2) :
    a n + n - m2 < a n + n - m1 := by
  omega

/-- Subtraction values in the toothcomb are mutually distinct. -/
theorem toothcomb_subtraction_values_distinct
    (n : Nat) {m1 m2 : Nat} (hm1 : m1 ≤ a n + n) (hm2 : m2 ≤ a n + n) (hne : m1 ≠ m2) :
    a n + n - m1 ≠ a n + n - m2 := by
  omega

/-- Toothcomb addition values are strictly greater than all toothcomb subtraction values. -/
theorem toothcomb_additions_strictly_above_subtractions
    (n : Nat) (m k : Nat) :
    a n + n - m < a n + 2 * n + 4 + k := by
  omega

/-- The subtraction candidate at step `m` strictly avoids all prior subtraction values
`k < m` in the toothcomb. -/
theorem toothcomb_candidate_avoids_prior_subtractions
    (n : Nat) {m k : Nat} (hm : m ≤ a n + n) (hlt : k < m) :
    a n + n - m ≠ a n + n - k := by
  omega

/-- The subtraction candidate at step `m` strictly avoids all prior addition values
`k ≤ m` in the toothcomb. -/
theorem toothcomb_candidate_avoids_additions
    (n : Nat) (m k : Nat) :
    a n + n - m ≠ a n + 2 * n + 4 + k := by
  omega

/-! ### Part 3: Grand Toothcomb Horizon Synthesis -/

/-- Grand Toothcomb Horizon Synthesis:
1. Every toothcomb descent inside the high regime satisfies `5 * m + n + 6 ≤ a n`.
2. Any toothcomb extending beyond `a n < 5 * m + n + 6` strictly downcrosses:
   `val < 2 * (n + 3 + 2 * m)`.
3. Inside the high regime, all prior toothcomb subtraction values are strictly
   greater than the current value.
4. All toothcomb addition values are strictly greater than the current candidate. -/
theorem grand_toothcomb_horizon_synthesis
    {n m : Nat} {val : Nat}
    (hval : val = a n + n - m) :
    (2 * (n + 3 + 2 * m) ≤ val ↔ 5 * m + n + 6 ≤ a n) ∧
    (a n < 5 * m + n + 6 → val < 2 * (n + 3 + 2 * m)) ∧
    (2 * (n + 3 + 2 * m) ≤ val → ∀ k, k < m → a n + n - m < a n + n - k) ∧
    (∀ k, a n + n - m < a n + 2 * n + 4 + k) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro hhigh
    exact toothcomb_high_regime_inequality hval hhigh
  · intro hbound
    omega
  · intro hbound
    exact toothcomb_exceeds_high_bound_forces_downcrossing hval hbound
  · intro hhigh k hlt
    have : 5 * m + n + 6 ≤ a n := toothcomb_high_regime_inequality hval hhigh
    omega
  · intro k
    omega

end Recaman
