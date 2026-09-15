import Recaman.PermanentHighGlobalSynthesis
import Recaman.TailDowncrossingDichotomy
import Recaman.TailDowncrossingLedger

namespace Recaman

/-! # Tail Downcrossing Inevitability and Corridor Re-entry Synthesis

This module formalizes the inevitability of downcrossings from any high-regime
escape back into the corridor:

1. **Discrete Boundary Crossing Lemma (`exists_downcrossing_of_high_to_low`)**:
   If an orbit satisfies `2H ≤ a H` at time `H` and strictly falls below twice
   the clock at a later time `T` (`a T < 2T`), then by discrete intermediate
   descent, there strictly exists a downcrossing step `k` between `H` and `T`:
   `H ≤ k ∧ k < T ∧ 2k ≤ a k ∧ a (k + 1) < 2(k + 1)`.

2. **Toothcomb Downcrossing Forcing (`toothcomb_forced_downcrossing_step`)**:
   Whenever a toothcomb descent extends beyond the high regime horizon
   (`a n < 5m + n + 6`), the value strictly downcrosses below twice the clock,
   unconditionally forcing a certified downcrossing step `k` between `H` and `T`.

3. **Downcrossing Properties (`downcrossing_step_properties`)**:
   Every downcrossing step `k` is a legal subtraction (`CanSubtract (k + 1)`),
   deposits its full clock into the subtraction ledger (`k + 1 ≤ subSum (k + 1)`),
   and lands on a historically fresh value (`a (k + 1) ∉ valuesThrough k`).

4. **Corridor Re-entry (`tail_downcrossing_corridor_reentry_synthesis`)**:
   In any hypothetical least missing tail, the downcrossing landing value strictly
   lands above the tail minimum (`a time + 1 ≤ a (k + 1) < 2(k + 1)`) and re-enters
   the subtraction ledger corridor:
   `2 * subSum (k + 1) + (a time + 1) ≤ upperTri (k + 1) < 2 * subSum (k + 1) + 2(k + 1)`.

5. **Grand Downcrossing Inevitability Synthesis**:
   Unifies the discrete boundary crossing lemma, toothcomb downcrossing forcing,
   legal subtraction freshness, and corridor re-entry into a master synthesis theorem.
-/

/-! ### Part 1: Discrete Boundary Crossing Lemma -/

/-- Discrete boundary crossing lemma:
If an orbit is at or above twice the clock at H, and strictly below twice the
clock at a later time T, then there strictly exists a downcrossing step k
between H and T. -/
theorem exists_downcrossing_of_high_to_low
    {H T : Nat} (hle : H ≤ T)
    (hH : 2 * H ≤ a H)
    (hT : a T < 2 * T) :
    ∃ k, H ≤ k ∧ k < T ∧ 2 * k ≤ a k ∧ a (k + 1) < 2 * (k + 1) := by
  classical
  by_cases hex : ∃ k, H ≤ k ∧ k < T ∧ 2 * k ≤ a k ∧ a (k + 1) < 2 * (k + 1)
  · exact hex
  · exfalso
    have hstep : ∀ k, H ≤ k → k < T → 2 * k ≤ a k → 2 * (k + 1) ≤ a (k + 1) := by
      intro k hk_ge hk_lt hk_high
      by_cases hnext : 2 * (k + 1) ≤ a (k + 1)
      · exact hnext
      · exfalso
        apply hex
        refine ⟨k, hk_ge, hk_lt, hk_high, by omega⟩
    have hind : ∀ d, d ≤ T - H → 2 * (H + d) ≤ a (H + d) := by
      intro d
      induction d with
      | zero =>
          intro _
          simpa using hH
      | succ d ih =>
          intro hd
          have hd_lt : d < T - H := by omega
          have hd_le : d ≤ T - H := by omega
          have ih_val := ih hd_le
          have hk_ge : H ≤ H + d := by omega
          have hk_lt : H + d < T := by omega
          have hnext := hstep (H + d) hk_ge hk_lt ih_val
          have heq : H + (d + 1) = (H + d) + 1 := by omega
          rw [heq]
          exact hnext
    have hd_eq : T - H ≤ T - H := by omega
    have hT_val := hind (T - H) hd_eq
    have heqT : H + (T - H) = T := by omega
    rw [heqT] at hT_val
    omega

/-! ### Part 2: Toothcomb Downcrossing Forcing -/

/-- Toothcomb downcrossing forcing:
Whenever a toothcomb descent extends beyond the high regime horizon,
a certified downcrossing step k between H and T is strictly forced! -/
theorem toothcomb_forced_downcrossing_step
    {H n m T : Nat} {val : Nat}
    (hH_le_n : H ≤ n)
    (hH : 2 * H ≤ a H)
    (hT : T = n + 3 + 2 * m)
    (hval : val = a n + n - m)
    (haT : a T = val)
    (hbound : a n < 5 * m + n + 6) :
    ∃ k, H ≤ k ∧ k < T ∧ 2 * k ≤ a k ∧ a (k + 1) < 2 * (k + 1) := by
  have hT_low : a T < 2 * T := by
    rw [haT]
    have hlow := toothcomb_exceeds_high_bound_forces_downcrossing hval hbound
    rw [← hT] at hlow
    exact hlow
  have hH_le_T : H ≤ T := by omega
  exact exists_downcrossing_of_high_to_low hH_le_T hH hT_low

/-! ### Part 3: Downcrossing Properties and Corridor Re-entry -/

/-- Downcrossing properties:
Every downcrossing step is a legal subtraction that deposits its clock into the
subtraction ledger and lands on a historically fresh value. -/
theorem downcrossing_step_properties
    {k : Nat} (hk : 1 ≤ k)
    (hhigh : 2 * k ≤ a k)
    (hlow : a (k + 1) < 2 * (k + 1)) :
    CanSubtract (k + 1) (stateAt k) ∧
    k + 1 ≤ subSum (k + 1) ∧
    a (k + 1) ∉ valuesThrough k := by
  have hsub := downcrossing_step_must_be_subtraction hk hhigh hlow
  have hsum := downcrossing_subSum_ge_clock hk hhigh hlow
  have hstep := a_succ_of_canSubtract hsub
  have hfresh : a (k + 1) ∉ valuesThrough k := by
    rw [hstep]
    exact hsub.2
  exact ⟨hsub, hsum, hfresh⟩

/-- Tail downcrossing corridor re-entry:
When a downcrossing occurs after the certified tail minimum time,
the landing value strictly lands above the tail minimum and re-enters the
subtraction ledger corridor. -/
theorem tail_downcrossing_corridor_reentry_synthesis
    {target start time firstTime k : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (hk_time : time ≤ k) (hk_pos : 1 ≤ k)
    (hhigh : 2 * k ≤ a k)
    (hlow : a (k + 1) < 2 * (k + 1)) :
    CanSubtract (k + 1) (stateAt k) ∧
    a time + 1 ≤ a (k + 1) ∧
    a (k + 1) < 2 * (k + 1) ∧
    2 * subSum (k + 1) + (a time + 1) ≤ upperTri (k + 1) ∧
    upperTri (k + 1) < 2 * subSum (k + 1) + 2 * (k + 1) := by
  have hsub := downcrossing_step_must_be_subtraction hk_pos hhigh hlow
  have hbounds := tail_downcrossing_value_bounds hmin hk_time hk_pos hhigh hlow
  have hledger := tail_downcrossing_ledger_corridor_reentry hmin hk_time hk_pos hhigh hlow
  exact ⟨hsub, hbounds.1, hbounds.2.1, hledger.1, hledger.2⟩

/-! ### Part 4: Grand Tail Downcrossing Inevitability Synthesis -/

/-- Grand Tail Downcrossing Inevitability Synthesis:
1. High-to-low discrete boundary crossing lemma.
2. Toothcomb horizon exceedance strictly forces downcrossing.
3. Downcrossing steps are legal subtractions depositing clock into subSum.
4. Downcrossing landing values re-enter the corridor above the tail minimum. -/
theorem grand_tail_downcrossing_inevitability_synthesis
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    (∀ H T, H ≤ T → 2 * H ≤ a H → a T < 2 * T →
       ∃ k, H ≤ k ∧ k < T ∧ 2 * k ≤ a k ∧ a (k + 1) < 2 * (k + 1)) ∧
    (∀ k, 1 ≤ k → 2 * k ≤ a k → a (k + 1) < 2 * (k + 1) →
       CanSubtract (k + 1) (stateAt k) ∧ k + 1 ≤ subSum (k + 1) ∧ a (k + 1) ∉ valuesThrough k) ∧
    (∀ k, time ≤ k → 1 ≤ k → 2 * k ≤ a k → a (k + 1) < 2 * (k + 1) →
       CanSubtract (k + 1) (stateAt k) ∧
       a time + 1 ≤ a (k + 1) ∧
       a (k + 1) < 2 * (k + 1) ∧
       2 * subSum (k + 1) + (a time + 1) ≤ upperTri (k + 1) ∧
       upperTri (k + 1) < 2 * subSum (k + 1) + 2 * (k + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro H T hle hH hT
    exact exists_downcrossing_of_high_to_low hle hH hT
  · intro k hk hhigh hlow
    exact downcrossing_step_properties hk hhigh hlow
  · intro k hk_time hk_pos hhigh hlow
    exact tail_downcrossing_corridor_reentry_synthesis hmin hk_time hk_pos hhigh hlow

end Recaman
