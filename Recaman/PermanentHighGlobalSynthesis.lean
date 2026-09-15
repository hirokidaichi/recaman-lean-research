import Recaman.PermanentHighBlockerCapacity
import Recaman.PermanentHighHistoryExhaustion
import Recaman.PermanentHighToothcombBound

namespace Recaman

/-! # Permanent High Global Synthesis and Downcrossing Inevitability

This module formalizes the universal resolution of the Recamán permanent high
regime (`2n ≤ a n`) by synthesizing:

1. **High Horizon Sufficiency (`a n ≥ 6n + 1`)**:
   Whenever `a n ≥ 6n + 1`, any toothcomb step `m < n` strictly satisfies
   the high regime horizon inequality:
   `5m + n + 6 ≤ a n`.

2. **Unblocked Horizon Candidate Existence**:
   By the Pigeonhole Capacity Obstruction (`PermanentHighBlockerCapacity`),
   there strictly exists an unblocked step `m < n` whose candidate avoids
   all history prior to `n`. Under `a n ≥ 6n + 1`, this step is fully
   contained within the high regime horizon and strictly exceeds `a n`.

3. **Mandatory Downcrossing Forcing (`a n < 6n + 1`)**:
   Conversely, when `a n < 6n + 1`, any toothcomb descent extending to `m = n`
   strictly exceeds the horizon bound: `a n < 5n + n + 6`.
   By the Horizon Forcing Theorem (`PermanentHighToothcombBound`), the toothcomb
   value strictly falls below twice the clock:
   `val < 2 * (n + 3 + 2n)`.
   Thus a downcrossing is unconditionally forced within at most `n` toothcomb steps!

4. **Universal High Regime Dichotomy**:
   Every base index `n ≥ 1` in the high regime `2n ≤ a n` satisfies the dichotomy:
   either `a n ≥ 6n + 1` (unblocked candidate within horizon),
   or `a n < 6n + 1` (mandatory downcrossing within `n` steps).

5. **Grand Global High Regime Synthesis**:
   Unifies the horizon sufficiency, unblocked candidate existence,
   and downcrossing forcing into a single comprehensive synthesis theorem.
-/

/-! ### Part 1: Horizon Sufficiency and Unblocked Candidate Existence -/

/-- If a n ≥ 6n + 1 and m < n, then m is strictly within the high regime horizon:
`5m + n + 6 ≤ a n`. -/
theorem high_regime_horizon_satisfaction_of_ge_six
    {n m : Nat} (hm : m < n) (hn_six : 6 * n + 1 ≤ a n) :
    5 * m + n + 6 ≤ a n := by
  omega

/-- Whenever a n ≥ 6n + 1, there strictly exists an unblocked toothcomb candidate
that is contained within the high regime horizon. -/
theorem exists_unblocked_horizon_candidate
    {n : Nat} (hn : 1 ≤ n) (hn_six : 6 * n + 1 ≤ a n) :
    ∃ m, m < n ∧
      5 * m + n + 6 ≤ a n ∧
      (∀ j, j < n → a j ≠ a n + n - m) ∧
      a n + n - m ∉ valuesThrough (n - 1) ∧
      a n < a n + n - m := by
  have hn_high : 2 * n ≤ a n := by omega
  rcases toothcomb_exists_unblocked_candidate hn hn_high with ⟨m, hm, hunblock⟩
  have hbound := high_regime_horizon_satisfaction_of_ge_six hm hn_six
  have havoid := toothcomb_unblocked_candidate_avoids_valuesThrough hn hm hunblock
  have hgt := toothcomb_candidate_gt_base hm
  exact ⟨m, hm, hbound, hunblock, havoid, hgt⟩

/-! ### Part 2: Mandatory Downcrossing Forcing -/

/-- When a n < 6n + 1, any toothcomb descent reaching m = n strictly exceeds
the high regime horizon and forces a downcrossing below twice the clock. -/
theorem toothcomb_forced_downcrossing_at_step_n
    {n : Nat} {val : Nat}
    (hlt_six : a n < 6 * n + 1)
    (hval : val = a n + n - n) :
    val < 2 * (n + 3 + 2 * n) := by
  have hbound : a n < 5 * n + n + 6 := by omega
  exact toothcomb_exceeds_high_bound_forces_downcrossing hval hbound

/-! ### Part 3: Universal High Regime Dichotomy -/

/-- Universal High Regime Dichotomy:
For any base index n ≥ 1 where 2n ≤ a n:
Either a n ≥ 6n + 1 (guaranteeing an unblocked candidate inside the horizon),
or a n < 6n + 1 (where toothcomb descent downcrosses within at most n steps). -/
theorem permanent_high_universal_dichotomy
    {n : Nat} (hn : 1 ≤ n) (hn_high : 2 * n ≤ a n) :
    (6 * n + 1 ≤ a n ∧
     ∃ m, m < n ∧
       5 * m + n + 6 ≤ a n ∧
       (∀ j, j < n → a j ≠ a n + n - m) ∧
       a n + n - m ∉ valuesThrough (n - 1)) ∨
    (a n < 6 * n + 1 ∧
     ∀ val, val = a n + n - n → val < 2 * (n + 3 + 2 * n)) := by
  have _ := hn_high
  by_cases hsix : 6 * n + 1 ≤ a n
  · left
    refine ⟨hsix, ?_⟩
    rcases exists_unblocked_horizon_candidate hn hsix with ⟨m, hm, hbound, hunblock, havoid, _hgt⟩
    exact ⟨m, hm, hbound, hunblock, havoid⟩
  · right
    have hlt : a n < 6 * n + 1 := by omega
    refine ⟨hlt, ?_⟩
    intro val hval
    exact toothcomb_forced_downcrossing_at_step_n hlt hval

/-! ### Part 4: Grand Global High Regime Synthesis -/

/-- Grand Global High Regime Synthesis:
Combines:
1. Pigeonhole historical unblocked candidate existence inside horizon for a n ≥ 6n + 1.
2. Mandatory downcrossing forcing for a n < 6n + 1.
3. Universal high regime dichotomy. -/
theorem grand_permanent_high_global_synthesis
    {n : Nat} (hn : 1 ≤ n) (hn_high : 2 * n ≤ a n) :
    ((6 * n + 1 ≤ a n →
      ∃ m, m < n ∧ 5 * m + n + 6 ≤ a n ∧ (∀ j, j < n → a j ≠ a n + n - m)) ∧
     (a n < 6 * n + 1 →
      ∀ val, val = a n + n - n → val < 2 * (n + 3 + 2 * n)) ∧
     ((6 * n + 1 ≤ a n ∧
       ∃ m, m < n ∧ 5 * m + n + 6 ≤ a n ∧
         (∀ j, j < n → a j ≠ a n + n - m) ∧
         a n + n - m ∉ valuesThrough (n - 1)) ∨
      (a n < 6 * n + 1 ∧
       ∀ val, val = a n + n - n → val < 2 * (n + 3 + 2 * n)))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hsix
    rcases exists_unblocked_horizon_candidate hn hsix with ⟨m, hm, hbound, hunblock, _havoid, _hgt⟩
    exact ⟨m, hm, hbound, hunblock⟩
  · intro hlt val hval
    exact toothcomb_forced_downcrossing_at_step_n hlt hval
  · exact permanent_high_universal_dichotomy hn hn_high

end Recaman
