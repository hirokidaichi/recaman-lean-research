import Recaman.ExtremalSupplyRigidity
import Recaman.LagElevenPeriodic

/-!
# StratifiedCapacityHierarchy: Master Synthesis of the Multi-Tier Capacity and Deficit Hierarchy

This module establishes the unified multi-tier capacity and deficit hierarchy
spanning all 4 quantum tiers (L ≤ 7, L ≤ 11, L < 15, L < 19):

1. `tier1_capacity_bound`: Tier 1 (L ≤ 7) capacity: `|U7| ≤ |D|` holds unconditionally for all periods.
2. `tier2_capacity_bound`: Tier 2 (L ≤ 11) joint capacity: `|U7 ∪ U11min| ≤ |D|` holds unconditionally.
3. `tier3_deficit_buffer`: Tier 3 (L < 15) strict deficit buffer: `slack ≥ n2 + 2*n3`.
4. `tier4_deficit_buffer`: Tier 4 (L < 19) strict deficit buffer: `slack ≥ n2 + 2*n3 + 3*n4 + 4*n5`.
5. `high_ss_forces_strict_deficit_hierarchy`: Any high-SS window forces `slack ≥ 1` across all tiers.
6. `super_high_ss_forces_higher_slack`: An SS=3 window forces `slack ≥ 2`, an SS=4 window forces `slack ≥ 3`,
   and an SS=5 window forces `slack ≥ 4`.
7. `two_high_ss_forces_double_slack`: Two high-SS windows force `slack ≥ 2`, two SS=3 force `slack ≥ 4`,
   and two SS=5 force `slack ≥ 8`.
8. `saturated_supply_pure_low_ss_hierarchy`: Saturated supplies (`|U| = |D|`) strictly exclude
   all high-SS windows below lag 19 (`n2 = n3 = n4 = n5 = 0`).
9. `global_capacity_reduction_principle`: Global capacity `|U| ≤ |D|` across all tiers below lag 19
   reduces unconditionally to the low-SS capacity problem.
10. `grand_stratified_capacity_synthesis`: Master synthesis theorem unifying all 4 capacity tiers.
-/

namespace Recaman.StratifiedCapacityHierarchy

open ShortPeriodicSupply LagElevenPeriodic
open FiveSSWeightCapacity FourTierCapacityReduction TwoSSWeightCapacity
open ExtremalSupplyRigidity GrandPeriodicBottleneckTheorem

/-- Tier 1 (L ≤ 7) unconditional capacity bound: |U7| ≤ |D| holds for all periods. -/
theorem tier1_capacity_bound (e : Int → Bool) (p : Nat)
    (hp : ∀ x : Int, e (x + p) = e x) (t : Int) :
    suppliedCount e t p ≤ subtractionCount e t p :=
  periodic_capacity e p hp t

/-- Tier 2 (L ≤ 11) unconditional joint capacity bound: |U7 ∪ U11min| ≤ |D| holds for all periods. -/
theorem tier2_capacity_bound (e : Int → Bool) (t : Int) {p : Nat}
    (hper : ∀ x : Int, e (x + p) = e x) (hp : 0 < p) :
    suppliedCount e t p + u11Count e t p ≤ subtractionCount e t p :=
  suppliedCount_add_u11Count_le_subtractionCount e t hper hp

/-- Tier 3 (L < 15) strict deficit buffer: slack ≥ n2 + 2*n3. -/
theorem tier3_deficit_buffer (n0 n2 n3 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 ≤ nD) :
    n2 + 2 * n3 ≤ nD - (n0 + n2 + n3) := by
  omega

/-- Tier 4 (L < 19) strict deficit buffer: slack ≥ n2 + 2*n3 + 3*n4 + 4*n5. -/
theorem tier4_deficit_buffer (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD) :
    n2 + 2 * n3 + 3 * n4 + 4 * n5 ≤ nD - (n0 + n2 + n3 + n4 + n5) :=
  five_tier_slack_bound n0 n2 n3 n4 n5 nD h_weight

/-- High-SS windows force strict positive slack (slack ≥ 1) across all tiers below lag 19. -/
theorem high_ss_forces_strict_deficit_hierarchy (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD)
    (h_high : 1 ≤ n2 + n3 + n4 + n5) :
    1 ≤ nD - (n0 + n2 + n3 + n4 + n5) := by
  have hs := five_tier_slack_bound n0 n2 n3 n4 n5 nD h_weight
  omega

/-- Super-high-SS windows force higher deficit buffers: SS=3 forces slack ≥ 2,
SS=4 forces slack ≥ 3, and SS=5 forces slack ≥ 4. -/
theorem super_high_ss_forces_higher_slack (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD) :
    (1 ≤ n3 → 2 ≤ nD - (n0 + n2 + n3 + n4 + n5)) ∧
    (1 ≤ n4 → 3 ≤ nD - (n0 + n2 + n3 + n4 + n5)) ∧
    (1 ≤ n5 → 4 ≤ nD - (n0 + n2 + n3 + n4 + n5)) := by
  have hs := five_tier_slack_bound n0 n2 n3 n4 n5 nD h_weight
  refine ⟨by omega, by omega, by omega⟩

/-- Multiple high-SS windows force cumulative deficit buffers:
two high-SS force slack ≥ 2, two SS=3 force slack ≥ 4, and two SS=5 force slack ≥ 8. -/
theorem two_high_ss_forces_double_slack (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD) :
    (2 ≤ n2 + n3 + n4 + n5 → 2 ≤ nD - (n0 + n2 + n3 + n4 + n5)) ∧
    (2 ≤ n3 → 4 ≤ nD - (n0 + n2 + n3 + n4 + n5)) ∧
    (2 ≤ n5 → 8 ≤ nD - (n0 + n2 + n3 + n4 + n5)) := by
  have hs := five_tier_slack_bound n0 n2 n3 n4 n5 nD h_weight
  refine ⟨by omega, by omega, by omega⟩

/-- Saturated supplies (nD ≤ n_tot) strictly exclude all high-SS windows below lag 19. -/
theorem saturated_supply_pure_low_ss_hierarchy (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD)
    (h_sat : nD ≤ n0 + n2 + n3 + n4 + n5) :
    n2 = 0 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 0 :=
  five_tier_extremal_forces_zero n0 n2 n3 n4 n5 nD h_weight h_sat

/-- Global Capacity Reduction Principle: For any periodic supply below lag 19,
global capacity |U| ≤ |D| holds unconditionally if it holds on low-SS supplies. -/
theorem global_capacity_reduction_principle (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD)
    (_h_low : n0 ≤ nD) :
    n0 + n2 + n3 + n4 + n5 ≤ nD := by
  have h := five_tier_weight_inequality n0 n2 n3 n4 n5 nD h_weight
  omega

/-- Master Synthesis: Grand Stratified Capacity Hierarchy.
Unifying Tier 1 through Tier 4 capacity bounds, deficit buffers, and low-SS purification. -/
theorem grand_stratified_capacity_synthesis (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD) :
    (n0 + n2 + n3 + n4 + n5 ≤ nD - (n2 + 2 * n3 + 3 * n4 + 4 * n5)) ∧
    (1 ≤ n2 + n3 + n4 + n5 → 1 ≤ nD - (n0 + n2 + n3 + n4 + n5)) ∧
    (nD ≤ n0 + n2 + n3 + n4 + n5 → n2 = 0 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 0) := by
  have hle := five_tier_weight_inequality n0 n2 n3 n4 n5 nD h_weight
  have hstrict : 1 ≤ n2 + n3 + n4 + n5 → 1 ≤ nD - (n0 + n2 + n3 + n4 + n5) :=
    fun h => high_ss_forces_strict_deficit_hierarchy n0 n2 n3 n4 n5 nD h_weight h
  have hzero : nD ≤ n0 + n2 + n3 + n4 + n5 → n2 = 0 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 0 :=
    fun h => saturated_supply_pure_low_ss_hierarchy n0 n2 n3 n4 n5 nD h_weight h
  exact ⟨hle, hstrict, hzero⟩

end Recaman.StratifiedCapacityHierarchy
