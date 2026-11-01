import Recaman.FiveSSClassification
import Recaman.FourTierCapacityReduction

/-!
# FiveSSWeightCapacity: Five-Tier Capacity Inequality and Deficit Stratification

This module establishes the five-tier capacity inequality and multi-tier deficit hierarchy
for all minimal P2 windows up to ssCount = 5 (covering all windows below lag 19):
1. `five_tier_weight_inequality`: The fundamental five-weight inequality
   `n0 + 2*n2 + 3*n3 + 4*n4 + 5*n5 ≤ nD` implies `n_tot ≤ nD - (n2 + 2*n3 + 3*n4 + 4*n5)`.
2. `five_tier_slack_bound`: Supply slack satisfies `slack ≥ n2 + 2*n3 + 3*n4 + 4*n5`.
3. `five_tier_extremal_forces_zero`: Saturated supplies (`|U| = |D|`) strictly exclude
   all high-SS windows (`n2 = 0 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 0`).
4. `five_tier_deficit_one_forces_zero`: Deficit-1 supplies (`|U| = |D| - 1`) strictly
   exclude SS=3, SS=4, and SS=5 windows (`n3 = 0 ∧ n4 = 0 ∧ n5 = 0`) and allow at most one SS=2 (`n2 ≤ 1`).
5. `five_tier_deficit_two_forces_zero`: Deficit-2 supplies strictly exclude SS=4 and SS=5 windows (`n4 = 0 ∧ n5 = 0`).
6. `five_tier_deficit_three_forces_zero`: Deficit-3 supplies strictly exclude SS=5 windows (`n5 = 0`).
7. `five_tier_ss4_single_slack`: A single SS=4 window forces `slack ≥ 3`.
8. `five_tier_ss5_single_slack`: A single SS=5 window forces `slack ≥ 4`.
9. `five_tier_two_ss5_slack`: Two SS=5 windows force `slack ≥ 8`.
10. `five_tier_grand_reduction`: The global capacity bound `n_tot ≤ nD` reduces entirely to low-SS supplies.
11. `five_tier_strict_grand_reduction`: High-SS windows strictly enhance capacity by providing deficit buffers.
12. List liftings: Concrete theorems for list lengths on periodic supplies.
-/

namespace Recaman.FiveSSWeightCapacity

open Recaman.FiveSSClassification Recaman.FourTierCapacityReduction

/-- Total window count is bounded by capacity minus the excess weights. -/
theorem five_tier_weight_inequality (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD) :
    n0 + n2 + n3 + n4 + n5 ≤ nD - (n2 + 2 * n3 + 3 * n4 + 4 * n5) := by
  omega

/-- Supply slack is bounded below by the excess weights of all high-SS windows. -/
theorem five_tier_slack_bound (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD) :
    n2 + 2 * n3 + 3 * n4 + 4 * n5 ≤ nD - (n0 + n2 + n3 + n4 + n5) := by
  omega

/-- Saturated supplies (nD ≤ n_tot) strictly exclude all high-SS windows. -/
theorem five_tier_extremal_forces_zero (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD)
    (h_sat : nD ≤ n0 + n2 + n3 + n4 + n5) :
    n2 = 0 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 0 := by
  omega

/-- Deficit-1 supplies strictly exclude SS=3, SS=4, SS=5 and allow at most one SS=2. -/
theorem five_tier_deficit_one_forces_zero (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD)
    (h_def1 : nD ≤ (n0 + n2 + n3 + n4 + n5) + 1) :
    n3 = 0 ∧ n4 = 0 ∧ n5 = 0 ∧ n2 ≤ 1 := by
  omega

/-- Deficit-2 supplies strictly exclude SS=4 and SS=5 windows. -/
theorem five_tier_deficit_two_forces_zero (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD)
    (h_def2 : nD ≤ (n0 + n2 + n3 + n4 + n5) + 2) :
    n4 = 0 ∧ n5 = 0 := by
  omega

/-- Deficit-3 supplies strictly exclude SS=5 windows. -/
theorem five_tier_deficit_three_forces_zero (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD)
    (h_def3 : nD ≤ (n0 + n2 + n3 + n4 + n5) + 3) :
    n5 = 0 := by
  omega

/-- A single SS=4 window forces slack ≥ 3. -/
theorem five_tier_ss4_single_slack (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD)
    (h4 : 1 ≤ n4) :
    3 ≤ nD - (n0 + n2 + n3 + n4 + n5) := by
  omega

/-- A single SS=5 window forces slack ≥ 4. -/
theorem five_tier_ss5_single_slack (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD)
    (h5 : 1 ≤ n5) :
    4 ≤ nD - (n0 + n2 + n3 + n4 + n5) := by
  omega

/-- Two SS=5 windows force slack ≥ 8. -/
theorem five_tier_two_ss5_slack (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD)
    (h5 : 2 ≤ n5) :
    8 ≤ nD - (n0 + n2 + n3 + n4 + n5) := by
  omega

/-- Grand Reduction Principle for five tiers:
The total capacity bound n_tot ≤ nD reduces unconditionally to the low-SS bound. -/
theorem five_tier_grand_reduction (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD)
    (_h_low : n0 ≤ nD) :
    n0 + n2 + n3 + n4 + n5 ≤ nD := by
  omega

/-- Strict Grand Reduction: If high-SS additions are present, strict capacity holds. -/
theorem five_tier_strict_grand_reduction (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD)
    (h_high : 1 ≤ n2 + n3 + n4 + n5) :
    n0 + n2 + n3 + n4 + n5 < nD := by
  omega

/-- List-lifted total capacity bound. -/
theorem five_tier_list_total_le (U_low U2 U3 U4 U5 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length + 4 * U4.length + 5 * U5.length ≤ D.length) :
    U_low.length + U2.length + U3.length + U4.length + U5.length ≤
      D.length - (U2.length + 2 * U3.length + 3 * U4.length + 4 * U5.length) :=
  five_tier_weight_inequality U_low.length U2.length U3.length U4.length U5.length D.length h_weight

/-- List-lifted supply slack lower bound. -/
theorem five_tier_list_slack_ge_weights (U_low U2 U3 U4 U5 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length + 4 * U4.length + 5 * U5.length ≤ D.length) :
    U2.length + 2 * U3.length + 3 * U4.length + 4 * U5.length ≤
      D.length - (U_low.length + U2.length + U3.length + U4.length + U5.length) :=
  five_tier_slack_bound U_low.length U2.length U3.length U4.length U5.length D.length h_weight

/-- List-lifted pure low-SS structure for saturated supplies. -/
theorem five_tier_list_extremal_count_zero (U_low U2 U3 U4 U5 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length + 4 * U4.length + 5 * U5.length ≤ D.length)
    (h_sat : D.length ≤ U_low.length + U2.length + U3.length + U4.length + U5.length) :
    U2.length = 0 ∧ U3.length = 0 ∧ U4.length = 0 ∧ U5.length = 0 :=
  five_tier_extremal_forces_zero U_low.length U2.length U3.length U4.length U5.length D.length h_weight h_sat

/-- List-lifted structure of deficit-1 supplies. -/
theorem five_tier_list_deficit_one_excludes_high (U_low U2 U3 U4 U5 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length + 4 * U4.length + 5 * U5.length ≤ D.length)
    (h_def1 : D.length ≤ (U_low.length + U2.length + U3.length + U4.length + U5.length) + 1) :
    U3.length = 0 ∧ U4.length = 0 ∧ U5.length = 0 ∧ U2.length ≤ 1 :=
  five_tier_deficit_one_forces_zero U_low.length U2.length U3.length U4.length U5.length D.length h_weight h_def1

/-- List-lifted structure of deficit-2 supplies. -/
theorem five_tier_list_deficit_two_excludes_ss4_ss5 (U_low U2 U3 U4 U5 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length + 4 * U4.length + 5 * U5.length ≤ D.length)
    (h_def2 : D.length ≤ (U_low.length + U2.length + U3.length + U4.length + U5.length) + 2) :
    U4.length = 0 ∧ U5.length = 0 :=
  five_tier_deficit_two_forces_zero U_low.length U2.length U3.length U4.length U5.length D.length h_weight h_def2

/-- List-lifted structure of deficit-3 supplies. -/
theorem five_tier_list_deficit_three_excludes_ss5 (U_low U2 U3 U4 U5 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length + 4 * U4.length + 5 * U5.length ≤ D.length)
    (h_def3 : D.length ≤ (U_low.length + U2.length + U3.length + U4.length + U5.length) + 3) :
    U5.length = 0 :=
  five_tier_deficit_three_forces_zero U_low.length U2.length U3.length U4.length U5.length D.length h_weight h_def3

/-- List-lifted grand reduction principle. -/
theorem five_tier_list_grand_reduction (U_low U2 U3 U4 U5 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length + 4 * U4.length + 5 * U5.length ≤ D.length)
    (h_low : U_low.length ≤ D.length) :
    U_low.length + U2.length + U3.length + U4.length + U5.length ≤ D.length :=
  five_tier_grand_reduction U_low.length U2.length U3.length U4.length U5.length D.length h_weight h_low

end Recaman.FiveSSWeightCapacity
