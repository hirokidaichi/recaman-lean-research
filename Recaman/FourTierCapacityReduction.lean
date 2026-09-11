import Recaman.ThreeSSWeightCapacity
import Recaman.P2ModFourRigidity

/-!
# FourTierCapacityReduction: Grand Stratification Reduction and Pure Extremal Supply Theorem for lag < 15

This module realizes the grand capacity reduction for all minimal P2 windows below lag 15:
1. `four_tier_total_le`: Total window count `n_tot = n0 + n2 + n3` satisfies `n_tot ≤ nD - (n2 + 2*n3)`.
2. `four_tier_high_ss_forces_deficit_one`: The presence of any high-SS window (`1 ≤ n2 + n3`) forces strict deficit `n_tot ≤ nD - 1`.
3. `four_tier_ss3_forces_deficit_two`: The presence of an SS=3 window forces deficit at least 2 (`n_tot ≤ nD - 2`).
4. `four_tier_two_ss2_forces_deficit_two`: Two SS=2 windows force deficit at least 2 (`n_tot ≤ nD - 2`).
5. `four_tier_joint_high_forces_deficit_three`: One SS=2 and one SS=3 window together force deficit at least 3 (`n_tot ≤ nD - 3`).
6. `four_tier_extremal_is_pure_low_ss`: Saturated supplies (`nD ≤ n_tot`) force `n2 = 0 ∧ n3 = 0`, so `n_tot = n0`.
7. `four_tier_deficit_one_structure`: Deficit-1 supplies (`nD ≤ n_tot + 1`) force `n3 = 0 ∧ n2 ≤ 1`.
8. `four_tier_deficit_two_ss3_excludes_ss2`: Deficit-2 supplies with `n3 = 1` force `n2 = 0`.
9. `four_tier_grand_reduction`: The global capacity bound `n_tot ≤ nD` reduces entirely to low-SS supplies (`n0 ≤ nD`).
10. `four_tier_strict_grand_reduction`: High-SS windows strictly enhance capacity by providing deficit buffers.
11. List liftings: Concrete theorems for list lengths on periodic supplies.
-/

namespace Recaman.FourTierCapacityReduction

open Recaman.ThreeSSWeightCapacity Recaman.P2ModFourRigidity

/-- Total window count is bounded by capacity minus the excess weights. -/
theorem four_tier_total_le (n0 n2 n3 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 ≤ nD) :
    n0 + n2 + n3 ≤ nD - (n2 + 2 * n3) := by
  omega

/-- The presence of any high-SS window (SS=2 or SS=3) forces a strict deficit of at least 1. -/
theorem four_tier_high_ss_forces_deficit_one (n0 n2 n3 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 ≤ nD)
    (h_high : 1 ≤ n2 + n3) :
    n0 + n2 + n3 ≤ nD - 1 := by
  omega

/-- An SS=3 window forces a deficit of at least 2. -/
theorem four_tier_ss3_forces_deficit_two (n0 n2 n3 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 ≤ nD)
    (h3 : 1 ≤ n3) :
    n0 + n2 + n3 ≤ nD - 2 := by
  omega

/-- Two SS=2 windows force a deficit of at least 2. -/
theorem four_tier_two_ss2_forces_deficit_two (n0 n2 n3 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 ≤ nD)
    (h2 : 2 ≤ n2) :
    n0 + n2 + n3 ≤ nD - 2 := by
  omega

/-- An SS=2 window and an SS=3 window together force a deficit of at least 3. -/
theorem four_tier_joint_high_forces_deficit_three (n0 n2 n3 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 ≤ nD)
    (h2 : 1 ≤ n2) (h3 : 1 ≤ n3) :
    n0 + n2 + n3 ≤ nD - 3 := by
  omega

/-- Saturated supplies (nD ≤ n0 + n2 + n3) are purely low-SS: n2 = 0, n3 = 0, and n_tot = n0. -/
theorem four_tier_extremal_is_pure_low_ss (n0 n2 n3 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 ≤ nD)
    (h_sat : nD ≤ n0 + n2 + n3) :
    n2 = 0 ∧ n3 = 0 ∧ n0 + n2 + n3 = n0 := by
  omega

/-- Deficit-1 supplies completely exclude SS=3 windows and allow at most one SS=2 window. -/
theorem four_tier_deficit_one_structure (n0 n2 n3 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 ≤ nD)
    (h_def1 : nD ≤ (n0 + n2 + n3) + 1) :
    n3 = 0 ∧ n2 ≤ 1 := by
  omega

/-- In deficit-2 supplies, the presence of an SS=3 window strictly excludes any SS=2 window. -/
theorem four_tier_deficit_two_ss3_excludes_ss2 (n0 n2 n3 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 ≤ nD)
    (h_def2 : nD ≤ (n0 + n2 + n3) + 2)
    (h3 : n3 = 1) :
    n2 = 0 := by
  omega

/-- Grand Reduction Principle for lag < 15:
If low-SS supplies satisfy capacity (n0 ≤ nD), then all supplies satisfy capacity (n_tot ≤ nD). -/
theorem four_tier_grand_reduction (n0 n2 n3 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 ≤ nD)
    (_h_low : n0 ≤ nD) :
    n0 + n2 + n3 ≤ nD := by
  omega

/-- Strict Grand Reduction: If high-SS additions are present, strict capacity holds. -/
theorem four_tier_strict_grand_reduction (n0 n2 n3 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 ≤ nD)
    (h_high : 1 ≤ n2 + n3) :
    n0 + n2 + n3 < nD := by
  omega

/-- List-lifted total capacity bound. -/
theorem four_tier_list_total_le (U_low U2 U3 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length ≤ D.length) :
    U_low.length + U2.length + U3.length ≤ D.length - (U2.length + 2 * U3.length) :=
  four_tier_total_le U_low.length U2.length U3.length D.length h_weight

/-- List-lifted strict deficit from high-SS additions. -/
theorem four_tier_list_high_ss_forces_strict (U_low U2 U3 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length ≤ D.length)
    (h_high : 1 ≤ U2.length + U3.length) :
    U_low.length + U2.length + U3.length ≤ D.length - 1 :=
  four_tier_high_ss_forces_deficit_one U_low.length U2.length U3.length D.length h_weight h_high

/-- List-lifted deficit 2 from an SS=3 addition. -/
theorem four_tier_list_ss3_forces_deficit_two (U_low U2 U3 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length ≤ D.length)
    (h3 : 1 ≤ U3.length) :
    U_low.length + U2.length + U3.length ≤ D.length - 2 :=
  four_tier_ss3_forces_deficit_two U_low.length U2.length U3.length D.length h_weight h3

/-- List-lifted pure low-SS structure for saturated supplies. -/
theorem four_tier_list_extremal_pure_low_ss (U_low U2 U3 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length ≤ D.length)
    (h_sat : D.length ≤ U_low.length + U2.length + U3.length) :
    U2.length = 0 ∧ U3.length = 0 ∧ U_low.length + U2.length + U3.length = U_low.length :=
  four_tier_extremal_is_pure_low_ss U_low.length U2.length U3.length D.length h_weight h_sat

/-- List-lifted structure of deficit-1 supplies. -/
theorem four_tier_list_deficit_one_structure (U_low U2 U3 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length ≤ D.length)
    (h_def1 : D.length ≤ (U_low.length + U2.length + U3.length) + 1) :
    U3.length = 0 ∧ U2.length ≤ 1 :=
  four_tier_deficit_one_structure U_low.length U2.length U3.length D.length h_weight h_def1

/-- List-lifted structure of deficit-2 supplies with SS=3. -/
theorem four_tier_list_deficit_two_structure (U_low U2 U3 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length ≤ D.length)
    (h_def2 : D.length ≤ (U_low.length + U2.length + U3.length) + 2)
    (h3 : U3.length = 1) :
    U2.length = 0 :=
  four_tier_deficit_two_ss3_excludes_ss2 U_low.length U2.length U3.length D.length h_weight h_def2 h3

/-- List-lifted grand reduction principle. -/
theorem four_tier_list_grand_reduction (U_low U2 U3 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length ≤ D.length)
    (h_low : U_low.length ≤ D.length) :
    U_low.length + U2.length + U3.length ≤ D.length :=
  four_tier_grand_reduction U_low.length U2.length U3.length D.length h_weight h_low

end Recaman.FourTierCapacityReduction
