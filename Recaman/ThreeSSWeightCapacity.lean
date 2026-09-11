import Recaman.ThreeSSClassification
import Recaman.TwoSSWeightCapacity

/-!
# ThreeSSWeightCapacity: Three-Weight SS=3 Capacity and Multi-Tier Deficit Hierarchy

This module establishes the three-weight capacity theorem and the deficit hierarchy
for periodic supplies containing SS=3 windows:

1. `ss3_weight_inequality`: The fundamental triple-weight inequality
   `n0 + 2*n2 + 3*n3 ≤ nD` implies `n0 + n2 + n3 ≤ nD - (n2 + 2*n3)`.
2. `ss3_slack_bound`: Supply slack satisfies `slack ≥ n2 + 2*n3`.
3. `ss3_extremal_forces_zero`: Saturated supplies (`|U| = |D|`) strictly exclude
   both SS=2 and SS=3 windows (`n2 = 0 ∧ n3 = 0`).
4. `ss3_deficit_one_forces_zero`: Deficit-1 supplies (`|U| = |D| - 1`) strictly
   exclude any SS=3 window (`n3 = 0`).
5. `ss3_deficit_two_forces_le_one`: Deficit-2 supplies (`|U| = |D| - 2`) allow
   at most one SS=3 window (`n3 ≤ 1`).
6. `ss3_deficit_k_forces_bound`: For any deficit k, `2*n3 ≤ k`.
7. `ss3_single_donor_slack`: A single SS=3 window forces `slack ≥ 2`.
8. `ss3_two_donors_slack`: Two SS=3 windows force `slack ≥ 4`.
9. `ss3_joint_ss2_slack`: One SS=2 window and one SS=3 window together force `slack ≥ 3`.
10. `three_ss_slack_ge_weights`: In any periodic word partitioned into low-SS, SS=2, and SS=3,
    the supply slack is at least `|U2| + 2*|U3|`.
11. `three_ss_extremal_count_zero`: Extremal supplies have zero SS=2 and zero SS=3 additions.
12. `three_ss_deficit_one_excludes_ss3`: Deficit-1 supplies have zero SS=3 additions.
13. `three_ss_deficit_two_count_le_one`: Deficit-2 supplies have at most one SS=3 addition.
-/

namespace Recaman.ThreeSSWeightCapacity

open Recaman.TightP2ParityRigidity Recaman.TwoSSEndpoint Recaman.LeadingRunSupply
open Recaman.LagSevenTightObstruction Recaman.OneSSMultiplicity Recaman.SS2MinimalLagBound
open Recaman.SS2LagElevenForcing Recaman.TightSSZeroRigidity Recaman.TightCapacityHierarchy
open Recaman.UniversalSSStratification Recaman.ThreeSSClassification
open Recaman.TwoSSWeightCapacity

/-- Fundamental Three-Weight Capacity Inequality:
The triple-weight bound n0 + 2*n2 + 3*n3 ≤ nD implies that the total additions
n0 + n2 + n3 are bounded by nD - (n2 + 2*n3). -/
theorem ss3_weight_inequality (n0 n2 n3 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 ≤ nD) :
    n0 + n2 + n3 ≤ nD - (n2 + 2 * n3) := by
  omega

/-- Supply Slack Lower Bound:
The slack nD - (n0 + n2 + n3) is at least n2 + 2*n3. -/
theorem ss3_slack_bound (n0 n2 n3 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 ≤ nD) :
    n2 + 2 * n3 ≤ nD - (n0 + n2 + n3) := by
  omega

/-- Saturated supplies (nD ≤ n0 + n2 + n3) strictly exclude both SS=2 and SS=3 windows. -/
theorem ss3_extremal_forces_zero (n0 n2 n3 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 ≤ nD)
    (h_sat : nD ≤ n0 + n2 + n3) :
    n2 = 0 ∧ n3 = 0 := by
  omega

/-- Deficit-1 supplies (nD ≤ n0 + n2 + n3 + 1) strictly exclude any SS=3 window. -/
theorem ss3_deficit_one_forces_zero (n0 n2 n3 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 ≤ nD)
    (h_def1 : nD ≤ (n0 + n2 + n3) + 1) :
    n3 = 0 := by
  omega

/-- Deficit-2 supplies (nD ≤ n0 + n2 + n3 + 2) allow at most one SS=3 window. -/
theorem ss3_deficit_two_forces_le_one (n0 n2 n3 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 ≤ nD)
    (h_def2 : nD ≤ (n0 + n2 + n3) + 2) :
    n3 ≤ 1 := by
  omega

/-- General Deficit Hierarchy: In any deficit-k supply, 2*n3 ≤ k. -/
theorem ss3_deficit_k_forces_bound (n0 n2 n3 nD k : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 ≤ nD)
    (h_defk : nD ≤ (n0 + n2 + n3) + k) :
    2 * n3 ≤ k := by
  omega

/-- A single SS=3 window forces slack ≥ 2. -/
theorem ss3_single_donor_slack (n0 n2 n3 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 ≤ nD)
    (h3 : 1 ≤ n3) :
    2 ≤ nD - (n0 + n2 + n3) := by
  omega

/-- Two SS=3 windows force slack ≥ 4. -/
theorem ss3_two_donors_slack (n0 n2 n3 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 ≤ nD)
    (h3 : 2 ≤ n3) :
    4 ≤ nD - (n0 + n2 + n3) := by
  omega

/-- One SS=2 window and one SS=3 window together force slack ≥ 3. -/
theorem ss3_joint_ss2_slack (n0 n2 n3 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 ≤ nD)
    (h2 : 1 ≤ n2) (h3 : 1 ≤ n3) :
    3 ≤ nD - (n0 + n2 + n3) := by
  omega

/-- In any periodic word partitioned into low-SS (U_low), SS=2 (U2), and SS=3 (U3),
the supply slack |D| - |U| is at least |U2| + 2*|U3|. -/
theorem three_ss_slack_ge_weights (U_low U2 U3 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length ≤ D.length) :
    U2.length + 2 * U3.length ≤ D.length - (U_low.length + U2.length + U3.length) :=
  ss3_slack_bound U_low.length U2.length U3.length D.length h_weight

/-- Extremal supplies have zero SS=2 additions and zero SS=3 additions. -/
theorem three_ss_extremal_count_zero (U_low U2 U3 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length ≤ D.length)
    (h_sat : D.length ≤ U_low.length + U2.length + U3.length) :
    U2.length = 0 ∧ U3.length = 0 :=
  ss3_extremal_forces_zero U_low.length U2.length U3.length D.length h_weight h_sat

/-- Deficit-1 supplies strictly exclude any SS=3 additions. -/
theorem three_ss_deficit_one_excludes_ss3 (U_low U2 U3 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length ≤ D.length)
    (h_def1 : D.length ≤ (U_low.length + U2.length + U3.length) + 1) :
    U3.length = 0 :=
  ss3_deficit_one_forces_zero U_low.length U2.length U3.length D.length h_weight h_def1

/-- Deficit-2 supplies allow at most one SS=3 addition. -/
theorem three_ss_deficit_two_count_le_one (U_low U2 U3 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length ≤ D.length)
    (h_def2 : D.length ≤ (U_low.length + U2.length + U3.length) + 2) :
    U3.length ≤ 1 :=
  ss3_deficit_two_forces_le_one U_low.length U2.length U3.length D.length h_weight h_def2

end Recaman.ThreeSSWeightCapacity
