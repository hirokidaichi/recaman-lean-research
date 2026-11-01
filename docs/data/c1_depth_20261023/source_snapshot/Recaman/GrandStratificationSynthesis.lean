import Recaman.FiveSSWeightCapacity
import Recaman.SSSixLagBound

/-!
# GrandStratificationSynthesis: Master Synthesis of SS-Stratification and Capacity Reduction for lag < 19

This module synthesizes the overarching structural and capacity theorems for all minimal
P2 windows below lag 19:
1. `grand_quantum_lag_cases`: Any P2 window with `lag < 19` has length 3, 7, 11, or 15.
2. `grand_ss_count_bound`: Any P2 window with `lag < 19` satisfies `ssCount ≤ 5`.
3. `grand_ss_ge_four_forces_fifteen`: Any minimal window with `ssCount ≥ 4` and `lag < 19` has `lag = 15`.
4. `grand_no_ss_ge_six`: Windows with `ssCount ≥ 6` are strictly impossible below lag 19.
5. `grand_high_ss_forces_strict`: Any high-SS addition forces strict capacity deficit `slack ≥ 1`.
6. `grand_saturated_forces_low_ss`: Saturated supplies (`|U| = |D|`) are purely low-SS (`ssCount ≤ 1`).
7. `grand_capacity_reduction`: The global capacity inequality reduces unconditionally to low-SS supplies.
8. `grand_slack_ge_excess`: Supply slack is bounded below by the full sum of excess weights.
9. List liftings: Concrete theorems for list lengths on periodic supplies.
-/

namespace Recaman.GrandStratificationSynthesis

open Recaman.TwoSSEndpoint Recaman.LeadingRunSupply Recaman.OneSSMultiplicity
open Recaman.SS2MinimalLagBound Recaman.UniversalSSStratification Recaman.P2ModFourRigidity
open Recaman.SSSixLagBound Recaman.FiveSSClassification Recaman.FiveSSWeightCapacity

/-- Discrete Quantum Steps: Any P2 window below lag 19 has length 3, 7, 11, or 15. -/
theorem grand_quantum_lag_cases (w : List Bool) (hP : P2 w) (hlt : w.length < 19) :
    w.length = 3 ∨ w.length = 7 ∨ w.length = 11 ∨ w.length = 15 :=
  p2_length_lt_nineteen_cases w hlt hP

/-- Universal Upper Bound: Any P2 window below lag 19 has ssCount ≤ 5. -/
theorem grand_ss_count_bound (w : List Bool) (hP : P2 w) (hlt : w.length < 19) :
    ssCount w ≤ 5 :=
  p2_lag_lt_nineteen_ssCount_le_five w hP hlt

/-- Exact Lag 15 Forcing: Minimal windows with ssCount ≥ 4 below lag 19 are forced to lag = 15. -/
theorem grand_ss_ge_four_forces_fifteen (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hss : 4 ≤ ssCount w)
    (hlt : w.length < 19) :
    w.length = 15 := by
  have hge := minimal_ss_ge_four_lag_ge_fifteen w hP hmin hss
  have hcases := p2_length_lt_nineteen_cases w hlt hP
  rcases hcases with h3 | h7 | h11 | h15
  · omega
  · omega
  · omega
  · exact h15

/-- Windows with ssCount ≥ 6 cannot exist below lag 19. -/
theorem grand_no_ss_ge_six (w : List Bool) (hP : P2 w) (hlt : w.length < 19)
    (hss : 6 ≤ ssCount w) :
    False :=
  no_ss_ge_six_lag_lt_nineteen w hP hlt hss

/-- High-SS additions force a strict deficit buffer of at least 1. -/
theorem grand_high_ss_forces_strict (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD)
    (h_high : 1 ≤ n2 + n3 + n4 + n5) :
    n0 + n2 + n3 + n4 + n5 ≤ nD - 1 := by
  omega

/-- Pure Low-SS Extremal Rigidity: Saturated supplies strictly exclude all high-SS windows. -/
theorem grand_saturated_forces_low_ss (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD)
    (h_sat : nD ≤ n0 + n2 + n3 + n4 + n5) :
    n2 = 0 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 0 ∧ n0 + n2 + n3 + n4 + n5 = n0 := by
  omega

/-- Grand Capacity Reduction Principle:
The global capacity inequality n_tot ≤ nD reduces unconditionally to low-SS supplies. -/
theorem grand_capacity_reduction (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD)
    (_h_low : n0 ≤ nD) :
    n0 + n2 + n3 + n4 + n5 ≤ nD := by
  omega

/-- Supply slack is bounded below by the full sum of excess weights. -/
theorem grand_slack_ge_excess (n0 n2 n3 n4 n5 nD : Nat)
    (h_weight : n0 + 2 * n2 + 3 * n3 + 4 * n4 + 5 * n5 ≤ nD) :
    n2 + 2 * n3 + 3 * n4 + 4 * n5 ≤ nD - (n0 + n2 + n3 + n4 + n5) :=
  five_tier_slack_bound n0 n2 n3 n4 n5 nD h_weight

/-- List-lifted pure low-SS structure for saturated supplies. -/
theorem grand_list_extremal_pure_low_ss (U_low U2 U3 U4 U5 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length + 4 * U4.length + 5 * U5.length ≤ D.length)
    (h_sat : D.length ≤ U_low.length + U2.length + U3.length + U4.length + U5.length) :
    U2.length = 0 ∧ U3.length = 0 ∧ U4.length = 0 ∧ U5.length = 0 ∧
    U_low.length + U2.length + U3.length + U4.length + U5.length = U_low.length :=
  grand_saturated_forces_low_ss U_low.length U2.length U3.length U4.length U5.length D.length h_weight h_sat

/-- List-lifted strict deficit from high-SS additions. -/
theorem grand_list_high_ss_forces_strict_deficit (U_low U2 U3 U4 U5 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length + 4 * U4.length + 5 * U5.length ≤ D.length)
    (h_high : 1 ≤ U2.length + U3.length + U4.length + U5.length) :
    U_low.length + U2.length + U3.length + U4.length + U5.length ≤ D.length - 1 :=
  grand_high_ss_forces_strict U_low.length U2.length U3.length U4.length U5.length D.length h_weight h_high

/-- List-lifted grand capacity reduction principle. -/
theorem grand_list_capacity_reduction (U_low U2 U3 U4 U5 D : List Nat)
    (h_weight : U_low.length + 2 * U2.length + 3 * U3.length + 4 * U4.length + 5 * U5.length ≤ D.length)
    (h_low : U_low.length ≤ D.length) :
    U_low.length + U2.length + U3.length + U4.length + U5.length ≤ D.length :=
  grand_capacity_reduction U_low.length U2.length U3.length U4.length U5.length D.length h_weight h_low

end Recaman.GrandStratificationSynthesis
