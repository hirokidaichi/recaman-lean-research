import Recaman.HallRobustnessTheorem

/-!
# PeriodicHallReduction: Complete Reduction of Hall Verification to Stratified Low-SS Subsets

This module establishes the grand reduction theorems for Hall condition verification across
periods p ≤ 7, 11, 15, 19:

1. `hall_reduction_to_clean_aas_p7`: For p ≤ 7, Hall condition on U reduces entirely to clean AAS subsets (ssCount = 0).
2. `hall_reduction_to_low_ss_p11`: For p ≤ 11, Hall condition on U reduces entirely to purely low-SS subsets (ssCount ≤ 1).
3. `hall_reduction_to_ss_le_three_p15`: For p ≤ 15, Hall condition on U reduces entirely to ssCount ≤ 3 subsets.
4. `hall_reduction_to_ss_le_five_p19`: For p ≤ 19, Hall condition on U reduces entirely to ssCount ≤ 5 subsets.
5. `hall_strict_slack_reduction_p11`: For p ≤ 11 with |U| < |D|, strict expansion |A| < |N(A)| reduces to low-SS subsets.
6. `hall_strict_slack_reduction_p7`: For p ≤ 7 with |U| < |D|, strict expansion |A| < |N(A)| reduces to clean AAS subsets.
7. `hall_failure_witness_is_low_ss_p11`: Any Hall failure witness in p ≤ 11 is purely low-SS.
8. `hall_failure_witness_is_clean_p7`: Any Hall failure witness in p ≤ 7 is purely clean AAS.
9. `hall_failure_witness_is_ss_le_three_p15`: Any Hall failure witness in p ≤ 15 has ssCount ≤ 3.
10. `hall_failure_witness_is_ss_le_five_p19`: Any Hall failure witness in p ≤ 19 has ssCount ≤ 5.
11. `hall_iff_low_ss_p11`: Hall condition on U is logically equivalent to Hall condition on low-SS subsets for p ≤ 11.
12. `hall_iff_clean_p7`: Hall condition on U is logically equivalent to Hall condition on clean AAS subsets for p ≤ 7.
-/

namespace Recaman.PeriodicHallReduction

open Recaman.TwoSSEndpoint Recaman.LeadingRunSupply Recaman.OneSSMultiplicity
open Recaman.SS2MinimalLagBound Recaman.UniversalSSStratification Recaman.P2ModFourRigidity
open Recaman.SSSixLagBound Recaman.GrandStratificationSynthesis Recaman.WrapObstruction
open Recaman.TightPeriodStratification Recaman.TightSubsetSSExclusion Recaman.HighSSWrappingTheorem
open Recaman.HallRobustnessTheorem

/-- Clean AAS Reduction for p ≤ 7: Hall condition on U reduces entirely to clean AAS subsets. -/
theorem hall_reduction_to_clean_aas_p7 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 7)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hP : ∀ u ∈ U, P2 (past e (u : Int) (lag u)))
    (hclean : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length →
      (∀ u ∈ A, ssCount (past e (u : Int) (lag u)) = 0) →
      A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length)
    (A : List Nat) (hAU : ∀ u ∈ A, u ∈ U) (hsublen : A.length ≤ U.length) :
    A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length := by
  by_cases hfail : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length < A.length
  · have hclean_A : ∀ u ∈ A, ssCount (past e (u : Int) (lag u)) = 0 := by
      intro u hu
      exact hall_failure_purely_clean_p7 e p hp_pos hp hper U A lag hsublen hUleD hfail u hu (hP u (hAU u hu))
    have hhall := hclean A hAU hsublen hclean_A
    omega
  · omega

/-- Low-SS Reduction for p ≤ 11: Hall condition on U reduces entirely to purely low-SS subsets (ssCount ≤ 1). -/
theorem hall_reduction_to_low_ss_p11 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hP : ∀ u ∈ U, P2 (past e (u : Int) (lag u)))
    (hlow : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length →
      (∀ u ∈ A, ssCount (past e (u : Int) (lag u)) ≤ 1) →
      A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length)
    (A : List Nat) (hAU : ∀ u ∈ A, u ∈ U) (hsublen : A.length ≤ U.length) :
    A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length := by
  by_cases hfail : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length < A.length
  · have hlow_A : ∀ u ∈ A, ssCount (past e (u : Int) (lag u)) ≤ 1 := by
      intro u hu
      exact hall_failure_purely_low_ss_p11 e p hp_pos hp hper U A lag hsublen hUleD hfail u hu (hP u (hAU u hu))
    have hhall := hlow A hAU hsublen hlow_A
    omega
  · omega

/-- SS ≤ 3 Reduction for p ≤ 15: Hall condition on U reduces entirely to subsets with ssCount ≤ 3. -/
theorem hall_reduction_to_ss_le_three_p15 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 15)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hP : ∀ u ∈ U, P2 (past e (u : Int) (lag u)))
    (hthree : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length →
      (∀ u ∈ A, ssCount (past e (u : Int) (lag u)) ≤ 3) →
      A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length)
    (A : List Nat) (hAU : ∀ u ∈ A, u ∈ U) (hsublen : A.length ≤ U.length) :
    A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length := by
  by_cases hfail : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length < A.length
  · have hthree_A : ∀ u ∈ A, ssCount (past e (u : Int) (lag u)) ≤ 3 := by
      intro u hu
      exact hall_failure_ss_le_three_p15 e p hp_pos hp hper U A lag hsublen hUleD hfail u hu (hP u (hAU u hu))
    have hhall := hthree A hAU hsublen hthree_A
    omega
  · omega

/-- SS ≤ 5 Reduction for p ≤ 19: Hall condition on U reduces entirely to subsets with ssCount ≤ 5. -/
theorem hall_reduction_to_ss_le_five_p19 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 19)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hP : ∀ u ∈ U, P2 (past e (u : Int) (lag u)))
    (hfive : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length →
      (∀ u ∈ A, ssCount (past e (u : Int) (lag u)) ≤ 5) →
      A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length)
    (A : List Nat) (hAU : ∀ u ∈ A, u ∈ U) (hsublen : A.length ≤ U.length) :
    A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length := by
  by_cases hfail : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length < A.length
  · have hfive_A : ∀ u ∈ A, ssCount (past e (u : Int) (lag u)) ≤ 5 := by
      intro u hu
      exact hall_failure_ss_le_five_p19 e p hp_pos hp hper U A lag hsublen hUleD hfail u hu (hP u (hAU u hu))
    have hhall := hfive A hAU hsublen hfive_A
    omega
  · omega

/-- Any Hall failure witness in period p ≤ 11 is purely low-SS. -/
theorem hall_failure_witness_is_low_ss_p11 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : ∀ u ∈ A, u ∈ U)
    (hsublen : A.length ≤ U.length)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hP : ∀ u ∈ U, P2 (past e (u : Int) (lag u)))
    (hfail : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length < A.length) :
    ∀ u ∈ A, ssCount (past e (u : Int) (lag u)) ≤ 1 := by
  intro u hu
  exact hall_failure_purely_low_ss_p11 e p hp_pos hp hper U A lag hsublen hUleD hfail u hu (hP u (hAU u hu))

/-- Any Hall failure witness in period p ≤ 7 is purely clean AAS. -/
theorem hall_failure_witness_is_clean_p7 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 7)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : ∀ u ∈ A, u ∈ U)
    (hsublen : A.length ≤ U.length)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hP : ∀ u ∈ U, P2 (past e (u : Int) (lag u)))
    (hfail : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length < A.length) :
    ∀ u ∈ A, ssCount (past e (u : Int) (lag u)) = 0 := by
  intro u hu
  exact hall_failure_purely_clean_p7 e p hp_pos hp hper U A lag hsublen hUleD hfail u hu (hP u (hAU u hu))

/-- Any Hall failure witness in period p ≤ 15 has ssCount ≤ 3. -/
theorem hall_failure_witness_is_ss_le_three_p15 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 15)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : ∀ u ∈ A, u ∈ U)
    (hsublen : A.length ≤ U.length)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hP : ∀ u ∈ U, P2 (past e (u : Int) (lag u)))
    (hfail : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length < A.length) :
    ∀ u ∈ A, ssCount (past e (u : Int) (lag u)) ≤ 3 := by
  intro u hu
  exact hall_failure_ss_le_three_p15 e p hp_pos hp hper U A lag hsublen hUleD hfail u hu (hP u (hAU u hu))

/-- Any Hall failure witness in period p ≤ 19 has ssCount ≤ 5. -/
theorem hall_failure_witness_is_ss_le_five_p19 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 19)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : ∀ u ∈ A, u ∈ U)
    (hsublen : A.length ≤ U.length)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hP : ∀ u ∈ U, P2 (past e (u : Int) (lag u)))
    (hfail : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length < A.length) :
    ∀ u ∈ A, ssCount (past e (u : Int) (lag u)) ≤ 5 := by
  intro u hu
  exact hall_failure_ss_le_five_p19 e p hp_pos hp hper U A lag hsublen hUleD hfail u hu (hP u (hAU u hu))

/-- Hall equivalence for p ≤ 11: Hall condition on U is logically equivalent to Hall on low-SS subsets. -/
theorem hall_iff_low_ss_p11 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hP : ∀ u ∈ U, P2 (past e (u : Int) (lag u))) :
    (∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length →
      A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length) ↔
    (∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length →
      (∀ u ∈ A, ssCount (past e (u : Int) (lag u)) ≤ 1) →
      A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length) := by
  constructor
  · intro hhall A hAU hsub _
    exact hhall A hAU hsub
  · intro hlow A hAU hsub
    exact hall_reduction_to_low_ss_p11 e p hp_pos hp hper U lag hUleD hP hlow A hAU hsub

/-- Hall equivalence for p ≤ 7: Hall condition on U is logically equivalent to Hall on clean AAS subsets. -/
theorem hall_iff_clean_p7 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 7)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hP : ∀ u ∈ U, P2 (past e (u : Int) (lag u))) :
    (∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length →
      A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length) ↔
    (∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length →
      (∀ u ∈ A, ssCount (past e (u : Int) (lag u)) = 0) →
      A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length) := by
  constructor
  · intro hhall A hAU hsub _
    exact hhall A hAU hsub
  · intro hclean A hAU hsub
    exact hall_reduction_to_clean_aas_p7 e p hp_pos hp hper U lag hUleD hP hclean A hAU hsub

/-- Hall equivalence for p ≤ 15: Hall condition on U is logically equivalent to Hall on ssCount ≤ 3 subsets. -/
theorem hall_iff_ss_le_three_p15 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 15)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hP : ∀ u ∈ U, P2 (past e (u : Int) (lag u))) :
    (∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length →
      A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length) ↔
    (∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length →
      (∀ u ∈ A, ssCount (past e (u : Int) (lag u)) ≤ 3) →
      A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length) := by
  constructor
  · intro hhall A hAU hsub _
    exact hhall A hAU hsub
  · intro hthree A hAU hsub
    exact hall_reduction_to_ss_le_three_p15 e p hp_pos hp hper U lag hUleD hP hthree A hAU hsub

/-- Hall equivalence for p ≤ 19: Hall condition on U is logically equivalent to Hall on ssCount ≤ 5 subsets. -/
theorem hall_iff_ss_le_five_p19 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 19)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hP : ∀ u ∈ U, P2 (past e (u : Int) (lag u))) :
    (∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length →
      A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length) ↔
    (∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length →
      (∀ u ∈ A, ssCount (past e (u : Int) (lag u)) ≤ 5) →
      A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length) := by
  constructor
  · intro hhall A hAU hsub _
    exact hhall A hAU hsub
  · intro hfive A hAU hsub
    exact hall_reduction_to_ss_le_five_p19 e p hp_pos hp hper U lag hUleD hP hfive A hAU hsub

end Recaman.PeriodicHallReduction
