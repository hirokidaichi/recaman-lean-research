import Recaman.HighSSWrappingTheorem

/-!
# HallRobustnessTheorem: Immunity of High-SS Subsets to Hall Condition Failure

This module establishes that in any periodic word where total additions do not exceed
subtractions (|U| ≤ |D|), subsets containing high-SS windows are automatically immune
to Hall condition failure (|N(A)| < |A|). Consequently, any potential Hall failure is
strictly localized to low-SS subsets:

1. `high_ss_subset_hall_satisfied_p11`: Subsets with ssCount ≥ 2 windows satisfy |A| ≤ |N(A)| for p ≤ 11.
2. `high_ss_subset_hall_strict_slack_p11`: Subsets with ssCount ≥ 2 windows satisfy |A| < |N(A)| when |U| < |D|.
3. `hall_failure_excludes_high_ss_p11`: Any Hall failure subset (|N(A)| < |A|) excludes ssCount ≥ 2 for p ≤ 11.
4. `hall_failure_purely_low_ss_p11`: Hall failure subsets are purely low-SS (ssCount ≤ 1) for p ≤ 11.
5. `non_clean_subset_hall_satisfied_p7`: Subsets with ssCount ≥ 1 windows satisfy |A| ≤ |N(A)| for p ≤ 7.
6. `hall_failure_purely_clean_p7`: Hall failure subsets are purely clean AAS (ssCount = 0) for p ≤ 7.
7. `ss_ge_four_subset_hall_satisfied_p15`: Subsets with ssCount ≥ 4 windows satisfy |A| ≤ |N(A)| for p ≤ 15.
8. `hall_failure_excludes_ss_ge_four_p15`: Any Hall failure subset excludes ssCount ≥ 4 for p ≤ 15.
9. `hall_failure_ss_le_three_p15`: Hall failure subsets are restricted to ssCount ≤ 3 for p ≤ 15.
10. `ss_ge_six_subset_hall_satisfied_p19`: Subsets with ssCount ≥ 6 windows satisfy |A| ≤ |N(A)| for p ≤ 19.
11. `hall_failure_excludes_ss_ge_six_p19`: Any Hall failure subset excludes ssCount ≥ 6 for p ≤ 19.
12. `hall_failure_ss_le_five_p19`: Hall failure subsets are restricted to ssCount ≤ 5 for p ≤ 19.
-/

namespace Recaman.HallRobustnessTheorem

open Recaman.TwoSSEndpoint Recaman.LeadingRunSupply Recaman.OneSSMultiplicity
open Recaman.SS2MinimalLagBound Recaman.UniversalSSStratification Recaman.P2ModFourRigidity
open Recaman.SSSixLagBound Recaman.GrandStratificationSynthesis Recaman.WrapObstruction
open Recaman.TightPeriodStratification Recaman.TightSubsetSSExclusion Recaman.HighSSWrappingTheorem

/-- In period p ≤ 11, any subset containing an ssCount ≥ 2 window satisfies |A| ≤ |N(A)| if |U| ≤ |D|. -/
theorem high_ss_subset_hall_satisfied_p11 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 2 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length := by
  have hlen := high_ss_subset_length_eq_D_p11 e p hp_pos hp hper A lag u0 hu0 hP hss
  omega

/-- In period p ≤ 11, any subset containing an ssCount ≥ 2 window satisfies |A| < |N(A)| if |U| < |D|. -/
theorem high_ss_subset_hall_strict_slack_p11 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 2 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    A.length < (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length := by
  exact high_ss_subset_strictly_expands_p_le_eleven e p hp_pos hp hper U A lag hAU hslack u0 hu0 hP hss

/-- Any potential Hall failure subset excludes ssCount ≥ 2 windows for p ≤ 11. -/
theorem hall_failure_excludes_high_ss_p11 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hfail : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length < A.length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 2 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    False := by
  have hhall := high_ss_subset_hall_satisfied_p11 e p hp_pos hp hper U A lag hAU hUleD u0 hu0 hP hss
  omega

/-- All windows in any Hall failure subset in period p ≤ 11 are purely low-SS (ssCount ≤ 1). -/
theorem hall_failure_purely_low_ss_p11 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hfail : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length < A.length)
    (u : Nat) (hu : u ∈ A)
    (hP : P2 (past e (u : Int) (lag u))) :
    ssCount (past e (u : Int) (lag u)) ≤ 1 := by
  by_cases hss : 2 ≤ ssCount (past e (u : Int) (lag u))
  · exfalso
    exact hall_failure_excludes_high_ss_p11 e p hp_pos hp hper U A lag hAU hUleD hfail u hu hP hss
  · omega

/-- In period p ≤ 7, any subset containing an ssCount ≥ 1 window satisfies |A| ≤ |N(A)| if |U| ≤ |D|. -/
theorem non_clean_subset_hall_satisfied_p7 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 7)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 1 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length := by
  have hwrap : p ≤ lag u0 := by
    by_cases hlt : lag u0 < p
    · have hlen : (past e (u0 : Int) (lag u0)).length = lag u0 := by simp [past]
      have hzero := tight_ss_zero_of_p_le_seven p hp (past e (u0 : Int) (lag u0)) hP (by omega)
      omega
    · omega
  have hlen := neighborhood_length_of_has_wrap e p hp_pos hper A lag u0 hu0 hwrap
  omega

/-- All windows in any Hall failure subset in period p ≤ 7 are clean AAS (ssCount = 0). -/
theorem hall_failure_purely_clean_p7 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 7)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hfail : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length < A.length)
    (u : Nat) (hu : u ∈ A)
    (hP : P2 (past e (u : Int) (lag u))) :
    ssCount (past e (u : Int) (lag u)) = 0 := by
  by_cases hss : 1 ≤ ssCount (past e (u : Int) (lag u))
  · have hhall := non_clean_subset_hall_satisfied_p7 e p hp_pos hp hper U A lag hAU hUleD u hu hP hss
    omega
  · omega

/-- In period p ≤ 15, any subset containing an ssCount ≥ 4 window satisfies |A| ≤ |N(A)| if |U| ≤ |D|. -/
theorem ss_ge_four_subset_hall_satisfied_p15 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 15)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 4 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length := by
  have hwrap := ss_ge_four_is_wrapping_p15 e p hp u0 lag hP hss
  have hlen := neighborhood_length_of_has_wrap e p hp_pos hper A lag u0 hu0 hwrap
  omega

/-- Any potential Hall failure subset excludes ssCount ≥ 4 windows for p ≤ 15. -/
theorem hall_failure_excludes_ss_ge_four_p15 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 15)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hfail : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length < A.length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 4 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    False := by
  have hhall := ss_ge_four_subset_hall_satisfied_p15 e p hp_pos hp hper U A lag hAU hUleD u0 hu0 hP hss
  omega

/-- All windows in any Hall failure subset in period p ≤ 15 satisfy ssCount ≤ 3. -/
theorem hall_failure_ss_le_three_p15 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 15)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hfail : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length < A.length)
    (u : Nat) (hu : u ∈ A)
    (hP : P2 (past e (u : Int) (lag u))) :
    ssCount (past e (u : Int) (lag u)) ≤ 3 := by
  by_cases hss : 4 ≤ ssCount (past e (u : Int) (lag u))
  · exfalso
    exact hall_failure_excludes_ss_ge_four_p15 e p hp_pos hp hper U A lag hAU hUleD hfail u hu hP hss
  · omega

/-- In period p ≤ 19, any subset containing an ssCount ≥ 6 window satisfies |A| ≤ |N(A)| if |U| ≤ |D|. -/
theorem ss_ge_six_subset_hall_satisfied_p19 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 19)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 6 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    A.length ≤ (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length := by
  have hwrap := ss_ge_six_is_wrapping_p19 e p hp u0 lag hP hss
  have hlen := neighborhood_length_of_has_wrap e p hp_pos hper A lag u0 hu0 hwrap
  omega

/-- Any potential Hall failure subset excludes ssCount ≥ 6 windows for p ≤ 19. -/
theorem hall_failure_excludes_ss_ge_six_p19 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 19)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hfail : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length < A.length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 6 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    False := by
  have hhall := ss_ge_six_subset_hall_satisfied_p19 e p hp_pos hp hper U A lag hAU hUleD u0 hu0 hP hss
  omega

/-- All windows in any Hall failure subset in period p ≤ 19 satisfy ssCount ≤ 5. -/
theorem hall_failure_ss_le_five_p19 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 19)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hfail : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length < A.length)
    (u : Nat) (hu : u ∈ A)
    (hP : P2 (past e (u : Int) (lag u))) :
    ssCount (past e (u : Int) (lag u)) ≤ 5 := by
  by_cases hss : 6 ≤ ssCount (past e (u : Int) (lag u))
  · exfalso
    exact hall_failure_excludes_ss_ge_six_p19 e p hp_pos hp hper U A lag hAU hUleD hfail u hu hP hss
  · omega

end Recaman.HallRobustnessTheorem
