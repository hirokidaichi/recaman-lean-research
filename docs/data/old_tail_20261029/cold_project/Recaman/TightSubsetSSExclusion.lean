import Recaman.TightPeriodStratification

/-!
# TightSubsetSSExclusion: Universal Exclusion of High-SS Windows from Tight Bottlenecks

This module establishes the universal principle that in any periodic word with positive slack,
all subsets containing high-SS windows expand strictly, and all tight bottleneck subsets
(|N(A)| = |A|) are strictly restricted to low-SS windows:

1. `high_ss_subset_strictly_expands_p_le_eleven`: Any subset containing an `ssCount ≥ 2` window
   strictly expands (`|A| < |N(A)|`) for `p ≤ 11`.
2. `high_ss_not_in_tight_p_le_eleven`: No tight subset can contain any `ssCount ≥ 2` window for `p ≤ 11`.
3. `tight_subsets_purely_low_ss_p_le_eleven`: Every window in every tight subset has `ssCount ≤ 1` for `p ≤ 11`.
4. `non_clean_subset_strictly_expands_p_le_seven`: Any subset containing an `ssCount ≥ 1` window
   strictly expands (`|A| < |N(A)|`) for `p ≤ 7`.
5. `non_clean_not_in_tight_p_le_seven`: No tight subset can contain an `ssCount ≥ 1` window for `p ≤ 7`.
6. `tight_subsets_ss_zero_p_le_seven`: Every window in every tight subset has `ssCount = 0` for `p ≤ 7`.
7. `ss_ge_four_subset_strictly_expands_p_le_fifteen`: Any subset containing an `ssCount ≥ 4` window
   strictly expands for `p ≤ 15`.
8. `ss_ge_four_not_in_tight_p_le_fifteen`: No tight subset can contain an `ssCount ≥ 4` window for `p ≤ 15`.
9. `tight_subsets_ss_le_three_p_le_fifteen`: Every window in every tight subset has `ssCount ≤ 3` for `p ≤ 15`.
10. `ss_ge_six_subset_strictly_expands_p_le_nineteen`: Any subset containing an `ssCount ≥ 6` window
    strictly expands for `p ≤ 19`.
11. `ss_ge_six_not_in_tight_p_le_nineteen`: No tight subset can contain an `ssCount ≥ 6` window for `p ≤ 19`.
12. `tight_subsets_ss_le_five_p_le_nineteen`: Every window in every tight subset has `ssCount ≤ 5` for `p ≤ 19`.
-/

namespace Recaman.TightSubsetSSExclusion

open Recaman.TwoSSEndpoint Recaman.LeadingRunSupply Recaman.OneSSMultiplicity
open Recaman.SS2MinimalLagBound Recaman.UniversalSSStratification Recaman.P2ModFourRigidity
open Recaman.SSSixLagBound Recaman.GrandStratificationSynthesis Recaman.WrapObstruction
open Recaman.TightPeriodStratification

/-- For p ≤ 7, any subset containing a window with ssCount ≥ 1 strictly expands. -/
theorem non_clean_subset_strictly_expands_p_le_seven
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 7)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 1 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    A.length < (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length := by
  have hwrap : p ≤ lag u0 := by
    by_cases hlt : lag u0 < p
    · have hlen : (past e (u0 : Int) (lag u0)).length = lag u0 := by simp [past]
      have hzero := tight_ss_zero_of_p_le_seven p hp (past e (u0 : Int) (lag u0)) hP (by omega)
      omega
    · omega
  exact tight_excludes_wrapping_window e p hp_pos hper U A lag hAU hslack u0 hu0 hwrap

/-- For p ≤ 7, no tight subset can contain a window with ssCount ≥ 1. -/
theorem non_clean_not_in_tight_p_le_seven
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 7)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length = A.length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 1 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    False := by
  have hlt := non_clean_subset_strictly_expands_p_le_seven e p hp_pos hp hper U A lag hAU hslack u0 hu0 hP hss
  omega

/-- Clean AAS Rigidity: Every window in every tight subset in period p ≤ 7 has ssCount = 0. -/
theorem tight_subsets_ss_zero_p_le_seven
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 7)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hP : P2 (past e (u : Int) (lag u))) :
    ssCount (past e (u : Int) (lag u)) = 0 := by
  by_cases hss : 1 ≤ ssCount (past e (u : Int) (lag u))
  · exfalso
    exact non_clean_not_in_tight_p_le_seven e p hp_pos hp hper U A lag hAU hslack htight u hu hP hss
  · omega

/-- For p ≤ 11, any subset containing a high-SS window (ssCount ≥ 2) strictly expands. -/
theorem high_ss_subset_strictly_expands_p_le_eleven
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 2 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    A.length < (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length := by
  have hwrap : p ≤ lag u0 := by
    by_cases hlt : lag u0 < p
    · have hlen : (past e (u0 : Int) (lag u0)).length = lag u0 := by simp [past]
      have hle1 := tight_ss_le_one_of_p_le_eleven p hp (past e (u0 : Int) (lag u0)) hP (by omega)
      omega
    · omega
  exact tight_excludes_wrapping_window e p hp_pos hper U A lag hAU hslack u0 hu0 hwrap

/-- For p ≤ 11, no tight subset can contain a high-SS window (ssCount ≥ 2). -/
theorem high_ss_not_in_tight_p_le_eleven
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length = A.length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 2 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    False := by
  have hlt := high_ss_subset_strictly_expands_p_le_eleven e p hp_pos hp hper U A lag hAU hslack u0 hu0 hP hss
  omega

/-- Pure Low-SS Rigidity: Every window in every tight subset in period p ≤ 11 has ssCount ≤ 1. -/
theorem tight_subsets_purely_low_ss_p_le_eleven
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hP : P2 (past e (u : Int) (lag u))) :
    ssCount (past e (u : Int) (lag u)) ≤ 1 := by
  by_cases hss : 2 ≤ ssCount (past e (u : Int) (lag u))
  · exfalso
    exact high_ss_not_in_tight_p_le_eleven e p hp_pos hp hper U A lag hAU hslack htight u hu hP hss
  · omega

/-- For p ≤ 15, any subset containing a window with ssCount ≥ 4 strictly expands. -/
theorem ss_ge_four_subset_strictly_expands_p_le_fifteen
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 15)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 4 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    A.length < (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length := by
  have hwrap : p ≤ lag u0 := by
    by_cases hlt : lag u0 < p
    · have hlen : (past e (u0 : Int) (lag u0)).length = lag u0 := by simp [past]
      have hle3 := tight_ss_le_three_of_p_le_fifteen p hp (past e (u0 : Int) (lag u0)) hP (by omega)
      omega
    · omega
  exact tight_excludes_wrapping_window e p hp_pos hper U A lag hAU hslack u0 hu0 hwrap

/-- For p ≤ 15, no tight subset can contain a window with ssCount ≥ 4. -/
theorem ss_ge_four_not_in_tight_p_le_fifteen
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 15)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length = A.length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 4 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    False := by
  have hlt := ss_ge_four_subset_strictly_expands_p_le_fifteen e p hp_pos hp hper U A lag hAU hslack u0 hu0 hP hss
  omega

/-- SS ≤ 3 Rigidity: Every window in every tight subset in period p ≤ 15 has ssCount ≤ 3. -/
theorem tight_subsets_ss_le_three_p_le_fifteen
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 15)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hP : P2 (past e (u : Int) (lag u))) :
    ssCount (past e (u : Int) (lag u)) ≤ 3 := by
  by_cases hss : 4 ≤ ssCount (past e (u : Int) (lag u))
  · exfalso
    exact ss_ge_four_not_in_tight_p_le_fifteen e p hp_pos hp hper U A lag hAU hslack htight u hu hP hss
  · omega

/-- For p ≤ 19, any subset containing a window with ssCount ≥ 6 strictly expands. -/
theorem ss_ge_six_subset_strictly_expands_p_le_nineteen
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 19)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 6 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    A.length < (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length := by
  have hwrap : p ≤ lag u0 := by
    by_cases hlt : lag u0 < p
    · have hlen : (past e (u0 : Int) (lag u0)).length = lag u0 := by simp [past]
      have hle5 := tight_ss_le_five_of_p_le_nineteen p hp (past e (u0 : Int) (lag u0)) hP (by omega)
      omega
    · omega
  exact tight_excludes_wrapping_window e p hp_pos hper U A lag hAU hslack u0 hu0 hwrap

/-- For p ≤ 19, no tight subset can contain a window with ssCount ≥ 6. -/
theorem ss_ge_six_not_in_tight_p_le_nineteen
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 19)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length = A.length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 6 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    False := by
  have hlt := ss_ge_six_subset_strictly_expands_p_le_nineteen e p hp_pos hp hper U A lag hAU hslack u0 hu0 hP hss
  omega

/-- SS ≤ 5 Rigidity: Every window in every tight subset in period p ≤ 19 has ssCount ≤ 5. -/
theorem tight_subsets_ss_le_five_p_le_nineteen
    (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 19)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hP : P2 (past e (u : Int) (lag u))) :
    ssCount (past e (u : Int) (lag u)) ≤ 5 := by
  by_cases hss : 6 ≤ ssCount (past e (u : Int) (lag u))
  · exfalso
    exact ss_ge_six_not_in_tight_p_le_nineteen e p hp_pos hp hper U A lag hAU hslack htight u hu hP hss
  · omega

end Recaman.TightSubsetSSExclusion
