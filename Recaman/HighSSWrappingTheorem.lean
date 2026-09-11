import Recaman.TightSubsetSSExclusion

/-!
# HighSSWrappingTheorem: Universal Wrapping and Maximal Coverage of High-SS Windows

This module establishes that threshold high-SS windows are universally wrapping windows
across periods p ≤ 11, 15, 19, and therefore provide maximal coverage N(A) = D:

1. `p2_ss_ge_two_lag_ge_eleven`: Every P2 word with `ssCount ≥ 2` has `w.length ≥ 11`.
2. `p2_ss_ge_four_lag_ge_fifteen`: Every P2 word with `ssCount ≥ 4` has `w.length ≥ 15`.
3. `high_ss_is_wrapping_p11`: For `p ≤ 11`, every P2 window with `ssCount ≥ 2` satisfies `lag ≥ p`.
4. `ss_ge_four_is_wrapping_p15`: For `p ≤ 15`, every P2 window with `ssCount ≥ 4` satisfies `lag ≥ p`.
5. `ss_ge_six_is_wrapping_p19`: For `p ≤ 19`, every P2 window with `ssCount ≥ 6` satisfies `lag ≥ p`.
6. `high_ss_covers_all_p11`: For `p ≤ 11`, every `ssCount ≥ 2` window covers every subtraction phase `s ∈ D`.
7. `high_ss_neighborhood_eq_D_p11`: For `p ≤ 11`, any subset containing an `ssCount ≥ 2` window has `N(A) = D`.
8. `high_ss_subset_length_eq_D_p11`: For `p ≤ 11`, any subset containing an `ssCount ≥ 2` window has `|N(A)| = |D|`.
9. `high_ss_slack_ge_global_slack_p11`: Any subset containing an `ssCount ≥ 2` window has `|N(A)| - |A| ≥ |D| - |U|`.
10. `high_ss_avoids_all_tight_p11`: In any positive-slack word with `p ≤ 11`, no tight subset contains any `ssCount ≥ 2` window.
11. `ss_ge_four_neighborhood_eq_D_p15`: For `p ≤ 15`, any subset containing an `ssCount ≥ 4` window has `N(A) = D`.
12. `ss_ge_six_neighborhood_eq_D_p19`: For `p ≤ 19`, any subset containing an `ssCount ≥ 6` window has `N(A) = D`.
-/

namespace Recaman.HighSSWrappingTheorem

open Recaman.TwoSSEndpoint Recaman.LeadingRunSupply Recaman.OneSSMultiplicity
open Recaman.SS2MinimalLagBound Recaman.UniversalSSStratification Recaman.P2ModFourRigidity
open Recaman.SSSixLagBound Recaman.GrandStratificationSynthesis Recaman.WrapObstruction
open Recaman.TightPeriodStratification Recaman.TightSubsetSSExclusion

/-- Every P2 word with ssCount ≥ 2 has length ≥ 11 (unconditional on minimality). -/
theorem p2_ss_ge_two_lag_ge_eleven (w : List Bool) (hP : P2 w) (hss : 2 ≤ ssCount w) :
    11 ≤ w.length := by
  have hmod := p2_length_mod_four_eq_three w hP
  by_cases hlt : w.length < 11
  · have hcases : w.length = 3 ∨ w.length = 7 := by omega
    rcases hcases with h3 | h7
    · have h0 := minimal_lag_le_five_ssCount_zero w hP (by omega)
      omega
    · have h1 := p2_length_seven_ssCount_le_one w h7 hP
      omega
  · omega

/-- Every P2 word with ssCount ≥ 4 has length ≥ 15 (unconditional on minimality). -/
theorem p2_ss_ge_four_lag_ge_fifteen (w : List Bool) (hP : P2 w) (hss : 4 ≤ ssCount w) :
    15 ≤ w.length := by
  have hmod := p2_length_mod_four_eq_three w hP
  by_cases hlt : w.length < 15
  · have hcases : w.length = 3 ∨ w.length = 7 ∨ w.length = 11 := by omega
    rcases hcases with h3 | h7 | h11
    · have h0 := minimal_lag_le_five_ssCount_zero w hP (by omega)
      omega
    · have h1 := p2_length_seven_ssCount_le_one w h7 hP
      omega
    · have h3 := p2_length_eleven_ssCount_le_three w h11 hP
      omega
  · omega

/-- In any period p ≤ 11, every P2 window with ssCount ≥ 2 is a wrapping window: lag ≥ p. -/
theorem high_ss_is_wrapping_p11 (e : Int → Bool) (p : Nat) (hp : p ≤ 11)
    (u0 : Nat) (lag : Nat → Nat)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 2 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    p ≤ lag u0 := by
  have h11 := p2_ss_ge_two_lag_ge_eleven (past e (u0 : Int) (lag u0)) hP hss
  have hlen : (past e (u0 : Int) (lag u0)).length = lag u0 := by simp [past]
  omega

/-- In any period p ≤ 15, every P2 window with ssCount ≥ 4 is a wrapping window: lag ≥ p. -/
theorem ss_ge_four_is_wrapping_p15 (e : Int → Bool) (p : Nat) (hp : p ≤ 15)
    (u0 : Nat) (lag : Nat → Nat)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 4 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    p ≤ lag u0 := by
  have h15 := p2_ss_ge_four_lag_ge_fifteen (past e (u0 : Int) (lag u0)) hP hss
  have hlen : (past e (u0 : Int) (lag u0)).length = lag u0 := by simp [past]
  omega

/-- In any period p ≤ 19, every P2 window with ssCount ≥ 6 is a wrapping window: lag ≥ p. -/
theorem ss_ge_six_is_wrapping_p19 (e : Int → Bool) (p : Nat) (hp : p ≤ 19)
    (u0 : Nat) (lag : Nat → Nat)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 6 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    p ≤ lag u0 := by
  have h19 := p2_ss_ge_six_lag_ge_nineteen (past e (u0 : Int) (lag u0)) hP hss
  have hlen : (past e (u0 : Int) (lag u0)).length = lag u0 := by simp [past]
  omega

/-- In period p ≤ 11, any P2 window with ssCount ≥ 2 covers ALL subtractions in D. -/
theorem high_ss_covers_all_p11 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (u0 : Nat) (lag : Nat → Nat)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 2 ≤ ssCount (past e (u0 : Int) (lag u0)))
    (s : Nat) (hs : s ∈ LagElevenPeriodic.subPhases e 0 p) :
    Recaman.TwoSSTightDisjoint.WindowCoversSubtraction e p (u0 : Int) (lag u0) s := by
  have hwrap := high_ss_is_wrapping_p11 e p hp u0 lag hP hss
  exact window_wrap_covers_all_subtractions e p hp_pos hper (u0 : Int) (lag u0) hwrap s hs

/-- In period p ≤ 11, any subset containing a high-SS window has N(A) = D. -/
theorem high_ss_neighborhood_eq_D_p11 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 2 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    Recaman.TwoSSTightDisjoint.neighborhood e p A lag = LagElevenPeriodic.subPhases e 0 p := by
  have hwrap := high_ss_is_wrapping_p11 e p hp u0 lag hP hss
  exact neighborhood_eq_subPhases_of_has_wrap e p hp_pos hper A lag u0 hu0 hwrap

/-- In period p ≤ 11, any subset containing a high-SS window has |N(A)| = |D|. -/
theorem high_ss_subset_length_eq_D_p11 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 2 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length = (LagElevenPeriodic.subPhases e 0 p).length := by
  rw [high_ss_neighborhood_eq_D_p11 e p hp_pos hp hper A lag u0 hu0 hP hss]

/-- In period p ≤ 11, any subset containing a high-SS window has local slack ≥ global slack. -/
theorem high_ss_slack_ge_global_slack_p11 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 2 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    (LagElevenPeriodic.subPhases e 0 p).length - U.length ≤
      (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length - A.length := by
  rw [high_ss_subset_length_eq_D_p11 e p hp_pos hp hper A lag u0 hu0 hP hss]
  omega

/-- In any positive-slack word with p ≤ 11, no tight subset contains any high-SS window. -/
theorem high_ss_avoids_all_tight_p11 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length = A.length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 2 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    False := by
  exact high_ss_not_in_tight_p_le_eleven e p hp_pos hp hper U A lag hAU hslack htight u0 hu0 hP hss

/-- In period p ≤ 15, any subset containing an ssCount ≥ 4 window has N(A) = D. -/
theorem ss_ge_four_neighborhood_eq_D_p15 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 15)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 4 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    Recaman.TwoSSTightDisjoint.neighborhood e p A lag = LagElevenPeriodic.subPhases e 0 p := by
  have hwrap := ss_ge_four_is_wrapping_p15 e p hp u0 lag hP hss
  exact neighborhood_eq_subPhases_of_has_wrap e p hp_pos hper A lag u0 hu0 hwrap

/-- In period p ≤ 19, any subset containing an ssCount ≥ 6 window has N(A) = D. -/
theorem ss_ge_six_neighborhood_eq_D_p19 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 19)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 6 ≤ ssCount (past e (u0 : Int) (lag u0))) :
    Recaman.TwoSSTightDisjoint.neighborhood e p A lag = LagElevenPeriodic.subPhases e 0 p := by
  have hwrap := ss_ge_six_is_wrapping_p19 e p hp u0 lag hP hss
  exact neighborhood_eq_subPhases_of_has_wrap e p hp_pos hper A lag u0 hu0 hwrap

end Recaman.HighSSWrappingTheorem
