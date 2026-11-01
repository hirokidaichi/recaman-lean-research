import Recaman.WrapObstruction
import Recaman.GrandStratificationSynthesis

/-!
# TightPeriodStratification: Universal Tight Bottleneck Localization and SS Exclusion by Period

This module establishes the exact classification and SS bounds for all tight bottleneck
windows across periods p ≤ 19:
1. `tight_lags_p_le_fifteen`: For `p ≤ 15`, non-wrapping P2 windows have `lag ∈ {3, 7, 11}`.
2. `tight_lags_p_le_nineteen`: For `p ≤ 19`, non-wrapping P2 windows have `lag ∈ {3, 7, 11, 15}`.
3. `tight_lags_p_le_twenty_three`: For `p ≤ 23`, non-wrapping P2 windows have `lag ∈ {3, 7, 11, 15, 19}`.
4. `tight_ss_zero_of_p_le_seven`: For `p ≤ 7`, all tight windows have `ssCount = 0` (clean AAS).
5. `tight_ss_le_one_of_p_le_eleven`: For `p ≤ 11`, all tight windows have `ssCount ≤ 1`.
6. `tight_ss_le_three_of_p_le_fifteen`: For `p ≤ 15`, all tight windows have `ssCount ≤ 3`.
7. `tight_ss_le_five_of_p_le_nineteen`: For `p ≤ 19`, all tight windows have `ssCount ≤ 5`.
8. `tight_excludes_high_ss_for_p_le_eleven`: Tight subsets for `p ≤ 11` strictly exclude `ssCount ≥ 2`.
9. `tight_excludes_ss_ge_four_for_p_le_fifteen`: Tight subsets for `p ≤ 15` strictly exclude `ssCount ≥ 4`.
10. `tight_excludes_ss_ge_six_for_p_le_nineteen`: Tight subsets for `p ≤ 19` strictly exclude `ssCount ≥ 6`.
11. `tight_excludes_wrapping_window`: Positive-slack periodic words strictly exclude wrapping windows from tight subsets.
-/

namespace Recaman.TightPeriodStratification

open Recaman.TwoSSEndpoint Recaman.LeadingRunSupply Recaman.OneSSMultiplicity
open Recaman.SS2MinimalLagBound Recaman.UniversalSSStratification Recaman.P2ModFourRigidity
open Recaman.SSSixLagBound Recaman.GrandStratificationSynthesis Recaman.WrapObstruction
open Recaman.LagSevenTightObstruction

/-- For p ≤ 15, any non-wrapping P2 window has lag in {3, 7, 11}. -/
theorem tight_lags_p_le_fifteen (p : Nat) (hp : p ≤ 15)
    (d : Nat) (hd_lt : d < p) (hpos : 0 < d) (hmod : d % 4 = 3) :
    d = 3 ∨ d = 7 ∨ d = 11 := by
  omega

/-- For p ≤ 19, any non-wrapping P2 window has lag in {3, 7, 11, 15}. -/
theorem tight_lags_p_le_nineteen (p : Nat) (hp : p ≤ 19)
    (d : Nat) (hd_lt : d < p) (hpos : 0 < d) (hmod : d % 4 = 3) :
    d = 3 ∨ d = 7 ∨ d = 11 ∨ d = 15 := by
  omega

/-- For p ≤ 23, any non-wrapping P2 window has lag in {3, 7, 11, 15, 19}. -/
theorem tight_lags_p_le_twenty_three (p : Nat) (hp : p ≤ 23)
    (d : Nat) (hd_lt : d < p) (hpos : 0 < d) (hmod : d % 4 = 3) :
    d = 3 ∨ d = 7 ∨ d = 11 ∨ d = 15 ∨ d = 19 := by
  omega

/-- Clean AAS Rigidity for p ≤ 7: Every non-wrapping P2 window in period p ≤ 7 has ssCount = 0. -/
theorem tight_ss_zero_of_p_le_seven (p : Nat) (hp : p ≤ 7)
    (w : List Bool) (hP : P2 w) (hlt : w.length < p) :
    ssCount w = 0 := by
  have hmod := p2_length_mod_four_eq_three w hP
  have hpos : 0 < w.length := by omega
  have hd := tight_lags_for_p_le_seven p hp w.length hlt hpos hmod
  exact minimal_lag_le_five_ssCount_zero w hP (by omega)

/-- Low-SS Rigidity for p ≤ 11: Every non-wrapping P2 window in period p ≤ 11 has ssCount ≤ 1. -/
theorem tight_ss_le_one_of_p_le_eleven (p : Nat) (hp : p ≤ 11)
    (w : List Bool) (hP : P2 w) (hlt : w.length < p) :
    ssCount w ≤ 1 := by
  have hmod := p2_length_mod_four_eq_three w hP
  have hpos : 0 < w.length := by omega
  have hd := tight_lags_for_p_le_eleven p hp w.length hlt hpos hmod
  rcases hd with h3 | h7
  · have h0 := minimal_lag_le_five_ssCount_zero w hP (by omega)
    omega
  · exact p2_length_seven_ssCount_le_one w h7 hP

/-- SS ≤ 3 Bound for p ≤ 15: Every non-wrapping P2 window in period p ≤ 15 has ssCount ≤ 3. -/
theorem tight_ss_le_three_of_p_le_fifteen (p : Nat) (hp : p ≤ 15)
    (w : List Bool) (hP : P2 w) (hlt : w.length < p) :
    ssCount w ≤ 3 := by
  have hmod := p2_length_mod_four_eq_three w hP
  have hpos : 0 < w.length := by omega
  have hd := tight_lags_p_le_fifteen p hp w.length hlt hpos hmod
  rcases hd with h3 | h7 | h11
  · have h0 := minimal_lag_le_five_ssCount_zero w hP (by omega)
    omega
  · have h1 := p2_length_seven_ssCount_le_one w h7 hP
    omega
  · exact p2_length_eleven_ssCount_le_three w h11 hP

/-- SS ≤ 5 Bound for p ≤ 19: Every non-wrapping P2 window in period p ≤ 19 has ssCount ≤ 5. -/
theorem tight_ss_le_five_of_p_le_nineteen (p : Nat) (hp : p ≤ 19)
    (w : List Bool) (hP : P2 w) (hlt : w.length < p) :
    ssCount w ≤ 5 := by
  have hmod := p2_length_mod_four_eq_three w hP
  have hpos : 0 < w.length := by omega
  have hd := tight_lags_p_le_nineteen p hp w.length hlt hpos hmod
  rcases hd with h3 | h7 | h11 | h15
  · have h0 := minimal_lag_le_five_ssCount_zero w hP (by omega)
    omega
  · have h1 := p2_length_seven_ssCount_le_one w h7 hP
    omega
  · have h3 := p2_length_eleven_ssCount_le_three w h11 hP
    omega
  · exact p2_length_fifteen_ssCount_le_five w h15 hP

/-- Non-wrapping windows with ssCount ≥ 2 are impossible in period p ≤ 11. -/
theorem tight_excludes_high_ss_for_p_le_eleven (p : Nat) (hp : p ≤ 11)
    (w : List Bool) (hP : P2 w) (hlt : w.length < p)
    (hss : 2 ≤ ssCount w) : False := by
  have hle1 := tight_ss_le_one_of_p_le_eleven p hp w hP hlt
  omega

/-- Non-wrapping windows with ssCount ≥ 4 are impossible in period p ≤ 15. -/
theorem tight_excludes_ss_ge_four_for_p_le_fifteen (p : Nat) (hp : p ≤ 15)
    (w : List Bool) (hP : P2 w) (hlt : w.length < p)
    (hss : 4 ≤ ssCount w) : False := by
  have hle3 := tight_ss_le_three_of_p_le_fifteen p hp w hP hlt
  omega

/-- Non-wrapping windows with ssCount ≥ 6 are impossible in period p ≤ 19. -/
theorem tight_excludes_ss_ge_six_for_p_le_nineteen (p : Nat) (hp : p ≤ 19)
    (w : List Bool) (hP : P2 w) (hlt : w.length < p)
    (hss : 6 ≤ ssCount w) : False := by
  have hle5 := tight_ss_le_five_of_p_le_nineteen p hp w hP hlt
  omega

/-- In any positive-slack word, any subset containing a wrapping window expands strictly beyond its size. -/
theorem tight_excludes_wrapping_window (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hsublen : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hwrap : p ≤ lag u0) :
    A.length < (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length :=
  strict_expansion_of_has_wrap e p hp hper U A lag hsublen hslack u0 hu0 hwrap

/-- NO tight subset can contain a wrapping window. -/
theorem tight_excludes_wrapping_window_ne (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hsublen : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hwrap : p ≤ lag u0) :
    (Recaman.TwoSSTightDisjoint.neighborhood e p A lag).length ≠ A.length :=
  no_tight_subset_contains_wrap e p hp hper U A lag hsublen hslack u0 hu0 hwrap

end Recaman.TightPeriodStratification
