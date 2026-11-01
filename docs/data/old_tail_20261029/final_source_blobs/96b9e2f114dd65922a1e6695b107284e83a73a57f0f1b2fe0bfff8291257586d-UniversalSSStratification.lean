import Recaman.SS2LagElevenForcing
import Recaman.TightCapacityHierarchy

/-!
# UniversalSSStratification: Universal Lag-Stratification by SS-Count

This module establishes the complete four-tier lag hierarchy for minimal P2 windows
as a function of their adjacent subtraction count (`ssCount`):

1. `bitWords_eleven_ssCount_le_three`: Exhaustive verification that all P2 words of length 11
   satisfy `ssCount ≤ 3`.
2. `p2_length_eleven_ssCount_le_three`: Any P2 word of length 11 satisfies `ssCount ≤ 3`.
3. `minimal_lag_le_five_ssCount_zero`: Any minimal P2 window with `lag ≤ 5` has `ssCount = 0`.
4. `minimal_ss_ge_one_lag_ge_seven`: Any minimal P2 window with `ssCount ≥ 1` satisfies `lag ≥ 7`.
5. `minimal_ss_ge_two_lag_ge_eleven`: Any minimal P2 window with `ssCount ≥ 2` satisfies `lag ≥ 11`.
6. `minimal_lag_lt_fifteen_ssCount_le_three`: Every minimal P2 window with `lag < 15` satisfies `ssCount ≤ 3`.
7. `minimal_ss_ge_four_lag_ge_fifteen`: Any minimal P2 window with `ssCount ≥ 4` satisfies `lag ≥ 15`.
8. `no_ss_ge_four_lag_lt_fifteen`: No minimal P2 window with `lag < 15` can have `ssCount ≥ 4`.
-/

namespace Recaman.UniversalSSStratification

open Recaman.TightP2ParityRigidity Recaman.TwoSSEndpoint Recaman.LeadingRunSupply
open Recaman.LagSevenTightObstruction Recaman.OneSSMultiplicity Recaman.SS2MinimalLagBound
open Recaman.SS2LagElevenForcing Recaman.TightSSZeroRigidity Recaman.TightCapacityHierarchy

set_option maxRecDepth 2000000

instance (w : List Bool) : Decidable (P2 w) :=
  inferInstanceAs (Decidable (mass w = 1 ∧ moment w = 0))

/-- Exhaustive decision that all P2 words of length 11 have ssCount ≤ 3. -/
theorem bitWords_eleven_ssCount_le_three :
    ((bitWords 11).filter (fun w => decide (P2 w))).all (fun w => decide (ssCount w ≤ 3)) = true := by decide

/-- Any P2 word of length 11 satisfies ssCount ≤ 3. -/
theorem p2_length_eleven_ssCount_le_three (w : List Bool) (hlen : w.length = 11) (hP : P2 w) :
    ssCount w ≤ 3 := by
  have hmem : w ∈ bitWords 11 := by
    have hm := mem_bitWords w
    rw [hlen] at hm
    exact hm
  have hfilt : w ∈ (bitWords 11).filter (fun w => decide (P2 w)) := by
    rw [List.mem_filter]
    exact ⟨hmem, by simp [hP]⟩
  have hall := bitWords_eleven_ssCount_le_three
  rw [List.all_eq_true] at hall
  have hspec := hall w hfilt
  simp at hspec
  exact hspec

/-- Any minimal P2 window with lag ≤ 5 has ssCount = 0. -/
theorem minimal_lag_le_five_ssCount_zero (w : List Bool) (hP : P2 w) (hle : w.length ≤ 5) :
    ssCount w = 0 := by
  have hodd := p2_odd_length w hP
  have hcases : w.length = 1 ∨ w.length = 3 ∨ w.length = 5 := by omega
  rcases hcases with h1 | h3 | h5
  · exact False.elim (no_p2_length_one w h1 hP)
  · have heq := p2_length_three_eq_aas w h3 hP
    rw [heq]
    exact aas_ssCount_zero
  · exact False.elim (no_p2_length_five w h5 hP)

/-- Any minimal P2 window with ssCount ≥ 1 satisfies lag ≥ 7. -/
theorem minimal_ss_ge_one_lag_ge_seven (w : List Bool) (hP : P2 w) (hss1 : 1 ≤ ssCount w) :
    7 ≤ w.length := by
  by_cases hlt : w.length < 7
  · have hle5 : w.length ≤ 5 := by
      have hodd := p2_odd_length w hP
      omega
    have h0 := minimal_lag_le_five_ssCount_zero w hP hle5
    omega
  · omega

/-- Any minimal P2 window with ssCount ≥ 2 satisfies lag ≥ 11. -/
theorem minimal_ss_ge_two_lag_ge_eleven (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hss2 : 2 ≤ ssCount w) :
    11 ≤ w.length := by
  have hodd := p2_odd_length w hP
  by_cases hlt : w.length < 11
  · have hcases : w.length = 1 ∨ w.length = 3 ∨ w.length = 5 ∨ w.length = 7 ∨ w.length = 9 := by omega
    rcases hcases with h1 | h3 | h5 | h7 | h9
    · exact False.elim (no_p2_length_one w h1 hP)
    · have heq := p2_length_three_eq_aas w h3 hP
      rw [heq] at hss2
      rw [aas_ssCount_zero] at hss2
      omega
    · exact False.elim (no_p2_length_five w h5 hP)
    · have hle1 := minimal_lag_seven_ssCount_le_one w hP h7 (fun d hd hpos => hmin d (by omega) hpos)
      omega
    · exact False.elim (no_p2_length_nine w h9 hP)
  · omega

/-- Universal Upper Bound on ssCount for lag < 15:
Every minimal P2 window with lag < 15 satisfies ssCount ≤ 3. -/
theorem minimal_lag_lt_fifteen_ssCount_le_three (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hlt : w.length < 15) :
    ssCount w ≤ 3 := by
  have hodd := p2_odd_length w hP
  have hcases : w.length = 1 ∨ w.length = 3 ∨ w.length = 5 ∨ w.length = 7 ∨ w.length = 9 ∨ w.length = 11 ∨ w.length = 13 := by omega
  rcases hcases with h1 | h3 | h5 | h7 | h9 | h11 | h13
  · exact False.elim (no_p2_length_one w h1 hP)
  · have heq := p2_length_three_eq_aas w h3 hP
    rw [heq]
    have h0 := aas_ssCount_zero
    omega
  · exact False.elim (no_p2_length_five w h5 hP)
  · have hle1 := minimal_lag_seven_ssCount_le_one w hP h7 (fun d hd hpos => hmin d (by omega) hpos)
    omega
  · exact False.elim (no_p2_length_nine w h9 hP)
  · exact p2_length_eleven_ssCount_le_three w h11 hP
  · exact False.elim (no_p2_length_thirteen w h13 hP)

/-- Fundamental Lag-15 Lower Bound for ssCount ≥ 4:
Any minimal P2 window with ssCount ≥ 4 satisfies lag ≥ 15. -/
theorem minimal_ss_ge_four_lag_ge_fifteen (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hss4 : 4 ≤ ssCount w) :
    15 ≤ w.length := by
  by_cases hlt : w.length < 15
  · have hle3 := minimal_lag_lt_fifteen_ssCount_le_three w hP hmin hlt
    omega
  · omega

/-- No minimal P2 window with lag < 15 can have ssCount ≥ 4. -/
theorem no_ss_ge_four_lag_lt_fifteen (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hlt : w.length < 15)
    (hss4 : 4 ≤ ssCount w) : False := by
  have hge15 := minimal_ss_ge_four_lag_ge_fifteen w hP hmin hss4
  omega

end Recaman.UniversalSSStratification
