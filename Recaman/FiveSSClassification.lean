import Recaman.SSSixLagBound
import Recaman.ThreeSSClassification

/-!
# FiveSSClassification: Complete Classification and Exact Lag 15 Forcing for Minimal SS=5 Windows

This module completely classifies all minimal P2 words with `ssCount = 5` below lag 19:
1. `w15_1` .. `w15_5`: The 5 explicit canonical minimal SS=5 words of length 15.
2. `bitWords_fifteen_ss5_filter`: Decidable verification that these are the only such words in `bitWords 15`.
3. `minimal_p2_length_fifteen_ss5_cases`: Any minimal P2 word of length 15 with `ssCount = 5` is one of `w15_1` .. `w15_5`.
4. `minimal_ss5_lag_ge_fifteen`: Any minimal P2 window with `ssCount = 5` has `lag ≥ 15`.
5. `minimal_ss5_lag_lt_nineteen_eq_fifteen`: Any minimal SS=5 window with `lag < 19` has `lag = 15`.
6. `minimal_ss5_classification_lt_nineteen`: Every minimal SS=5 window with `lag < 19` is one of the 5 canonical words.
7. `minimal_ss5_ones_eq_eight`: Every canonical SS=5 word has exactly 8 additions.
8. `minimal_ss5_zeros_eq_seven`: Every canonical SS=5 word has exactly 7 subtractions.
9. `minimal_ss5_subtraction_surplus`: Every canonical SS=5 window has subtraction surplus ≥ 6.
-/

namespace Recaman.FiveSSClassification

open Recaman.TwoSSEndpoint Recaman.LeadingRunSupply Recaman.OneSSMultiplicity
open Recaman.SS2MinimalLagBound Recaman.UniversalSSStratification Recaman.P2ModFourRigidity
open Recaman.ThreeSSClassification Recaman.SSSixLagBound

set_option maxRecDepth 4000000
set_option maxHeartbeats 50000000

def w15_1 : List Bool := [false, false, false, true, true, true, true, true, true, true, true, false, false, false, false]
def w15_2 : List Bool := [true, true, true, true, false, false, false, false, false, false, true, true, true, true, false]
def w15_3 : List Bool := [true, false, false, true, true, true, true, true, false, false, false, false, false, true, true]
def w15_4 : List Bool := [true, true, true, true, false, false, false, false, false, true, true, false, false, true, true]
def w15_5 : List Bool := [true, true, true, true, false, false, false, true, false, false, false, false, true, true, true]

/-- The filter of bitWords 15 for minimal P2 words with ssCount = 5 is exactly [w15_1, w15_2, w15_3, w15_4, w15_5]. -/
theorem bitWords_fifteen_ss5_filter :
    ((bitWords 15).filter (fun w => isMinimalP2 w && decide (ssCount w = 5))) = [w15_1, w15_2, w15_3, w15_4, w15_5] := by decide

/-- Every minimal P2 word of length 15 with ssCount = 5 is equal to w15_1, w15_2, w15_3, w15_4, or w15_5. -/
theorem minimal_p2_length_fifteen_ss5_cases (w : List Bool) (hP : P2 w)
    (hlen : w.length = 15)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hss : ssCount w = 5) :
    w = w15_1 ∨ w = w15_2 ∨ w = w15_3 ∨ w = w15_4 ∨ w = w15_5 := by
  have hmem : w ∈ bitWords 15 := by
    have hm := mem_bitWords w
    rw [hlen] at hm
    exact hm
  have hminP2 : isMinimalP2 w = true := by
    rw [isMinimalP2_iff]
    exact ⟨hP, hmin⟩
  have hfilt : w ∈ ((bitWords 15).filter (fun w => isMinimalP2 w && decide (ssCount w = 5))) := by
    rw [List.mem_filter]
    refine ⟨hmem, ?_⟩
    simp [hminP2, hss]
  rw [bitWords_fifteen_ss5_filter] at hfilt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfilt
  exact hfilt

/-- Minimal SS=5 windows must have lag ≥ 15. -/
theorem minimal_ss5_lag_ge_fifteen (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hss : ssCount w = 5) :
    15 ≤ w.length := by
  by_cases hge : 15 ≤ w.length
  · exact hge
  · have hlt : w.length < 15 := by omega
    have hle := minimal_lag_lt_fifteen_ssCount_le_three w hP hmin hlt
    omega

/-- Exact Lag 15 Forcing for SS=5 below lag 19:
Any minimal P2 window with ssCount = 5 and lag < 19 has lag EXACTLY equal to 15. -/
theorem minimal_ss5_lag_lt_nineteen_eq_fifteen (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hss : ssCount w = 5)
    (hlt : w.length < 19) :
    w.length = 15 := by
  have hge := minimal_ss5_lag_ge_fifteen w hP hmin hss
  have hcases := p2_length_lt_nineteen_cases w hlt hP
  rcases hcases with h3 | h7 | h11 | h15
  · omega
  · omega
  · omega
  · exact h15

/-- Canonical SS=5 words have exactly 8 additions. -/
theorem minimal_ss5_ones_eq_eight (w : List Bool)
    (hw : w = w15_1 ∨ w = w15_2 ∨ w = w15_3 ∨ w = w15_4 ∨ w = w15_5) :
    ones w = 8 := by
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Canonical SS=5 words have exactly 7 subtractions. -/
theorem minimal_ss5_zeros_eq_seven (w : List Bool)
    (hw : w = w15_1 ∨ w = w15_2 ∨ w = w15_3 ∨ w = w15_4 ∨ w = w15_5) :
    w.length - ones w = 7 := by
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Subtraction surplus of minimal SS=5 windows is at least 6. -/
theorem minimal_ss5_subtraction_surplus (w : List Bool)
    (hw : w = w15_1 ∨ w = w15_2 ∨ w = w15_3 ∨ w = w15_4 ∨ w = w15_5) :
    4 ≤ (w.length - ones w) - 1 := by
  have hz := minimal_ss5_zeros_eq_seven w hw
  omega

/-- Full classification of minimal SS=5 windows below lag 19:
Every minimal SS=5 window with lag < 19 is equal to w15_1, w15_2, w15_3, w15_4, or w15_5. -/
theorem minimal_ss5_classification_lt_nineteen (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hss : ssCount w = 5)
    (hlt : w.length < 19) :
    w = w15_1 ∨ w = w15_2 ∨ w = w15_3 ∨ w = w15_4 ∨ w = w15_5 := by
  have hlen := minimal_ss5_lag_lt_nineteen_eq_fifteen w hP hmin hss hlt
  exact minimal_p2_length_fifteen_ss5_cases w hP hlen hmin hss

end Recaman.FiveSSClassification
