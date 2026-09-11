import Recaman.HighSSEliminationGrandTheorem

/-!
# SS2MinimalLagBound: Length 9 Impossibility and Minimal SS=2 Lag Lower Bound

This module proves that minimal SS=2 donor windows cannot have lag ≤ 9:

1. `bitWords_nine_p2`: Exhaustive verification that no word of length 9 satisfies P2.
2. `no_p2_length_nine`: No P2 word has length 9.
3. `p2_odd_length`: Every P2 word automatically has odd length (d % 2 = 1).
4. `minimal_p2_length_seven_cases`: Any minimal P2 word of length 7 is either
   [false, true, true, true, true, false, false] or [true, false, true, true, false, true, false].
5. `w1_ssCount`: The first minimal length 7 P2 word has ssCount = 1.
6. `w2_ssCount`: The second minimal length 7 P2 word has ssCount = 0.
7. `minimal_lag_seven_ssCount_le_one`: Every minimal P2 word of length 7 has ssCount ≤ 1.
8. `minimal_lag_seven_not_ss2`: No minimal P2 word of length 7 can have ssCount = 2.
9. `no_ss2_lag_three`: The canonical lag 3 window has ssCount = 0 ≠ 2.
10. `no_ss2_lag_le_five`: Any P2 window with lag ≤ 5 has ssCount = 0 ≠ 2.
11. `minimal_ss2_lag_ge_eleven`: Any minimal P2 window with ssCount = 2 satisfies lag ≥ 11.
-/

namespace Recaman.SS2MinimalLagBound

open Recaman.TightP2ParityRigidity Recaman.TwoSSEndpoint Recaman.LeadingRunSupply Recaman.LagSevenTightObstruction Recaman.OneSSMultiplicity

set_option maxRecDepth 200000

instance (w : List Bool) : Decidable (P2 w) :=
  inferInstanceAs (Decidable (mass w = 1 ∧ moment w = 0))

/-- There are no P2 words of length 9. -/
theorem bitWords_nine_p2 :
    (bitWords 9).filter (fun w => decide (P2 w)) = [] := by decide

/-- No P2 word has length 9. -/
theorem no_p2_length_nine (w : List Bool) (hlen : w.length = 9) (hP : P2 w) : False := by
  have hmem : w ∈ bitWords 9 := by
    have hm := mem_bitWords w
    rw [hlen] at hm
    exact hm
  have hfilt : w ∈ (bitWords 9).filter (fun w => decide (P2 w)) := by
    rw [List.mem_filter]
    exact ⟨hmem, by simp [hP]⟩
  rw [bitWords_nine_p2] at hfilt
  cases hfilt

/-- Every P2 word automatically has odd length. -/
theorem p2_odd_length (w : List Bool) (hP : P2 w) : w.length % 2 = 1 := by
  have hm := hP.1
  have hmass := mass_eq w
  omega

/-- Exhaustive classification of minimal length 7 P2 words into 2 words. -/
theorem minimal_p2_length_seven_cases (w : List Bool) (hP : P2 w) (hlen : w.length = 7)
    (hmin : ∀ d < 7, 0 < d → ¬ P2 (w.take d)) :
    w = [false, true, true, true, true, false, false] ∨
    w = [true, false, true, true, false, true, false] := by
  have hcases := p2_length_seven_cases w hP hlen
  rcases hcases with rfl | rfl | rfl | rfl
  · left; rfl
  · right; rfl
  · have h3 := hmin 3 (by omega) (by omega)
    have hp3 : P2 ([true, true, false, false, true, true, false].take 3) := by decide
    contradiction
  · have h3 := hmin 3 (by omega) (by omega)
    have hp3 : P2 ([true, true, false, true, false, false, true].take 3) := by decide
    contradiction

/-- The first minimal length 7 P2 word has ssCount = 1. -/
theorem w1_ssCount : ssCount [false, true, true, true, true, false, false] = 1 := by decide

/-- The second minimal length 7 P2 word has ssCount = 0. -/
theorem w2_ssCount : ssCount [true, false, true, true, false, true, false] = 0 := by decide

/-- Any minimal P2 word of length 7 has ssCount ≤ 1. -/
theorem minimal_lag_seven_ssCount_le_one (w : List Bool) (hP : P2 w) (hlen : w.length = 7)
    (hmin : ∀ d < 7, 0 < d → ¬ P2 (w.take d)) :
    ssCount w ≤ 1 := by
  have hcases := minimal_p2_length_seven_cases w hP hlen hmin
  rcases hcases with rfl | rfl
  · rw [w1_ssCount]; omega
  · rw [w2_ssCount]; omega

/-- No minimal P2 word of length 7 can have ssCount = 2. -/
theorem minimal_lag_seven_not_ss2 (w : List Bool) (hP : P2 w) (hlen : w.length = 7)
    (hmin : ∀ d < 7, 0 < d → ¬ P2 (w.take d)) :
    ssCount w ≠ 2 := by
  have hle := minimal_lag_seven_ssCount_le_one w hP hlen hmin
  omega

/-- The canonical lag 3 window has ssCount = 0 ≠ 2. -/
theorem no_ss2_lag_three : ssCount [true, true, false] ≠ 2 := by decide

/-- Any P2 window with lag ≤ 5 has ssCount = 0 ≠ 2. -/
theorem no_ss2_lag_le_five (w : List Bool) (hP : P2 w) (hle : w.length ≤ 5) :
    ssCount w ≠ 2 := by
  by_cases h1 : w.length = 1
  · exact False.elim (no_p2_length_one w h1 hP)
  · by_cases h3 : w.length = 3
    · have heq := p2_length_three_eq_aas w h3 hP
      rw [heq]
      exact no_ss2_lag_three
    · by_cases h5 : w.length = 5
      · exact False.elim (no_p2_length_five w h5 hP)
      · have hodd := p2_odd_length w hP
        omega

/-- Fundamental Lower Bound on Minimal SS=2 Lags:
Any minimal P2 window with ssCount = 2 satisfies lag ≥ 11. -/
theorem minimal_ss2_lag_ge_eleven (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hss2 : ssCount w = 2) :
    11 ≤ w.length := by
  have hodd := p2_odd_length w hP
  by_cases hlt : w.length < 11
  · have hcases : w.length = 1 ∨ w.length = 3 ∨ w.length = 5 ∨ w.length = 7 ∨ w.length = 9 := by
      omega
    rcases hcases with h1 | h3 | h5 | h7 | h9
    · exact False.elim (no_p2_length_one w h1 hP)
    · have heq := p2_length_three_eq_aas w h3 hP
      rw [heq] at hss2
      exact False.elim (no_ss2_lag_three hss2)
    · exact False.elim (no_p2_length_five w h5 hP)
    · exact False.elim (minimal_lag_seven_not_ss2 w hP h7 (fun d hd hpos => hmin d (by omega) hpos) hss2)
    · exact False.elim (no_p2_length_nine w h9 hP)
  · omega

end Recaman.SS2MinimalLagBound
