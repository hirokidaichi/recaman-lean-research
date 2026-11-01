import Recaman.UniversalSSStratification

/-!
# ThreeSSClassification: Classification and Lag Forcing of Minimal SS=3 P2 Windows

This module completely classifies all minimal SS=3 P2 windows:

1. `w1`, `w2`, `w3`: The three canonical length-11 SS=3 P2 words:
   - `w1` = `SSAAAAAASSS`
   - `w2` = `AAASSSSAAAS`
   - `w3` = `AAASSASSSAA`
2. `isMinimalP2`: Decidable predicate identifying minimal P2 words.
3. `isMinimalP2_iff`: Correctness equivalence of `isMinimalP2`.
4. `bitWords_eleven_ss3_filter`: Exhaustive verification that exactly 3 minimal P2 words
   of length 11 have `ssCount = 3`.
5. `minimal_p2_length_eleven_ss3_cases`: Any minimal P2 word of length 11 with `ssCount = 3`
   is equal to `w1`, `w2`, or `w3`.
6. `minimal_ss3_lag_ge_eleven`: Any minimal P2 window with `ssCount = 3` satisfies `lag ≥ 11`.
7. `minimal_ss3_lag_lt_fifteen_eq_eleven`: Any minimal P2 window with `ssCount = 3` and `lag < 15`
   must have `lag = 11`.
8. `minimal_ss3_ones_eq_six`: Any minimal SS=3 window with `lag < 15` contains exactly 6 additions.
9. `minimal_ss3_zeros_eq_five`: Any minimal SS=3 window with `lag < 15` contains exactly 5 subtractions.
10. `minimal_ss3_subtraction_surplus`: Any minimal SS=3 window with `lag < 15` possesses a surplus
    of at least 4 internal subtractions beyond its primary subtraction.
11. `minimal_ss3_classification_lt_fifteen`: Every minimal SS=3 window with `lag < 15` is equal
    to one of the 3 explicit canonical words `w1`, `w2`, or `w3`.
-/

namespace Recaman.ThreeSSClassification

open Recaman.TightP2ParityRigidity Recaman.TwoSSEndpoint Recaman.LeadingRunSupply
open Recaman.LagSevenTightObstruction Recaman.OneSSMultiplicity Recaman.SS2MinimalLagBound
open Recaman.SS2LagElevenForcing Recaman.TightSSZeroRigidity Recaman.TightCapacityHierarchy Recaman.UniversalSSStratification

set_option maxRecDepth 2000000

instance (w : List Bool) : Decidable (P2 w) :=
  inferInstanceAs (Decidable (mass w = 1 ∧ moment w = 0))

/-- Decidable predicate for minimal P2 words. -/
def isMinimalP2 (w : List Bool) : Bool :=
  decide (P2 w) && (List.range w.length).all (fun d => d == 0 || !decide (P2 (w.take d)))

/-- Correctness equivalence of isMinimalP2. -/
theorem isMinimalP2_iff (w : List Bool) :
    isMinimalP2 w = true ↔ P2 w ∧ (∀ d < w.length, 0 < d → ¬ P2 (w.take d)) := by
  unfold isMinimalP2
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨hP, hall⟩
    refine ⟨hP, ?_⟩
    intro d hd hpos
    have hspec := hall d hd
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hspec
    rcases hspec with rfl | hnot
    · omega
    · exact hnot
  · rintro ⟨hP, hmin⟩
    refine ⟨hP, ?_⟩
    intro d hd
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not]
    by_cases hd0 : d = 0
    · left; exact hd0
    · right
      exact hmin d hd (by omega)

/-- Canonical minimal SS=3 word 1: SSAAAAAASSS. -/
def w1 : List Bool := [false, false, true, true, true, true, true, true, false, false, false]

/-- Canonical minimal SS=3 word 2: AAASSSSAAAS. -/
def w2 : List Bool := [true, true, true, false, false, false, false, true, true, true, false]

/-- Canonical minimal SS=3 word 3: AAASSASSSAA. -/
def w3 : List Bool := [true, true, true, false, false, true, false, false, false, true, true]

/-- Exhaustive classification of minimal length 11 SS=3 words. -/
theorem bitWords_eleven_ss3_filter :
    ((bitWords 11).filter (fun w => isMinimalP2 w && decide (ssCount w = 3))) = [w1, w2, w3] := by decide

/-- Every minimal P2 word of length 11 with ssCount = 3 is w1, w2, or w3. -/
theorem minimal_p2_length_eleven_ss3_cases (w : List Bool) (hlen : w.length = 11)
    (hP : P2 w) (hmin : ∀ d < 11, 0 < d → ¬ P2 (w.take d)) (hss3 : ssCount w = 3) :
    w = w1 ∨ w = w2 ∨ w = w3 := by
  have hmem : w ∈ bitWords 11 := by
    have hm := mem_bitWords w
    rw [hlen] at hm
    exact hm
  have hminP2 : isMinimalP2 w = true := by
    rw [isMinimalP2_iff]
    refine ⟨hP, ?_⟩
    intro d hd hpos
    rw [hlen] at hd
    exact hmin d hd hpos
  have hfilt : w ∈ ((bitWords 11).filter (fun w => isMinimalP2 w && decide (ssCount w = 3))) := by
    rw [List.mem_filter]
    refine ⟨hmem, ?_⟩
    simp [hminP2, hss3]
  rw [bitWords_eleven_ss3_filter] at hfilt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfilt
  exact hfilt

/-- Any minimal P2 window with ssCount = 3 satisfies lag ≥ 11. -/
theorem minimal_ss3_lag_ge_eleven (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hss3 : ssCount w = 3) :
    11 ≤ w.length := by
  have h2 : 2 ≤ ssCount w := by omega
  exact minimal_ss_ge_two_lag_ge_eleven w hP hmin h2

/-- Any minimal P2 window with ssCount = 3 and lag < 15 has lag exactly equal to 11. -/
theorem minimal_ss3_lag_lt_fifteen_eq_eleven (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hss3 : ssCount w = 3)
    (hlt : w.length < 15) :
    w.length = 11 := by
  have hodd := p2_odd_length w hP
  have hge := minimal_ss3_lag_ge_eleven w hP hmin hss3
  have hcases : w.length = 11 ∨ w.length = 13 := by omega
  rcases hcases with h11 | h13
  · exact h11
  · exact False.elim (no_p2_length_thirteen w h13 hP)

/-- Any minimal SS=3 window with lag < 15 contains exactly 6 additions. -/
theorem minimal_ss3_ones_eq_six (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hss3 : ssCount w = 3)
    (hlt : w.length < 15) :
    ones w = 6 := by
  have h11 := minimal_ss3_lag_lt_fifteen_eq_eleven w hP hmin hss3 hlt
  exact p2_length_eleven_ones w hP h11

/-- Any minimal SS=3 window with lag < 15 contains exactly 5 subtractions. -/
theorem minimal_ss3_zeros_eq_five (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hss3 : ssCount w = 3)
    (hlt : w.length < 15) :
    w.length - ones w = 5 := by
  have h11 := minimal_ss3_lag_lt_fifteen_eq_eleven w hP hmin hss3 hlt
  exact p2_length_eleven_zeros w hP h11

/-- Any minimal SS=3 window with lag < 15 has a surplus of at least 4 subtractions. -/
theorem minimal_ss3_subtraction_surplus (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hss3 : ssCount w = 3)
    (hlt : w.length < 15) :
    4 ≤ (w.length - ones w) - 1 := by
  have h5 := minimal_ss3_zeros_eq_five w hP hmin hss3 hlt
  omega

/-- Complete classification of all minimal SS=3 windows below lag 15:
Every minimal SS=3 window with lag < 15 is equal to w1, w2, or w3. -/
theorem minimal_ss3_classification_lt_fifteen (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hss3 : ssCount w = 3)
    (hlt : w.length < 15) :
    w = w1 ∨ w = w2 ∨ w = w3 := by
  have h11 := minimal_ss3_lag_lt_fifteen_eq_eleven w hP hmin hss3 hlt
  have hmin11 : ∀ d < 11, 0 < d → ¬ P2 (w.take d) := by
    intro d hd hpos
    rw [← h11] at hd
    exact hmin d hd hpos
  exact minimal_p2_length_eleven_ss3_cases w h11 hP hmin11 hss3

end Recaman.ThreeSSClassification
