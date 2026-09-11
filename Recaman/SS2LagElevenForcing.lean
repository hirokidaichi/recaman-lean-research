import Recaman.SS2MinimalLagBound

/-!
# SS2LagElevenForcing: Length 13 Impossibility and Exact Lag 11 Forcing for Minimal SS=2 Donors

This module establishes the exact geometric determination of minimal SS=2 donor windows:

1. `bitWords_thirteen_p2`: Exhaustive verification that no word of length 13 satisfies P2.
2. `no_p2_length_thirteen`: No P2 word has length 13.
3. `minimal_ss2_lag_lt_fifteen_eq_eleven`: Any minimal P2 window with ssCount = 2 and lag < 15
   satisfies `lag = 11` (exact lag forcing).
4. `minimal_ss2_donor_phase_eq_eleven`: For any minimal SS=2 donor window at addition index `u`,
   its donation phase `s*(u)` is uniquely `endpointPhase p u 11`.
5. `p2_length_eleven_ones`: Any length 11 P2 window contains exactly 6 additions (`ones = 6`).
6. `p2_length_eleven_zeros`: Any length 11 P2 window contains exactly 5 subtractions (`zeros = 5`).
7. `minimal_ss2_ones_eq_six`: Every minimal SS=2 window with lag < 15 has exactly 6 additions.
8. `minimal_ss2_zeros_eq_five`: Every minimal SS=2 window with lag < 15 has exactly 5 subtractions.
9. `minimal_ss2_subtraction_surplus`: Every minimal SS=2 window with lag < 15 possesses a surplus
   of at least 4 internal subtractions beyond its single donated subtraction.
-/

namespace Recaman.SS2LagElevenForcing

open Recaman.TightP2ParityRigidity Recaman.TwoSSEndpoint Recaman.LeadingRunSupply
open Recaman.LagSevenTightObstruction Recaman.OneSSMultiplicity Recaman.SS2MinimalLagBound
open Recaman.TwoSSLocalDonation LowSSPeriodicSupply

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000

instance (w : List Bool) : Decidable (P2 w) :=
  inferInstanceAs (Decidable (mass w = 1 ∧ moment w = 0))

/-- There are no P2 words of length 13. -/
theorem bitWords_thirteen_p2 :
    (bitWords 13).filter (fun w => decide (P2 w)) = [] := by decide

/-- No P2 word has length 13. -/
theorem no_p2_length_thirteen (w : List Bool) (hlen : w.length = 13) (hP : P2 w) : False := by
  have hmem : w ∈ bitWords 13 := by
    have hm := mem_bitWords w
    rw [hlen] at hm
    exact hm
  have hfilt : w ∈ (bitWords 13).filter (fun w => decide (P2 w)) := by
    rw [List.mem_filter]
    exact ⟨hmem, by simp [hP]⟩
  rw [bitWords_thirteen_p2] at hfilt
  cases hfilt

/-- Fundamental Uniqueness Theorem of Minimal SS=2 Donor Lag:
Any minimal P2 window with ssCount = 2 and lag < 15 must have lag EXACTLY equal to 11. -/
theorem minimal_ss2_lag_lt_fifteen_eq_eleven (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hss2 : ssCount w = 2)
    (hlt : w.length < 15) :
    w.length = 11 := by
  have hodd := p2_odd_length w hP
  have hge := minimal_ss2_lag_ge_eleven w hP hmin hss2
  have hcases : w.length = 11 ∨ w.length = 13 := by omega
  rcases hcases with h11 | h13
  · exact h11
  · exact False.elim (no_p2_length_thirteen w h13 hP)

/-- The donation phase of any minimal SS=2 donor window with lag < 15 is uniquely endpointPhase p u 11. -/
theorem minimal_ss2_donor_phase_eq_eleven (p : Nat) (u : Nat) (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hss2 : ssCount w = 2)
    (hlt : w.length < 15) :
    oldestSubtractionPhase p u w.length = endpointPhase p (u : Int) 11 := by
  have h11 := minimal_ss2_lag_lt_fifteen_eq_eleven w hP hmin hss2 hlt
  unfold oldestSubtractionPhase
  rw [h11]

/-- Any length 11 P2 window contains exactly 6 additions. -/
theorem p2_length_eleven_ones (w : List Bool) (hP : P2 w) (hlen : w.length = 11) :
    ones w = 6 := by
  have hm := hP.1
  have hmass := mass_eq w
  omega

/-- Any minimal SS=2 window with lag < 15 contains exactly 6 additions. -/
theorem minimal_ss2_ones_eq_six (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hss2 : ssCount w = 2)
    (hlt : w.length < 15) :
    ones w = 6 := by
  have h11 := minimal_ss2_lag_lt_fifteen_eq_eleven w hP hmin hss2 hlt
  exact p2_length_eleven_ones w hP h11

/-- Any length 11 P2 window contains exactly 5 subtractions. -/
theorem p2_length_eleven_zeros (w : List Bool) (hP : P2 w) (hlen : w.length = 11) :
    w.length - ones w = 5 := by
  have h6 := p2_length_eleven_ones w hP hlen
  omega

/-- Any minimal SS=2 window with lag < 15 contains exactly 5 subtractions. -/
theorem minimal_ss2_zeros_eq_five (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hss2 : ssCount w = 2)
    (hlt : w.length < 15) :
    w.length - ones w = 5 := by
  have h11 := minimal_ss2_lag_lt_fifteen_eq_eleven w hP hmin hss2 hlt
  exact p2_length_eleven_zeros w hP h11

/-- Any minimal SS=2 window with lag < 15 has a surplus of at least 4 subtractions
beyond its single donated subtraction. -/
theorem minimal_ss2_subtraction_surplus (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hss2 : ssCount w = 2)
    (hlt : w.length < 15) :
    4 ≤ (w.length - ones w) - 1 := by
  have h5 := minimal_ss2_zeros_eq_five w hP hmin hss2 hlt
  omega

end Recaman.SS2LagElevenForcing
