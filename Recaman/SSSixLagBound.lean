import Recaman.LagSevenTightObstruction
import Recaman.UniversalSSStratification
import Recaman.P2ModFourRigidity

/-!
# SSSixLagBound: Universal Stratification Tier 5 and Lag 19 Bound for ssCount ≥ 6

This module establishes the fifth tier of the universal SS stratification hierarchy:
1. `bitWords_fifteen_ss_ge_six`: Decidable enumeration confirms no length 15 P2 word has `ssCount ≥ 6`.
2. `p2_length_fifteen_ssCount_le_five`: Any P2 word of length 15 satisfies `ssCount w ≤ 5`.
3. `p2_length_seven_ssCount_le_one`: Any P2 word of length 7 satisfies `ssCount w ≤ 1`.
4. `p2_lag_lt_nineteen_ssCount_le_five`: Every P2 window with `lag < 19` has `ssCount ≤ 5`.
5. `p2_ss_ge_six_lag_ge_nineteen`: Any P2 window with `ssCount ≥ 6` has `lag ≥ 19`.
6. `no_ss_ge_six_lag_lt_nineteen`: No P2 window with `lag < 19` can have `ssCount ≥ 6`.
-/

namespace Recaman.SSSixLagBound

open Recaman.TwoSSEndpoint Recaman.LeadingRunSupply Recaman.OneSSMultiplicity
open Recaman.SS2MinimalLagBound Recaman.UniversalSSStratification Recaman.P2ModFourRigidity
open Recaman.LagSevenTightObstruction

set_option maxRecDepth 4000000
set_option maxHeartbeats 50000000

instance (w : List Bool) : Decidable (P2 w) :=
  inferInstanceAs (Decidable (mass w = 1 ∧ moment w = 0))

/-- Exhaustive check: There are no P2 words of length 15 with ssCount ≥ 6. -/
theorem bitWords_fifteen_ss_ge_six :
    ((bitWords 15).filter (fun w => decide (P2 w) && decide (6 ≤ ssCount w))) = [] := by decide

/-- Any P2 word of length 15 has ssCount ≤ 5. -/
theorem p2_length_fifteen_ssCount_le_five (w : List Bool) (hlen : w.length = 15) (hP : P2 w) :
    ssCount w ≤ 5 := by
  have hmem : w ∈ bitWords 15 := by
    have hm := mem_bitWords w
    rw [hlen] at hm
    exact hm
  by_cases hle : ssCount w ≤ 5
  · exact hle
  · have h6 : 6 ≤ ssCount w := by omega
    have hfilt : w ∈ ((bitWords 15).filter (fun w => decide (P2 w) && decide (6 ≤ ssCount w))) := by
      rw [List.mem_filter]
      refine ⟨hmem, ?_⟩
      simp [hP, h6]
    rw [bitWords_fifteen_ss_ge_six] at hfilt
    cases hfilt

/-- Any P2 word of length 7 has ssCount ≤ 1. -/
theorem p2_length_seven_ssCount_le_one (w : List Bool) (hlen : w.length = 7) (hP : P2 w) :
    ssCount w ≤ 1 := by
  have hcases := p2_length_seven_cases w hP hlen
  rcases hcases with rfl | rfl | rfl | rfl <;> decide

/-- Every P2 window with lag < 19 has ssCount ≤ 5. -/
theorem p2_lag_lt_nineteen_ssCount_le_five (w : List Bool) (hP : P2 w)
    (hlt : w.length < 19) :
    ssCount w ≤ 5 := by
  have hcases := p2_length_lt_nineteen_cases w hlt hP
  rcases hcases with h3 | h7 | h11 | h15
  · have hss := minimal_lag_le_five_ssCount_zero w hP (by omega)
    omega
  · have hss := p2_length_seven_ssCount_le_one w h7 hP
    omega
  · have hss := p2_length_eleven_ssCount_le_three w h11 hP
    omega
  · exact p2_length_fifteen_ssCount_le_five w h15 hP

/-- Universal Tier 5 Bound: Any P2 window with ssCount ≥ 6 must have lag ≥ 19. -/
theorem p2_ss_ge_six_lag_ge_nineteen (w : List Bool) (hP : P2 w)
    (hss : 6 ≤ ssCount w) :
    19 ≤ w.length := by
  by_cases hge : 19 ≤ w.length
  · exact hge
  · have hlt : w.length < 19 := by omega
    have hle := p2_lag_lt_nineteen_ssCount_le_five w hP hlt
    omega

/-- No P2 window with lag < 19 can have ssCount ≥ 6. -/
theorem no_ss_ge_six_lag_lt_nineteen (w : List Bool) (hP : P2 w)
    (hlt : w.length < 19)
    (hss : 6 ≤ ssCount w) :
    False := by
  have hge := p2_ss_ge_six_lag_ge_nineteen w hP hss
  omega

end Recaman.SSSixLagBound
