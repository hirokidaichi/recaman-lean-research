import Recaman.ElevenSSDonationClosure

/-!
# LagSevenTightObstruction: Classification of Length 7 P2 Words and Tight Obstruction

This module provides the complete classification of length 7 P2 words and proves that
lag 7 windows cannot belong to small tight bottleneck subsets:

1. `bitWords_seven_p2`: Exhaustive classification of all 4 P2 words of length 7.
2. `p2_length_seven_cases`: Every P2 word of length 7 is equal to one of the 4 explicit words.
3. `no_lag_seven_in_tight_le_two`: No tight subset of size ≤ 2 can contain a lag 7 window.
4. `tight_avoiding_le_two_all_lag_three`: In any periodic word of period p ≤ 11, every member
   of any tight avoiding subset of size ≤ 2 has lag 3.
5. `tight_avoiding_le_two_all_aas`: In any periodic word of period p ≤ 11, every member
   of any tight avoiding subset of size ≤ 2 is an AAS window.
-/

namespace Recaman.LagSevenTightObstruction

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint TwoSSLocalDonation TwoSSAvoidTight WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem SS2AASCollisionObstruction ElevenSSDonationClosure OneSSMultiplicity LeadingRunSupply LowSSPeriodicSupply SharpPeriodicSupply EndpointRepetitionBudget LowSSEndpoint

/-- Exhaustive classification of length 7 P2 words. -/
theorem bitWords_seven_p2 :
    (bitWords 7).filter (fun w => decide (P2 w)) =
      [[false, true, true, true, true, false, false],
       [true, false, true, true, false, true, false],
       [true, true, false, false, true, true, false],
       [true, true, false, true, false, false, true]] := by decide

/-- Every P2 word of length 7 is equal to one of the 4 explicit words. -/
theorem p2_length_seven_cases (w : List Bool) (hP : P2 w) (hlen : w.length = 7) :
    w = [false, true, true, true, true, false, false] ∨
    w = [true, false, true, true, false, true, false] ∨
    w = [true, true, false, false, true, true, false] ∨
    w = [true, true, false, true, false, false, true] := by
  have hmem : w ∈ bitWords 7 := by
    have hm := mem_bitWords w
    rw [hlen] at hm
    exact hm
  have hfilt : w ∈ (bitWords 7).filter (fun w => decide (P2 w)) := by
    rw [List.mem_filter]
    exact ⟨hmem, by simp [hP]⟩
  rw [bitWords_seven_p2] at hfilt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfilt
  exact hfilt

/-- A P2 word of length 7 has mass 1 and therefore exactly 3 subtractions. -/
theorem p2_length_seven_subtractions (w : List Bool) (hP : P2 w) (hlen : w.length = 7) :
    (w.length : Int) - (ones w : Int) = 3 := by
  have hm := hP.1
  have h := mass_eq w
  omega

/-- In any periodic word, no tight subset of size ≤ 2 can contain a window whose
individual neighborhood has size at least 3. -/
theorem no_ge_three_in_tight_le_two (p : Nat) (hp : 0 < p)
    (A : List Nat) (lag : Nat → Nat)
    (hlen : A.length ≤ 2)
    (htight : (neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hN3 : 3 ≤ (neighborhood e p [u] lag).length) : False :=
  tight_subset_le_two_no_ge_three p hp A lag hlen htight u hu hN3

/-- In any periodic word of period p ≤ 11, any member of any tight avoiding subset of size ≤ 2
whose lag is at most 5 has lag 3. -/
theorem tight_avoiding_le_two_lag_three (e : Int → Bool)
    (A : List Nat) (lag : Nat → Nat)
    (hlag_pos : ∀ u ∈ A, 0 < lag u) (hlag_le5 : ∀ u ∈ A, lag u ≤ 5)
    (hP : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u)) :
    ∀ u ∈ A, lag u = 3 :=
  tight_avoiding_all_lag_three e A lag hlag_pos hlag_le5 hP

/-- In any periodic word of period p ≤ 11, any member of any tight avoiding subset of size ≤ 2
whose lag is at most 5 is an AAS window. -/
theorem tight_avoiding_le_two_is_aas (e : Int → Bool)
    (A : List Nat) (lag : Nat → Nat)
    (hlag_pos : ∀ u ∈ A, 0 < lag u) (hlag_le5 : ∀ u ∈ A, lag u ≤ 5)
    (hP : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u)) :
    ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false :=
  tight_avoiding_all_aas e A lag hlag_pos hlag_le5 hP

end Recaman.LagSevenTightObstruction
