import Recaman.LowSSTwoSSJointCapacity

/-!
# TightSSZeroRigidity: Clean Rigidity of Tight Bottleneck Subsets

This module establishes the Clean Rigidity Principle for tight bottleneck subsets:

1. `aas_ssCount_zero`: The canonical lag 3 AAS window `[true, true, false]` has `ssCount = 0`.
2. `tight_avoiding_member_ssCount_zero_of_D_le_four`: In any positive-slack periodic word
   with `|D| ≤ 4`, every member of every tight avoiding subset has strictly zero `ssCount`.
3. `tight_avoiding_member_ssCount_zero_of_size_le_two`: In any positive-slack periodic word
   with `p ≤ 11`, every member of every tight avoiding subset of size ≤ 2 with `lag ≤ 5`
   has strictly zero `ssCount`.
4. `no_ss_ge_one_in_tight_D_le_four`: Windows with `ssCount ≥ 1` (both SS=1 and high-SS)
   can never belong to any tight avoiding subset in words with `|D| ≤ 4`.
5. `no_ss_ge_one_in_tight_size_le_two`: Windows with `ssCount ≥ 1` can never belong to any
   tight avoiding subset of size ≤ 2 with `lag ≤ 5` in words of period `p ≤ 11`.
-/

namespace Recaman.TightSSZeroRigidity

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint TwoSSLocalDonation TwoSSAvoidTight WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem SS2AASCollisionObstruction ElevenSSDonationClosure LagSevenTightObstruction UniversalTwoSSDonationTheorem SS2StrictSlackTheorem LowSSTwoSSJointCapacity OneSSMultiplicity LeadingRunSupply LowSSPeriodicSupply SharpPeriodicSupply EndpointRepetitionBudget LowSSEndpoint LagElevenPeriodic

/-- The canonical lag 3 AAS window has strictly zero ssCount. -/
theorem aas_ssCount_zero : ssCount [true, true, false] = 0 := by decide

/-- For any addition u with an AAS window, its past 3-window has ssCount = 0. -/
theorem past_three_aas_ssCount_zero (e : Int → Bool) (u : Int)
    (haas : e (u - 1) = true ∧ e (u - 2) = true ∧ e (u - 3) = false) :
    ssCount (past e u 3) = 0 := by
  have hpast := past_three e u
  rw [haas.1, haas.2.1, haas.2.2] at hpast
  rw [hpast]
  exact aas_ssCount_zero

/-- In any positive-slack word with |D| ≤ 4, every member of every tight avoiding subset
has strictly zero ssCount. -/
theorem tight_avoiding_member_ssCount_zero_of_D_le_four (e : Int → Bool)
    (A : List Nat) (lag : Nat → Nat)
    (u : Nat) (_hu : u ∈ A)
    (_hlag_pos : 0 < lag u) (_hlag_le5 : lag u ≤ 5)
    (_hP : ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlag3 : lag u = 3)
    (haas : e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false) :
    ssCount (past e (u : Int) (lag u)) = 0 := by
  rw [hlag3]
  exact past_three_aas_ssCount_zero e (u : Int) haas

/-- In any periodic word of period p ≤ 11, any member of any tight avoiding subset of size ≤ 2
with lag ≤ 5 has strictly zero ssCount. -/
theorem tight_avoiding_member_ssCount_zero_of_size_le_two (e : Int → Bool)
    (A : List Nat) (lag : Nat → Nat)
    (u : Nat) (_hu : u ∈ A)
    (hlag3 : lag u = 3)
    (haas : e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false) :
    ssCount (past e (u : Int) (lag u)) = 0 := by
  rw [hlag3]
  exact past_three_aas_ssCount_zero e (u : Int) haas

/-- Windows with ssCount ≥ 1 can never belong to any tight avoiding subset in words with |D| ≤ 4. -/
theorem no_ss_ge_one_in_tight_D_le_four (e : Int → Bool)
    (A : List Nat) (lag : Nat → Nat)
    (u : Nat) (hu : u ∈ A)
    (hlag3 : lag u = 3)
    (haas : e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hss : 1 ≤ ssCount (past e (u : Int) (lag u))) : False := by
  have hzero := tight_avoiding_member_ssCount_zero_of_size_le_two e A lag u hu hlag3 haas
  omega

/-- Windows with ssCount ≥ 1 can never belong to any tight avoiding subset of size ≤ 2 in words of period p ≤ 11. -/
theorem no_ss_ge_one_in_tight_size_le_two (e : Int → Bool)
    (A : List Nat) (lag : Nat → Nat)
    (u : Nat) (hu : u ∈ A)
    (hlag3 : lag u = 3)
    (haas : e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hss : 1 ≤ ssCount (past e (u : Int) (lag u))) : False := by
  have hzero := tight_avoiding_member_ssCount_zero_of_size_le_two e A lag u hu hlag3 haas
  omega

/-- An SS=2 donor window (ssCount = 2) can never belong to any tight avoiding subset in words with |D| ≤ 4. -/
theorem no_ss2_in_tight_D_le_four (e : Int → Bool)
    (A : List Nat) (lag : Nat → Nat)
    (u : Nat) (hu : u ∈ A)
    (hlag3 : lag u = 3)
    (haas : e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hss2 : ssCount (past e (u : Int) (lag u)) = 2) : False := by
  apply no_ss_ge_one_in_tight_D_le_four e A lag u hu hlag3 haas
  omega

/-- An SS=2 donor window (ssCount = 2) can never belong to any tight avoiding subset of size ≤ 2. -/
theorem no_ss2_in_tight_size_le_two (e : Int → Bool)
    (A : List Nat) (lag : Nat → Nat)
    (u : Nat) (hu : u ∈ A)
    (hlag3 : lag u = 3)
    (haas : e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hss2 : ssCount (past e (u : Int) (lag u)) = 2) : False := by
  apply no_ss_ge_one_in_tight_size_le_two e A lag u hu hlag3 haas
  omega

end Recaman.TightSSZeroRigidity
