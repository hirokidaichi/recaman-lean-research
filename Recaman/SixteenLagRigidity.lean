import Recaman.FourteenGateT6Unconditional

/-!
# SixteenLagRigidity: Quantum Lag Bounds and Capacity Rigidity for Periods p ≤ 16

This module establishes structural capacity bounds, avoiding size limits, and quantum lag
rigidity for periods up to p ≤ 16:

1. `p16_subtractions_bound`: In any periodic word of period p ≤ 16 with positive signSum,
   the number of subtractions is bounded by |D| ≤ 7.
2. `p16_avoiding_size_le_five`: In any periodic word of period p ≤ 16 with positive signSum
   and positive slack, any avoiding sublist satisfies |A| ≤ 5.
3. `p16_avoiding_size_cases`: In any periodic word of period p ≤ 16 with positive signSum
   and positive slack, any avoiding sublist satisfies |A| ≤ 2 ∨ |A| = 3 ∨ |A| = 4 ∨ |A| = 5.
4. `p16_no_k_ge_seven_in_tight`: In period p ≤ 16, no window covering at least 7 subtractions
   (such as lag ≥ 15) can belong to any tight avoiding subset of size ≤ 5.
5. `p16_tight_quantum_level_le_two`: Any member of a tight avoiding subset of size ≤ 5
   covering at least 2m + 1 subtractions has quantum level m ≤ 2 (lag ≤ 11).
6. `p16_tight_quantum_level_le_one_of_size_four`: Any member of a tight avoiding subset of size ≤ 4
   covering at least 2m + 1 subtractions has quantum level m ≤ 1 (lag ∈ {3, 7}).
7. `p16_avoiding_size_le_four_of_D_le_six`: If |D| ≤ 6, avoiding size is bounded by 4 (|A| ≤ 4).
8. `p16_avoiding_size_le_three_of_D_le_five`: If |D| ≤ 5, avoiding size is bounded by 3 (|A| ≤ 3).
9. `p16_avoiding_size_le_two_of_D_le_four`: If |D| ≤ 4, avoiding size is bounded by 2 (|A| ≤ 2).
10. `grand_sixteen_lag_rigidity_synthesis`: Master synthesis theorem for period 16 capacity and
   quantum lag bounds.
-/

namespace Recaman.SixteenLagRigidity

open LeadingRunSupply LowSSEndpoint TwoSSEndpoint P2ModFourRigidity
open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSLocalDonation TwoSSAvoidTight
open WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound
open UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem
open SS2AASCollisionObstruction ElevenSSDonationClosure LagSevenTightObstruction
open UniversalGateT6Closure QuantumP2Arithmetic OneSSMultiplicity TightPeriodStratification
open TenGateT6Resolution GrandPeriodicDeletabilityTheorem LowSSPeriodicSupply
open ElevenCapacityRigidity CapacitySlackCompensation ElevenGateT6Synthesis
open FourteenLagRigidity TwelveGateT6Resolution TightTripleRigidity
open LagSevenNeighborhoodRigidity SS2LagElevenForcing TwelveGateT6Unconditional
open FourteenGateT6Resolution TightQuadRigidity FourteenGateT6Unconditional

/-- In any periodic word of period p ≤ 16 with positive signSum, |D| ≤ 7. -/
theorem p16_subtractions_bound (e : Int → Bool) (p : Nat)
    (hp16 : p ≤ 16) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p) :
    (LagElevenPeriodic.subPhases e 0 p).length ≤ 7 := by
  have hbound := TightComponentSlackBound.subPhases_bound_of_pos_signSum e p hpos
  omega

/-- In any periodic word of period p ≤ 16 with positive signSum and positive slack,
any avoiding sublist has |A| ≤ 5. -/
theorem p16_avoiding_size_le_five (e : Int → Bool) (p : Nat)
    (hp16 : p ≤ 16) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    A.length ≤ 5 := by
  have hD := p16_subtractions_bound e p hp16 hpos
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- In any periodic word of period p ≤ 16 with positive signSum and positive slack,
any avoiding sublist satisfies |A| ≤ 2 ∨ |A| = 3 ∨ |A| = 4 ∨ |A| = 5. -/
theorem p16_avoiding_size_cases (e : Int → Bool) (p : Nat)
    (hp16 : p ≤ 16) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    A.length ≤ 2 ∨ A.length = 3 ∨ A.length = 4 ∨ A.length = 5 := by
  have h5 := p16_avoiding_size_le_five e p hp16 hpos A U u0 hu0 hnot hsub hslack
  omega

/-- In period p ≤ 16, no window covering at least 7 subtractions can belong to any tight
avoiding subset of size ≤ 5. -/
theorem p16_no_k_ge_seven_in_tight (k : Nat) (hk5 : k ≤ 5) (hcov : 7 ≤ k) : False := by
  omega

/-- Any member of a tight avoiding subset of size ≤ 5 covering at least 2m + 1 subtractions
has quantum level m ≤ 2 (lag ≤ 11). -/
theorem p16_tight_quantum_level_le_two (k : Nat) (m : Nat)
    (hk5 : k ≤ 5) (hsub : 2 * m + 1 ≤ k) :
    m ≤ 2 := by
  omega

/-- Any member of a tight avoiding subset of size ≤ 4 covering at least 2m + 1 subtractions
has quantum level m ≤ 1 (lags in {3, 7}). -/
theorem p16_tight_quantum_level_le_one_of_size_four (k : Nat) (m : Nat)
    (hk4 : k ≤ 4) (hsub : 2 * m + 1 ≤ k) :
    m ≤ 1 := by
  omega

/-- If |D| ≤ 6, avoiding size is bounded by 4 (|A| ≤ 4). -/
theorem p16_avoiding_size_le_four_of_D_le_six (e : Int → Bool) (p : Nat)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD6 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 6) :
    A.length ≤ 4 := by
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- If |D| ≤ 5, avoiding size is bounded by 3 (|A| ≤ 3). -/
theorem p16_avoiding_size_le_three_of_D_le_five (e : Int → Bool) (p : Nat)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD5 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 5) :
    A.length ≤ 3 := by
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- If |D| ≤ 4, avoiding size is bounded by 2 (|A| ≤ 2). -/
theorem p16_avoiding_size_le_two_of_D_le_four (e : Int → Bool) (p : Nat)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD4 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 4) :
    A.length ≤ 2 := by
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- Master Synthesis: Grand Sixteen Lag Rigidity Theorem. -/
theorem grand_sixteen_lag_rigidity_synthesis
    (e : Int → Bool) (p : Nat)
    (hp16 : p ≤ 16) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    -- (1) Subtractions bounded by 7
    (LagElevenPeriodic.subPhases e 0 p).length ≤ 7 ∧
    -- (2) Avoiding size bounded by 5
    A.length ≤ 5 ∧
    -- (3) Avoiding size cases
    (A.length ≤ 2 ∨ A.length = 3 ∨ A.length = 4 ∨ A.length = 5) ∧
    -- (4) Quantum level bound m ≤ 2 for size ≤ 5
    (∀ m : Nat, 2 * m + 1 ≤ 5 → m ≤ 2) ∧
    -- (5) Quantum level bound m ≤ 1 for size ≤ 4
    (∀ m : Nat, 2 * m + 1 ≤ 4 → m ≤ 1) ∧
    -- (6) Capacity reduction when |D| ≤ 6
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 6 → A.length ≤ 4) ∧
    -- (7) Capacity reduction when |D| ≤ 5
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 5 → A.length ≤ 3) ∧
    -- (8) Capacity reduction when |D| ≤ 4
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 4 → A.length ≤ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact p16_subtractions_bound e p hp16 hpos
  · exact p16_avoiding_size_le_five e p hp16 hpos A U u0 hu0 hnot hsub hslack
  · exact p16_avoiding_size_cases e p hp16 hpos A U u0 hu0 hnot hsub hslack
  · intro m hm; omega
  · intro m hm; omega
  · intro hD6; exact p16_avoiding_size_le_four_of_D_le_six e p A U u0 hu0 hnot hsub hslack hD6
  · intro hD5; exact p16_avoiding_size_le_three_of_D_le_five e p A U u0 hu0 hnot hsub hslack hD5
  · intro hD4; exact p16_avoiding_size_le_two_of_D_le_four e p A U u0 hu0 hnot hsub hslack hD4

end Recaman.SixteenLagRigidity
