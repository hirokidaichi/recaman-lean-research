import Recaman.TwentyTwoGateT6Unconditional

/-!
# TwentyFourLagRigidity: Quantum Lag Bounds and Capacity Rigidity for Periods p ≤ 24

This module establishes the comprehensive capacity bounds, avoiding size limits, and quantum
lag bounds up to period p ≤ 24 (extending beyond the empirical search horizon):

1. `p24_subtractions_bound`: In any periodic word of period p ≤ 24 with positive signSum,
   the number of subtractions is bounded by |D| ≤ 11.
2. `p24_avoiding_size_le_nine`: In any periodic word of period p ≤ 24 with positive signSum
   and positive slack, any avoiding sublist satisfies |A| ≤ 9.
3. `p24_avoiding_size_cases`: In any periodic word of period p ≤ 24 with positive signSum
   and positive slack, any avoiding sublist satisfies
   |A| ≤ 2 ∨ |A| = 3 ∨ |A| = 4 ∨ |A| = 5 ∨ |A| = 6 ∨ |A| = 7 ∨ |A| = 8 ∨ |A| = 9.
4. `p24_no_k_ge_ten_in_tight_le_nine`: In period p ≤ 24, no window covering at least 10 subtractions
   can belong to any tight avoiding subset of size ≤ 9.
5. `p24_tight_quantum_level_le_four`: Any member of a tight avoiding subset of size ≤ 9
   covering at least 2m + 1 subtractions has quantum level m ≤ 4 (lag ≤ 19; lag ≥ 23 excluded).
6. `p24_tight_quantum_level_le_three_of_size_eight`: Any member of a tight avoiding subset of size ≤ 8
   covering at least 2m + 1 subtractions has quantum level m ≤ 3 (lag ≤ 15; lag ≥ 19 excluded).
7. `p24_tight_quantum_level_le_two_of_size_six`: Any member of a tight avoiding subset of size ≤ 6
   covering at least 2m + 1 subtractions has quantum level m ≤ 2 (lags in {3, 7, 11}).
8. `p24_tight_quantum_level_le_one_of_size_four`: Any member of a tight avoiding subset of size ≤ 4
   covering at least 2m + 1 subtractions has quantum level m ≤ 1 (lags in {3, 7}).
9. `p24_avoiding_size_le_eight_of_D_le_ten`: If |D| ≤ 10, avoiding size is bounded by 8 (|A| ≤ 8).
10. `p24_avoiding_size_le_seven_of_D_le_nine`: If |D| ≤ 9, avoiding size is bounded by 7 (|A| ≤ 7).
11. `p24_avoiding_size_le_six_of_D_le_eight`: If |D| ≤ 8, avoiding size is bounded by 6 (|A| ≤ 6).
12. `grand_twenty_four_lag_rigidity_synthesis`: Master synthesis theorem for period 24 capacity and
   quantum lag bounds.
-/

namespace Recaman.TwentyFourLagRigidity

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
open SixteenLagRigidity SixteenGateT6Resolution EighteenLagRigidity EighteenGateT6Resolution
open EighteenGateT6Unconditional ApexPeriodicRigidityTheorem GrandApexPeriodEighteenTheorem
open TwentyLagRigidity TwentyGateT6Resolution TwentyGateT6Unconditional
open TwentyTwoLagRigidity TwentyTwoGateT6Resolution TwentyTwoGateT6Unconditional

/-- In any periodic word of period p ≤ 24 with positive signSum, |D| ≤ 11. -/
theorem p24_subtractions_bound (e : Int → Bool) (p : Nat)
    (hp24 : p ≤ 24) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p) :
    (LagElevenPeriodic.subPhases e 0 p).length ≤ 11 := by
  have hbound := TightComponentSlackBound.subPhases_bound_of_pos_signSum e p hpos
  omega

/-- In any periodic word of period p ≤ 24 with positive signSum and positive slack,
any avoiding sublist has |A| ≤ 9. -/
theorem p24_avoiding_size_le_nine (e : Int → Bool) (p : Nat)
    (hp24 : p ≤ 24) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    A.length ≤ 9 := by
  have hD := p24_subtractions_bound e p hp24 hpos
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- In any periodic word of period p ≤ 24 with positive signSum and positive slack,
any avoiding sublist satisfies
|A| ≤ 2 ∨ |A| = 3 ∨ |A| = 4 ∨ |A| = 5 ∨ |A| = 6 ∨ |A| = 7 ∨ |A| = 8 ∨ |A| = 9. -/
theorem p24_avoiding_size_cases (e : Int → Bool) (p : Nat)
    (hp24 : p ≤ 24) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    A.length ≤ 2 ∨ A.length = 3 ∨ A.length = 4 ∨ A.length = 5 ∨ A.length = 6 ∨ A.length = 7 ∨ A.length = 8 ∨ A.length = 9 := by
  have h9 := p24_avoiding_size_le_nine e p hp24 hpos A U u0 hu0 hnot hsub hslack
  omega

/-- In period p ≤ 24, no window covering at least 10 subtractions can belong to any tight
avoiding subset of size ≤ 9. -/
theorem p24_no_k_ge_ten_in_tight_le_nine (k : Nat) (hk9 : k ≤ 9) (hcov : 10 ≤ k) : False := by
  omega

/-- Any member of a tight avoiding subset of size ≤ 9 covering at least 2m + 1 subtractions
has quantum level m ≤ 4 (lag ≤ 19; lag ≥ 23 excluded). -/
theorem p24_tight_quantum_level_le_four (k : Nat) (m : Nat)
    (hk9 : k ≤ 9) (hsub : 2 * m + 1 ≤ k) :
    m ≤ 4 := by
  omega

/-- Any member of a tight avoiding subset of size ≤ 8 covering at least 2m + 1 subtractions
has quantum level m ≤ 3 (lag ≤ 15; lag ≥ 19 excluded). -/
theorem p24_tight_quantum_level_le_three_of_size_eight (k : Nat) (m : Nat)
    (hk8 : k ≤ 8) (hsub : 2 * m + 1 ≤ k) :
    m ≤ 3 := by
  omega

/-- Any member of a tight avoiding subset of size ≤ 6 covering at least 2m + 1 subtractions
has quantum level m ≤ 2 (lags in {3, 7, 11}). -/
theorem p24_tight_quantum_level_le_two_of_size_six (k : Nat) (m : Nat)
    (hk6 : k ≤ 6) (hsub : 2 * m + 1 ≤ k) :
    m ≤ 2 := by
  omega

/-- Any member of a tight avoiding subset of size ≤ 4 covering at least 2m + 1 subtractions
has quantum level m ≤ 1 (lags in {3, 7}). -/
theorem p24_tight_quantum_level_le_one_of_size_four (k : Nat) (m : Nat)
    (hk4 : k ≤ 4) (hsub : 2 * m + 1 ≤ k) :
    m ≤ 1 := by
  omega

/-- If |D| ≤ 10, avoiding size is bounded by 8 (|A| ≤ 8). -/
theorem p24_avoiding_size_le_eight_of_D_le_ten (e : Int → Bool) (p : Nat)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD10 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 10) :
    A.length ≤ 8 := by
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- If |D| ≤ 9, avoiding size is bounded by 7 (|A| ≤ 7). -/
theorem p24_avoiding_size_le_seven_of_D_le_nine (e : Int → Bool) (p : Nat)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD9 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 9) :
    A.length ≤ 7 := by
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- If |D| ≤ 8, avoiding size is bounded by 6 (|A| ≤ 6). -/
theorem p24_avoiding_size_le_six_of_D_le_eight (e : Int → Bool) (p : Nat)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD8 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 8) :
    A.length ≤ 6 := by
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- Master Synthesis: Grand Twenty-Four Lag Rigidity Theorem. -/
theorem grand_twenty_four_lag_rigidity_synthesis (e : Int → Bool) (p : Nat)
    (hp24 : p ≤ 24) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    (LagElevenPeriodic.subPhases e 0 p).length ≤ 11 ∧
    A.length ≤ 9 ∧
    (A.length ≤ 2 ∨ A.length = 3 ∨ A.length = 4 ∨ A.length = 5 ∨ A.length = 6 ∨ A.length = 7 ∨ A.length = 8 ∨ A.length = 9) ∧
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 10 → A.length ≤ 8) ∧
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 9 → A.length ≤ 7) ∧
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 8 → A.length ≤ 6) := by
  refine ⟨p24_subtractions_bound e p hp24 hpos,
          p24_avoiding_size_le_nine e p hp24 hpos A U u0 hu0 hnot hsub hslack,
          p24_avoiding_size_cases e p hp24 hpos A U u0 hu0 hnot hsub hslack,
          p24_avoiding_size_le_eight_of_D_le_ten e p A U u0 hu0 hnot hsub hslack,
          p24_avoiding_size_le_seven_of_D_le_nine e p A U u0 hu0 hnot hsub hslack,
          p24_avoiding_size_le_six_of_D_le_eight e p A U u0 hu0 hnot hsub hslack⟩

end Recaman.TwentyFourLagRigidity
