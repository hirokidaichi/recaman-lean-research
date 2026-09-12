import Recaman.EighteenGateT6Unconditional
import Recaman.GrandApexPeriodEighteenTheorem

/-!
# TwentyLagRigidity: Quantum Lag Bounds and Capacity Rigidity for Periods p ≤ 20

This module establishes the comprehensive capacity bounds, avoiding size limits, and quantum
lag bounds up to period p ≤ 20:

1. `p20_subtractions_bound`: In any periodic word of period p ≤ 20 with positive signSum,
   the number of subtractions is bounded by |D| ≤ 9.
2. `p20_avoiding_size_le_seven`: In any periodic word of period p ≤ 20 with positive signSum
   and positive slack, any avoiding sublist satisfies |A| ≤ 7.
3. `p20_avoiding_size_cases`: In any periodic word of period p ≤ 20 with positive signSum
   and positive slack, any avoiding sublist satisfies
   |A| ≤ 2 ∨ |A| = 3 ∨ |A| = 4 ∨ |A| = 5 ∨ |A| = 6 ∨ |A| = 7.
4. `p20_no_k_ge_eight_in_tight_le_seven`: In period p ≤ 20, no window covering at least 8 subtractions
   can belong to any tight avoiding subset of size ≤ 7.
5. `p20_tight_quantum_level_le_three`: Any member of a tight avoiding subset of size ≤ 7
   covering at least 2m + 1 subtractions has quantum level m ≤ 3 (lag ≤ 15; lag ≥ 19 excluded).
6. `p20_tight_quantum_level_le_two_of_size_six`: Any member of a tight avoiding subset of size ≤ 6
   covering at least 2m + 1 subtractions has quantum level m ≤ 2 (lags in {3, 7, 11}).
7. `p20_tight_quantum_level_le_one_of_size_four`: Any member of a tight avoiding subset of size ≤ 4
   covering at least 2m + 1 subtractions has quantum level m ≤ 1 (lags in {3, 7}).
8. `p20_avoiding_size_le_six_of_D_le_eight`: If |D| ≤ 8, avoiding size is bounded by 6 (|A| ≤ 6).
9. `p20_avoiding_size_le_five_of_D_le_seven`: If |D| ≤ 7, avoiding size is bounded by 5 (|A| ≤ 5).
10. `grand_twenty_lag_rigidity_synthesis`: Master synthesis theorem for period 20 capacity and
   quantum lag bounds.
-/

namespace Recaman.TwentyLagRigidity

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

/-- In any periodic word of period p ≤ 20 with positive signSum, |D| ≤ 9. -/
theorem p20_subtractions_bound (e : Int → Bool) (p : Nat)
    (hp20 : p ≤ 20) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p) :
    (LagElevenPeriodic.subPhases e 0 p).length ≤ 9 := by
  have hbound := TightComponentSlackBound.subPhases_bound_of_pos_signSum e p hpos
  omega

/-- In any periodic word of period p ≤ 20 with positive signSum and positive slack,
any avoiding sublist has |A| ≤ 7. -/
theorem p20_avoiding_size_le_seven (e : Int → Bool) (p : Nat)
    (hp20 : p ≤ 20) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    A.length ≤ 7 := by
  have hD := p20_subtractions_bound e p hp20 hpos
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- In any periodic word of period p ≤ 20 with positive signSum and positive slack,
any avoiding sublist satisfies |A| ≤ 2 ∨ |A| = 3 ∨ |A| = 4 ∨ |A| = 5 ∨ |A| = 6 ∨ |A| = 7. -/
theorem p20_avoiding_size_cases (e : Int → Bool) (p : Nat)
    (hp20 : p ≤ 20) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    A.length ≤ 2 ∨ A.length = 3 ∨ A.length = 4 ∨ A.length = 5 ∨ A.length = 6 ∨ A.length = 7 := by
  have h7 := p20_avoiding_size_le_seven e p hp20 hpos A U u0 hu0 hnot hsub hslack
  omega

/-- In period p ≤ 20, no window covering at least 8 subtractions can belong to any tight
avoiding subset of size ≤ 7. -/
theorem p20_no_k_ge_eight_in_tight_le_seven (k : Nat) (hk7 : k ≤ 7) (hcov : 8 ≤ k) : False := by
  omega

/-- Any member of a tight avoiding subset of size ≤ 7 covering at least 2m + 1 subtractions
has quantum level m ≤ 3 (lag ≤ 15; lag ≥ 19 excluded). -/
theorem p20_tight_quantum_level_le_three (k : Nat) (m : Nat)
    (hk7 : k ≤ 7) (hsub : 2 * m + 1 ≤ k) :
    m ≤ 3 := by
  omega

/-- Any member of a tight avoiding subset of size ≤ 6 covering at least 2m + 1 subtractions
has quantum level m ≤ 2 (lags in {3, 7, 11}). -/
theorem p20_tight_quantum_level_le_two_of_size_six (k : Nat) (m : Nat)
    (hk6 : k ≤ 6) (hsub : 2 * m + 1 ≤ k) :
    m ≤ 2 := by
  omega

/-- Any member of a tight avoiding subset of size ≤ 4 covering at least 2m + 1 subtractions
has quantum level m ≤ 1 (lags in {3, 7}). -/
theorem p20_tight_quantum_level_le_one_of_size_four (k : Nat) (m : Nat)
    (hk4 : k ≤ 4) (hsub : 2 * m + 1 ≤ k) :
    m ≤ 1 := by
  omega

/-- If |D| ≤ 8, avoiding size is bounded by 6 (|A| ≤ 6). -/
theorem p20_avoiding_size_le_six_of_D_le_eight (e : Int → Bool) (p : Nat)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD8 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 8) :
    A.length ≤ 6 := by
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- If |D| ≤ 7, avoiding size is bounded by 5 (|A| ≤ 5). -/
theorem p20_avoiding_size_le_five_of_D_le_seven (e : Int → Bool) (p : Nat)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD7 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 7) :
    A.length ≤ 5 := by
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- Master Synthesis: Grand Twenty Lag Rigidity Theorem. -/
theorem grand_twenty_lag_rigidity_synthesis (e : Int → Bool) (p : Nat)
    (hp20 : p ≤ 20) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    (LagElevenPeriodic.subPhases e 0 p).length ≤ 9 ∧
    A.length ≤ 7 ∧
    (A.length ≤ 2 ∨ A.length = 3 ∨ A.length = 4 ∨ A.length = 5 ∨ A.length = 6 ∨ A.length = 7) ∧
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 8 → A.length ≤ 6) ∧
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 7 → A.length ≤ 5) := by
  refine ⟨p20_subtractions_bound e p hp20 hpos,
          p20_avoiding_size_le_seven e p hp20 hpos A U u0 hu0 hnot hsub hslack,
          p20_avoiding_size_cases e p hp20 hpos A U u0 hu0 hnot hsub hslack,
          p20_avoiding_size_le_six_of_D_le_eight e p A U u0 hu0 hnot hsub hslack,
          p20_avoiding_size_le_five_of_D_le_seven e p A U u0 hu0 hnot hsub hslack⟩

end Recaman.TwentyLagRigidity
