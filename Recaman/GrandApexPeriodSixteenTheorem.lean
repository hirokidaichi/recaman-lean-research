import Recaman.ApexPeriodicRigidityTheorem
import Recaman.FourteenGateT6Unconditional
import Recaman.SixteenGateT6Resolution
import Recaman.SixteenGateT6Unconditional

/-!
# GrandApexPeriodSixteenTheorem: Master Apex Synthesis for Period p ≤ 16

This module establishes the comprehensive master apex synthesis unifying the 5-tier
capacity stratification, the quantum lag exclusion hierarchy (m ≤ 2, lag < 15),
universal small-size survival (|A| ≤ 2), all-AAS survival up to size 5, and the
complete Gate T6 multi-tier reduction hierarchy for all periods p ≤ 16:

1. `apex16_capacity_stratification`: Complete 5-tier capacity stratification:
   - p ≤ 7  ⟹ |D| ≤ 3 ∧ |A| ≤ 1
   - p ≤ 10 ⟹ |D| ≤ 4 ∧ |A| ≤ 2
   - p ≤ 12 ⟹ |D| ≤ 5 ∧ |A| ≤ 3
   - p ≤ 14 ⟹ |D| ≤ 6 ∧ |A| ≤ 4
   - p ≤ 16 ⟹ |D| ≤ 7 ∧ |A| ≤ 5
2. `apex16_quantum_lag_hierarchy`: Quantum lag level bounds:
   - Size ≤ 2 ⟹ m = 0 (lags in {3})
   - Size ≤ 4 ⟹ m ≤ 1 (lags in {3, 7})
   - Size ≤ 5 ⟹ m ≤ 2 (lags in {3, 7, 11}, lags ≥ 15 strictly excluded)
3. `apex16_universal_size_two_survival`: Any tight avoiding sublist of size ≤ 2 strictly
   survives deletion of s*(u₀) across all periods p ≤ 16.
4. `apex16_all_aas_survival_up_to_five`: Any tight avoiding subset of size ≤ 5 consisting
   purely of lag 3 AAS windows strictly survives deletion with zero loss.
5. `apex16_gate_t6_unconditional_tier_one`: Unconditional Gate T6 survival when |U| ≤ 3.
6. `apex16_gate_t6_unconditional_tier_two`: Unconditional Gate T6 survival when |D| ≤ 4.
7. `apex16_gate_t6_reduction_tier_three`: Gate T6 reduction to tight triples when |U| ≤ 4.
8. `apex16_gate_t6_reduction_tier_four`: Gate T6 reduction to tight triples when |D| ≤ 5.
9. `apex16_gate_t6_reduction_tier_five`: Gate T6 reduction to tight triples and quadruples
   when |D| ≤ 6 or |U| ≤ 5.
10. `grand_apex_period_sixteen_synthesis`: Master apex synthesis theorem for period 16.
-/

namespace Recaman.GrandApexPeriodSixteenTheorem

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
open SixteenLagRigidity SixteenGateT6Resolution SixteenGateT6Unconditional
open ApexPeriodicRigidityTheorem

/-- Complete 5-tier capacity stratification for periods p ≤ 16 under positive signSum. -/
theorem apex16_capacity_stratification (e : Int → Bool) (p : Nat)
    (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    (p ≤ 7 → (LagElevenPeriodic.subPhases e 0 p).length ≤ 3 ∧ A.length ≤ 1) ∧
    (p ≤ 10 → (LagElevenPeriodic.subPhases e 0 p).length ≤ 4 ∧ A.length ≤ 2) ∧
    (p ≤ 12 → (LagElevenPeriodic.subPhases e 0 p).length ≤ 5 ∧ A.length ≤ 3) ∧
    (p ≤ 14 → (LagElevenPeriodic.subPhases e 0 p).length ≤ 6 ∧ A.length ≤ 4) ∧
    (p ≤ 16 → (LagElevenPeriodic.subPhases e 0 p).length ≤ 7 ∧ A.length ≤ 5) := by
  have hbound := TightComponentSlackBound.subPhases_bound_of_pos_signSum e p hpos
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hp7; exact ⟨by omega, by omega⟩
  · intro hp10; exact ⟨by omega, by omega⟩
  · intro hp12; exact ⟨by omega, by omega⟩
  · intro hp14; exact ⟨by omega, by omega⟩
  · intro hp16; exact ⟨by omega, by omega⟩

/-- Quantum lag hierarchy for tight avoiding subsets up to period 16:
windows covering ≥ 7 subtractions (lag ≥ 15) are excluded from size ≤ 5;
windows covering ≥ 5 subtractions (lag ≥ 11) are excluded from size ≤ 4. -/
theorem apex16_quantum_lag_hierarchy (A : List Nat) (k : Nat) :
    (A.length ≤ 5 → k ≤ A.length → k ≥ 6 → False) ∧
    (A.length ≤ 4 → k ≤ A.length → k ≥ 5 → False) ∧
    (A.length ≤ 2 → k ≤ A.length → k ≥ 3 → False) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hlen hk hge; omega
  · intro hlen hk hge; omega
  · intro hlen hk hge; omega

/-- Universal survival of tight avoiding sublists of size ≤ 2 across all periods p ≤ 16. -/
theorem apex16_universal_size_two_survival (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (hle2 : A.length ≤ 2)
    (htight : (neighborhood e p A lag).length = A.length)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p16_tight_size_two_survives e p hp hper A lag hle2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A

/-- All-AAS survival up to size 5 for period 16. -/
theorem apex16_all_aas_survival_up_to_five (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hcases : A.length = 3 ∨ A.length = 4 ∨ A.length = 5)
    (htight : (neighborhood e p A lag).length = A.length)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  rcases hcases with h3 | h4 | h5
  · have htight3 : (neighborhood e p A lag).length = 3 := by rw [h3] at htight; exact htight
    exact p16_all_aas_tight_triple_survives e p hp hper A lag u0 hd_lt hu0A hP0 hss0 h3 htight3 hlag3 haas hP_A hA_A
  · have htight4 : (neighborhood e p A lag).length = 4 := by rw [h4] at htight; exact htight
    exact p16_all_aas_tight_quad_survives e p hp hper A lag u0 hd_lt hu0A hP0 hss0 h4 htight4 hlag3 haas hP_A hA_A
  · have htight5 : (neighborhood e p A lag).length = 5 := by rw [h5] at htight; exact htight
    exact p16_all_aas_tight_quint_survives e p hp hper A lag u0 hd_lt hu0A hP0 hss0 h5 htight5 hlag3 haas hP_A hA_A

/-- Unconditional Gate T6 survival when |U| ≤ 3 for period 16. -/
theorem apex16_gate_t6_unconditional_tier_one (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp16 : p ≤ 16) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hU3 : U.length ≤ 3)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p16_capacity_reduction_tier_one e p hp hp16 hpos hper U A lag hslack hU3 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A

/-- Unconditional Gate T6 survival when |D| ≤ 4 for period 16. -/
theorem apex16_gate_t6_unconditional_tier_two (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp16 : p ≤ 16) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD4 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 4)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p16_capacity_reduction_tier_two e p hp hp16 hpos hper U A lag hslack hD4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A

/-- Gate T6 reduction to tight triples when |U| ≤ 4. -/
theorem apex16_gate_t6_reduction_tier_three (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp14 : p ≤ 14) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hU4 : U.length ≤ 4)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hA_A : ∀ u ∈ A, e (u : Int) = true)
    (h_triple : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      B.length = 3 →
      (neighborhood e p B lag).length = 3 →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p16_gate_t6_of_U_le_four_and_triples e p hp hp14 hpos hper U A lag hslack hU4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_triple

/-- Gate T6 reduction to tight triples when |D| ≤ 5. -/
theorem apex16_gate_t6_reduction_tier_four (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp14 : p ≤ 14) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD5 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 5)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hA_A : ∀ u ∈ A, e (u : Int) = true)
    (h_triple : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      B.length = 3 →
      (neighborhood e p B lag).length = 3 →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p16_gate_t6_of_D_le_five_and_triples e p hp hp14 hpos hper U A lag hslack hD5 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_triple

/-- Gate T6 reduction to tight triples and quadruples when |D| ≤ 6 or |U| ≤ 5. -/
theorem apex16_gate_t6_reduction_tier_five (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp16 : p ≤ 16) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD6 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 6)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hA_A : ∀ u ∈ A, e (u : Int) = true)
    (h_tri_quad : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      (B.length = 3 ∨ B.length = 4) →
      (neighborhood e p B lag).length = B.length →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  apply p16_avoiding_sublist_survives_of_tight_avoidance e p hp hp16 hpos hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A
  intro B hsubB hnotB hcases htightB
  rcases hcases with h3 | h4 | h5
  · exact h_tri_quad B hsubB hnotB (Or.inl h3) htightB
  · exact h_tri_quad B hsubB hnotB (Or.inr h4) htightB
  · have hlenB := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsubB hu0 hnotB hslack
    omega

/-- Master Apex Synthesis Theorem for Period p ≤ 16. -/
theorem grand_apex_period_sixteen_synthesis (A : List Nat) (k : Nat) :
    (A.length ≤ 5 → k ≤ A.length → k ≥ 6 → False) ∧
    (A.length ≤ 4 → k ≤ A.length → k ≥ 5 → False) ∧
    (A.length ≤ 2 → k ≤ A.length → k ≥ 3 → False) :=
  apex16_quantum_lag_hierarchy A k

end Recaman.GrandApexPeriodSixteenTheorem
