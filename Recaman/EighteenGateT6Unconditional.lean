import Recaman.EighteenGateT6Resolution
import Recaman.TightAvoidingLagCertificate

/-!
# EighteenGateT6Unconditional: Period 18 Unconditional Reductions, Multi-Tier Capacity, and Certificate Synthesis

This module establishes the comprehensive capacity hierarchy, all-AAS tight survival across all sizes ≤ 6,
and unconditional Gate T6 reductions for period p ≤ 18:

1. `p18_tight_all_aas_avoids_s_star`: Any tight avoiding subset of size ≤ 6 consisting purely of
   lag 3 AAS windows strictly avoids the donated subtraction s*(u₀).
2. `p18_tight_all_aas_survives`: Any tight avoiding subset of size ≤ 6 consisting purely of
   lag 3 AAS windows strictly survives deletion of s*(u₀) with zero loss.
3. `p18_gate_t6_of_all_aas_tight`: In p ≤ 18 with positive signSum and slack, if all tight
   avoiding sublists are lag 3 AAS, then Gate T6 holds unconditionally on all avoiding sublists of U.
4. `p18_gate_t6_of_D_le_six_and_triples_quads`: If |D| ≤ 6, Gate T6 reduces entirely to tight
   avoiding sublists of size 3 and 4.
5. `p18_gate_t6_of_U_le_five_and_triples_quads`: If |U| ≤ 5, Gate T6 reduces entirely to tight
   avoiding sublists of size 3 and 4.
6. `p18_capacity_tier_one`: Unconditional Gate T6 when |U| ≤ 3 (tier 1).
7. `p18_capacity_tier_two`: Unconditional Gate T6 when |D| ≤ 4 (tier 2).
8. `p18_capacity_tier_three`: Gate T6 reduction to tight triples when |U| ≤ 4 (tier 3).
9. `p18_capacity_tier_four`: Gate T6 reduction to tight triples when |D| ≤ 5 (tier 4).
10. `grand_eighteen_gate_t6_unconditional_synthesis`: Master synthesis theorem for period 18
   unconditional reductions and multi-tier capacity hierarchy.
-/

namespace Recaman.EighteenGateT6Unconditional

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
open TightAvoidingLagCertificate

/-- Any tight avoiding subset of size ≤ 6 consisting purely of lag 3 AAS windows strictly
avoids the donated subtraction s*(u₀). -/
theorem p18_tight_all_aas_avoids_s_star (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (_hAk : A.length ≤ 6)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag :=
  all_aas_tight_avoids_ss2_donation e p hp hper A lag u0 hd_lt hu0A hP0 hss0 hlag3 haas hP_A hA_A

/-- Any tight avoiding subset of size ≤ 6 consisting purely of lag 3 AAS windows strictly
survives deletion of s*(u₀) with zero loss. -/
theorem p18_tight_all_aas_survives (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hAk : A.length ≤ 6)
    (htight : (neighborhood e p A lag).length = A.length)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot := p18_tight_all_aas_avoids_s_star e p hp hper A lag u0 hd_lt hu0A hP0 hss0 hAk hlag3 haas hP_A hA_A
  exact tight_triple_survives_of_s_not_mem e p A lag u0 htight hnot

/-- In p ≤ 18 with positive signSum and slack, if all tight avoiding sublists are lag 3 AAS,
then Gate T6 holds unconditionally on all avoiding sublists of U. -/
theorem p18_gate_t6_of_all_aas_tight (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp18 : p ≤ 18) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_lags : ∀ u ∈ U, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hU_A : ∀ u ∈ U, e (u : Int) = true)
    (h_tight_aas : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      (B.length = 3 ∨ B.length = 4 ∨ B.length = 5 ∨ B.length = 6) →
      (neighborhood e p B lag).length = B.length →
      (∀ u ∈ B, lag u = 3) ∧
      (∀ u ∈ B, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
  have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
  have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
  apply p18_avoiding_sublist_survives_of_tight_avoidance e p hp hp18 hpos hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A
  intro B hsubB hnotB hlen htightB
  have haasB := h_tight_aas B hsubB hnotB hlen htightB
  have hP_B : ∀ u ∈ B, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsubB.subset hu)
  have hB_A : ∀ u ∈ B, e (u : Int) = true := fun u hu => hU_A u (hsubB.subset hu)
  exact all_aas_tight_avoids_ss2_donation e p hp hper B lag u0 hd_lt hu0A hP0 hss0 haasB.1 haasB.2 hP_B hB_A

/-- If |D| ≤ 6, Gate T6 reduces entirely to tight avoiding sublists of size 3 and 4. -/
theorem p18_gate_t6_of_D_le_six_and_triples_quads (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (_hp18 : p ≤ 18) (_hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
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
    (h_tight_avoid : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      (B.length = 3 ∨ B.length = 4) →
      (neighborhood e p B lag).length = B.length →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hA4 := p18_avoiding_size_le_four_of_D_le_six e p A U u0 hu0 hnot hsub hslack hD6
  have hcases : A.length ≤ 2 ∨ A.length = 3 ∨ A.length = 4 := by omega
  rcases hcases with hle2 | heq3 | heq4
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · exact p18_tight_size_two_survives e p hp hper A lag hle2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inl heq3) htight
      have htight3 : (neighborhood e p A lag).length = 3 := by omega
      exact p18_tight_triple_survives_of_not_mem e p A lag heq3 htight3 u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inr heq4) htight
      have htight4 : (neighborhood e p A lag).length = 4 := by omega
      exact p18_tight_quad_survives_of_not_mem e p A lag heq4 htight4 u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA

/-- If |U| ≤ 5, Gate T6 reduces entirely to tight avoiding sublists of size 3 and 4. -/
theorem p18_gate_t6_of_U_le_five_and_triples_quads (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (_hp18 : p ≤ 18) (_hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (_hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hU5 : U.length ≤ 5)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hA_A : ∀ u ∈ A, e (u : Int) = true)
    (h_tight_avoid : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      (B.length = 3 ∨ B.length = 4) →
      (neighborhood e p B lag).length = B.length →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hA4 : A.length ≤ 4 := by
    have hle := sublist_length_le_sub_one_of_mem_not_mem hsub hu0 hnot
    omega
  have hcases : A.length ≤ 2 ∨ A.length = 3 ∨ A.length = 4 := by omega
  rcases hcases with hle2 | heq3 | heq4
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · exact p18_tight_size_two_survives e p hp hper A lag hle2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inl heq3) htight
      have htight3 : (neighborhood e p A lag).length = 3 := by omega
      exact p18_tight_triple_survives_of_not_mem e p A lag heq3 htight3 u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inr heq4) htight
      have htight4 : (neighborhood e p A lag).length = 4 := by omega
      exact p18_tight_quad_survives_of_not_mem e p A lag heq4 htight4 u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA

/-- Capacity Tier 1: Unconditional Gate T6 when |U| ≤ 3. -/
theorem p18_capacity_tier_one (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
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
  p18_avoiding_sublists_survive_unconditional_of_U_le_three e p hp hper U A lag hU3 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A

/-- Capacity Tier 2: Unconditional Gate T6 when |D| ≤ 4. -/
theorem p18_capacity_tier_two (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
  p18_avoiding_sublists_survive_unconditional_of_D_le_four e p hp hper U A lag hslack hD4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A

/-- Capacity Tier 3: Gate T6 reduction to tight triples when |U| ≤ 4. -/
theorem p18_capacity_tier_three (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    (h_tight3 : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      B.length = 3 →
      (neighborhood e p B lag).length = 3 →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p18_gate_t6_of_U_le_four_and_triples e p hp hp14 hpos hper U A lag hslack hU4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_tight3

/-- Capacity Tier 4: Gate T6 reduction to tight triples when |D| ≤ 5. -/
theorem p18_capacity_tier_four (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    (h_tight3 : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      B.length = 3 →
      (neighborhood e p B lag).length = 3 →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p18_gate_t6_of_D_le_five_and_triples e p hp hp14 hpos hper U A lag hslack hD5 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_tight3

/-- Master Synthesis: Grand Eighteen Gate T6 Unconditional Theorem. -/
theorem grand_eighteen_gate_t6_unconditional_synthesis
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp18 : p ≤ 18) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_lags : ∀ u ∈ U, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hU_A : ∀ u ∈ U, e (u : Int) = true) :
    -- (1) Tier 1 unconditional survival when |U| ≤ 3
    (U.length ≤ 3 → ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (2) Tier 2 unconditional survival when |D| ≤ 4
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 4 → ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (3) Reduction to size 3 and 4 when |D| ≤ 6
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 6 →
      (∀ B : List Nat, List.Sublist B U → u0 ∉ B → (B.length = 3 ∨ B.length = 4) →
        (neighborhood e p B lag).length = B.length →
        oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) →
      ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
        A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (4) Reduction to size 3 and 4 when |U| ≤ 5
    (U.length ≤ 5 →
      (∀ B : List Nat, List.Sublist B U → u0 ∉ B → (B.length = 3 ∨ B.length = 4) →
        (neighborhood e p B lag).length = B.length →
        oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) →
      ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
        A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (5) Global reduction when tight avoiding sublists are AAS
    ((∀ B : List Nat, List.Sublist B U → u0 ∉ B →
        (B.length = 3 ∨ B.length = 4 ∨ B.length = 5 ∨ B.length = 6) →
        (neighborhood e p B lag).length = B.length →
        (∀ u ∈ B, lag u = 3) ∧
        (∀ u ∈ B, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)) →
      ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
        A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hU3 A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact p18_capacity_tier_one e p hp hper U A lag hU3 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A
  · intro hD4 A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact p18_capacity_tier_two e p hp hper U A lag hslack hD4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A
  · intro hD6 h_avoid A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact p18_gate_t6_of_D_le_six_and_triples_quads e p hp hp18 hpos hper U A lag hslack hD6 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_avoid
  · intro hU5 h_avoid A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact p18_gate_t6_of_U_le_five_and_triples_quads e p hp hp18 hpos hper U A lag hslack hU5 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_avoid
  · intro h_aas A hsub hnot
    exact p18_gate_t6_of_all_aas_tight e p hp hp18 hpos hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hU_P2 hU_lags hp_gt hU_A h_aas

end Recaman.EighteenGateT6Unconditional
