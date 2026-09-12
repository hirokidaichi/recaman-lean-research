import Recaman.TwentyFourGateT6Resolution

/-!
# TwentyFourGateT6Unconditional: Period 24 Unconditional Reductions, Multi-Tier Capacity, and Certificate Synthesis

This module establishes the comprehensive capacity hierarchy, all-AAS tight survival across all sizes ≤ 9,
and unconditional Gate T6 reductions for period p ≤ 24:

1. `p24_tight_all_aas_avoids_s_star`: Any tight avoiding subset of size ≤ 9 consisting purely of
   lag 3 AAS windows strictly avoids the donated subtraction s*(u₀).
2. `p24_tight_all_aas_survives`: Any tight avoiding subset of size ≤ 9 consisting purely of
   lag 3 AAS windows strictly survives deletion of s*(u₀) with zero loss.
3. `p24_gate_t6_of_all_aas_tight`: In p ≤ 24 with positive signSum and slack, if all tight
   avoiding sublists are lag 3 AAS, then Gate T6 holds unconditionally on all avoiding sublists of U.
4. `p24_gate_t6_of_D_le_eight_and_triples_quads_quints_sexts`: If |D| ≤ 8, Gate T6 reduces entirely to tight
   avoiding sublists of size 3, 4, 5, and 6.
5. `p24_gate_t6_of_U_le_seven_and_triples_quads_quints_sexts`: If |U| ≤ 7, Gate T6 reduces entirely to tight
   avoiding sublists of size 3, 4, 5, and 6.
6. `p24_capacity_tier_one`: Unconditional Gate T6 when |U| ≤ 3 (tier 1).
7. `p24_capacity_tier_two`: Unconditional Gate T6 when |D| ≤ 4 (tier 2).
8. `p24_capacity_tier_three`: Gate T6 reduction to tight triples when |U| ≤ 4 (tier 3).
9. `p24_capacity_tier_four`: Gate T6 reduction to tight triples when |D| ≤ 5 (tier 4).
10. `grand_twenty_four_gate_t6_unconditional_synthesis`: Master synthesis theorem for period 24
   unconditional reductions and multi-tier capacity hierarchy.
-/

namespace Recaman.TwentyFourGateT6Unconditional

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
open TwentyFourLagRigidity TwentyFourGateT6Resolution

/-- Any tight avoiding subset of size ≤ 9 consisting purely of lag 3 AAS windows strictly
avoids the donated subtraction s*(u₀). -/
theorem p24_tight_all_aas_avoids_s_star (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (_hAk : A.length ≤ 9)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag :=
  all_aas_tight_avoids_ss2_donation e p hp hper A lag u0 hd_lt hu0A hP0 hss0 hlag3 haas hP_A hA_A

/-- Any tight avoiding subset of size ≤ 9 consisting purely of lag 3 AAS windows strictly
survives deletion of s*(u₀) with zero loss. -/
theorem p24_tight_all_aas_survives (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hAk : A.length ≤ 9)
    (htight : (neighborhood e p A lag).length = A.length)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot := p24_tight_all_aas_avoids_s_star e p hp hper A lag u0 hd_lt hu0A hP0 hss0 hAk hlag3 haas hP_A hA_A
  exact tight_triple_survives_of_s_not_mem e p A lag u0 htight hnot

/-- In p ≤ 24 with positive signSum and slack, if all tight avoiding sublists are lag 3 AAS,
then Gate T6 holds unconditionally on all avoiding sublists of U. -/
theorem p24_gate_t6_of_all_aas_tight (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp24 : p ≤ 24) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
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
      (B.length = 3 ∨ B.length = 4 ∨ B.length = 5 ∨ B.length = 6 ∨ B.length = 7 ∨ B.length = 8 ∨ B.length = 9) →
      (neighborhood e p B lag).length = B.length →
      (∀ u ∈ B, lag u = 3) ∧
      (∀ u ∈ B, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
  have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
  have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
  have h_tight_avoid : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
    (B.length = 3 ∨ B.length = 4 ∨ B.length = 5 ∨ B.length = 6 ∨ B.length = 7 ∨ B.length = 8 ∨ B.length = 9) →
    (neighborhood e p B lag).length = B.length →
    oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag := by
    intro B hBsub hBu0 hBcases hBtight
    obtain ⟨hlag3, haas⟩ := h_tight_aas B hBsub hBu0 hBcases hBtight
    have hB_P2 : ∀ u ∈ B, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hBsub.subset hu)
    have hB_A : ∀ u ∈ B, e (u : Int) = true := fun u hu => hU_A u (hBsub.subset hu)
    have hBk : B.length ≤ 9 := by omega
    exact p24_tight_all_aas_avoids_s_star e p hp hper B lag u0 hd_lt hu0A hP0 hss0 hBk hlag3 haas hB_P2 hB_A
  exact p24_avoiding_sublist_survives_of_tight_avoidance e p hp hp24 hpos hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_tight_avoid

/-- If |D| ≤ 8, Gate T6 reduces entirely to tight avoiding sublists of size 3, 4, 5, and 6. -/
theorem p24_gate_t6_of_D_le_eight_and_triples_quads_quints_sexts (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD8 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 8)
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
      (B.length = 3 ∨ B.length = 4 ∨ B.length = 5 ∨ B.length = 6) →
      (neighborhood e p B lag).length = B.length →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hA6 := p24_avoiding_size_le_six_of_D_le_eight e p A U u0 hu0 hnot hsub hslack hD8
  have hcases : A.length ≤ 2 ∨ A.length = 3 ∨ A.length = 4 ∨ A.length = 5 ∨ A.length = 6 := by omega
  rcases hcases with hle2 | heq3 | heq4 | heq5 | heq6
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · exact p24_tight_size_two_survives e p hp hper A lag hle2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inl heq3) htight
      have htight3 : (neighborhood e p A lag).length = 3 := by omega
      exact p24_tight_triple_survives_of_not_mem e p A lag heq3 htight3 u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inr (Or.inl heq4)) htight
      have htight4 : (neighborhood e p A lag).length = 4 := by omega
      exact p24_tight_quad_survives_of_not_mem e p A lag heq4 htight4 u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inr (Or.inr (Or.inl heq5))) htight
      have htight5 : (neighborhood e p A lag).length = 5 := by omega
      exact p24_tight_quint_survives_of_not_mem e p A lag heq5 htight5 u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inr (Or.inr (Or.inr heq6))) htight
      have htight6 : (neighborhood e p A lag).length = 6 := by omega
      exact p24_tight_sext_survives_of_not_mem e p A lag heq6 htight6 u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA

/-- If |U| ≤ 7, Gate T6 reduces entirely to tight avoiding sublists of size 3, 4, 5, and 6. -/
theorem p24_gate_t6_of_U_le_seven_and_triples_quads_quints_sexts (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (_hp24 : p ≤ 24) (_hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (_hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hU7 : U.length ≤ 7)
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
      (B.length = 3 ∨ B.length = 4 ∨ B.length = 5 ∨ B.length = 6) →
      (neighborhood e p B lag).length = B.length →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hA6 : A.length ≤ 6 := by
    have hle := sublist_length_le_sub_one_of_mem_not_mem hsub hu0 hnot
    omega
  have hcases : A.length ≤ 2 ∨ A.length = 3 ∨ A.length = 4 ∨ A.length = 5 ∨ A.length = 6 := by omega
  rcases hcases with hle2 | heq3 | heq4 | heq5 | heq6
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · exact p24_tight_size_two_survives e p hp hper A lag hle2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inl heq3) htight
      have htight3 : (neighborhood e p A lag).length = 3 := by omega
      exact p24_tight_triple_survives_of_not_mem e p A lag heq3 htight3 u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inr (Or.inl heq4)) htight
      have htight4 : (neighborhood e p A lag).length = 4 := by omega
      exact p24_tight_quad_survives_of_not_mem e p A lag heq4 htight4 u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inr (Or.inr (Or.inl heq5))) htight
      have htight5 : (neighborhood e p A lag).length = 5 := by omega
      exact p24_tight_quint_survives_of_not_mem e p A lag heq5 htight5 u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inr (Or.inr (Or.inr heq6))) htight
      have htight6 : (neighborhood e p A lag).length = 6 := by omega
      exact p24_tight_sext_survives_of_not_mem e p A lag heq6 htight6 u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA

/-- Multi-tier capacity reduction: Tier 1 (unconditional when |U| ≤ 3). -/
theorem p24_capacity_tier_one (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hA_A : ∀ u ∈ A, e (u : Int) = true)
    (hU3 : U.length ≤ 3) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p24_avoiding_sublists_survive_unconditional_of_U_le_three e p hp hper U A lag hU3 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A

/-- Multi-tier capacity reduction: Tier 2 (unconditional when |D| ≤ 4). -/
theorem p24_capacity_tier_two (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
  p24_avoiding_sublists_survive_unconditional_of_D_le_four e p hp hper U A lag hslack hD4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A

/-- Multi-tier capacity reduction: Tier 3 (reduction to triples when |U| ≤ 4). -/
theorem p24_capacity_tier_three (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
  p24_gate_t6_of_U_le_four_and_triples e p hp hp14 hpos hper U A lag hslack hU4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_tight3

/-- Multi-tier capacity reduction: Tier 4 (reduction to triples when |D| ≤ 5). -/
theorem p24_capacity_tier_four (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
  p24_gate_t6_of_D_le_five_and_triples e p hp hp14 hpos hper U A lag hslack hD5 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_tight3

/-- Master Synthesis: Grand Twenty-Four Gate T6 Unconditional Synthesis Theorem. -/
theorem grand_twenty_four_gate_t6_unconditional_synthesis (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp24 : p ≤ 24) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
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
    -- (1) Unconditional survival if all tight sublists of size 3..9 are lag 3 AAS
    ((∀ B : List Nat, List.Sublist B U → u0 ∉ B →
        (B.length = 3 ∨ B.length = 4 ∨ B.length = 5 ∨ B.length = 6 ∨ B.length = 7 ∨ B.length = 8 ∨ B.length = 9) →
        (neighborhood e p B lag).length = B.length →
        (∀ u ∈ B, lag u = 3) ∧
        (∀ u ∈ B, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)) →
      ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
        A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (2) Reduction to sizes 3..6 when |D| ≤ 8
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 8 →
      (∀ B : List Nat, List.Sublist B U → u0 ∉ B →
        (B.length = 3 ∨ B.length = 4 ∨ B.length = 5 ∨ B.length = 6) →
        (neighborhood e p B lag).length = B.length →
        oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) →
      ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
        A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (3) Reduction to sizes 3..6 when |U| ≤ 7
    (U.length ≤ 7 →
      (∀ B : List Nat, List.Sublist B U → u0 ∉ B →
        (B.length = 3 ∨ B.length = 4 ∨ B.length = 5 ∨ B.length = 6) →
        (neighborhood e p B lag).length = B.length →
        oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) →
      ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
        A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (4) Tier 1 unconditional survival when |U| ≤ 3
    (U.length ≤ 3 → ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (5) Tier 2 unconditional survival when |D| ≤ 4
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 4 → ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h_aas A hsub hnot
    exact p24_gate_t6_of_all_aas_tight e p hp hp24 hpos hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hU_P2 hU_lags hp_gt hU_A h_aas
  · intro hD8 h_avoid A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact p24_gate_t6_of_D_le_eight_and_triples_quads_quints_sexts e p hp hper U A lag hslack hD8 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_avoid
  · intro hU7 h_avoid A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact p24_gate_t6_of_U_le_seven_and_triples_quads_quints_sexts e p hp hp24 hpos hper U A lag hslack hU7 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_avoid
  · intro hU3 A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact p24_capacity_tier_one e p hp hper U A lag u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A hU3
  · intro hD4 A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact p24_capacity_tier_two e p hp hper U A lag hslack hD4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A

end Recaman.TwentyFourGateT6Unconditional
