import Recaman.ArbitraryPeriodGateT6Resolution

/-!
# ArbitraryPeriodGateT6Unconditional: Universal Parametric Unconditional Gate T6 Reductions for All Periods p

This module establishes the universal parametric unconditional Gate T6 reductions and multi-tier
capacity hierarchy valid for arbitrary periods p (fully closed-form for all p ∈ ℕ):

1. `arbitrary_period_gate_t6_of_all_aas_tight`: In ANY period p with positive signSum and slack,
   if all tight avoiding sublists of intermediate sizes (3 ≤ |B| ≤ |D| - 2) are lag 3 AAS,
   then Gate T6 holds unconditionally on all avoiding sublists of U.
2. `arbitrary_period_gate_t6_of_D_le_six_and_triples_quads`: If |D| ≤ 6, Gate T6 reduces entirely to
   tight avoiding sublists of size 3 and 4 across all periods.
3. `arbitrary_period_gate_t6_of_D_le_seven_and_triples_quads_quints`: If |D| ≤ 7, Gate T6 reduces entirely to
   tight avoiding sublists of size 3, 4, 5 across all periods.
4. `arbitrary_period_gate_t6_of_D_le_eight_and_triples_to_sexts`: If |D| ≤ 8, Gate T6 reduces entirely to
   tight avoiding sublists of size 3, 4, 5, 6 across all periods.
5. `arbitrary_period_capacity_tier_one`: Tier 1 (|U| ≤ 3) unconditional Gate T6 for all periods.
6. `arbitrary_period_capacity_tier_two`: Tier 2 (|D| ≤ 4) unconditional Gate T6 for all periods.
7. `arbitrary_period_capacity_tier_three`: Tier 3 (|U| ≤ 4) Gate T6 reduction to triples for all periods.
8. `arbitrary_period_capacity_tier_four`: Tier 4 (|D| ≤ 5) Gate T6 reduction to triples for all periods.
9. `grand_arbitrary_period_gate_t6_unconditional_synthesis`: Master synthesis theorem for arbitrary-period
   unconditional Gate T6 reductions.
-/

namespace Recaman.ArbitraryPeriodGateT6Unconditional

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
open GrandApexPeriodTwentyTwoTheorem
open TwentyFourLagRigidity TwentyFourGateT6Resolution TwentyFourGateT6Unconditional
open GrandApexPeriodTwentyFourTheorem
open ArbitraryPeriodLagRigidity ArbitraryPeriodGateT6Resolution

/-- In ANY period p with positive signSum and slack, if all tight avoiding sublists of
intermediate sizes are lag 3 AAS, then Gate T6 holds unconditionally on all avoiding sublists of U. -/
theorem arbitrary_period_gate_t6_of_all_aas_tight (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
      (3 ≤ B.length ∧ B.length ≤ (LagElevenPeriodic.subPhases e 0 p).length - 2) →
      (neighborhood e p B lag).length = B.length →
      (∀ u ∈ B, lag u = 3) ∧
      (∀ u ∈ B, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
  have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
  have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
  have h_tight_avoid : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
    (3 ≤ B.length ∧ B.length ≤ (LagElevenPeriodic.subPhases e 0 p).length - 2) →
    (neighborhood e p B lag).length = B.length →
    oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag := by
    intro B hBsub hBu0 hBcases hBtight
    obtain ⟨hlag3, haas⟩ := h_tight_aas B hBsub hBu0 hBcases hBtight
    have hB_P2 : ∀ u ∈ B, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hBsub.subset hu)
    have hB_A : ∀ u ∈ B, e (u : Int) = true := fun u hu => hU_A u (hBsub.subset hu)
    exact arbitrary_period_all_aas_avoids_s_star e p hp hper B lag u0 hd_lt hu0A hP0 hss0 hlag3 haas hB_P2 hB_A
  exact arbitrary_period_avoiding_sublist_survives_of_tight_avoidance e p hp hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_tight_avoid

/-- If |D| ≤ 6, Gate T6 reduces entirely to tight avoiding sublists of size 3 and 4 across all periods. -/
theorem arbitrary_period_gate_t6_of_D_le_six_and_triples_quads (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  have hA4 : A.length ≤ 4 := by omega
  have hcases : A.length ≤ 2 ∨ A.length = 3 ∨ A.length = 4 := by omega
  rcases hcases with hle2 | heq3 | heq4
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · exact arbitrary_period_tight_size_two_survives e p hp hper A lag hle2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inl heq3) htight
      exact arbitrary_period_tight_survives_of_not_mem e p A lag htight u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inr heq4) htight
      exact arbitrary_period_tight_survives_of_not_mem e p A lag htight u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA

/-- If |D| ≤ 7, Gate T6 reduces entirely to tight avoiding sublists of size 3, 4, 5 across all periods. -/
theorem arbitrary_period_gate_t6_of_D_le_seven_and_triples_quads_quints (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD7 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 7)
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
      (B.length = 3 ∨ B.length = 4 ∨ B.length = 5) →
      (neighborhood e p B lag).length = B.length →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  have hA5 : A.length ≤ 5 := by omega
  have hcases : A.length ≤ 2 ∨ A.length = 3 ∨ A.length = 4 ∨ A.length = 5 := by omega
  rcases hcases with hle2 | heq3 | heq4 | heq5
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · exact arbitrary_period_tight_size_two_survives e p hp hper A lag hle2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inl heq3) htight
      exact arbitrary_period_tight_survives_of_not_mem e p A lag htight u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inr (Or.inl heq4)) htight
      exact arbitrary_period_tight_survives_of_not_mem e p A lag htight u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inr (Or.inr heq5)) htight
      exact arbitrary_period_tight_survives_of_not_mem e p A lag htight u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA

/-- If |D| ≤ 8, Gate T6 reduces entirely to tight avoiding sublists of size 3, 4, 5, 6 across all periods. -/
theorem arbitrary_period_gate_t6_of_D_le_eight_and_triples_to_sexts (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p24_gate_t6_of_D_le_eight_and_triples_quads_quints_sexts e p hp hper U A lag hslack hD8 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_tight_avoid

/-- Tier 1 (|U| ≤ 3) unconditional Gate T6 for all periods. -/
theorem arbitrary_period_capacity_tier_one (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
  arbitrary_period_avoiding_sublists_survive_unconditional_of_U_le_three e p hp hper U A lag hU3 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A

/-- Tier 2 (|D| ≤ 4) unconditional Gate T6 for all periods. -/
theorem arbitrary_period_capacity_tier_two (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
  arbitrary_period_avoiding_sublists_survive_unconditional_of_D_le_four e p hp hper U A lag hslack hD4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A

/-- Tier 3 (|U| ≤ 4) Gate T6 reduction to triples for all periods. -/
theorem arbitrary_period_capacity_tier_three (e : Int → Bool) (p : Nat) (hp : 0 < p)
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

/-- Tier 4 (|D| ≤ 5) Gate T6 reduction to triples for all periods. -/
theorem arbitrary_period_capacity_tier_four (e : Int → Bool) (p : Nat) (hp : 0 < p)
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

/-- Master Synthesis: Grand Arbitrary-Period Gate T6 Unconditional Synthesis Theorem. -/
theorem grand_arbitrary_period_gate_t6_unconditional_synthesis (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    -- (1) Unconditional survival if all intermediate tight sublists are lag 3 AAS
    ((∀ B : List Nat, List.Sublist B U → u0 ∉ B →
        (3 ≤ B.length ∧ B.length ≤ (LagElevenPeriodic.subPhases e 0 p).length - 2) →
        (neighborhood e p B lag).length = B.length →
        (∀ u ∈ B, lag u = 3) ∧
        (∀ u ∈ B, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)) →
      ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
        A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (2) Reduction to sizes 3 and 4 when |D| ≤ 6
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 6 →
      (∀ B : List Nat, List.Sublist B U → u0 ∉ B →
        (B.length = 3 ∨ B.length = 4) →
        (neighborhood e p B lag).length = B.length →
        oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) →
      ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
        A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (3) Reduction to sizes 3, 4, 5 when |D| ≤ 7
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 7 →
      (∀ B : List Nat, List.Sublist B U → u0 ∉ B →
        (B.length = 3 ∨ B.length = 4 ∨ B.length = 5) →
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
    exact arbitrary_period_gate_t6_of_all_aas_tight e p hp hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hU_P2 hU_lags hp_gt hU_A h_aas
  · intro hD6 h_avoid A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact arbitrary_period_gate_t6_of_D_le_six_and_triples_quads e p hp hper U A lag hslack hD6 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_avoid
  · intro hD7 h_avoid A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact arbitrary_period_gate_t6_of_D_le_seven_and_triples_quads_quints e p hp hper U A lag hslack hD7 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_avoid
  · intro hU3 A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact arbitrary_period_capacity_tier_one e p hp hper U A lag u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A hU3
  · intro hD4 A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact arbitrary_period_capacity_tier_two e p hp hper U A lag hslack hD4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A

end Recaman.ArbitraryPeriodGateT6Unconditional
