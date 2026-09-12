import Recaman.TightQuadRigidity

/-!
# FourteenGateT6Unconditional: Period 14 Gate T6 Unconditional Reductions and Capacity Hierarchy

This module establishes the comprehensive capacity hierarchy, non-wrapping donor properties,
and unconditional Gate T6 reductions for period p ≤ 14:

1. `ss2_donor_nonwrapping_p12_to_p14`: In any period 11 < p ≤ 14, any minimal SS=2 donor with
   lag < 15 has lag = 11 and is strictly non-wrapping (lag < p).
2. `p14_all_aas_tight_triple_avoids`: Any tight triple of size 3 consisting purely of lag 3 AAS
   windows strictly avoids the donated subtraction s*(u₀).
3. `p14_all_aas_tight_triple_survives`: Any tight triple of size 3 consisting purely of lag 3 AAS
   windows strictly survives deletion of s*(u₀) with zero loss.
4. `p14_gate_t6_of_triples_and_quads_aas`: In p ≤ 14 with positive signSum and slack, if all tight
   avoiding triples and quadruples are lag 3 AAS, then Gate T6 holds unconditionally on all
   avoiding sublists of U.
5. `p14_gate_t6_of_triples_aas_when_U_le_four`: In p ≤ 14 with positive signSum and slack, if
   |U| ≤ 4, and all tight avoiding triples are lag 3 AAS, then Gate T6 holds unconditionally.
6. `p14_gate_t6_of_triples_aas_when_D_le_five`: In p ≤ 14 with positive signSum and slack, if
   |D| ≤ 5, and all tight avoiding triples are lag 3 AAS, then Gate T6 holds unconditionally.
7. `p14_capacity_reduction_tier_one`: Unconditional Gate T6 when |U| ≤ 3 (capacity tier 1).
8. `p14_capacity_reduction_tier_two`: Unconditional Gate T6 when |D| ≤ 4 (capacity tier 2).
9. `p14_avoiding_size_hierarchy`: Complete 4-tier avoiding size hierarchy: |D| ≤ 3 ⟹ |A| ≤ 1,
   |D| ≤ 4 ⟹ |A| ≤ 2, |D| ≤ 5 ⟹ |A| ≤ 3, |D| ≤ 6 ⟹ |A| ≤ 4.
10. `grand_fourteen_gate_t6_unconditional_synthesis`: Master synthesis theorem for period 14
   unconditional reductions and capacity stratification.
-/

namespace Recaman.FourteenGateT6Unconditional

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
open FourteenGateT6Resolution TightQuadRigidity

/-- In any period 11 < p ≤ 14, any minimal SS=2 donor with lag < 15 has lag = 11 and is
strictly non-wrapping (lag < p). -/
theorem ss2_donor_nonwrapping_p12_to_p14 (p : Nat) (hp_gt : 11 < p) (_hp14 : p ≤ 14)
    (w : List Bool) (hP : P2 w)
    (hmin : ∀ d < w.length, 0 < d → ¬ P2 (w.take d))
    (hss2 : ssCount w = 2)
    (hlt : w.length < 15) :
    w.length = 11 ∧ w.length < p := by
  have h11 := minimal_ss2_lag_lt_fifteen_eq_eleven w hP hmin hss2 hlt
  refine ⟨h11, by omega⟩

/-- Any tight triple of size 3 consisting purely of lag 3 AAS windows strictly avoids the
donated subtraction s*(u₀). -/
theorem p14_all_aas_tight_triple_avoids (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (_hA3 : A.length = 3)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag :=
  all_aas_tight_avoids_ss2_donation e p hp hper A lag u0 hd_lt hu0A hP0 hss0 hlag3 haas hP_A hA_A

/-- Any tight triple of size 3 consisting purely of lag 3 AAS windows strictly survives
deletion of s*(u₀) with zero loss. -/
theorem p14_all_aas_tight_triple_survives (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hA3 : A.length = 3)
    (htight : (neighborhood e p A lag).length = 3)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot := p14_all_aas_tight_triple_avoids e p hp hper A lag u0 hd_lt hu0A hP0 hss0 hA3 hlag3 haas hP_A hA_A
  have htight' : (neighborhood e p A lag).length = A.length := by omega
  exact tight_triple_survives_of_s_not_mem e p A lag u0 htight' hnot

/-- In p ≤ 14 with positive signSum and slack, if all tight avoiding triples and quadruples
are lag 3 AAS, then Gate T6 holds unconditionally on all avoiding sublists of U. -/
theorem p14_gate_t6_of_triples_and_quads_aas (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp14 : p ≤ 14) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
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
      (B.length = 3 ∨ B.length = 4) →
      (neighborhood e p B lag).length = B.length →
      (∀ u ∈ B, lag u = 3) ∧
      (∀ u ∈ B, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
  have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
  have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
  apply p14_gate_t6_complete_quad_reduction e p hp hp14 hpos hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A
  intro B hsubB hnotB hlen htightB
  have haasB := h_tight_aas B hsubB hnotB hlen htightB
  have hP_B : ∀ u ∈ B, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsubB.subset hu)
  have hB_A : ∀ u ∈ B, e (u : Int) = true := fun u hu => hU_A u (hsubB.subset hu)
  exact all_aas_tight_avoids_ss2_donation e p hp hper B lag u0 hd_lt hu0A hP0 hss0 haasB.1 haasB.2 hP_B hB_A

/-- In p ≤ 14 with positive signSum and slack, if |U| ≤ 4, and all tight avoiding triples
are lag 3 AAS, then Gate T6 holds unconditionally. -/
theorem p14_gate_t6_of_triples_aas_when_U_le_four (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_lags : ∀ u ∈ U, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hU_A : ∀ u ∈ U, e (u : Int) = true)
    (h_tight_aas3 : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      B.length = 3 →
      (neighborhood e p B lag).length = 3 →
      (∀ u ∈ B, lag u = 3) ∧
      (∀ u ∈ B, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
  have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
  have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
  apply p14_gate_t6_of_U_le_four_and_triples e p hp hp14 hpos hper U A lag hslack hU4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A
  intro B hsubB hnotB hlen3 htight3
  have haasB := h_tight_aas3 B hsubB hnotB hlen3 htight3
  have hP_B : ∀ u ∈ B, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsubB.subset hu)
  have hB_A : ∀ u ∈ B, e (u : Int) = true := fun u hu => hU_A u (hsubB.subset hu)
  exact all_aas_tight_avoids_ss2_donation e p hp hper B lag u0 hd_lt hu0A hP0 hss0 haasB.1 haasB.2 hP_B hB_A

/-- In p ≤ 14 with positive signSum and slack, if |D| ≤ 5, and all tight avoiding triples
are lag 3 AAS, then Gate T6 holds unconditionally. -/
theorem p14_gate_t6_of_triples_aas_when_D_le_five (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_lags : ∀ u ∈ U, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hU_A : ∀ u ∈ U, e (u : Int) = true)
    (h_tight_aas3 : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      B.length = 3 →
      (neighborhood e p B lag).length = 3 →
      (∀ u ∈ B, lag u = 3) ∧
      (∀ u ∈ B, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
  have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
  have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
  apply p14_gate_t6_of_D_le_five_and_triples e p hp hp14 hpos hper U A lag hslack hD5 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A
  intro B hsubB hnotB hlen3 htight3
  have haasB := h_tight_aas3 B hsubB hnotB hlen3 htight3
  have hP_B : ∀ u ∈ B, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsubB.subset hu)
  have hB_A : ∀ u ∈ B, e (u : Int) = true := fun u hu => hU_A u (hsubB.subset hu)
  exact all_aas_tight_avoids_ss2_donation e p hp hper B lag u0 hd_lt hu0A hP0 hss0 haasB.1 haasB.2 hP_B hB_A

/-- Unconditional Gate T6 resolution when |U| ≤ 3 (capacity tier 1). -/
theorem p14_capacity_reduction_tier_one (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
  p14_avoiding_sublists_survive_unconditional_of_U_le_three e p hp hper U A lag hU3 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A

/-- Unconditional Gate T6 resolution when |D| ≤ 4 (capacity tier 2). -/
theorem p14_capacity_reduction_tier_two (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
  p14_avoiding_sublists_survive_unconditional_of_D_le_four e p hp hper U A lag hslack hD4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A

/-- Complete 4-tier avoiding size hierarchy: |D| ≤ 3 ⟹ |A| ≤ 1, |D| ≤ 4 ⟹ |A| ≤ 2,
|D| ≤ 5 ⟹ |A| ≤ 3, |D| ≤ 6 ⟹ |A| ≤ 4. -/
theorem p14_avoiding_size_hierarchy (e : Int → Bool) (p : Nat)
    (A U : List Nat) (u0 : Nat)
    (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 3 → A.length ≤ 1) ∧
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 4 → A.length ≤ 2) ∧
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 5 → A.length ≤ 3) ∧
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 6 → A.length ≤ 4) := by
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  refine ⟨fun h3 => by omega, fun h4 => by omega, fun h5 => by omega, fun h6 => by omega⟩

/-- Master Synthesis: Grand Fourteen Gate T6 Unconditional Theorem. -/
theorem grand_fourteen_gate_t6_unconditional_synthesis
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp14 : p ≤ 14) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
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
    -- (3) Tier 3 Gate T6 reduction to AAS tight triples when |D| ≤ 5
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 5 →
      (∀ B : List Nat, List.Sublist B U → u0 ∉ B → B.length = 3 →
        (neighborhood e p B lag).length = 3 →
        (∀ u ∈ B, lag u = 3) ∧
        (∀ u ∈ B, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)) →
      ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
        A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (4) Tier 4 Gate T6 reduction to AAS tight triples when |U| ≤ 4
    (U.length ≤ 4 →
      (∀ B : List Nat, List.Sublist B U → u0 ∉ B → B.length = 3 →
        (neighborhood e p B lag).length = 3 →
        (∀ u ∈ B, lag u = 3) ∧
        (∀ u ∈ B, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)) →
      ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
        A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (5) Global Gate T6 reduction when tight avoiding subsets of size 3 and 4 are AAS
    ((∀ B : List Nat, List.Sublist B U → u0 ∉ B →
        (B.length = 3 ∨ B.length = 4) →
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
    exact p14_capacity_reduction_tier_one e p hp hper U A lag hU3 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A
  · intro hD4 A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact p14_capacity_reduction_tier_two e p hp hper U A lag hslack hD4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A
  · intro hD5 h_aas3 A hsub hnot
    exact p14_gate_t6_of_triples_aas_when_D_le_five e p hp hp14 hpos hper U A lag hslack hD5 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hU_P2 hU_lags hp_gt hU_A h_aas3
  · intro hU4 h_aas3 A hsub hnot
    exact p14_gate_t6_of_triples_aas_when_U_le_four e p hp hp14 hpos hper U A lag hslack hU4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hU_P2 hU_lags hp_gt hU_A h_aas3
  · intro h_aas A hsub hnot
    exact p14_gate_t6_of_triples_and_quads_aas e p hp hp14 hpos hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hU_P2 hU_lags hp_gt hU_A h_aas

end Recaman.FourteenGateT6Unconditional
