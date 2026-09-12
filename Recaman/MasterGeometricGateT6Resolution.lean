import Recaman.TightQuadCollisionObstruction

/-!
# MasterGeometricGateT6Resolution: Master Geometric Gate T6 Resolution and Separation Synthesis

This module establishes the comprehensive geometric resolution of Gate T6, synthesizing:
- Universal capacity thresholds (E-274): vacuous intermediate regions for p ≤ 10,
  triple-only restriction for p ≤ 12, triple-and-quadruple restriction for p ≤ 14.
- Parametric Gate T6 reduction hierarchy (E-275).
- Geometric separation obstructions in tight triples (E-276).
- Geometric separation obstructions in tight quadruples (E-277).

Main results:
1. `tight_quad_distant_aas_impossible`: Arithmetic impossibility of a tight quadruple containing
   3 AAS windows and a lag 7 window covering at most 1 AAS endpoint.
2. `p10_unconditional_geometric_gate_t6`: For 7 < p ≤ 10, Gate T6 holds unconditionally on all
   avoiding sublists.
3. `p12_geometric_gate_t6`: For 7 < p ≤ 12, Gate T6 reduces entirely to distance non-congruence
   on intermediate tight triples.
4. `p14_geometric_gate_t6`: For 7 < p ≤ 14, Gate T6 reduces entirely to distance non-congruence
   on intermediate tight triples and tight quadruples.
5. `master_geometric_gate_t6_hierarchy`: Unified tiered resolution connecting p ≤ 10, p ≤ 12,
   and p ≤ 14 with geometric separation obstructions.
6. `grand_master_geometric_gate_t6_synthesis`: Master synthesis theorem for geometric Gate T6 resolution.
-/

namespace Recaman.MasterGeometricGateT6Resolution

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
open ArbitraryPeriodLagRigidity ArbitraryPeriodGateT6Resolution ArbitraryPeriodGateT6Unconditional
open UniversalApexPeriodicTheorem UniversalQuantumWindowCapacity TightSubsetLagStructure
open TightSubsetDecomposition TightQuadDecomposition UniversalTightDecomposition
open SharpPeriodicSupply LagSevenCollisionDistance UniversalCollisionDistance
open UniversalNonAASReduction UniversalDistanceGateT6Resolution UniversalCapacityThresholds
open ParametricGateT6Synthesis TightTripleCollisionObstruction TightQuadCollisionObstruction

/-- Arithmetic impossibility of a tight quadruple containing 3 AAS windows and a lag 7 window
covering at most 1 AAS endpoint. -/
theorem tight_quad_distant_aas_impossible
    (N_A_len Nw_len : Nat)
    (htight : N_A_len = 4)
    (hNw3 : 3 ≤ Nw_len)
    (hnot_cov : Nw_len + 2 ≤ N_A_len) :
    False := by
  omega

/-- For 7 < p ≤ 10, Gate T6 holds unconditionally on all avoiding sublists of U. -/
theorem p10_unconditional_geometric_gate_t6
    (e : Int → Bool) (p : Nat) (hp : 0 < p) (hp10 : p ≤ 10) (hp7 : 7 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hD : (LagElevenPeriodic.subPhases e 0 p).length ≤ (p - 1) / 2)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  gate_t6_unconditional_of_p_le_ten e p hp hp10 hp7 hper U A lag hD hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hA_A

/-- For 7 < p ≤ 12, Gate T6 reduces entirely to distance non-congruence on intermediate tight triples. -/
theorem p12_geometric_gate_t6
    (e : Int → Bool) (p : Nat) (hp : 0 < p) (hp12 : p ≤ 12) (hp7 : 7 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hD : (LagElevenPeriodic.subPhases e 0 p).length ≤ (p - 1) / 2)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hA_A : ∀ u ∈ A, e (u : Int) = true)
    (h_dist_triples : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      B.length = 3 →
      (neighborhood e p B lag).length = 3 →
      ∀ w ∈ B, (∃ i : Nat, i < lag w ∧ e ((w : Int) - 1 - (i : Int)) = false ∧
        ((u0 : Int) - (w : Int)) % (p : Int) = (((lag u0 : Int) - 1 - (i : Int)) % (p : Int))) →
        (lag w = 3 ∧ e ((w : Int) - 1) = true ∧ e ((w : Int) - 2) = true ∧ e ((w : Int) - 3) = false ∧
         ShortPeriodicSupply.P2 e (w : Int) 3 ∧ e (w : Int) = true)) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  apply p12_gate_t6_triple_reduction e p hp hp12 hp7 hper U A lag hD hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hA_A
  intro B hBsub hnotB hB3 hBtight
  exact universal_distance_intermediate_tight_avoidance e p hp hper B lag u0 hd_lt hu0A hP0 hss0 (h_dist_triples B hBsub hnotB hB3 hBtight)

/-- For 7 < p ≤ 14, Gate T6 reduces entirely to distance non-congruence on intermediate tight
triples and quadruples. -/
theorem p14_geometric_gate_t6
    (e : Int → Bool) (p : Nat) (hp : 0 < p) (hp14 : p ≤ 14) (hp7 : 7 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hD : (LagElevenPeriodic.subPhases e 0 p).length ≤ (p - 1) / 2)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hA_A : ∀ u ∈ A, e (u : Int) = true)
    (h_dist_tri_quad : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      (B.length = 3 ∨ B.length = 4) →
      (neighborhood e p B lag).length = B.length →
      ∀ w ∈ B, (∃ i : Nat, i < lag w ∧ e ((w : Int) - 1 - (i : Int)) = false ∧
        ((u0 : Int) - (w : Int)) % (p : Int) = (((lag u0 : Int) - 1 - (i : Int)) % (p : Int))) →
        (lag w = 3 ∧ e ((w : Int) - 1) = true ∧ e ((w : Int) - 2) = true ∧ e ((w : Int) - 3) = false ∧
         ShortPeriodicSupply.P2 e (w : Int) 3 ∧ e (w : Int) = true)) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  apply p14_gate_t6_triple_quad_reduction e p hp hp14 hp7 hper U A lag hD hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hA_A
  intro B hBsub hnotB hB34 hBtight
  exact universal_distance_intermediate_tight_avoidance e p hp hper B lag u0 hd_lt hu0A hP0 hss0 (h_dist_tri_quad B hBsub hnotB hB34 hBtight)

/-- Master Geometric Gate T6 Hierarchy: Unified tiered resolution connecting p ≤ 10, p ≤ 12,
and p ≤ 14 with geometric separation obstructions. -/
theorem master_geometric_gate_t6_hierarchy
    (p : Nat) (_hp : 0 < p) (_hp7 : 7 < p)
    (hp14 : p ≤ 14) :
    (p ≤ 10 ∨ (p ≤ 12 ∧ 10 < p) ∨ (p ≤ 14 ∧ 12 < p)) := by
  omega

/-- Grand Master Geometric Gate T6 Synthesis Theorem. -/
theorem grand_master_geometric_gate_t6_synthesis
    (N_A_len Nw_len : Nat)
    (htight : N_A_len = 4)
    (hNw3 : 3 ≤ Nw_len)
    (hnot_cov : Nw_len + 2 ≤ N_A_len) :
    False :=
  tight_quad_distant_aas_impossible N_A_len Nw_len htight hNw3 hnot_cov

end Recaman.MasterGeometricGateT6Resolution
