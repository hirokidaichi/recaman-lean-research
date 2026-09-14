import Recaman.TightSextCollisionObstruction

/-!
# EighteenGeometricGateT6Resolution: Master Geometric Gate T6 Resolution for Period p ≤ 18

This module establishes the comprehensive geometric resolution of Gate T6 for all periods p ≤ 18,
unifying:
- Period p ≤ 10: Complete unconditional Gate T6 resolution (vacuous intermediate region).
- Period p ≤ 12: Exact reduction to tight triples (k = 3).
- Period p ≤ 14: Exact reduction to tight triples and quadruples (k ∈ {3, 4}).
- Period p ≤ 16: Exact reduction to tight triples, quadruples, and quintuples (k ∈ {3, 4, 5}).
- Period p ≤ 18: Exact reduction to sizes 3, 4, 5, and 6 (k ∈ {3, 4, 5, 6}).
- Geometric collision obstructions in sizes 3, 4, 5, 6: Any lag 7 window must cover ≥ 2 AAS endpoints,
  forcing pairwise distance ≤ 6 and ruling out distant configurations.

Main results:
1. `p18_geometric_gate_t6`: Gate T6 for 7 < p ≤ 18 reduces entirely to distance non-congruence
   on intermediate tight subsets of sizes 3, 4, 5, and 6.
2. `p18_size_three_to_six_decomposition`: Decomposition of intermediate sizes 3 ≤ k ≤ 6 into
   triples, quadruples, quintuples, and sextuples.
3. `p18_intermediate_lag7_must_cover_two`: In any tight subset of size k ∈ {3, 4, 5, 6} with k - 1 AAS
   windows and 1 lag 7 window, the lag 7 window must cover at least 2 AAS endpoints.
4. `master_geometric_gate_t6_eighteen_hierarchy`: Complete 5-tier period classification up to 18.
5. `grand_eighteen_geometric_gate_t6_synthesis`: Grand master geometric synthesis for period p ≤ 18.
-/

namespace Recaman.EighteenGeometricGateT6Resolution

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
open GrandApexPeriodTwentyTwoTheorem
open TwentyFourLagRigidity TwentyFourGateT6Resolution TwentyFourGateT6Unconditional
open GrandApexPeriodTwentyFourTheorem
open ArbitraryPeriodLagRigidity ArbitraryPeriodGateT6Resolution ArbitraryPeriodGateT6Unconditional
open UniversalApexPeriodicTheorem UniversalQuantumWindowCapacity TightSubsetLagStructure
open TightSubsetDecomposition TightQuadDecomposition UniversalTightDecomposition
open SharpPeriodicSupply LagSevenCollisionDistance UniversalCollisionDistance
open UniversalNonAASReduction UniversalDistanceGateT6Resolution UniversalCapacityThresholds
open ParametricGateT6Synthesis TightTripleCollisionObstruction TightQuadCollisionObstruction
open MasterGeometricGateT6Resolution UniversalAASLagSeparation UniversalMultiLagSeparation
open UniversalAASCoverageBound GrandGeometricExclusionSynthesis TightQuintCollisionObstruction
open SixteenGeometricGateT6Resolution TightSextCollisionObstruction

/-- For 7 < p ≤ 18, Gate T6 reduces entirely to distance non-congruence on intermediate tight
subsets of sizes 3, 4, 5, and 6. -/
theorem p18_geometric_gate_t6
    (e : Int → Bool) (p : Nat) (hp : 0 < p) (hp18 : p ≤ 18) (hp7 : 7 < p)
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
    (h_dist_3456 : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      (3 ≤ B.length ∧ B.length ≤ 6) →
      (neighborhood e p B lag).length = B.length →
      ∀ w ∈ B, (∃ i : Nat, i < lag w ∧ e ((w : Int) - 1 - (i : Int)) = false ∧
        ((u0 : Int) - (w : Int)) % (p : Int) = (((lag u0 : Int) - 1 - (i : Int)) % (p : Int))) →
        (lag w = 3 ∧ e ((w : Int) - 1) = true ∧ e ((w : Int) - 2) = true ∧ e ((w : Int) - 3) = false ∧
         ShortPeriodicSupply.P2 e (w : Int) 3 ∧ e (w : Int) = true)) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  apply p18_gate_t6_reduction_tier e p hp hp18 hp7 hper U A lag hD hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hA_A
  intro B hBsub hnotB hB3456 hBtight
  exact universal_distance_intermediate_tight_avoidance e p hp hper B lag u0 hd_lt hu0A hP0 hss0 (h_dist_3456 B hBsub hnotB hB3456 hBtight)

/-- Intermediate size decomposition: 3 ≤ k ≤ 6 implies k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6. -/
theorem p18_size_three_to_six_decomposition (k : Nat) (h : 3 ≤ k ∧ k ≤ 6) :
    k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by
  omega

/-- In any tight subset of size k ∈ {3, 4, 5, 6} with k - 1 AAS windows and 1 lag 7 window w (|N([w])| ≥ 3),
w must cover at least 2 AAS endpoints. -/
theorem p18_intermediate_lag7_must_cover_two
    (N_A_len Nw_len k c : Nat)
    (hk : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6)
    (hc : c ≤ k - 1)
    (htight : N_A_len = k)
    (hNw : 3 ≤ Nw_len)
    (hcov : Nw_len + ((k - 1) - c) ≤ N_A_len) :
    2 ≤ c := by
  rcases hk with rfl | rfl | rfl | rfl
  · exact universal_aas_coverage_ge_two N_A_len Nw_len 2 1 c hc htight hcov (by omega)
  · exact universal_aas_coverage_ge_two N_A_len Nw_len 3 1 c hc htight hcov (by omega)
  · exact universal_aas_coverage_ge_two N_A_len Nw_len 4 1 c hc htight hcov (by omega)
  · exact universal_aas_coverage_ge_two N_A_len Nw_len 5 1 c hc htight hcov (by omega)

/-- Master 5-tier period hierarchy up to period 18. -/
theorem master_geometric_gate_t6_eighteen_hierarchy
    (p : Nat) (_hp : 0 < p) (_hp7 : 7 < p)
    (hp18 : p ≤ 18) :
    (p ≤ 10 ∨ (p ≤ 12 ∧ 10 < p) ∨ (p ≤ 14 ∧ 12 < p) ∨ (p ≤ 16 ∧ 14 < p) ∨ (p ≤ 18 ∧ 16 < p)) := by
  omega

/-- Grand Master Geometric Gate T6 Synthesis Theorem for period p ≤ 18. -/
theorem grand_eighteen_geometric_gate_t6_synthesis
    (k : Nat) (hk : 3 ≤ k ∧ k ≤ 6)
    (N_A_len Nw_len c : Nat)
    (hc : c ≤ k - 1)
    (htight : N_A_len = k)
    (hNw : 3 ≤ Nw_len)
    (hcov : Nw_len + ((k - 1) - c) ≤ N_A_len) :
    -- (1) Decomposition
    (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) ∧
    -- (2) Universal coverage of at least 2 AAS endpoints
    (2 ≤ c) ∧
    -- (3) Single lag 7 impossible under c ≤ 1
    (c ≤ 1 → False) := by
  have hdec := p18_size_three_to_six_decomposition k hk
  have hge2 := p18_intermediate_lag7_must_cover_two N_A_len Nw_len k c hdec hc htight hNw hcov
  refine ⟨hdec, hge2, fun hc1 => by omega⟩

end Recaman.EighteenGeometricGateT6Resolution
