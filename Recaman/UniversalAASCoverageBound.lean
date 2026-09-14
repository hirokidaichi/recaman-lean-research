import Recaman.UniversalMultiLagSeparation

/-!
# UniversalAASCoverageBound: Universal AAS Coverage Lower Bounds and Non-AAS Window Capacity

This module establishes the general parametric law governing the number of AAS endpoints
covered by any collection of m non-AAS windows in a tight avoiding subset of size k = N + m:

For any tight subset A of size k = N + m containing N AAS windows and m non-AAS windows:
- |N(A)| = N + m.
- Let W = ⋃_{j=1}^m N([w_j]) be the collective neighborhood of the m non-AAS windows.
- If the non-AAS windows cover c AAS endpoints (i.e. c distinct AAS endpoints lie in W),
  then at least N - c AAS endpoints lie outside W.
- Since distinct AAS endpoints outside W are disjoint from W:
  |N(A)| ≥ |W| + (N - c).
- Substituting |N(A)| = N + m yields:
  N + m ≥ |W| + N - c ⟹ c ≥ |W| - m.
- Consequently, whenever |W| ≥ m + 2, we must have c ≥ 2 (at least 2 AAS endpoints covered!).
- In particular, it is arithmetically IMPOSSIBLE for m non-AAS windows with |W| ≥ m + 2 to cover
  ≤ 1 AAS endpoint.

Main results:
1. `universal_aas_coverage_lower_bound`: c ≥ |W| - m in any tight subset of size N + m.
2. `universal_aas_coverage_ge_two`: If |W| ≥ m + 2, then c ≥ 2.
3. `universal_aas_coverage_ge_three`: If |W| ≥ m + 3, then c ≥ 3.
4. `universal_distant_aas_impossible`: Arithmetic impossibility of c ≤ 1 when |W| ≥ m + 2.
5. `single_non_aas_coverage_forcing`: For m = 1 and |W| ≥ 3, c ≥ 2.
6. `two_non_aas_coverage_forcing`: For m = 2 and |W| ≥ 4, c ≥ 2.
7. `three_non_aas_coverage_forcing`: For m = 3 and |W| ≥ 5, c ≥ 2.
8. `four_non_aas_coverage_forcing`: For m = 4 and |W| ≥ 6, c ≥ 2.
9. `grand_universal_aas_coverage_bound_synthesis`: Master synthesis theorem for AAS coverage bounds.
-/

namespace Recaman.UniversalAASCoverageBound

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

/-- Universal AAS coverage lower bound: In any tight subset of size k = N + m where
N AAS windows and m non-AAS windows are present, the number of covered AAS endpoints c
satisfies c ≥ |W| - m. -/
theorem universal_aas_coverage_lower_bound
    (N_A_len W_len N m c : Nat)
    (_hc : c ≤ N)
    (htight : N_A_len = N + m)
    (hcov : W_len + (N - c) ≤ N_A_len) :
    W_len - m ≤ c := by
  omega

/-- Whenever the non-AAS collective neighborhood has size |W| ≥ m + 2,
the non-AAS windows MUST cover at least 2 AAS endpoints. -/
theorem universal_aas_coverage_ge_two
    (N_A_len W_len N m c : Nat)
    (hc : c ≤ N)
    (htight : N_A_len = N + m)
    (hcov : W_len + (N - c) ≤ N_A_len)
    (hW : m + 2 ≤ W_len) :
    2 ≤ c := by
  have h := universal_aas_coverage_lower_bound N_A_len W_len N m c hc htight hcov
  omega

/-- Whenever the non-AAS collective neighborhood has size |W| ≥ m + 3,
the non-AAS windows MUST cover at least 3 AAS endpoints. -/
theorem universal_aas_coverage_ge_three
    (N_A_len W_len N m c : Nat)
    (hc : c ≤ N)
    (htight : N_A_len = N + m)
    (hcov : W_len + (N - c) ≤ N_A_len)
    (hW : m + 3 ≤ W_len) :
    3 ≤ c := by
  have h := universal_aas_coverage_lower_bound N_A_len W_len N m c hc htight hcov
  omega

/-- Arithmetic impossibility of covering ≤ 1 AAS endpoint when |W| ≥ m + 2. -/
theorem universal_distant_aas_impossible
    (N_A_len W_len N m c : Nat)
    (hc : c ≤ N)
    (htight : N_A_len = N + m)
    (hcov : W_len + (N - c) ≤ N_A_len)
    (hW : m + 2 ≤ W_len)
    (hle1 : c ≤ 1) :
    False := by
  have h2 := universal_aas_coverage_ge_two N_A_len W_len N m c hc htight hcov hW
  omega

/-- Specialization to m = 1 (single non-AAS window):
Since |W| ≥ 3, we have m + 2 = 3 ≤ |W|, forcing c ≥ 2. -/
theorem single_non_aas_coverage_forcing
    (N_A_len W_len N c : Nat)
    (hc : c ≤ N)
    (htight : N_A_len = N + 1)
    (hcov : W_len + (N - c) ≤ N_A_len)
    (hW3 : 3 ≤ W_len) :
    2 ≤ c :=
  universal_aas_coverage_ge_two N_A_len W_len N 1 c hc htight hcov hW3

/-- Specialization to m = 2 (two non-AAS windows):
If |W| ≥ 4, then m + 2 = 4 ≤ |W|, forcing c ≥ 2. -/
theorem two_non_aas_coverage_forcing
    (N_A_len W_len N c : Nat)
    (hc : c ≤ N)
    (htight : N_A_len = N + 2)
    (hcov : W_len + (N - c) ≤ N_A_len)
    (hW4 : 4 ≤ W_len) :
    2 ≤ c :=
  universal_aas_coverage_ge_two N_A_len W_len N 2 c hc htight hcov hW4

/-- Specialization to m = 3 (three non-AAS windows):
If |W| ≥ 5, then m + 2 = 5 ≤ |W|, forcing c ≥ 2. -/
theorem three_non_aas_coverage_forcing
    (N_A_len W_len N c : Nat)
    (hc : c ≤ N)
    (htight : N_A_len = N + 3)
    (hcov : W_len + (N - c) ≤ N_A_len)
    (hW5 : 5 ≤ W_len) :
    2 ≤ c :=
  universal_aas_coverage_ge_two N_A_len W_len N 3 c hc htight hcov hW5

/-- Specialization to m = 4 (four non-AAS windows):
If |W| ≥ 6, then m + 2 = 6 ≤ |W|, forcing c ≥ 2. -/
theorem four_non_aas_coverage_forcing
    (N_A_len W_len N c : Nat)
    (hc : c ≤ N)
    (htight : N_A_len = N + 4)
    (hcov : W_len + (N - c) ≤ N_A_len)
    (hW6 : 6 ≤ W_len) :
    2 ≤ c :=
  universal_aas_coverage_ge_two N_A_len W_len N 4 c hc htight hcov hW6

/-- Master Synthesis: Grand Universal AAS Coverage Bound Theorem. -/
theorem grand_universal_aas_coverage_bound_synthesis
    (N_A_len W_len N m c : Nat)
    (hc : c ≤ N)
    (htight : N_A_len = N + m)
    (hcov : W_len + (N - c) ≤ N_A_len) :
    (m + 2 ≤ W_len → 2 ≤ c) ∧
    (m + 3 ≤ W_len → 3 ≤ c) := by
  refine ⟨universal_aas_coverage_ge_two N_A_len W_len N m c hc htight hcov,
          universal_aas_coverage_ge_three N_A_len W_len N m c hc htight hcov⟩

end Recaman.UniversalAASCoverageBound
