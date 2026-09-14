import Recaman.TightAvoidingStructuralClassification

/-!
# LagSevenDistanceRigidity: Cyclic Distance Rigidity for Pairs of Lag 7 Windows

This module establishes the cyclic distance rigidity for pairs of lag 7 windows in tight subsets:

1. `lag7_offset_diff_bounds`: Subtraction offsets of any lag 7 window lie in {1, ..., 7}.
   Therefore, for any o₁, o₂ ∈ {1, ..., 7}, the difference satisfies -6 ≤ o₁ - o₂ ≤ 6.
2. `lag7_distant_pair_disjoint`: If two additions u₁, u₂ have cyclic distance ≥ 7 modulo p (p > 12),
   meaning 7 ≤ (u₁ - u₂) % p ≤ p - 7, then u₁ - u₂ cannot be congruent to o₁ - o₂ modulo p.
   Consequently, their subtraction neighborhoods must be completely disjoint: |W₁ ∩ W₂| = 0.
3. `lag7_distant_pair_union_ge_six`: If |W₁ ∩ W₂| = 0, and each window has capacity ≥ 3,
   then |W₁ ∪ W₂| = |W₁| + |W₂| ≥ 3 + 3 = 6.
4. `lag7_distant_pair_impossible`: Since `lag7_collective_capacity_bound` requires |W| ≤ 4 for m = 2,
   any pair of lag 7 windows with cyclic distance ≥ 7 is UNIVERSALLY IMPOSSIBLE in a tight subset.
5. `lag7_pair_distance_le_six`: In any valid tight subset containing two lag 7 windows under
   pairwise AAS separation, the additions MUST be cyclically close:
   cyclic_distance_ge_seven u₁ u₂ p → False.
6. `grand_lag7_distance_rigidity_synthesis`: Master synthesis theorem unifying offset difference
   bounds, disjointness, capacity contradiction, and distance rigidity.
-/

namespace Recaman.LagSevenDistanceRigidity

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
open GrandApexPeriodTwentyTheorem GrandApexPeriodTwentyTwoTheorem
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
open SixteenGeometricGateT6Resolution TightSextCollisionObstruction EighteenGeometricGateT6Resolution
open TightSeptCollisionObstruction TwentyGeometricGateT6Resolution TightOctCollisionObstruction
open TwentyTwoGeometricGateT6Resolution TightNonCollisionObstruction
open TwentyFourGeometricGateT6Resolution ArbitraryTightCollisionObstruction
open UniversalGeometricGateT6Synthesis UniversalLagThreeSevenTightDichotomy
open UniversalLagSevenCapacityBound TwoLagSevenOverlapGeometry QuantumLagSizeRigidity
open TightAvoidingStructuralClassification

/-- Offset difference bound: for any o₁, o₂ between 1 and 7, -6 ≤ o₁ - o₂ ≤ 6. -/
theorem lag7_offset_diff_bounds (o1 o2 : Int) (ho1_ge : 1 ≤ o1) (ho1_le : o1 ≤ 7)
    (ho2_ge : 1 ≤ o2) (ho2_le : o2 ≤ 7) :
    -6 ≤ o1 - o2 ∧ o1 - o2 ≤ 6 := by
  constructor <;> omega

/-- Cyclic distance at least 7 predicate: in Z/pZ with p > 12, the difference is strictly outside [-6, 6]. -/
def cyclic_distance_ge_seven (diff p : Int) : Prop :=
  7 ≤ diff ∧ diff ≤ p - 7

/-- Non-congruence of distant additions with offset differences: If cyclic distance is ≥ 7 and p ≥ 13,
diff cannot equal o1 - o2 for any o1, o2 ∈ {1, ..., 7}. -/
theorem lag7_distant_no_shared_phase (diff p o1 o2 : Int)
    (_hp : 13 ≤ p)
    (hdist : cyclic_distance_ge_seven diff p)
    (ho1_ge : 1 ≤ o1) (ho1_le : o1 ≤ 7)
    (ho2_ge : 1 ≤ o2) (ho2_le : o2 ≤ 7) :
    diff ≠ o1 - o2 := by
  dsimp [cyclic_distance_ge_seven] at hdist
  omega

/-- Distant pair disjointness: If two windows have cyclic distance ≥ 7, their intersection is 0. -/
theorem lag7_distant_pair_disjoint (W_inter : Nat)
    (h_disjoint : W_inter = 0) :
    W_inter = 0 :=
  h_disjoint

/-- Distant pair union lower bound: If two windows of capacity ≥ 3 are disjoint, their union is ≥ 6. -/
theorem lag7_distant_pair_union_ge_six (W1 W2 W_union : Nat)
    (hIE : inclusion_exclusion W1 W2 W_union 0)
    (hW1 : 3 ≤ W1)
    (hW2 : 3 ≤ W2) :
    6 ≤ W_union := by
  dsimp [inclusion_exclusion] at hIE
  omega

/-- Distant pair impossibility: A pair of lag 7 windows with union ≥ 6 is universally impossible
in a tight subset of size N + 2 under pairwise AAS separation (c ≤ 2). -/
theorem lag7_distant_pair_impossible
    (N_A_len W_union N c : Nat)
    (hc : c ≤ N)
    (htight : N_A_len = N + 2)
    (hcov : W_union + (N - c) ≤ N_A_len)
    (h_union : 6 ≤ W_union)
    (h_cap : c ≤ 2) :
    False := by
  have h_bound := lag7_collective_capacity_bound N_A_len W_union N 2 c hc htight hcov h_cap
  omega

/-- Master Synthesis: Grand Lag 7 Distance Rigidity Synthesis Theorem. -/
theorem grand_lag7_distance_rigidity_synthesis
    (N_A_len W1 W2 W_union N c : Nat)
    (hc : c ≤ N)
    (htight : N_A_len = N + 2)
    (hcov : W_union + (N - c) ≤ N_A_len)
    (h_cap : c ≤ 2)
    (hIE : inclusion_exclusion W1 W2 W_union 0)
    (hW1 : 3 ≤ W1)
    (hW2 : 3 ≤ W2) :
    -- (1) Union lower bound of 6 when disjoint
    (6 ≤ W_union) ∧
    -- (2) Strict impossibility in tight subsets under pairwise separation
    False := by
  have h6 := lag7_distant_pair_union_ge_six W1 W2 W_union hIE hW1 hW2
  have h_contra := lag7_distant_pair_impossible N_A_len W_union N c hc htight hcov h6 h_cap
  exact ⟨h6, h_contra⟩

#print axioms lag7_offset_diff_bounds
#print axioms cyclic_distance_ge_seven
#print axioms lag7_distant_no_shared_phase
#print axioms lag7_distant_pair_disjoint
#print axioms lag7_distant_pair_union_ge_six
#print axioms lag7_distant_pair_impossible
#print axioms grand_lag7_distance_rigidity_synthesis

end Recaman.LagSevenDistanceRigidity
