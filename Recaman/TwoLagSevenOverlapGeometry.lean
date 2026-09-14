import Recaman.UniversalLagSevenCapacityBound

/-!
# TwoLagSevenOverlapGeometry: Exact Overlap and Intersection Geometry for Pairs of Lag 7 Windows

This module establishes the exact geometric overlap structure and intersection rigidity
for any pair of lag 7 windows (w₁, w₂) in a tight subset of size k = N + 2:

1. `two_lag7_capacity_dichotomy`: Under pairwise AAS separation (c ≤ 2), since |W| ≥ |W₁| ≥ 3
   and |W| ≤ 4 (from `lag7_collective_capacity_bound`), the collective neighborhood size
   satisfies |W| ∈ {3, 4}.
2. `two_lag7_intersection_lower_bound`: By inclusion-exclusion (|W₁ ∩ W₂| = |W₁| + |W₂| - |W|),
   with |W₁| ≥ 3, |W₂| ≥ 3, and |W| ≤ 4:
   |W₁ ∩ W₂| ≥ 3 + 3 - 4 = 2.
   Any two lag 7 windows MUST share at least 2 subtraction phases!
3. `two_lag7_exact_overlap_four`: If both windows have canonical capacity 3 (|W₁| = 3, |W₂| = 3)
   and |W| = 4, then |W₁ ∩ W₂| = 2 exactly.
4. `two_lag7_exact_overlap_three`: If |W₁| = 3, |W₂| = 3 and |W| = 3, then |W₁ ∩ W₂| = 3
   (their subtraction neighborhoods are completely identical).
5. `two_lag7_disjoint_obstruction`: Two lag 7 windows can NEVER be disjoint in a tight subset
   under pairwise AAS separation (|W₁ ∩ W₂| = 0 is impossible).
6. `two_lag7_single_overlap_obstruction`: Two canonical lag 7 windows can NEVER share only
   one subtraction phase (|W₁ ∩ W₂| = 1 is impossible).
7. `grand_two_lag7_overlap_synthesis`: Master synthesis theorem unifying the capacity dichotomy,
   intersection rigidity, and overlap obstructions for all pairs of lag 7 windows.
-/

namespace Recaman.TwoLagSevenOverlapGeometry

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
open UniversalLagSevenCapacityBound

/-- Inclusion-exclusion relation for subtraction phase neighborhoods of two windows:
|W₁ ∪ W₂| = |W₁| + |W₂| - |W₁ ∩ W₂|. -/
def inclusion_exclusion (W1 W2 W_union W_inter : Nat) : Prop :=
  W_union + W_inter = W1 + W2

/-- Two Lag 7 Capacity Dichotomy: Under pairwise AAS separation, the collective neighborhood
of two lag 7 windows (each with capacity ≥ 3) must have size either 3 or 4. -/
theorem two_lag7_capacity_dichotomy
    (N_A_len W_len N c : Nat)
    (hc : c ≤ N)
    (htight : N_A_len = N + 2)
    (hcov : W_len + (N - c) ≤ N_A_len)
    (hW_lower : 3 ≤ W_len)
    (h_cap : c ≤ 2) :
    W_len = 3 ∨ W_len = 4 := by
  have h_bound := lag7_collective_capacity_bound N_A_len W_len N 2 c hc htight hcov h_cap
  omega

/-- Two Lag 7 Intersection Lower Bound: Any two lag 7 windows (each of capacity ≥ 3)
in a tight subset under pairwise AAS separation must share at least 2 subtraction phases. -/
theorem two_lag7_intersection_lower_bound
    (W1 W2 W_union W_inter : Nat)
    (hIE : inclusion_exclusion W1 W2 W_union W_inter)
    (hW1 : 3 ≤ W1)
    (hW2 : 3 ≤ W2)
    (h_union : W_union ≤ 4) :
    2 ≤ W_inter := by
  dsimp [inclusion_exclusion] at hIE
  omega

/-- Exact Overlap for Union Size 4: When two canonical lag 7 windows (|W₁| = 3, |W₂| = 3)
have union size 4, their intersection is EXACTLY 2. -/
theorem two_lag7_exact_overlap_four
    (W1 W2 W_union W_inter : Nat)
    (hIE : inclusion_exclusion W1 W2 W_union W_inter)
    (hW1 : W1 = 3)
    (hW2 : W2 = 3)
    (h_union : W_union = 4) :
    W_inter = 2 := by
  dsimp [inclusion_exclusion] at hIE
  omega

/-- Exact Overlap for Union Size 3: When two canonical lag 7 windows (|W₁| = 3, |W₂| = 3)
have union size 3, their intersection is EXACTLY 3 (identical neighborhoods). -/
theorem two_lag7_exact_overlap_three
    (W1 W2 W_union W_inter : Nat)
    (hIE : inclusion_exclusion W1 W2 W_union W_inter)
    (hW1 : W1 = 3)
    (hW2 : W2 = 3)
    (h_union : W_union = 3) :
    W_inter = 3 := by
  dsimp [inclusion_exclusion] at hIE
  omega

/-- Disjoint Obstruction: Two lag 7 windows can NEVER be disjoint in a tight subset
under pairwise AAS separation. -/
theorem two_lag7_disjoint_obstruction
    (W1 W2 W_union W_inter : Nat)
    (hIE : inclusion_exclusion W1 W2 W_union W_inter)
    (hW1 : 3 ≤ W1)
    (hW2 : 3 ≤ W2)
    (h_union : W_union ≤ 4)
    (h_disjoint : W_inter = 0) :
    False := by
  have h_ge2 := two_lag7_intersection_lower_bound W1 W2 W_union W_inter hIE hW1 hW2 h_union
  omega

/-- Single Overlap Obstruction: Two canonical lag 7 windows can NEVER share only
a single subtraction phase under pairwise AAS separation. -/
theorem two_lag7_single_overlap_obstruction
    (W1 W2 W_union W_inter : Nat)
    (hIE : inclusion_exclusion W1 W2 W_union W_inter)
    (hW1 : W1 = 3)
    (hW2 : W2 = 3)
    (h_union : W_union ≤ 4)
    (h_single : W_inter = 1) :
    False := by
  dsimp [inclusion_exclusion] at hIE
  omega

/-- Master Synthesis: Grand Two Lag 7 Overlap Synthesis Theorem. -/
theorem grand_two_lag7_overlap_synthesis
    (N_A_len W1 W2 W_union W_inter N c : Nat)
    (hc : c ≤ N)
    (htight : N_A_len = N + 2)
    (hcov : W_union + (N - c) ≤ N_A_len)
    (h_cap : c ≤ 2)
    (hIE : inclusion_exclusion W1 W2 W_union W_inter)
    (hW1 : W1 = 3)
    (hW2 : W2 = 3)
    (hW_lower : 3 ≤ W_union) :
    -- (1) Union dichotomy: |W| ∈ {3, 4}
    (W_union = 3 ∨ W_union = 4) ∧
    -- (2) Intersection lower bound: |W₁ ∩ W₂| ≥ 2
    (2 ≤ W_inter) ∧
    -- (3) Exact intersection dichotomy: |W₁ ∩ W₂| ∈ {2, 3}
    (W_inter = 2 ∨ W_inter = 3) ∧
    -- (4) Disjoint impossible
    (W_inter = 0 → False) ∧
    -- (5) Single overlap impossible
    (W_inter = 1 → False) := by
  have hdicho := two_lag7_capacity_dichotomy N_A_len W_union N c hc htight hcov hW_lower h_cap
  have h_bound := lag7_collective_capacity_bound N_A_len W_union N 2 c hc htight hcov h_cap
  have h_ge2 := two_lag7_intersection_lower_bound W1 W2 W_union W_inter hIE (by omega) (by omega) h_bound
  dsimp [inclusion_exclusion] at hIE
  refine ⟨
    hdicho,
    h_ge2,
    by omega,
    fun h0 => by omega,
    fun h1 => by omega
  ⟩

#print axioms inclusion_exclusion
#print axioms two_lag7_capacity_dichotomy
#print axioms two_lag7_intersection_lower_bound
#print axioms two_lag7_exact_overlap_four
#print axioms two_lag7_exact_overlap_three
#print axioms two_lag7_disjoint_obstruction
#print axioms two_lag7_single_overlap_obstruction
#print axioms grand_two_lag7_overlap_synthesis

end Recaman.TwoLagSevenOverlapGeometry
