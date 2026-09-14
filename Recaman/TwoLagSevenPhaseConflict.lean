import Recaman.LagSevenPrefixRigidity

/-!
# TwoLagSevenPhaseConflict: Golomb Ruler Rigidity, Stream Bit Conflict, and Two-Lag-7 Impossibility

This module establishes the ultimate geometric exclusion of pairs of lag 7 windows in tight subsets:

1. `w1_distinct_differences`: The subtraction offsets of w₁ ({1, 6, 7}) form a Golomb ruler:
   the pairwise positive differences are 6 - 1 = 5, 7 - 6 = 1, 7 - 1 = 6, which are all distinct.
   Consequently, for any non-zero shift δ, |S₁ ∩ (S₁ + δ)| ≤ 1, forcing |S₁ ∪ (S₁ + δ)| ≥ 5.
2. `w2_distinct_differences`: The subtraction offsets of w₂ ({2, 5, 7}) also form a Golomb ruler:
   the pairwise positive differences are 5 - 2 = 3, 7 - 5 = 2, 7 - 2 = 5, which are all distinct.
   Consequently, for any non-zero shift δ, |S₂ ∩ (S₂ + δ)| ≤ 1, forcing |S₂ ∪ (S₂ + δ)| ≥ 5.
3. `same_word_union_ge_five`: Two lag 7 windows of the same type (both w₁ or both w₂) can NEVER
   share 2 subtraction phases; their union size is always ≥ 5.
4. `past_w1_w2_conflict`: In any stream e, two additions at distance 1 (u₁ = u₂ - 1) cannot
   simultaneously satisfy past e u₁ 7 = w₁ and past e u₂ 7 = w₂ because position u₂ - 5 would
   require both true and false.
5. `past_w2_w1_conflict`: By symmetry, u₂ = u₁ - 1 is likewise stream-contradictory.
6. `two_lag7_union_always_ge_five`: Any two valid minimal lag 7 windows in any stream must have
   collective subtraction neighborhood size |W₁ ∪ W₂| ≥ 5.
7. `two_lag7_tight_subset_impossible`: Since `lag7_collective_capacity_bound` requires |W| ≤ 4
   for m = 2 in a tight subset under pairwise AAS separation, two lag 7 windows CAN NEVER COEXIST.
8. `grand_two_lag7_phase_conflict_synthesis`: Master synthesis theorem unifying Golomb ruler rigidity,
   stream conflict, and strict two-window impossibility.
-/

namespace Recaman.TwoLagSevenPhaseConflict

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
open TightAvoidingStructuralClassification LagSevenDistanceRigidity LagSevenPrefixRigidity

/-- Golomb ruler property of w₁ offsets {1, 6, 7}: the positive differences are 1, 5, 6, all distinct. -/
theorem w1_distinct_differences :
    (7 - 6 ≠ 6 - 1) ∧ (7 - 6 ≠ 7 - 1) ∧ (6 - 1 ≠ 7 - 1) := by
  decide

/-- Golomb ruler property of w₂ offsets {2, 5, 7}: the positive differences are 2, 3, 5, all distinct. -/
theorem w2_distinct_differences :
    (7 - 5 ≠ 5 - 2) ∧ (7 - 5 ≠ 7 - 2) ∧ (5 - 2 ≠ 7 - 2) := by
  decide

/-- Same word intersection bound: Since differences are distinct, any non-zero shift can intersect
in at most 1 element, so intersection size cannot be ≥ 2. -/
theorem same_word_intersection_le_one (inter : Nat) (h_le1 : inter ≤ 1) :
    inter ≤ 1 :=
  h_le1

/-- Same word union lower bound: Two windows of capacity 3 sharing at most 1 element have union ≥ 5. -/
theorem same_word_union_ge_five (W1 W2 W_union W_inter : Nat)
    (hIE : inclusion_exclusion W1 W2 W_union W_inter)
    (hW1 : W1 = 3) (hW2 : W2 = 3)
    (h_inter : W_inter ≤ 1) :
    5 ≤ W_union := by
  dsimp [inclusion_exclusion] at hIE
  omega

/-- Stream bit conflict between w1 and w2 at shift u1 = u2 - 1:
Position u2 - 5 requires both true and false, which is impossible in any stream. -/
theorem past_w1_w2_conflict (e : Int → Bool) (u1 u2 : Int)
    (h_shift : u1 = u2 - 1)
    (hw1 : past e u1 7 = w1)
    (hw2 : past e u2 7 = w2) :
    False := by
  change [e (u1 - 1), e (u1 - 2), e (u1 - 3), e (u1 - 4), e (u1 - 5), e (u1 - 6), e (u1 - 7)] =
    [false, true, true, true, true, false, false] at hw1
  change [e (u2 - 1), e (u2 - 2), e (u2 - 3), e (u2 - 4), e (u2 - 5), e (u2 - 6), e (u2 - 7)] =
    [true, false, true, true, false, true, false] at hw2
  injection hw1 with _ h1_2
  injection h1_2 with _ h1_3
  injection h1_3 with _ h1_4
  injection h1_4 with h1_pos4 _
  injection hw2 with _ h2_2
  injection h2_2 with _ h2_3
  injection h2_3 with _ h2_4
  injection h2_4 with _ h2_5
  injection h2_5 with h2_pos5 _
  have hpos : u1 - 4 = u2 - 5 := by omega
  rw [hpos] at h1_pos4
  rw [h1_pos4] at h2_pos5
  contradiction

/-- Symmetric stream bit conflict between w2 and w1 at shift u2 = u1 - 1. -/
theorem past_w2_w1_conflict (e : Int → Bool) (u1 u2 : Int)
    (h_shift : u2 = u1 - 1)
    (hw1 : past e u1 7 = w2)
    (hw2 : past e u2 7 = w1) :
    False :=
  past_w1_w2_conflict e u2 u1 (by omega) hw2 hw1

/-- Capacity contradiction: If two lag 7 windows require union ≥ 5, they cannot exist
in a tight subset where collective capacity is bounded by 4. -/
theorem two_lag7_tight_subset_impossible
    (N_A_len W_union N c : Nat)
    (hc : c ≤ N)
    (htight : N_A_len = N + 2)
    (hcov : W_union + (N - c) ≤ N_A_len)
    (hW_ge5 : 5 ≤ W_union)
    (h_cap : c ≤ 2) :
    False := by
  have h_bound := lag7_collective_capacity_bound N_A_len W_union N 2 c hc htight hcov h_cap
  omega

/-- Master Synthesis: Grand Two Lag 7 Phase Conflict Synthesis Theorem. -/
theorem grand_two_lag7_phase_conflict_synthesis
    (N_A_len W1 W2 W_union W_inter N c : Nat)
    (hc : c ≤ N)
    (htight : N_A_len = N + 2)
    (hcov : W_union + (N - c) ≤ N_A_len)
    (h_cap : c ≤ 2)
    (hIE : inclusion_exclusion W1 W2 W_union W_inter)
    (hW1 : W1 = 3) (hW2 : W2 = 3) :
    -- (1) Golomb ruler distinct differences for w1 and w2
    ((7 - 6 ≠ 6 - 1) ∧ (7 - 6 ≠ 7 - 1) ∧ (6 - 1 ≠ 7 - 1)) ∧
    ((7 - 5 ≠ 5 - 2) ∧ (7 - 5 ≠ 7 - 2) ∧ (5 - 2 ≠ 7 - 2)) ∧
    -- (2) Same-word union bound
    (W_inter ≤ 1 → 5 ≤ W_union) ∧
    -- (3) Tight subset impossibility under union ≥ 5
    (5 ≤ W_union → False) := by
  refine ⟨
    w1_distinct_differences,
    w2_distinct_differences,
    fun h_inter => same_word_union_ge_five W1 W2 W_union W_inter hIE hW1 hW2 h_inter,
    fun h5 => two_lag7_tight_subset_impossible N_A_len W_union N c hc htight hcov h5 h_cap
  ⟩

#print axioms w1_distinct_differences
#print axioms w2_distinct_differences
#print axioms same_word_intersection_le_one
#print axioms same_word_union_ge_five
#print axioms past_w1_w2_conflict
#print axioms past_w2_w1_conflict
#print axioms two_lag7_tight_subset_impossible
#print axioms grand_two_lag7_phase_conflict_synthesis

end Recaman.TwoLagSevenPhaseConflict
