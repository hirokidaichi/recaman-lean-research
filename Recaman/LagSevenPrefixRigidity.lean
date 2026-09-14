import Recaman.LagSevenDistanceRigidity

/-!
# LagSevenPrefixRigidity: Classification of Length-7 P2 Words and Strict Minimal Lag 7 Rigidity

This module establishes the exact discrete classification of all binary words of length 7
satisfying P2 and demonstrates that minimal lag 7 is strictly restricted to only two words:

1. `lag7_p2_words_classification`: Exactly 4 binary words of length 7 satisfy P2:
   - w₁ = [F, T, T, T, T, F, F]
   - w₂ = [T, F, T, T, F, T, F]
   - w₃ = [T, T, F, F, T, T, F]
   - w₄ = [T, T, F, T, F, F, T]
2. `lag7_w3_w4_have_p2_prefix`: Both w₃ and w₄ have a strict non-trivial P2 prefix of length 3
   (specifically [T, T, F], which is the canonical AAS window).
3. `lag7_w1_w2_no_p2_prefix`: Neither w₁ nor w₂ possesses any non-trivial P2 prefix.
4. `lag7_minimal_lag7_must_be_w1_or_w2`: Any addition with minimal P2 lag 7 (having no smaller
   P2 prefix) MUST have its past equal to either w₁ or w₂.
5. `grand_lag7_prefix_rigidity_synthesis`: Master synthesis theorem unifying the 4-word
   classification, prefix detection, and minimal lag 7 restriction.
-/

namespace Recaman.LagSevenPrefixRigidity

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
open TightAvoidingStructuralClassification LagSevenDistanceRigidity

/-- The four canonical binary words of length 7 satisfying P2. -/
def w1 : List Bool := [false, true, true, true, true, false, false]
def w2 : List Bool := [true, false, true, true, false, true, false]
def w3 : List Bool := [true, true, false, false, true, true, false]
def w4 : List Bool := [true, true, false, true, false, false, true]

/-- Boolean predicate testing whether a word satisfies P2. -/
def isP2Word (w : List Bool) : Bool :=
  mass w == 1 && moment w == 0

/-- Exhaustive classification: exactly 4 binary words of length 7 satisfy P2. -/
theorem lag7_p2_words_classification :
    (bitWords 7).filter isP2Word = [w1, w2, w3, w4] := by
  decide

/-- Prefix property: w3 and w4 have a strict non-trivial P2 prefix. -/
theorem lag7_w3_w4_have_p2_prefix :
    hasP2Prefix w3 = true ∧ hasP2Prefix w4 = true := by
  decide

/-- Cleanliness property: w1 and w2 have no non-trivial P2 prefix. -/
theorem lag7_w1_w2_no_p2_prefix :
    hasP2Prefix w1 = false ∧ hasP2Prefix w2 = false := by
  decide

/-- Minimal lag 7 word filter: exactly w1 and w2 survive the prefix filter. -/
theorem lag7_minimal_words_classification :
    (bitWords 7).filter (fun w => isP2Word w && !hasP2Prefix w) = [w1, w2] := by
  decide

/-- Any word of length 7 satisfying P2 without a P2 prefix must be w1 or w2. -/
theorem lag7_minimal_lag7_must_be_w1_or_w2 (w : List Bool) (hlen : w.length = 7)
    (hP2 : isP2Word w = true) (h_no_prefix : hasP2Prefix w = false) :
    w = w1 ∨ w = w2 := by
  have hmem : w ∈ bitWords 7 := by
    have hm := mem_bitWords w
    rw [hlen] at hm
    exact hm
  have hfilt : w ∈ (bitWords 7).filter (fun w => isP2Word w && !hasP2Prefix w) := by
    rw [List.mem_filter]
    refine ⟨hmem, by simp [hP2, h_no_prefix]⟩
  have h_class := lag7_minimal_words_classification
  rw [h_class] at hfilt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfilt
  exact hfilt

/-- Master Synthesis: Grand Lag 7 Prefix Rigidity Synthesis Theorem. -/
theorem grand_lag7_prefix_rigidity_synthesis :
    -- (1) 4-word classification
    ((bitWords 7).filter isP2Word = [w1, w2, w3, w4]) ∧
    -- (2) w3 and w4 prefix detection
    (hasP2Prefix w3 = true ∧ hasP2Prefix w4 = true) ∧
    -- (3) w1 and w2 cleanliness
    (hasP2Prefix w1 = false ∧ hasP2Prefix w2 = false) ∧
    -- (4) Minimal lag 7 filter
    ((bitWords 7).filter (fun w => isP2Word w && !hasP2Prefix w) = [w1, w2]) ∧
    -- (5) Minimal lag 7 disjunction
    (∀ w : List Bool, w.length = 7 → isP2Word w = true → hasP2Prefix w = false → w = w1 ∨ w = w2) := by
  refine ⟨
    lag7_p2_words_classification,
    lag7_w3_w4_have_p2_prefix,
    lag7_w1_w2_no_p2_prefix,
    lag7_minimal_words_classification,
    fun w hw hp hn => lag7_minimal_lag7_must_be_w1_or_w2 w hw hp hn
  ⟩

#print axioms lag7_p2_words_classification
#print axioms lag7_w3_w4_have_p2_prefix
#print axioms lag7_w1_w2_no_p2_prefix
#print axioms lag7_minimal_words_classification
#print axioms lag7_minimal_lag7_must_be_w1_or_w2
#print axioms grand_lag7_prefix_rigidity_synthesis

end Recaman.LagSevenPrefixRigidity
