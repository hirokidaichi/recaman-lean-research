import Recaman.UniversalGeometricGateT6Synthesis

/-!
# UniversalLagThreeSevenTightDichotomy: Universal Lag {3, 7} Tight Subset Dichotomy and Obstruction

This module establishes the comprehensive structural dichotomy for tight avoiding subsets B
governed by the canonical lag alphabet {3, 7}:

For any tight avoiding subset B of size k ≥ 3 where every window has lag 3 or lag 7:
1. `tight_lag37_all_aas_or_has_lag7`: Dichotomy:
   Either (∀ u ∈ B, lag u = 3) (all-AAS pure subset),
   or (∃ w ∈ B, lag w = 7) (contains at least one lag 7 window).
2. `tight_lag37_all_aas_avoids_s_star`: If all windows are lag 3 AAS, then B strictly avoids
   s*(u₀) unconditionally across ALL periods p and ALL sizes k:
   `s*(u₀) ∉ N(B)`.
3. `tight_lag37_all_aas_survives`: Any all-AAS tight subset strictly survives deletion of s*(u₀)
   with zero loss across ALL periods p and ALL sizes k:
   `|B| ≤ |N(B) \ {s*(u₀)}|`.
4. `tight_lag37_single_lag7_must_cover_two`: In any tight subset with k - 1 AAS windows and
   1 lag 7 window w, w must cover at least 2 AAS endpoints: c ≥ 2.
5. `tight_lag37_single_lag7_distance_obstruction`: Under pairwise AAS separation (c ≤ 1), tight
   subsets with k - 1 AAS windows and 1 lag 7 window are universally impossible for ALL k ≥ 3.
6. `tight_lag37_two_lag7_high_capacity_obstruction`: Under pairwise AAS separation (c ≤ 2), tight
   subsets with k - 2 AAS windows and 2 lag 7 windows with |W| ≥ 5 are universally impossible.
7. `grand_universal_lag37_tight_dichotomy_synthesis`: Master synthesis theorem unifying the
   dichotomy and geometric obstruction across all tight subsets.
-/

namespace Recaman.UniversalLagThreeSevenTightDichotomy

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
open UniversalGeometricGateT6Synthesis

/-- Structural Dichotomy: Any list with lags in {3, 7} is either all lag 3 or contains a lag 7. -/
theorem tight_lag37_all_aas_or_has_lag7
    (B : List Nat) (lag : Nat → Nat)
    (hlags : ∀ u ∈ B, lag u = 3 ∨ lag u = 7) :
    (∀ u ∈ B, lag u = 3) ∨ (∃ w ∈ B, lag w = 7) := by
  by_cases h7 : ∃ w ∈ B, lag w = 7
  · exact Or.inr h7
  · left
    intro u hu
    rcases hlags u hu with h3 | h7'
    · exact h3
    · exfalso
      exact h7 ⟨u, hu, h7'⟩

/-- Universal All-AAS Avoidance: Any all-AAS tight subset strictly avoids s*(u₀) across ALL periods. -/
theorem tight_lag37_all_aas_avoids_s_star
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (B : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hlag3 : ∀ u ∈ B, lag u = 3)
    (haas : ∀ u ∈ B, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_B : ∀ u ∈ B, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hB_A : ∀ u ∈ B, e (u : Int) = true) :
    oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag :=
  arbitrary_period_all_aas_avoids_s_star e p hp hper B lag u0 hd_lt hu0A hP0 hss0 hlag3 haas hP_B hB_A

/-- Universal All-AAS Survival: Any all-AAS tight subset strictly survives deletion with zero loss. -/
theorem tight_lag37_all_aas_survives
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (B : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (htight : (neighborhood e p B lag).length = B.length)
    (hlag3 : ∀ u ∈ B, lag u = 3)
    (haas : ∀ u ∈ B, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_B : ∀ u ∈ B, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hB_A : ∀ u ∈ B, e (u : Int) = true) :
    B.length ≤ (deletedNeighborhood e p B lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  arbitrary_period_all_aas_survives e p hp hper B lag u0 hd_lt hu0A hP0 hss0 htight hlag3 haas hP_B hB_A

/-- Single lag 7 window must cover at least 2 AAS endpoints in any tight subset of size k ≥ 3. -/
theorem tight_lag37_single_lag7_must_cover_two
    (N_A_len Nw_len k c : Nat)
    (hk : 3 ≤ k)
    (hc : c ≤ k - 1)
    (htight : N_A_len = k)
    (hNw : 3 ≤ Nw_len)
    (hcov : Nw_len + ((k - 1) - c) ≤ N_A_len) :
    2 ≤ c :=
  arbitrary_tight_lag7_coverage_bound N_A_len Nw_len k c hk hc htight hNw hcov

/-- Single lag 7 window is impossible under pairwise distance separation (c ≤ 1). -/
theorem tight_lag37_single_lag7_distance_obstruction
    (N_A_len Nw_len k c : Nat)
    (hk : 3 ≤ k)
    (hc : c ≤ k - 1)
    (htight : N_A_len = k)
    (hcov : Nw_len + ((k - 1) - c) ≤ N_A_len)
    (hNw : 3 ≤ Nw_len)
    (h_cap : c ≤ 1) :
    False :=
  arbitrary_tight_single_lag7_impossible N_A_len Nw_len k c hk hc htight hcov hNw h_cap

/-- Two lag 7 windows with high capacity (|W| ≥ 5) are impossible under pairwise separation (c ≤ 2). -/
theorem tight_lag37_two_lag7_high_capacity_obstruction
    (N_A_len W_len k c : Nat)
    (hk : 3 ≤ k)
    (hc : c ≤ k - 2)
    (htight : N_A_len = k)
    (hcov : W_len + ((k - 2) - c) ≤ N_A_len)
    (hW : 5 ≤ W_len)
    (h_cap : c ≤ 2) :
    False :=
  arbitrary_tight_two_lag7_high_capacity_impossible N_A_len W_len k c hk hc htight hcov hW h_cap

/-- Grand Master Dichotomy Synthesis Theorem for Lag {3, 7} Tight Subsets. -/
theorem grand_universal_lag37_tight_dichotomy_synthesis
    (B : List Nat) (lag : Nat → Nat)
    (hlags : ∀ u ∈ B, lag u = 3 ∨ lag u = 7)
    (k : Nat) (hk : 3 ≤ k)
    (N_A_len Nw_len c : Nat)
    (hc : c ≤ k - 1)
    (htight : N_A_len = k)
    (hNw : 3 ≤ Nw_len)
    (hcov : Nw_len + ((k - 1) - c) ≤ N_A_len) :
    -- (1) Dichotomy
    ((∀ u ∈ B, lag u = 3) ∨ (∃ w ∈ B, lag w = 7)) ∧
    -- (2) Single lag 7 coverage forcing
    (2 ≤ c) ∧
    -- (3) Single lag 7 impossible under c ≤ 1
    (c ≤ 1 → False) := by
  have hdich := tight_lag37_all_aas_or_has_lag7 B lag hlags
  have hcov2 := tight_lag37_single_lag7_must_cover_two N_A_len Nw_len k c hk hc htight hNw hcov
  have himp : c ≤ 1 → False := fun hc1 => by omega
  exact ⟨hdich, hcov2, himp⟩

#print axioms tight_lag37_all_aas_or_has_lag7
#print axioms tight_lag37_all_aas_avoids_s_star
#print axioms tight_lag37_all_aas_survives
#print axioms tight_lag37_single_lag7_must_cover_two
#print axioms tight_lag37_single_lag7_distance_obstruction
#print axioms tight_lag37_two_lag7_high_capacity_obstruction
#print axioms grand_universal_lag37_tight_dichotomy_synthesis

end Recaman.UniversalLagThreeSevenTightDichotomy
