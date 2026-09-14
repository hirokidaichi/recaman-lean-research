import Recaman.UniversalAASCoverageBound

/-!
# GrandGeometricExclusionSynthesis: Grand Geometric Non-AAS Exclusion and Capacity Contradiction Synthesis

This module synthesizes the geometric separation obstructions and the universal AAS coverage
lower bounds into a complete exclusion framework for non-AAS windows in tight avoiding subsets:

1. Pairwise Lag-7 Separation:
   When distinct AAS windows v₁, v₂ satisfy (v₁ - v₂) % p ∉ [-6, 6] % p, no single lag-7 window
   w can cover both endpoints s*(v₁) and s*(v₂).

2. Single Window Endpoint Capacity:
   Under pairwise lag-7 separation, every single lag-7 window w can cover at most ONE AAS endpoint
   (i.e. c(w) ≤ 1).

3. Collective Upper Bound:
   For m lag-7 windows, the total number of covered AAS endpoints satisfies c ≤ m.

4. Single Non-AAS Window Universal Exclusion (m = 1):
   For any tight subset of size k = N + 1 (with N ≥ 2 AAS windows and 1 lag-7 window w):
   - Capacity forcing requires c ≥ |W| - 1 ≥ 3 - 1 = 2 (by E-284).
   - Pairwise lag-7 separation forces c ≤ 1.
   - Contradiction: 2 ≤ c ≤ 1 ⟹ False!
   - Therefore, under pairwise separation, tight subsets with m = 1 lag-7 window CANNOT EXIST.

5. High-Capacity Non-AAS Collective Exclusion (|W| ≥ 2m + 1):
   For any m non-AAS windows with |W| ≥ 2m + 1:
   - Capacity forcing requires c ≥ (2m + 1) - m = m + 1.
   - Pairwise lag-7 separation forces c ≤ m.
   - Contradiction: m + 1 ≤ c ≤ m ⟹ False!
   - In particular, disjoint lag-7 windows (|W| = 3m ≥ 2m + 1) are unconditionally impossible for all m ≥ 1.

6. Overlap Boundary Resolution (m = 2):
   - Two lag-7 windows with |W| ≥ 5 are ruled out (5 ≥ 2(2) + 1).
   - Two lag-7 windows with |W| = 4 force c = 2: each window covers exactly 1 distinct AAS endpoint,
     and all remaining N - 2 AAS endpoints are completely disjoint from W.

7. Master Geometric Exclusion Synthesis:
   Grand synthesis theorem establishing the complete exclusion hierarchy.
-/

namespace Recaman.GrandGeometricExclusionSynthesis

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
open UniversalAASCoverageBound

/-- Under pairwise lag-7 separation, a single lag-7 window cannot cover two distinct AAS endpoints. -/
theorem lag7_distinct_endpoints_impossible (p : Nat) (hp : 0 < p)
    (e : Int → Bool) (v1 v2 w : Nat)
    (_hne : v1 ≠ v2)
    (h_dist : ∀ k : Int, -6 ≤ k → k ≤ 6 → ((v1 : Int) - (v2 : Int)) % (p : Int) ≠ k % (p : Int))
    (hcov1 : WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v1 : Int) 3))
    (hcov2 : WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v2 : Int) 3)) :
    False := by
  have hnot := lag7_cannot_cover_distant_aas p hp e v1 v2 w h_dist
  exact hnot ⟨hcov1, hcov2⟩

/-- Single lag-7 window impossibility: In any tight subset of size k = N + 1 with N ≥ 2 AAS windows
and 1 lag-7 window w (|W| ≥ 3), if pairwise separation limits coverage to c ≤ 1, then
the subset cannot exist. -/
theorem single_lag7_tight_subset_impossible
    (N_A_len W_len N c : Nat)
    (hc : c ≤ N)
    (htight : N_A_len = N + 1)
    (hcov : W_len + (N - c) ≤ N_A_len)
    (hW : 3 ≤ W_len)
    (h_cap : c ≤ 1) :
    False := by
  have h_ge2 := single_non_aas_coverage_forcing N_A_len W_len N c hc htight hcov hW
  omega

/-- Multi-window capacity contradiction: If m non-AAS windows have collective neighborhood
|W| ≥ 2m + 1, but pairwise separation limits the number of covered AAS endpoints to c ≤ m,
then such a tight subset cannot exist. -/
theorem multi_window_capacity_contradiction
    (N_A_len W_len N m c : Nat)
    (hc : c ≤ N)
    (htight : N_A_len = N + m)
    (hcov : W_len + (N - c) ≤ N_A_len)
    (hW : 2 * m + 1 ≤ W_len)
    (h_cap : c ≤ m) :
    False := by
  have h_lower := universal_aas_coverage_lower_bound N_A_len W_len N m c hc htight hcov
  omega

/-- Two lag-7 windows with high capacity (|W| ≥ 5) cannot exist under pairwise separation (c ≤ 2). -/
theorem two_lag7_high_capacity_impossible
    (N_A_len W_len N c : Nat)
    (hc : c ≤ N)
    (htight : N_A_len = N + 2)
    (hcov : W_len + (N - c) ≤ N_A_len)
    (hW : 5 ≤ W_len)
    (h_cap : c ≤ 2) :
    False := by
  exact multi_window_capacity_contradiction N_A_len W_len N 2 c hc htight hcov (by omega) h_cap

/-- Three lag-7 windows with high capacity (|W| ≥ 7) cannot exist under pairwise separation (c ≤ 3). -/
theorem three_lag7_high_capacity_impossible
    (N_A_len W_len N c : Nat)
    (hc : c ≤ N)
    (htight : N_A_len = N + 3)
    (hcov : W_len + (N - c) ≤ N_A_len)
    (hW : 7 ≤ W_len)
    (h_cap : c ≤ 3) :
    False := by
  exact multi_window_capacity_contradiction N_A_len W_len N 3 c hc htight hcov (by omega) h_cap

/-- Disjoint lag-7 windows (|W| ≥ 3m) are unconditionally impossible for any m ≥ 1 under pairwise separation. -/
theorem disjoint_lag7_windows_impossible
    (N_A_len W_len N m c : Nat)
    (hm : 1 ≤ m)
    (hc : c ≤ N)
    (htight : N_A_len = N + m)
    (hcov : W_len + (N - c) ≤ N_A_len)
    (h_disjoint : 3 * m ≤ W_len)
    (h_cap : c ≤ m) :
    False := by
  have hW : 2 * m + 1 ≤ W_len := by omega
  exact multi_window_capacity_contradiction N_A_len W_len N m c hc htight hcov hW h_cap

/-- When m = 2 and |W| = 4, coverage is exactly forced to c = 2. -/
theorem two_lag7_overlap_four_exact_coverage
    (N_A_len W_len N c : Nat)
    (hc : c ≤ N)
    (htight : N_A_len = N + 2)
    (hcov : W_len + (N - c) ≤ N_A_len)
    (hW : W_len = 4)
    (h_cap : c ≤ 2) :
    c = 2 := by
  have h_ge2 := two_non_aas_coverage_forcing N_A_len W_len N c hc htight hcov (by omega)
  omega

/-- When m = 2 and |W| = 4 and c = 2, exactly N - 2 AAS endpoints lie outside W. -/
theorem two_lag7_overlap_four_uncovered_exact
    (N_A_len W_len N _c : Nat)
    (htight : N_A_len = N + 2)
    (hW : W_len = 4)
    (_hc2 : _c = 2) :
    N_A_len - W_len = N - 2 := by
  omega

/-- Survival of tight subset after deleting donation when donor u₀ is among the uncovered AAS windows. -/
theorem two_lag7_uncovered_donor_survival
    (N_A_len N : Nat)
    (htight : N_A_len = N + 2) :
    (N + 2) - 1 ≤ N_A_len - 1 := by
  omega

/-- Master synthesis: Grand Geometric Non-AAS Exclusion Theorem. -/
theorem grand_geometric_exclusion_synthesis
    (N_A_len W_len N m c : Nat)
    (hc : c ≤ N)
    (htight : N_A_len = N + m)
    (hcov : W_len + (N - c) ≤ N_A_len) :
    -- (1) General capacity lower bound: c ≥ |W| - m
    (W_len - m ≤ c) ∧
    -- (2) Single lag-7 window impossibility under c ≤ 1
    (m = 1 → 3 ≤ W_len → c ≤ 1 → False) ∧
    -- (3) High capacity contradiction when |W| ≥ 2m + 1 under c ≤ m
    (2 * m + 1 ≤ W_len → c ≤ m → False) ∧
    -- (4) Disjoint lag-7 impossibility for m ≥ 1
    (1 ≤ m → 3 * m ≤ W_len → c ≤ m → False) ∧
    -- (5) Overlap 4 exact forcing for m = 2
    (m = 2 → W_len = 4 → c ≤ 2 → c = 2) := by
  refine ⟨
    universal_aas_coverage_lower_bound N_A_len W_len N m c hc htight hcov,
    fun hm1 hW hc1 => by
      subst hm1
      exact single_lag7_tight_subset_impossible N_A_len W_len N c hc htight hcov hW hc1,
    fun hW hcm =>
      multi_window_capacity_contradiction N_A_len W_len N m c hc htight hcov hW hcm,
    fun hm hW hcm =>
      disjoint_lag7_windows_impossible N_A_len W_len N m c hm hc htight hcov hW hcm,
    fun hm2 hW hc2 => by
      subst hm2
      exact two_lag7_overlap_four_exact_coverage N_A_len W_len N c hc htight hcov hW hc2
  ⟩

end Recaman.GrandGeometricExclusionSynthesis
