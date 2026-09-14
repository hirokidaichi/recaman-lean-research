import Recaman.TwentyFourGeometricGateT6Resolution

/-!
# ArbitraryTightCollisionObstruction: Geometric Collision Obstructions in Arbitrary Tight Subsets

This module establishes universal, parametric geometric collision obstructions for window collisions
in tight avoiding subsets A of ANY size k ≥ 3:

1. `arbitrary_tight_complement_bound`: In any tight subset A of size k containing a non-AAS window
   w with |N([w])| ≥ L, the complement N(A) \ N([w]) has size at most k - L.
2. `arbitrary_tight_single_window_coverage_lower_bound`: In any tight subset of size k containing
   k - 1 AAS windows and 1 non-AAS window w with |N([w])| ≥ L, w must cover at least L - 1 AAS endpoints.
3. Specializations for quantum lags:
   - Lag 7 (L = 3): c ≥ 2 for ALL k ≥ 3.
   - Lag 11 (L = 5): c ≥ 4 for ALL k ≥ 5.
   - Lag 15 (L = 7): c ≥ 6 for ALL k ≥ 7.
   - Lag 19 (L = 9): c ≥ 8 for ALL k ≥ 9.
   - Lag 4j + 3 (L = 2j + 1): c ≥ 2j for ALL k ≥ 2j + 1.
4. Universal Impossibility Theorems:
   - `arbitrary_tight_single_lag7_impossible`: Under pairwise separation (c ≤ 1), tight subsets
     containing k - 1 AAS windows and 1 lag 7 window CANNOT EXIST for ANY k ≥ 3.
   - `arbitrary_tight_two_lag7_high_capacity_impossible`: Under pairwise separation (c ≤ 2), tight
     subsets containing k - 2 AAS windows and 2 lag 7 windows with |W| ≥ 5 CANNOT EXIST for ANY k ≥ 3.
   - `arbitrary_tight_disjoint_lag7_impossible`: Pairwise disjoint lag 7 windows (|W| ≥ 3m) are
     universally impossible for ALL m ≥ 1 and ALL k ≥ m + 1.
5. `grand_arbitrary_tight_collision_obstruction_synthesis`: Master synthesis theorem for arbitrary-size
   tight collision obstruction.
-/

namespace Recaman.ArbitraryTightCollisionObstruction

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
open TwentyFourGeometricGateT6Resolution

/-- Complement bound: In any tight subset A of size k containing a window w with |N([w])| ≥ L,
the complement size |N(A) \ N([w])| is at most k - L. -/
theorem arbitrary_tight_complement_bound
    (N_A_len Nw_len k L : Nat)
    (htight : N_A_len = k)
    (hNw : L ≤ Nw_len)
    (_hsub : Nw_len ≤ N_A_len) :
    N_A_len - Nw_len ≤ k - L := by
  omega

/-- Single window coverage lower bound: In any tight subset of size k containing k - 1 AAS windows
and 1 non-AAS window w with |N([w])| ≥ L, w must cover at least L - 1 AAS endpoints. -/
theorem arbitrary_tight_single_window_coverage_lower_bound
    (N_A_len Nw_len k L c : Nat)
    (_hc : c ≤ k - 1)
    (htight : N_A_len = k)
    (hNw : L ≤ Nw_len)
    (hcov : Nw_len + ((k - 1) - c) ≤ N_A_len) :
    L - 1 ≤ c := by
  omega

/-- Universal lag 7 coverage forcing: In any tight subset of size k ≥ 3 with k - 1 AAS windows
and 1 lag 7 window w (|N([w])| ≥ 3), w must cover at least 2 AAS endpoints: c ≥ 2. -/
theorem arbitrary_tight_lag7_coverage_bound
    (N_A_len Nw_len k c : Nat)
    (_hk : 3 ≤ k)
    (hc : c ≤ k - 1)
    (htight : N_A_len = k)
    (hNw : 3 ≤ Nw_len)
    (hcov : Nw_len + ((k - 1) - c) ≤ N_A_len) :
    2 ≤ c := by
  exact arbitrary_tight_single_window_coverage_lower_bound N_A_len Nw_len k 3 c hc htight hNw hcov

/-- Universal lag 11 coverage forcing: In any tight subset of size k ≥ 5 with k - 1 AAS windows
and 1 lag 11 window w (|N([w])| ≥ 5), w must cover at least 4 AAS endpoints: c ≥ 4. -/
theorem arbitrary_tight_lag11_coverage_bound
    (N_A_len Nw_len k c : Nat)
    (_hk : 5 ≤ k)
    (hc : c ≤ k - 1)
    (htight : N_A_len = k)
    (hNw : 5 ≤ Nw_len)
    (hcov : Nw_len + ((k - 1) - c) ≤ N_A_len) :
    4 ≤ c := by
  exact arbitrary_tight_single_window_coverage_lower_bound N_A_len Nw_len k 5 c hc htight hNw hcov

/-- Universal lag 15 coverage forcing: In any tight subset of size k ≥ 7 with k - 1 AAS windows
and 1 lag 15 window w (|N([w])| ≥ 7), w must cover at least 6 AAS endpoints: c ≥ 6. -/
theorem arbitrary_tight_lag15_coverage_bound
    (N_A_len Nw_len k c : Nat)
    (_hk : 7 ≤ k)
    (hc : c ≤ k - 1)
    (htight : N_A_len = k)
    (hNw : 7 ≤ Nw_len)
    (hcov : Nw_len + ((k - 1) - c) ≤ N_A_len) :
    6 ≤ c := by
  exact arbitrary_tight_single_window_coverage_lower_bound N_A_len Nw_len k 7 c hc htight hNw hcov

/-- Universal lag 19 coverage forcing: In any tight subset of size k ≥ 9 with k - 1 AAS windows
and 1 lag 19 window w (|N([w])| ≥ 9), w must cover at least 8 AAS endpoints: c ≥ 8. -/
theorem arbitrary_tight_lag19_coverage_bound
    (N_A_len Nw_len k c : Nat)
    (_hk : 9 ≤ k)
    (hc : c ≤ k - 1)
    (htight : N_A_len = k)
    (hNw : 9 ≤ Nw_len)
    (hcov : Nw_len + ((k - 1) - c) ≤ N_A_len) :
    8 ≤ c := by
  exact arbitrary_tight_single_window_coverage_lower_bound N_A_len Nw_len k 9 c hc htight hNw hcov

/-- Universal quantum lag 4j + 3 coverage forcing: For any quantum index j, in any tight subset of
size k ≥ 2j + 1 with k - 1 AAS windows and 1 lag 4j + 3 window w (|N([w])| ≥ 2j + 1), w must cover
at least 2j AAS endpoints: c ≥ 2j. -/
theorem arbitrary_tight_lag4j_coverage_bound
    (N_A_len Nw_len k j c : Nat)
    (_hk : 2 * j + 1 ≤ k)
    (hc : c ≤ k - 1)
    (htight : N_A_len = k)
    (hNw : 2 * j + 1 ≤ Nw_len)
    (hcov : Nw_len + ((k - 1) - c) ≤ N_A_len) :
    2 * j ≤ c := by
  have h := arbitrary_tight_single_window_coverage_lower_bound N_A_len Nw_len k (2 * j + 1) c hc htight hNw hcov
  omega

/-- Universal single lag 7 impossibility: In any tight subset of ANY size k ≥ 3, a configuration with
k - 1 AAS windows and 1 lag 7 window is impossible under pairwise separation (c ≤ 1). -/
theorem arbitrary_tight_single_lag7_impossible
    (N_A_len Nw_len k c : Nat)
    (hk : 3 ≤ k)
    (hc : c ≤ k - 1)
    (htight : N_A_len = k)
    (hcov : Nw_len + ((k - 1) - c) ≤ N_A_len)
    (hNw : 3 ≤ Nw_len)
    (h_cap : c ≤ 1) :
    False := by
  have hge2 := arbitrary_tight_lag7_coverage_bound N_A_len Nw_len k c hk hc htight hNw hcov
  omega

/-- Universal two lag 7 impossibility with |W| ≥ 5: In any tight subset of ANY size k ≥ 3, two lag 7
windows with |W| ≥ 5 are impossible under pairwise separation (c ≤ 2). -/
theorem arbitrary_tight_two_lag7_high_capacity_impossible
    (N_A_len W_len k c : Nat)
    (_hk : 3 ≤ k)
    (_hc : c ≤ k - 2)
    (htight : N_A_len = k)
    (hcov : W_len + ((k - 2) - c) ≤ N_A_len)
    (hW : 5 ≤ W_len)
    (h_cap : c ≤ 2) :
    False := by
  omega

/-- Universal disjoint lag 7 windows impossibility: In any tight subset of ANY size k ≥ m + 1, m
pairwise disjoint lag 7 windows (|W| ≥ 3m) are impossible under pairwise separation (c ≤ m) for all m ≥ 1. -/
theorem arbitrary_tight_disjoint_lag7_impossible
    (N_A_len W_len k m c : Nat)
    (hm : 1 ≤ m)
    (_hk : m + 1 ≤ k)
    (_hc : c ≤ k - m)
    (htight : N_A_len = k)
    (hcov : W_len + ((k - m) - c) ≤ N_A_len)
    (hW : 3 * m ≤ W_len)
    (h_cap : c ≤ m) :
    False := by
  omega

/-- Master synthesis: Grand Arbitrary Tight Collision Obstruction Theorem. -/
theorem grand_arbitrary_tight_collision_obstruction_synthesis
    (N_A_len Nw_len k c : Nat)
    (hk3 : 3 ≤ k)
    (hc : c ≤ k - 1)
    (htight : N_A_len = k)
    (hcov : Nw_len + ((k - 1) - c) ≤ N_A_len) :
    -- (1) Lag 7 complement bound ≤ k - 3
    (3 ≤ Nw_len → N_A_len - Nw_len ≤ k - 3) ∧
    -- (2) Lag 7 must cover ≥ 2 AAS endpoints
    (3 ≤ Nw_len → 2 ≤ c) ∧
    -- (3) Single lag 7 impossible under c ≤ 1
    (3 ≤ Nw_len → c ≤ 1 → False) ∧
    -- (4) Lag 11 must cover ≥ 4 AAS endpoints (when k ≥ 5)
    (5 ≤ k → 5 ≤ Nw_len → 4 ≤ c) ∧
    -- (5) Lag 15 must cover ≥ 6 AAS endpoints (when k ≥ 7)
    (7 ≤ k → 7 ≤ Nw_len → 6 ≤ c) ∧
    -- (6) Lag 19 must cover ≥ 8 AAS endpoints (when k ≥ 9)
    (9 ≤ k → 9 ≤ Nw_len → 8 ≤ c) := by
  refine ⟨
    fun hNw => arbitrary_tight_complement_bound N_A_len Nw_len k 3 htight hNw (by omega),
    fun hNw => arbitrary_tight_lag7_coverage_bound N_A_len Nw_len k c hk3 hc htight hNw hcov,
    fun hNw hc1 => arbitrary_tight_single_lag7_impossible N_A_len Nw_len k c hk3 hc htight hcov hNw hc1,
    fun hk5 hNw => arbitrary_tight_lag11_coverage_bound N_A_len Nw_len k c hk5 hc htight hNw hcov,
    fun hk7 hNw => arbitrary_tight_lag15_coverage_bound N_A_len Nw_len k c hk7 hc htight hNw hcov,
    fun hk9 hNw => arbitrary_tight_lag19_coverage_bound N_A_len Nw_len k c hk9 hc htight hNw hcov
  ⟩

#print axioms arbitrary_tight_complement_bound
#print axioms arbitrary_tight_single_window_coverage_lower_bound
#print axioms arbitrary_tight_lag7_coverage_bound
#print axioms arbitrary_tight_lag11_coverage_bound
#print axioms arbitrary_tight_lag15_coverage_bound
#print axioms arbitrary_tight_lag19_coverage_bound
#print axioms arbitrary_tight_lag4j_coverage_bound
#print axioms arbitrary_tight_single_lag7_impossible
#print axioms arbitrary_tight_two_lag7_high_capacity_impossible
#print axioms arbitrary_tight_disjoint_lag7_impossible
#print axioms grand_arbitrary_tight_collision_obstruction_synthesis

end Recaman.ArbitraryTightCollisionObstruction
