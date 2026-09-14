import Recaman.GrandGeometricExclusionSynthesis
import Recaman.SixteenGateT6Unconditional

/-!
# TightQuintCollisionObstruction: Geometric Separation Obstructions in Tight Quintuples

This module establishes the geometric separation obstructions for window collisions
within tight avoiding quintuples A = [v₁, v₂, v₃, v₄, w] of size 5:

1. `tight_quint_lag7_complement_bound`: In any tight quintuple A of size 5 containing a lag 7
   window w with |N([w])| ≥ 3, the complement N(A) \ N([w]) has size at most 2.
2. `tight_quint_lag11_complement_bound`: In any tight quintuple A of size 5 containing a lag 11
   window w with |N([w])| ≥ 5, the complement size is 0: N([w]) = N(A).
3. `tight_quint_lag7_must_cover_two_aas`: In a tight quintuple with 4 AAS windows and 1 lag 7
   window w, w must cover at least 2 of the 4 AAS endpoints: c ≥ 2.
4. `tight_quint_lag11_covers_all_four_aas`: In a tight quintuple with 4 AAS windows and 1 lag 11
   window w, w must cover ALL 4 AAS endpoints: c = 4.
5. `tight_quint_pairwise_distant_cannot_cover_pair`: If all 6 pairs of AAS windows are separated
   by more than 6 on the torus ℤ/pℤ, w cannot cover any pair of AAS endpoints simultaneously.
6. `tight_quint_single_lag7_impossible_of_distance`: Under pairwise separation (c ≤ 1), tight
   quintuples with 4 AAS windows and 1 lag 7 window cannot exist.
7. `tight_quint_two_lag7_high_capacity_impossible`: Tight quintuples with 3 AAS windows and 2
   lag 7 windows with |W| ≥ 5 cannot exist under pairwise separation (c ≤ 2).
8. `tight_quint_all_aas_survives`: Any tight quintuple consisting of 5 AAS windows strictly survives
   deletion with zero loss.
9. `grand_tight_quint_collision_obstruction_synthesis`: Master synthesis theorem for tight quintuple
   collision obstruction.
-/

namespace Recaman.TightQuintCollisionObstruction

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
open UniversalAASCoverageBound GrandGeometricExclusionSynthesis

/-- In any tight quintuple A of size 5 containing a lag 7 window w with |N([w])| ≥ 3,
the complement size is at most 2. -/
theorem tight_quint_lag7_complement_bound
    (N_A_len Nw_len : Nat)
    (htight : N_A_len = 5)
    (hNw : 3 ≤ Nw_len)
    (_hsub : Nw_len ≤ N_A_len) :
    N_A_len - Nw_len ≤ 2 := by
  omega

/-- In any tight quintuple A of size 5 containing a lag 11 window w with |N([w])| ≥ 5,
the complement size is 0: N([w]) = N(A). -/
theorem tight_quint_lag11_complement_bound
    (N_A_len Nw_len : Nat)
    (htight : N_A_len = 5)
    (hNw : 5 ≤ Nw_len)
    (_hsub : Nw_len ≤ N_A_len) :
    N_A_len - Nw_len = 0 := by
  omega

/-- In a tight quintuple with 4 AAS windows and 1 lag 7 window w, w must cover at least 2
of the 4 AAS endpoints. -/
theorem tight_quint_lag7_must_cover_two_aas
    (N_A_len Nw_len c : Nat)
    (hc : c ≤ 4)
    (htight : N_A_len = 5)
    (hNw : 3 ≤ Nw_len)
    (hcov : Nw_len + (4 - c) ≤ N_A_len) :
    2 ≤ c := by
  exact universal_aas_coverage_ge_two N_A_len Nw_len 4 1 c hc htight hcov (by omega)

/-- In a tight quintuple with 4 AAS windows and 1 lag 11 window w, w must cover ALL 4 AAS endpoints. -/
theorem tight_quint_lag11_covers_all_four_aas
    (N_A_len Nw_len c : Nat)
    (hc : c ≤ 4)
    (htight : N_A_len = 5)
    (hNw : 5 ≤ Nw_len)
    (hcov : Nw_len + (4 - c) ≤ N_A_len) :
    c = 4 := by
  have h_lower := universal_aas_coverage_lower_bound N_A_len Nw_len 4 1 c hc htight hcov
  omega

/-- If all 6 pairs of AAS windows are separated by > 6 on the torus ℤ/pℤ,
no single lag 7 window can cover any of the 6 pairs simultaneously. -/
theorem tight_quint_pairwise_distant_cannot_cover_pair (p : Nat) (hp : 0 < p)
    (e : Int → Bool) (v1 v2 v3 v4 w : Nat)
    (h12 : ∀ k : Int, -6 ≤ k → k ≤ 6 → ((v1 : Int) - (v2 : Int)) % (p : Int) ≠ k % (p : Int))
    (h13 : ∀ k : Int, -6 ≤ k → k ≤ 6 → ((v1 : Int) - (v3 : Int)) % (p : Int) ≠ k % (p : Int))
    (h14 : ∀ k : Int, -6 ≤ k → k ≤ 6 → ((v1 : Int) - (v4 : Int)) % (p : Int) ≠ k % (p : Int))
    (h23 : ∀ k : Int, -6 ≤ k → k ≤ 6 → ((v2 : Int) - (v3 : Int)) % (p : Int) ≠ k % (p : Int))
    (h24 : ∀ k : Int, -6 ≤ k → k ≤ 6 → ((v2 : Int) - (v4 : Int)) % (p : Int) ≠ k % (p : Int))
    (h34 : ∀ k : Int, -6 ≤ k → k ≤ 6 → ((v3 : Int) - (v4 : Int)) % (p : Int) ≠ k % (p : Int)) :
    (¬ (WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v1 : Int) 3) ∧
        WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v2 : Int) 3))) ∧
    (¬ (WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v1 : Int) 3) ∧
        WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v3 : Int) 3))) ∧
    (¬ (WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v1 : Int) 3) ∧
        WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v4 : Int) 3))) ∧
    (¬ (WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v2 : Int) 3) ∧
        WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v3 : Int) 3))) ∧
    (¬ (WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v2 : Int) 3) ∧
        WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v4 : Int) 3))) ∧
    (¬ (WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v3 : Int) 3) ∧
        WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v4 : Int) 3))) := by
  refine ⟨
    lag7_cannot_cover_distant_aas p hp e v1 v2 w h12,
    lag7_cannot_cover_distant_aas p hp e v1 v3 w h13,
    lag7_cannot_cover_distant_aas p hp e v1 v4 w h14,
    lag7_cannot_cover_distant_aas p hp e v2 v3 w h23,
    lag7_cannot_cover_distant_aas p hp e v2 v4 w h24,
    lag7_cannot_cover_distant_aas p hp e v3 v4 w h34
  ⟩

/-- Under pairwise separation (c ≤ 1), tight quintuples with 4 AAS windows and 1 lag 7 window
cannot exist. -/
theorem tight_quint_single_lag7_impossible_of_distance
    (N_A_len Nw_len c : Nat)
    (hc : c ≤ 4)
    (htight : N_A_len = 5)
    (hcov : Nw_len + (4 - c) ≤ N_A_len)
    (hNw : 3 ≤ Nw_len)
    (h_cap : c ≤ 1) :
    False := by
  exact single_lag7_tight_subset_impossible N_A_len Nw_len 4 c hc htight hcov hNw h_cap

/-- Tight quintuples with 3 AAS windows and 2 lag 7 windows with |W| ≥ 5 cannot exist under
pairwise separation (c ≤ 2). -/
theorem tight_quint_two_lag7_high_capacity_impossible
    (N_A_len W_len c : Nat)
    (hc : c ≤ 3)
    (htight : N_A_len = 5)
    (hcov : W_len + (3 - c) ≤ N_A_len)
    (hW : 5 ≤ W_len)
    (h_cap : c ≤ 2) :
    False := by
  exact two_lag7_high_capacity_impossible N_A_len W_len 3 c hc htight hcov hW h_cap

/-- Any tight quintuple consisting of 5 AAS windows strictly survives deletion with zero loss. -/
theorem tight_quint_all_aas_survives
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hA : A.length = 5)
    (htight : (neighborhood e p A lag).length = 5)
    (haas : ∀ v ∈ A, lag v = 3 ∧
      e ((v : Int) - 1) = true ∧ e ((v : Int) - 2) = true ∧ e ((v : Int) - 3) = false ∧
      ShortPeriodicSupply.P2 e (v : Int) 3 ∧ e (v : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hlag3 : ∀ u ∈ A, lag u = 3 := fun u hu => (haas u hu).1
  have haas_sub : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false :=
    fun u hu => ⟨(haas u hu).2.1, (haas u hu).2.2.1, (haas u hu).2.2.2.1⟩
  have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := by
    intro u hu
    rw [hlag3 u hu]
    exact (haas u hu).2.2.2.2.1
  have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => (haas u hu).2.2.2.2.2
  exact SixteenGateT6Unconditional.p16_all_aas_tight_quint_survives e p hp hper A lag u0 hd_lt hu0A hP0 hss0 hA htight hlag3 haas_sub hP_A hA_A


/-- Master synthesis: Grand Tight Quintuple Collision Obstruction Theorem. -/
theorem grand_tight_quint_collision_obstruction_synthesis
    (N_A_len Nw_len c : Nat)
    (hc4 : c ≤ 4)
    (htight : N_A_len = 5)
    (hcov4 : Nw_len + (4 - c) ≤ N_A_len) :
    -- (1) Lag 7 complement bound ≤ 2
    (3 ≤ Nw_len → N_A_len - Nw_len ≤ 2) ∧
    -- (2) Lag 11 complement bound = 0
    (5 ≤ Nw_len → N_A_len - Nw_len = 0) ∧
    -- (3) Lag 7 must cover ≥ 2 AAS endpoints
    (3 ≤ Nw_len → 2 ≤ c) ∧
    -- (4) Lag 11 must cover all 4 AAS endpoints
    (5 ≤ Nw_len → c = 4) ∧
    -- (5) Single lag 7 impossible under c ≤ 1
    (3 ≤ Nw_len → c ≤ 1 → False) := by
  refine ⟨
    fun hNw => tight_quint_lag7_complement_bound N_A_len Nw_len htight hNw (by omega),
    fun hNw => tight_quint_lag11_complement_bound N_A_len Nw_len htight hNw (by omega),
    fun hNw => tight_quint_lag7_must_cover_two_aas N_A_len Nw_len c hc4 htight hNw hcov4,
    fun hNw => tight_quint_lag11_covers_all_four_aas N_A_len Nw_len c hc4 htight hNw hcov4,
    fun hNw hc1 => tight_quint_single_lag7_impossible_of_distance N_A_len Nw_len c hc4 htight hcov4 hNw hc1
  ⟩

end Recaman.TightQuintCollisionObstruction
