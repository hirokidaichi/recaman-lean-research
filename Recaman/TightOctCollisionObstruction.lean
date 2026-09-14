import Recaman.TwentyGeometricGateT6Resolution
import Recaman.GrandApexPeriodTwentyTwoTheorem

/-!
# TightOctCollisionObstruction: Geometric Separation Obstructions in Tight Octuples

This module establishes the geometric separation obstructions for window collisions
within tight avoiding octuples A = [v₁, v₂, v₃, v₄, v₅, v₆, v₇, w] of size 8:

1. `tight_oct_lag7_complement_bound`: In any tight octuple A of size 8 containing a lag 7
   window w with |N([w])| ≥ 3, the complement N(A) \ N([w]) has size at most 5.
2. `tight_oct_lag11_complement_bound`: In any tight octuple A of size 8 containing a lag 11
   window w with |N([w])| ≥ 5, the complement size is at most 3.
3. `tight_oct_lag15_complement_bound`: In any tight octuple A of size 8 containing a lag 15
   window w with |N([w])| ≥ 7, the complement size is at most 1.
4. `tight_oct_lag7_must_cover_two_aas`: In a tight octuple with 7 AAS windows and 1 lag 7
   window w, w must cover at least 2 of the 7 AAS endpoints: c ≥ 2.
5. `tight_oct_lag11_must_cover_four_aas`: In a tight octuple with 7 AAS windows and 1 lag 11
   window w, w must cover at least 4 of the 7 AAS endpoints: c ≥ 4.
6. `tight_oct_lag15_must_cover_six_aas`: In a tight octuple with 7 AAS windows and 1 lag 15
   window w, w must cover at least 6 of the 7 AAS endpoints: c ≥ 6.
7. `tight_oct_single_lag7_impossible_of_distance`: Under pairwise separation (c ≤ 1), tight
   octuples with 7 AAS windows and 1 lag 7 window cannot exist.
8. `tight_oct_two_lag7_high_capacity_impossible`: Tight octuples with 6 AAS windows and 2
   lag 7 windows with |W| ≥ 5 cannot exist under pairwise separation (c ≤ 2).
9. `tight_oct_all_aas_survives`: Any tight octuple consisting of 8 AAS windows strictly survives
   deletion with zero loss.
10. `grand_tight_oct_collision_obstruction_synthesis`: Master synthesis theorem for tight octuple
    collision obstruction.
-/

namespace Recaman.TightOctCollisionObstruction

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
open TightSeptCollisionObstruction TwentyGeometricGateT6Resolution

/-- In any tight octuple A of size 8 containing a lag 7 window w with |N([w])| ≥ 3,
the complement size is at most 5. -/
theorem tight_oct_lag7_complement_bound
    (N_A_len Nw_len : Nat)
    (htight : N_A_len = 8)
    (hNw : 3 ≤ Nw_len)
    (_hsub : Nw_len ≤ N_A_len) :
    N_A_len - Nw_len ≤ 5 := by
  omega

/-- In any tight octuple A of size 8 containing a lag 11 window w with |N([w])| ≥ 5,
the complement size is at most 3. -/
theorem tight_oct_lag11_complement_bound
    (N_A_len Nw_len : Nat)
    (htight : N_A_len = 8)
    (hNw : 5 ≤ Nw_len)
    (_hsub : Nw_len ≤ N_A_len) :
    N_A_len - Nw_len ≤ 3 := by
  omega

/-- In any tight octuple A of size 8 containing a lag 15 window w with |N([w])| ≥ 7,
the complement size is at most 1. -/
theorem tight_oct_lag15_complement_bound
    (N_A_len Nw_len : Nat)
    (htight : N_A_len = 8)
    (hNw : 7 ≤ Nw_len)
    (_hsub : Nw_len ≤ N_A_len) :
    N_A_len - Nw_len ≤ 1 := by
  omega

/-- In a tight octuple with 7 AAS windows and 1 lag 7 window w, w must cover at least 2
of the 7 AAS endpoints. -/
theorem tight_oct_lag7_must_cover_two_aas
    (N_A_len Nw_len c : Nat)
    (hc : c ≤ 7)
    (htight : N_A_len = 8)
    (hNw : 3 ≤ Nw_len)
    (hcov : Nw_len + (7 - c) ≤ N_A_len) :
    2 ≤ c := by
  exact universal_aas_coverage_ge_two N_A_len Nw_len 7 1 c hc htight hcov (by omega)

/-- In a tight octuple with 7 AAS windows and 1 lag 11 window w, w must cover at least 4
of the 7 AAS endpoints. -/
theorem tight_oct_lag11_must_cover_four_aas
    (N_A_len Nw_len c : Nat)
    (hc : c ≤ 7)
    (htight : N_A_len = 8)
    (hNw : 5 ≤ Nw_len)
    (hcov : Nw_len + (7 - c) ≤ N_A_len) :
    4 ≤ c := by
  have h_lower := universal_aas_coverage_lower_bound N_A_len Nw_len 7 1 c hc htight hcov
  omega

/-- In a tight octuple with 7 AAS windows and 1 lag 15 window w, w must cover at least 6
of the 7 AAS endpoints. -/
theorem tight_oct_lag15_must_cover_six_aas
    (N_A_len Nw_len c : Nat)
    (hc : c ≤ 7)
    (htight : N_A_len = 8)
    (hNw : 7 ≤ Nw_len)
    (hcov : Nw_len + (7 - c) ≤ N_A_len) :
    6 ≤ c := by
  have h_lower := universal_aas_coverage_lower_bound N_A_len Nw_len 7 1 c hc htight hcov
  omega

/-- Under pairwise separation (c ≤ 1), tight octuples with 7 AAS windows and 1 lag 7 window
cannot exist. -/
theorem tight_oct_single_lag7_impossible_of_distance
    (N_A_len Nw_len c : Nat)
    (hc : c ≤ 7)
    (htight : N_A_len = 8)
    (hcov : Nw_len + (7 - c) ≤ N_A_len)
    (hNw : 3 ≤ Nw_len)
    (h_cap : c ≤ 1) :
    False := by
  exact single_lag7_tight_subset_impossible N_A_len Nw_len 7 c hc htight hcov hNw h_cap

/-- Tight octuples with 6 AAS windows and 2 lag 7 windows with |W| ≥ 5 cannot exist under
pairwise separation (c ≤ 2). -/
theorem tight_oct_two_lag7_high_capacity_impossible
    (N_A_len W_len c : Nat)
    (hc : c ≤ 6)
    (htight : N_A_len = 8)
    (hcov : W_len + (6 - c) ≤ N_A_len)
    (hW : 5 ≤ W_len)
    (h_cap : c ≤ 2) :
    False := by
  exact two_lag7_high_capacity_impossible N_A_len W_len 6 c hc htight hcov hW h_cap

/-- Any tight octuple of size 8 consisting purely of lag 3 AAS windows strictly survives
deletion with zero loss. -/
theorem tight_oct_all_aas_survives
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hA : A.length = 8)
    (htight : (neighborhood e p A lag).length = 8)
    (haas : ∀ v ∈ A, lag v = 3 ∧
      e ((v : Int) - 1) = true ∧ e ((v : Int) - 2) = true ∧ e ((v : Int) - 3) = false ∧
      ShortPeriodicSupply.P2 e (v : Int) 3 ∧ e (v : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hAk : A.length ≤ 8 := by omega
  have htight_eq : (neighborhood e p A lag).length = A.length := by rw [hA, htight]
  have hlag3 : ∀ u ∈ A, lag u = 3 := fun u hu => (haas u hu).1
  have haas_sub : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false :=
    fun u hu => ⟨(haas u hu).2.1, (haas u hu).2.2.1, (haas u hu).2.2.2.1⟩
  have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := by
    intro u hu
    rw [hlag3 u hu]
    exact (haas u hu).2.2.2.2.1
  have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => (haas u hu).2.2.2.2.2
  exact apex22_all_aas_survival_up_to_eight e p hp hper A lag u0 hd_lt hu0A hP0 hss0 hAk htight_eq hlag3 haas_sub hP_A hA_A

/-- Master synthesis: Grand Tight Octuple Collision Obstruction Theorem. -/
theorem grand_tight_oct_collision_obstruction_synthesis
    (N_A_len Nw_len c : Nat)
    (hc7 : c ≤ 7)
    (htight : N_A_len = 8)
    (hcov7 : Nw_len + (7 - c) ≤ N_A_len) :
    -- (1) Lag 7 complement bound ≤ 5
    (3 ≤ Nw_len → N_A_len - Nw_len ≤ 5) ∧
    -- (2) Lag 11 complement bound ≤ 3
    (5 ≤ Nw_len → N_A_len - Nw_len ≤ 3) ∧
    -- (3) Lag 15 complement bound ≤ 1
    (7 ≤ Nw_len → N_A_len - Nw_len ≤ 1) ∧
    -- (4) Lag 7 must cover ≥ 2 AAS endpoints
    (3 ≤ Nw_len → 2 ≤ c) ∧
    -- (5) Lag 11 must cover ≥ 4 AAS endpoints
    (5 ≤ Nw_len → 4 ≤ c) ∧
    -- (6) Lag 15 must cover ≥ 6 AAS endpoints
    (7 ≤ Nw_len → 6 ≤ c) ∧
    -- (7) Single lag 7 impossible under c ≤ 1
    (3 ≤ Nw_len → c ≤ 1 → False) := by
  refine ⟨
    fun hNw => tight_oct_lag7_complement_bound N_A_len Nw_len htight hNw (by omega),
    fun hNw => tight_oct_lag11_complement_bound N_A_len Nw_len htight hNw (by omega),
    fun hNw => tight_oct_lag15_complement_bound N_A_len Nw_len htight hNw (by omega),
    fun hNw => tight_oct_lag7_must_cover_two_aas N_A_len Nw_len c hc7 htight hNw hcov7,
    fun hNw => tight_oct_lag11_must_cover_four_aas N_A_len Nw_len c hc7 htight hNw hcov7,
    fun hNw => tight_oct_lag15_must_cover_six_aas N_A_len Nw_len c hc7 htight hNw hcov7,
    fun hNw hc1 => tight_oct_single_lag7_impossible_of_distance N_A_len Nw_len c hc7 htight hcov7 hNw hc1
  ⟩

end Recaman.TightOctCollisionObstruction
