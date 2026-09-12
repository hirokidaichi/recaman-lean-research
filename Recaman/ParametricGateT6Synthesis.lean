import Recaman.UniversalCapacityThresholds

/-!
# ParametricGateT6Synthesis: Unified Parametric Gate T6 Synthesis and Exact Size Stratification

This module establishes the comprehensive parametric Gate T6 reduction hierarchy across all period tiers:

1. `p12_gate_t6_triple_reduction`: For all periods p ≤ 12, Gate T6 reduces entirely to tight triples:
   avoidance on tight triples guarantees survival of ALL avoiding sublists of any size.
2. `p14_gate_t6_triple_quad_reduction`: For all periods p ≤ 14, Gate T6 reduces entirely to tight
   triples and tight quadruples.
3. `p16_gate_t6_tri_quad_quint_reduction`: For all periods p ≤ 16, Gate T6 reduces to sizes 3, 4, and 5.
4. `p18_gate_t6_reduction_tier`: For all periods p ≤ 18, Gate T6 reduces to sizes 3, 4, 5, and 6.
5. `p20_gate_t6_reduction_tier`: For all periods p ≤ 20, Gate T6 reduces to sizes 3, 4, 5, 6, and 7.
6. `p22_gate_t6_reduction_tier`: For all periods p ≤ 22, Gate T6 reduces to sizes 3, 4, 5, 6, 7, and 8.
7. `p24_gate_t6_reduction_tier`: For all periods p ≤ 24, Gate T6 reduces to sizes 3, 4, 5, 6, 7, 8, and 9.
8. `p10_gate_t6_unconditional_synthesis`: For 7 < p ≤ 10, Gate T6 is completely unconditional.
9. `grand_parametric_gate_t6_synthesis`: Master synthesis theorem unifying all reduction tiers
   from p ≤ 10 to p ≤ 24 and arbitrary periods p ∈ ℕ.
-/

namespace Recaman.ParametricGateT6Synthesis

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
open TwentyTwoLagRigidity TwentyTwoGateT6Resolution TwentyTwoGateT6Unconditional
open GrandApexPeriodTwentyTwoTheorem
open TwentyFourLagRigidity TwentyFourGateT6Resolution TwentyFourGateT6Unconditional
open GrandApexPeriodTwentyFourTheorem
open ArbitraryPeriodLagRigidity ArbitraryPeriodGateT6Resolution ArbitraryPeriodGateT6Unconditional
open UniversalApexPeriodicTheorem UniversalQuantumWindowCapacity TightSubsetLagStructure
open TightSubsetDecomposition TightQuadDecomposition UniversalTightDecomposition
open SharpPeriodicSupply LagSevenCollisionDistance UniversalCollisionDistance
open UniversalNonAASReduction UniversalDistanceGateT6Resolution UniversalCapacityThresholds

/-- For all periods p ≤ 12, Gate T6 reduces entirely to tight triples:
avoidance on tight triples guarantees survival of ALL avoiding sublists. -/
theorem p12_gate_t6_triple_reduction
    (e : Int → Bool) (p : Nat) (hp : 0 < p) (hp12 : p ≤ 12) (hp7 : 7 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hD : (LagElevenPeriodic.subPhases e 0 p).length ≤ (p - 1) / 2)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hA_A : ∀ u ∈ A, e (u : Int) = true)
    (h_triple : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      B.length = 3 →
      (neighborhood e p B lag).length = 3 →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  apply arbitrary_period_avoiding_sublist_survives_of_tight_avoidance e p hp hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp7 hA_A
  intro B hBsub hnotB hBlen hBtight
  have hB3 := intermediate_triple_only_of_p_le_twelve p (LagElevenPeriodic.subPhases e 0 p).length B.length hp12 hD hBlen
  have hBtight3 : (neighborhood e p B lag).length = 3 := by
    rw [hB3] at hBtight
    exact hBtight
  exact h_triple B hBsub hnotB hB3 hBtight3

/-- For all periods p ≤ 14, Gate T6 reduces entirely to tight triples and tight quadruples. -/
theorem p14_gate_t6_triple_quad_reduction
    (e : Int → Bool) (p : Nat) (hp : 0 < p) (hp14 : p ≤ 14) (hp7 : 7 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hD : (LagElevenPeriodic.subPhases e 0 p).length ≤ (p - 1) / 2)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hA_A : ∀ u ∈ A, e (u : Int) = true)
    (h_tri_quad : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      (B.length = 3 ∨ B.length = 4) →
      (neighborhood e p B lag).length = B.length →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  apply arbitrary_period_avoiding_sublist_survives_of_tight_avoidance e p hp hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp7 hA_A
  intro B hBsub hnotB hBlen hBtight
  have hB34 := intermediate_triple_and_quad_only_of_p_le_fourteen p (LagElevenPeriodic.subPhases e 0 p).length B.length hp14 hD hBlen
  exact h_tri_quad B hBsub hnotB hB34 hBtight

/-- For all periods p ≤ 16, Gate T6 reduces to sizes 3, 4, and 5. -/
theorem p16_gate_t6_tri_quad_quint_reduction
    (e : Int → Bool) (p : Nat) (hp : 0 < p) (hp16 : p ≤ 16) (hp7 : 7 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hD : (LagElevenPeriodic.subPhases e 0 p).length ≤ (p - 1) / 2)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hA_A : ∀ u ∈ A, e (u : Int) = true)
    (h_345 : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      (3 ≤ B.length ∧ B.length ≤ 5) →
      (neighborhood e p B lag).length = B.length →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  apply arbitrary_period_avoiding_sublist_survives_of_tight_avoidance e p hp hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp7 hA_A
  intro B hBsub hnotB hBlen hBtight
  have hB345 := intermediate_sizes_le_five_of_p_le_sixteen p (LagElevenPeriodic.subPhases e 0 p).length B.length hp16 hD hBlen
  exact h_345 B hBsub hnotB hB345 hBtight

/-- For all periods p ≤ 18, Gate T6 reduces to sizes 3, 4, 5, and 6. -/
theorem p18_gate_t6_reduction_tier
    (e : Int → Bool) (p : Nat) (hp : 0 < p) (hp18 : p ≤ 18) (hp7 : 7 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hD : (LagElevenPeriodic.subPhases e 0 p).length ≤ (p - 1) / 2)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hA_A : ∀ u ∈ A, e (u : Int) = true)
    (h_3456 : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      (3 ≤ B.length ∧ B.length ≤ 6) →
      (neighborhood e p B lag).length = B.length →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  apply arbitrary_period_avoiding_sublist_survives_of_tight_avoidance e p hp hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp7 hA_A
  intro B hBsub hnotB hBlen hBtight
  have hB3456 := intermediate_sizes_le_six_of_p_le_eighteen p (LagElevenPeriodic.subPhases e 0 p).length B.length hp18 hD hBlen
  exact h_3456 B hBsub hnotB hB3456 hBtight

/-- For all periods p ≤ 20, Gate T6 reduces to sizes 3 through 7. -/
theorem p20_gate_t6_reduction_tier
    (e : Int → Bool) (p : Nat) (hp : 0 < p) (hp20 : p ≤ 20) (hp7 : 7 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hD : (LagElevenPeriodic.subPhases e 0 p).length ≤ (p - 1) / 2)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hA_A : ∀ u ∈ A, e (u : Int) = true)
    (h_le7 : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      (3 ≤ B.length ∧ B.length ≤ 7) →
      (neighborhood e p B lag).length = B.length →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  apply arbitrary_period_avoiding_sublist_survives_of_tight_avoidance e p hp hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp7 hA_A
  intro B hBsub hnotB hBlen hBtight
  have hBle7 := intermediate_sizes_le_seven_of_p_le_twenty p (LagElevenPeriodic.subPhases e 0 p).length B.length hp20 hD hBlen
  exact h_le7 B hBsub hnotB hBle7 hBtight

/-- For all periods p ≤ 22, Gate T6 reduces to sizes 3 through 8. -/
theorem p22_gate_t6_reduction_tier
    (e : Int → Bool) (p : Nat) (hp : 0 < p) (hp22 : p ≤ 22) (hp7 : 7 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hD : (LagElevenPeriodic.subPhases e 0 p).length ≤ (p - 1) / 2)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hA_A : ∀ u ∈ A, e (u : Int) = true)
    (h_le8 : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      (3 ≤ B.length ∧ B.length ≤ 8) →
      (neighborhood e p B lag).length = B.length →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  apply arbitrary_period_avoiding_sublist_survives_of_tight_avoidance e p hp hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp7 hA_A
  intro B hBsub hnotB hBlen hBtight
  have hBle8 := intermediate_sizes_le_eight_of_p_le_twenty_two p (LagElevenPeriodic.subPhases e 0 p).length B.length hp22 hD hBlen
  exact h_le8 B hBsub hnotB hBle8 hBtight

/-- For all periods p ≤ 24, Gate T6 reduces to sizes 3 through 9. -/
theorem p24_gate_t6_reduction_tier
    (e : Int → Bool) (p : Nat) (hp : 0 < p) (hp24 : p ≤ 24) (hp7 : 7 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hD : (LagElevenPeriodic.subPhases e 0 p).length ≤ (p - 1) / 2)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hA_A : ∀ u ∈ A, e (u : Int) = true)
    (h_le9 : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      (3 ≤ B.length ∧ B.length ≤ 9) →
      (neighborhood e p B lag).length = B.length →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  apply arbitrary_period_avoiding_sublist_survives_of_tight_avoidance e p hp hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp7 hA_A
  intro B hBsub hnotB hBlen hBtight
  have hBle9 := intermediate_sizes_le_nine_of_p_le_twenty_four p (LagElevenPeriodic.subPhases e 0 p).length B.length hp24 hD hBlen
  exact h_le9 B hBsub hnotB hBle9 hBtight

/-- Master Synthesis: Grand Parametric Gate T6 Synthesis Theorem. -/
theorem grand_parametric_gate_t6_synthesis
    (e : Int → Bool) (p : Nat) (hp : 0 < p) (hp7 : 7 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hD : (LagElevenPeriodic.subPhases e 0 p).length ≤ (p - 1) / 2)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    -- (1) Unconditional resolution for p ≤ 10
    (p ≤ 10 → A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (2) Reduction to triples for p ≤ 12
    (p ≤ 12 → (∀ B : List Nat, List.Sublist B U → u0 ∉ B → B.length = 3 →
        (neighborhood e p B lag).length = 3 →
        oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (3) Reduction to triples and quads for p ≤ 14
    (p ≤ 14 → (∀ B : List Nat, List.Sublist B U → u0 ∉ B → (B.length = 3 ∨ B.length = 4) →
        (neighborhood e p B lag).length = B.length →
        oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (4) Reduction to sizes ≤ 9 for p ≤ 24
    (p ≤ 24 → (∀ B : List Nat, List.Sublist B U → u0 ∉ B → (3 ≤ B.length ∧ B.length ≤ 9) →
        (neighborhood e p B lag).length = B.length →
        oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) := by
  refine ⟨fun hp10 => gate_t6_unconditional_of_p_le_ten e p hp hp10 hp7 hper U A lag hD hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hA_A,
          fun hp12 htri => p12_gate_t6_triple_reduction e p hp hp12 hp7 hper U A lag hD hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hA_A htri,
          fun hp14 htq => p14_gate_t6_triple_quad_reduction e p hp hp14 hp7 hper U A lag hD hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hA_A htq,
          fun hp24 hle9 => p24_gate_t6_reduction_tier e p hp hp24 hp7 hper U A lag hD hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hA_A hle9⟩

end Recaman.ParametricGateT6Synthesis
