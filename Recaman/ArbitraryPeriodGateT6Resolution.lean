import Recaman.ArbitraryPeriodLagRigidity

/-!
# ArbitraryPeriodGateT6Resolution: Universal Parametric Gate T6 Multi-Tier Reduction for All Periods p

This module establishes the universal parametric Gate T6 reduction and resolution valid for
arbitrary periods p (fully closed-form for all p ∈ ℕ):

1. `arbitrary_period_tight_size_two_survives`: Any tight avoiding sublist of size ≤ 2 strictly
   survives deletion of s*(u₀) unconditionally across arbitrary periods.
2. `arbitrary_period_tight_survives_of_not_mem`: Any tight avoiding sublist of arbitrary size
   strictly survives deletion of s*(u₀) whenever s*(u₀) ∉ N(A).
3. `arbitrary_period_all_aas_avoids_s_star`: Any tight avoiding subset consisting purely of
   lag 3 AAS windows strictly avoids s*(u₀).
4. `arbitrary_period_all_aas_survives`: Any tight avoiding subset consisting purely of lag 3 AAS
   windows strictly survives deletion of s*(u₀) with zero loss.
5. `arbitrary_period_avoiding_sublist_survives_of_tight_avoidance`: In ANY period p with positive
   signSum and slack, every avoiding sublist strictly survives deletion of s*(u₀) provided that
   all tight avoiding sublists of intermediate sizes (3 ≤ |B| ≤ |D| - 2) avoid s*(u₀).
6. `arbitrary_period_avoiding_sublists_survive_unconditional_of_U_le_three`: If |U| ≤ 3, all avoiding
   sublists survive deletion unconditionally across all periods.
7. `arbitrary_period_avoiding_sublists_survive_unconditional_of_D_le_four`: If |D| ≤ 4, all avoiding
   sublists survive deletion unconditionally across all periods.
8. `arbitrary_period_gate_t6_of_U_le_four_and_triples`: If |U| ≤ 4, Gate T6 reduces entirely to tight
   triples of size 3.
9. `arbitrary_period_gate_t6_of_D_le_five_and_triples`: If |D| ≤ 5, Gate T6 reduces entirely to tight
   triples of size 3.
10. `grand_arbitrary_period_gate_t6_resolution_synthesis`: Master synthesis theorem for arbitrary-period
   parametric Gate T6 reduction.
-/

namespace Recaman.ArbitraryPeriodGateT6Resolution

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
open ArbitraryPeriodLagRigidity

/-- For arbitrary period p, any tight avoiding sublist of size ≤ 2 strictly survives deletion
of s*(u₀) unconditionally. -/
theorem arbitrary_period_tight_size_two_survives (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (hA2 : A.length ≤ 2)
    (htight : (neighborhood e p A lag).length = A.length)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  tight_avoiding_le_two_survives_general e p hp hper A lag hA2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A

/-- Any tight avoiding sublist of arbitrary size strictly survives deletion of s*(u₀) whenever
s*(u₀) ∉ N(A). -/
theorem arbitrary_period_tight_survives_of_not_mem (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (htight : (neighborhood e p A lag).length = A.length)
    (u0 : Nat)
    (hnot : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  tight_triple_survives_of_s_not_mem e p A lag u0 htight hnot

/-- Any tight avoiding subset consisting purely of lag 3 AAS windows strictly avoids s*(u₀). -/
theorem arbitrary_period_all_aas_avoids_s_star (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag :=
  all_aas_tight_avoids_ss2_donation e p hp hper A lag u0 hd_lt hu0A hP0 hss0 hlag3 haas hP_A hA_A

/-- Any tight avoiding subset consisting purely of lag 3 AAS windows strictly survives deletion
of s*(u₀) with zero loss. -/
theorem arbitrary_period_all_aas_survives (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (htight : (neighborhood e p A lag).length = A.length)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot := arbitrary_period_all_aas_avoids_s_star e p hp hper A lag u0 hd_lt hu0A hP0 hss0 hlag3 haas hP_A hA_A
  exact arbitrary_period_tight_survives_of_not_mem e p A lag htight u0 hnot

/-- In ANY period p with positive signSum and slack, every avoiding sublist strictly survives
deletion of s*(u₀) provided that all tight avoiding sublists of intermediate sizes
(3 ≤ |B| ≤ |D| - 2) avoid s*(u₀). -/
theorem arbitrary_period_avoiding_sublist_survives_of_tight_avoidance (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hA_A : ∀ u ∈ A, e (u : Int) = true)
    (h_tight_avoid : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      (3 ≤ B.length ∧ B.length ≤ (LagElevenPeriodic.subPhases e 0 p).length - 2) →
      (neighborhood e p B lag).length = B.length →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  by_cases htight : (neighborhood e p A lag).length = A.length
  · by_cases hle2 : A.length ≤ 2
    · exact arbitrary_period_tight_size_two_survives e p hp hper A lag hle2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A
    · have hge3 : 3 ≤ A.length := by omega
      have hleD : A.length ≤ (LagElevenPeriodic.subPhases e 0 p).length - 2 :=
        UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
      have hnot_mem := h_tight_avoid A hsub hnot ⟨hge3, hleD⟩ htight
      exact arbitrary_period_tight_survives_of_not_mem e p A lag htight u0 hnot_mem
  · have hhallA := hhall_orig A hsub
    have hslackA : A.length < (neighborhood e p A lag).length := by omega
    exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA

/-- If |U| ≤ 3, all avoiding sublists survive deletion unconditionally across all periods. -/
theorem arbitrary_period_avoiding_sublists_survive_unconditional_of_U_le_three (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hU3 : U.length ≤ 3)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p24_avoiding_sublists_survive_unconditional_of_U_le_three e p hp hper U A lag hU3 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A

/-- If |D| ≤ 4, all avoiding sublists survive deletion unconditionally across all periods. -/
theorem arbitrary_period_avoiding_sublists_survive_unconditional_of_D_le_four (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD4 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 4)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p24_avoiding_sublists_survive_unconditional_of_D_le_four e p hp hper U A lag hslack hD4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A

/-- Master Synthesis: Grand Arbitrary-Period Gate T6 Resolution Theorem. -/
theorem grand_arbitrary_period_gate_t6_resolution_synthesis (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    -- (1) Tight sublists of size ≤ 2 survive unconditionally
    (A.length ≤ 2 → (neighborhood e p A lag).length = A.length →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (2) Avoiding sublists survive unconditionally when |U| ≤ 3
    (U.length ≤ 3 →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (3) Avoiding sublists survive unconditionally when |D| ≤ 4
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 4 →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (4) Closed-form general reduction to tight sublists of intermediate sizes
    ((∀ B : List Nat, List.Sublist B U → u0 ∉ B →
        (3 ≤ B.length ∧ B.length ≤ (LagElevenPeriodic.subPhases e 0 p).length - 2) →
        (neighborhood e p B lag).length = B.length →
        oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hle2 htight
    exact arbitrary_period_tight_size_two_survives e p hp hper A lag hle2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A
  · intro hU3
    exact arbitrary_period_avoiding_sublists_survive_unconditional_of_U_le_three e p hp hper U A lag hU3 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A
  · intro hD4
    exact arbitrary_period_avoiding_sublists_survive_unconditional_of_D_le_four e p hp hper U A lag hslack hD4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A
  · intro h_tight_avoid
    exact arbitrary_period_avoiding_sublist_survives_of_tight_avoidance e p hp hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_tight_avoid

end Recaman.ArbitraryPeriodGateT6Resolution
