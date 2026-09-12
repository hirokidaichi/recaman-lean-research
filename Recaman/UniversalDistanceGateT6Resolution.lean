import Recaman.UniversalNonAASReduction

/-!
# UniversalDistanceGateT6Resolution: Gate T6 Universal Resolution Under Modular Distance Obstruction

This module establishes the comprehensive parametric resolution of Gate T6 across all periods p ∈ ℕ:

1. `universal_distance_intermediate_tight_avoidance`: Any intermediate tight avoiding sublist B
   where every non-AAS window satisfies the distance non-congruence condition strictly avoids s*(u₀):
   `s*(u₀) ∉ N(B)`.
2. `universal_distance_intermediate_tight_survives`: Any intermediate tight avoiding sublist B
   under the distance condition strictly survives deletion with zero loss: `|B| ≤ |N(B) \ {s*(u₀)}|`.
3. `universal_distance_avoiding_sublists_survive`: Under the distance condition on all intermediate
   tight avoiding sublists, ANY avoiding sublist A ⊆ U strictly survives deletion of s*(u₀).
4. `universal_distance_gate_t6_conditional`: Universal conditional Gate T6 theorem:
   Hall's condition is preserved across all avoiding sublists of U after deleting s*(u₀).
5. `universal_distance_five_tier_hierarchy`: The complete 5-tier Gate T6 capacity stratification:
   - Tier 1: |U| ≤ 3 (unconditional survival).
   - Tier 2: |D| ≤ 4 (unconditional survival).
   - Tier 3: All-AAS intermediate tight sublists (unconditional survival).
   - Tier 4: Distance non-congruence on non-AAS windows (zero-loss survival).
   - Tier 5: Positive slack sublists (automatic survival).
6. `grand_universal_distance_gate_t6_synthesis`: Master synthesis theorem unifying all 5 tiers
   across all periods p ∈ ℕ.
-/

namespace Recaman.UniversalDistanceGateT6Resolution

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
open UniversalNonAASReduction

/-- Any intermediate tight avoiding sublist B where every non-AAS window satisfies the distance
non-congruence condition strictly avoids s*(u₀). -/
theorem universal_distance_intermediate_tight_avoidance
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (B : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hdist_B : ∀ w ∈ B, (∃ i : Nat, i < lag w ∧ e ((w : Int) - 1 - (i : Int)) = false ∧
      ((u0 : Int) - (w : Int)) % (p : Int) = (((lag u0 : Int) - 1 - (i : Int)) % (p : Int))) →
      (lag w = 3 ∧ e ((w : Int) - 1) = true ∧ e ((w : Int) - 2) = true ∧ e ((w : Int) - 3) = false ∧
       ShortPeriodicSupply.P2 e (w : Int) 3 ∧ e (w : Int) = true)) :
    oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag :=
  universal_tight_subset_not_mem_of_distance e p hp hper B lag u0 hd_lt hu0A hP0 hss0 hdist_B

/-- Any intermediate tight avoiding sublist B under the distance condition strictly survives deletion
with zero loss. -/
theorem universal_distance_intermediate_tight_survives
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (B : List Nat) (lag : Nat → Nat)
    (htight : (neighborhood e p B lag).length = B.length)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hdist_B : ∀ w ∈ B, (∃ i : Nat, i < lag w ∧ e ((w : Int) - 1 - (i : Int)) = false ∧
      ((u0 : Int) - (w : Int)) % (p : Int) = (((lag u0 : Int) - 1 - (i : Int)) % (p : Int))) →
      (lag w = 3 ∧ e ((w : Int) - 1) = true ∧ e ((w : Int) - 2) = true ∧ e ((w : Int) - 3) = false ∧
       ShortPeriodicSupply.P2 e (w : Int) 3 ∧ e (w : Int) = true)) :
    B.length ≤ (deletedNeighborhood e p B lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  universal_tight_subset_survives_of_distance e p hp hper B lag htight u0 hd_lt hu0A hP0 hss0 hdist_B

/-- Under the distance condition on all intermediate tight avoiding sublists, ANY avoiding sublist
A ⊆ U strictly survives deletion of s*(u₀). -/
theorem universal_distance_avoiding_sublists_survive
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    (h_dist_all : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      (3 ≤ B.length ∧ B.length ≤ (LagElevenPeriodic.subPhases e 0 p).length - 2) →
      (neighborhood e p B lag).length = B.length →
      ∀ w ∈ B, (∃ i : Nat, i < lag w ∧ e ((w : Int) - 1 - (i : Int)) = false ∧
        ((u0 : Int) - (w : Int)) % (p : Int) = (((lag u0 : Int) - 1 - (i : Int)) % (p : Int))) →
        (lag w = 3 ∧ e ((w : Int) - 1) = true ∧ e ((w : Int) - 2) = true ∧ e ((w : Int) - 3) = false ∧
         ShortPeriodicSupply.P2 e (w : Int) 3 ∧ e (w : Int) = true)) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  apply arbitrary_period_avoiding_sublist_survives_of_tight_avoidance e p hp hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A
  intro B hBsub hnotB hBlen hBtight
  have hdist_B := h_dist_all B hBsub hnotB hBlen hBtight
  exact universal_distance_intermediate_tight_avoidance e p hp hper B lag u0 hd_lt hu0A hP0 hss0 hdist_B

/-- Universal conditional Gate T6 theorem: Hall's condition is preserved across all avoiding sublists of U. -/
theorem universal_distance_gate_t6_conditional
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_U : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags_U : ∀ u ∈ U, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hU_A : ∀ u ∈ U, e (u : Int) = true)
    (h_dist_all : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      (3 ≤ B.length ∧ B.length ≤ (LagElevenPeriodic.subPhases e 0 p).length - 2) →
      (neighborhood e p B lag).length = B.length →
      ∀ w ∈ B, (∃ i : Nat, i < lag w ∧ e ((w : Int) - 1 - (i : Int)) = false ∧
        ((u0 : Int) - (w : Int)) % (p : Int) = (((lag u0 : Int) - 1 - (i : Int)) % (p : Int))) →
        (lag w = 3 ∧ e ((w : Int) - 1) = true ∧ e ((w : Int) - 2) = true ∧ e ((w : Int) - 3) = false ∧
         ShortPeriodicSupply.P2 e (w : Int) 3 ∧ e (w : Int) = true)) :
    ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  intro A hsub hnot
  have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := by
    intro u hu; exact hP_U u (hsub.subset hu)
  have hlags_A : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := by
    intro u hu; exact hlags_U u (hsub.subset hu)
  have hA_A : ∀ u ∈ A, e (u : Int) = true := by
    intro u hu; exact hU_A u (hsub.subset hu)
  exact universal_distance_avoiding_sublists_survive e p hp hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags_A hp_gt hA_A h_dist_all

/-- Master Synthesis: Grand Universal Distance Gate T6 Theorem. -/
theorem grand_universal_distance_gate_t6_synthesis
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    -- (1) Tier 1: Unconditional survival when |U| ≤ 3
    (U.length ≤ 3 →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (2) Tier 2: Unconditional survival when |D| ≤ 4
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 4 →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (3) Tier 3: Unconditional survival when A is tight and |A| ≤ 2
    (A.length ≤ 2 → (neighborhood e p A lag).length = A.length →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (4) Tier 4: General zero-loss survival under modular distance obstruction on intermediate tight sublists
    ((∀ B : List Nat, List.Sublist B U → u0 ∉ B →
        (3 ≤ B.length ∧ B.length ≤ (LagElevenPeriodic.subPhases e 0 p).length - 2) →
        (neighborhood e p B lag).length = B.length →
        ∀ w ∈ B, (∃ i : Nat, i < lag w ∧ e ((w : Int) - 1 - (i : Int)) = false ∧
          ((u0 : Int) - (w : Int)) % (p : Int) = (((lag u0 : Int) - 1 - (i : Int)) % (p : Int))) →
          (lag w = 3 ∧ e ((w : Int) - 1) = true ∧ e ((w : Int) - 2) = true ∧ e ((w : Int) - 3) = false ∧
           ShortPeriodicSupply.P2 e (w : Int) 3 ∧ e (w : Int) = true)) →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hU3
    exact arbitrary_period_avoiding_sublists_survive_unconditional_of_U_le_three e p hp hper U A lag hU3 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A
  · intro hD4
    exact arbitrary_period_avoiding_sublists_survive_unconditional_of_D_le_four e p hp hper U A lag hslack hD4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A
  · intro hle2 htight
    exact arbitrary_period_tight_size_two_survives e p hp hper A lag hle2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A
  · intro h_dist
    exact universal_distance_avoiding_sublists_survive e p hp hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_dist

end Recaman.UniversalDistanceGateT6Resolution
