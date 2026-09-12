import Recaman.TightQuadDecomposition

/-!
# UniversalTightDecomposition: Universal AAS and Non-AAS Collision Decomposition

This module formalizes the universal structural decomposition of tight avoiding subsets of
arbitrary size |A| into AAS and non-AAS window components:

1. `universal_mem_neighborhood_iff`: A subtraction phase belongs to N(A) iff it belongs to
   N([u]) for some u ∈ A, for arbitrary subsets A.
2. `universal_non_aas_witness`: Any witness window covering s*(u₀) in any subset A cannot be
   a lag 3 AAS window.
3. `universal_all_aas_avoids`: Any subset A consisting purely of lag 3 AAS windows strictly
   avoids s*(u₀), regardless of size.
4. `universal_all_aas_survives`: Any tight subset A consisting purely of lag 3 AAS windows
   strictly survives deletion with zero loss: |A| ≤ |N(A) \ {s*(u₀)}|.
5. `universal_single_non_aas_collision_iff`: For any subset A where all elements except a single
   element w are lag 3 AAS, s*(u₀) ∈ N(A) ↔ s*(u₀) ∈ N([w]).
6. `universal_single_non_aas_survives`: For any tight subset A where all elements except w are
   lag 3 AAS, if s*(u₀) ∉ N([w]), then A strictly survives deletion.
7. `universal_two_non_aas_collision_iff`: For any subset A where all elements except w₁, w₂ are
   lag 3 AAS, s*(u₀) ∈ N(A) ↔ (s*(u₀) ∈ N([w₁]) ∨ s*(u₀) ∈ N([w₂])).
8. `universal_two_non_aas_survives`: For any tight subset A where all elements except w₁, w₂ are
   lag 3 AAS, if neither w₁ nor w₂ covers s*(u₀), then A strictly survives deletion.
9. `universal_hall_preservation_of_slack_or_not_mem`: General Hall preservation principle:
   any subset with slack |A| < |N(A)| or avoiding s strictly preserves Hall's condition.
10. `grand_universal_tight_decomposition_synthesis`: Master universal decomposition synthesis.
-/

namespace Recaman.UniversalTightDecomposition

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
open TightSubsetDecomposition TightQuadDecomposition

/-- A subtraction phase belongs to N(A) iff it belongs to N([u]) for some u ∈ A, for arbitrary subsets A. -/
theorem universal_mem_neighborhood_iff (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat) (s : Nat) :
    s ∈ neighborhood e p A lag ↔ ∃ u ∈ A, s ∈ neighborhood e p [u] lag :=
  mem_neighborhood_iff_exists_singleton e p A lag s

/-- Any witness window covering s*(u₀) in any subset A cannot be a lag 3 AAS window. -/
theorem universal_non_aas_witness (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (u0 : Nat) (lag : Nat → Nat)
    (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (w : Nat)
    (hw_cov : oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p [w] lag)
    (hwA : e (w : Int) = true)
    (hlw : lag w = 3)
    (hPw : ShortPeriodicSupply.P2 e (w : Int) 3)
    (haas : e ((w : Int) - 1) = true ∧ e ((w : Int) - 2) = true ∧ e ((w : Int) - 3) = false) :
    False :=
  neighborhood_collision_forces_non_aas e p hp hper u0 lag hd_lt hu0A hP0 hss0 w hw_cov hwA hlw hPw haas

/-- Any subset A consisting purely of lag 3 AAS windows strictly avoids s*(u₀), regardless of size. -/
theorem universal_all_aas_avoids (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat) (u0 : Nat)
    (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag :=
  all_aas_subset_avoids_s_star e p hp hper A lag u0 hd_lt hu0A hP0 hss0 hlag3 haas hP_A hA_A

/-- Any tight subset A consisting purely of lag 3 AAS windows strictly survives deletion with zero loss. -/
theorem universal_all_aas_survives (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (htight : (neighborhood e p A lag).length = A.length)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot := universal_all_aas_avoids e p hp hper A lag u0 hd_lt hu0A hP0 hss0 hlag3 haas hP_A hA_A
  exact arbitrary_period_tight_survives_of_not_mem e p A lag htight u0 hnot

/-- For any subset A where all elements except a single element w are lag 3 AAS,
s*(u₀) ∈ N(A) ↔ s*(u₀) ∈ N([w]). -/
theorem universal_single_non_aas_collision_iff (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (w : Nat) (hw : w ∈ A)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hlag3 : ∀ u ∈ A, u ≠ w → lag u = 3)
    (haas : ∀ u ∈ A, u ≠ w → e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, u ≠ w → ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, u ≠ w → e (u : Int) = true) :
    oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p A lag ↔
    oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p [w] lag := by
  rw [universal_mem_neighborhood_iff]
  constructor
  · rintro ⟨u, hu, hcov⟩
    by_cases huw : u = w
    · subst huw
      exact hcov
    · exfalso
      have hlu := hlag3 u hu huw
      have haasu := haas u hu huw
      have hPu : ShortPeriodicSupply.P2 e (u : Int) 3 := by
        have := hP_A u hu huw
        rwa [hlu] at this
      have huA := hA_A u hu huw
      exact universal_non_aas_witness e p hp hper u0 lag hd_lt hu0A hP0 hss0 u hcov huA hlu hPu haasu
  · intro hcov
    exact ⟨w, hw, hcov⟩

/-- For any tight subset A where all elements except w are lag 3 AAS, if s*(u₀) ∉ N([w]),
then A strictly survives deletion. -/
theorem universal_single_non_aas_survives (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (htight : (neighborhood e p A lag).length = A.length)
    (w : Nat) (hw : w ∈ A)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hlag3 : ∀ u ∈ A, u ≠ w → lag u = 3)
    (haas : ∀ u ∈ A, u ≠ w → e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, u ≠ w → ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, u ≠ w → e (u : Int) = true)
    (hnot : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p [w] lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot_A : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag := by
    intro hmem
    have hw_cov := (universal_single_non_aas_collision_iff e p hp hper A lag w hw u0 hd_lt hu0A hP0 hss0 hlag3 haas hP_A hA_A).mp hmem
    exact hnot hw_cov
  exact arbitrary_period_tight_survives_of_not_mem e p A lag htight u0 hnot_A

/-- For any subset A where all elements except w₁, w₂ are lag 3 AAS,
s*(u₀) ∈ N(A) ↔ (s*(u₀) ∈ N([w₁]) ∨ s*(u₀) ∈ N([w₂])). -/
theorem universal_two_non_aas_collision_iff (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (w1 w2 : Nat) (hw1 : w1 ∈ A) (hw2 : w2 ∈ A)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hlag3 : ∀ u ∈ A, u ≠ w1 → u ≠ w2 → lag u = 3)
    (haas : ∀ u ∈ A, u ≠ w1 → u ≠ w2 → e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, u ≠ w1 → u ≠ w2 → ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, u ≠ w1 → u ≠ w2 → e (u : Int) = true) :
    oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p A lag ↔
    (oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p [w1] lag ∨
     oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p [w2] lag) := by
  rw [universal_mem_neighborhood_iff]
  constructor
  · rintro ⟨u, hu, hcov⟩
    by_cases huw1 : u = w1
    · subst huw1
      exact Or.inl hcov
    · by_cases huw2 : u = w2
      · subst huw2
        exact Or.inr hcov
      · exfalso
        have hlu := hlag3 u hu huw1 huw2
        have haasu := haas u hu huw1 huw2
        have hPu : ShortPeriodicSupply.P2 e (u : Int) 3 := by
          have := hP_A u hu huw1 huw2
          rwa [hlu] at this
        have huA := hA_A u hu huw1 huw2
        exact universal_non_aas_witness e p hp hper u0 lag hd_lt hu0A hP0 hss0 u hcov huA hlu hPu haasu
  · rintro (h1 | h2)
    · exact ⟨w1, hw1, h1⟩
    · exact ⟨w2, hw2, h2⟩

/-- For any tight subset A where all elements except w₁, w₂ are lag 3 AAS,
if neither w₁ nor w₂ covers s*(u₀), then A strictly survives deletion. -/
theorem universal_two_non_aas_survives (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (htight : (neighborhood e p A lag).length = A.length)
    (w1 w2 : Nat) (hw1 : w1 ∈ A) (hw2 : w2 ∈ A)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hlag3 : ∀ u ∈ A, u ≠ w1 → u ≠ w2 → lag u = 3)
    (haas : ∀ u ∈ A, u ≠ w1 → u ≠ w2 → e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, u ≠ w1 → u ≠ w2 → ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, u ≠ w1 → u ≠ w2 → e (u : Int) = true)
    (hnot1 : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p [w1] lag)
    (hnot2 : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p [w2] lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot_A : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag := by
    intro hmem
    have h_or := (universal_two_non_aas_collision_iff e p hp hper A lag w1 w2 hw1 hw2 u0 hd_lt hu0A hP0 hss0 hlag3 haas hP_A hA_A).mp hmem
    rcases h_or with h1 | h2
    · exact hnot1 h1
    · exact hnot2 h2
  exact arbitrary_period_tight_survives_of_not_mem e p A lag htight u0 hnot_A

/-- General Hall preservation principle: any subset with slack |A| < |N(A)| or avoiding s
strictly preserves Hall's condition. -/
theorem universal_hall_preservation_of_slack_or_not_mem (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat) (s : Nat)
    (hhall : A.length ≤ (neighborhood e p A lag).length)
    (hcond : A.length < (neighborhood e p A lag).length ∨ s ∉ neighborhood e p A lag) :
    A.length ≤ (deletedNeighborhood e p A lag s).length :=
  hall_preserved_of_slack_or_avoid e p A lag s hhall hcond

/-- Master Synthesis: Grand Universal Tight Decomposition Theorem. -/
theorem grand_universal_tight_decomposition_synthesis
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (htight : (neighborhood e p A lag).length = A.length)
    (w : Nat) (hw : w ∈ A)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hlag3 : ∀ u ∈ A, u ≠ w → lag u = 3)
    (haas : ∀ u ∈ A, u ≠ w → e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, u ≠ w → ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, u ≠ w → e (u : Int) = true) :
    -- (1) Neighborhood singleton equivalence
    (∀ s, s ∈ neighborhood e p A lag ↔ ∃ u ∈ A, s ∈ neighborhood e p [u] lag) ∧
    -- (2) Single non-AAS collision equivalence
    (oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p A lag ↔
     oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p [w] lag) ∧
    -- (3) Survival when w does not cover s*(u₀)
    (oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p [w] lag →
     A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) := by
  refine ⟨fun s => universal_mem_neighborhood_iff e p A lag s,
          universal_single_non_aas_collision_iff e p hp hper A lag w hw u0 hd_lt hu0A hP0 hss0 hlag3 haas hP_A hA_A,
          universal_single_non_aas_survives e p hp hper A lag htight w hw u0 hd_lt hu0A hP0 hss0 hlag3 haas hP_A hA_A⟩

end Recaman.UniversalTightDecomposition
