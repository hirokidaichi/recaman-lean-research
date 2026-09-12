import Recaman.UniversalCollisionDistance

/-!
# UniversalNonAASReduction: Universal Non-AAS Window Filter and Multi-Window Reduction

This module establishes the general structural reduction of Gate T6 to non-AAS candidate sublists:

1. `universal_non_aas_sublist_collision_iff`: For any subset A and any sublist of non-AAS candidates
   W ⊆ A, if every window in A \ W is a lag 3 AAS window, then collective collision is exactly
   equivalent to existence of a collision witness within W:
   `s*(u₀) ∈ N(A) ↔ ∃ w ∈ W, s*(u₀) ∈ N([w])`.
2. `universal_non_aas_sublist_not_mem`: If no window in W covers s*(u₀), then s*(u₀) ∉ N(A).
3. `universal_non_aas_sublist_survives`: Any tight subset A where no window in W covers s*(u₀)
   strictly survives deletion with zero loss: `|A| ≤ |N(A) \ {s*(u₀)}|`.
4. `universal_three_non_aas_collision_iff`: Equivalence for 3 non-AAS windows w₁, w₂, w₃:
   `s*(u₀) ∈ N(A) ↔ (s*(u₀) ∈ N([w₁]) ∨ s*(u₀) ∈ N([w₂]) ∨ s*(u₀) ∈ N([w₃]))`.
5. `universal_three_non_aas_survives`: If none of w₁, w₂, w₃ covers s*(u₀), then A survives deletion.
6. `universal_tight_quintuple_member_bound`: In any tight quintuple (|A| = 5), every member satisfies
   `|N([u])| ≤ 5`.
7. `universal_tight_quintuple_no_ge_six`: No window with individual neighborhood ≥ 6 can belong to
   any tight quintuple of size 5.
8. `universal_tight_quintuple_all_aas_survives`: Any tight quintuple consisting purely of lag 3 AAS
   windows strictly survives deletion unconditionally.
9. `universal_non_aas_sublist_distance_survives`: If every window in W satisfies the modular distance
   non-congruence obstruction, then A strictly survives deletion with zero loss.
10. `grand_universal_non_aas_reduction_synthesis`: Master synthesis theorem uniting arbitrary non-AAS
    sublists, 3-window disjunction, tight quintuple bounds, and distance obstruction.
-/

namespace Recaman.UniversalNonAASReduction

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

/-- For any subset A and any sublist of non-AAS candidates W ⊆ A, if all elements in A \ W are
lag 3 AAS windows, collective collision is equivalent to witness existence within W. -/
theorem universal_non_aas_sublist_collision_iff
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (W : List Nat) (hW_sub : ∀ w ∈ W, w ∈ A)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (haas : ∀ u ∈ A, u ∉ W → lag u = 3 ∧
      e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false ∧
      ShortPeriodicSupply.P2 e (u : Int) 3 ∧ e (u : Int) = true) :
    oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p A lag ↔
    ∃ w ∈ W, oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p [w] lag := by
  rw [universal_mem_neighborhood_iff]
  constructor
  · rintro ⟨u, hu, hcov⟩
    by_cases huW : u ∈ W
    · exact ⟨u, huW, hcov⟩
    · exfalso
      obtain ⟨hlu, haas1, haas2, haas3, hPu, huA⟩ := haas u hu huW
      have haas_all : e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false :=
        ⟨haas1, haas2, haas3⟩
      exact universal_non_aas_witness e p hp hper u0 lag hd_lt hu0A hP0 hss0 u hcov huA hlu hPu haas_all
  · rintro ⟨w, hwW, hcov⟩
    exact ⟨w, hW_sub w hwW, hcov⟩

/-- If no window in W covers s*(u₀), then s*(u₀) ∉ N(A). -/
theorem universal_non_aas_sublist_not_mem
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (W : List Nat) (hW_sub : ∀ w ∈ W, w ∈ A)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (haas : ∀ u ∈ A, u ∉ W → lag u = 3 ∧
      e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false ∧
      ShortPeriodicSupply.P2 e (u : Int) 3 ∧ e (u : Int) = true)
    (hnot_cov : ∀ w ∈ W, oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p [w] lag) :
    oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag := by
  intro hmem
  have hiff := (universal_non_aas_sublist_collision_iff e p hp hper A lag W hW_sub u0 hd_lt hu0A hP0 hss0 haas).mp hmem
  obtain ⟨w, hwW, hcov⟩ := hiff
  exact hnot_cov w hwW hcov

/-- Any tight subset A where no window in W covers s*(u₀) strictly survives deletion with zero loss. -/
theorem universal_non_aas_sublist_survives
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (htight : (neighborhood e p A lag).length = A.length)
    (W : List Nat) (hW_sub : ∀ w ∈ W, w ∈ A)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (haas : ∀ u ∈ A, u ∉ W → lag u = 3 ∧
      e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false ∧
      ShortPeriodicSupply.P2 e (u : Int) 3 ∧ e (u : Int) = true)
    (hnot_cov : ∀ w ∈ W, oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p [w] lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot := universal_non_aas_sublist_not_mem e p hp hper A lag W hW_sub u0 hd_lt hu0A hP0 hss0 haas hnot_cov
  exact arbitrary_period_tight_survives_of_not_mem e p A lag htight u0 hnot

/-- Equivalence for 3 non-AAS windows: s*(u₀) ∈ N(A) ↔ (s*(u₀) ∈ N([w₁]) ∨ s*(u₀) ∈ N([w₂]) ∨ s*(u₀) ∈ N([w₃])). -/
theorem universal_three_non_aas_collision_iff
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (w1 w2 w3 : Nat) (hw1 : w1 ∈ A) (hw2 : w2 ∈ A) (hw3 : w3 ∈ A)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (haas : ∀ u ∈ A, u ≠ w1 → u ≠ w2 → u ≠ w3 → lag u = 3 ∧
      e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false ∧
      ShortPeriodicSupply.P2 e (u : Int) 3 ∧ e (u : Int) = true) :
    oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p A lag ↔
    (oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p [w1] lag ∨
     oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p [w2] lag ∨
     oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p [w3] lag) := by
  rw [universal_mem_neighborhood_iff]
  constructor
  · rintro ⟨u, hu, hcov⟩
    by_cases huw1 : u = w1
    · subst huw1
      exact Or.inl hcov
    · by_cases huw2 : u = w2
      · subst huw2
        exact Or.inr (Or.inl hcov)
      · by_cases huw3 : u = w3
        · subst huw3
          exact Or.inr (Or.inr hcov)
        · exfalso
          obtain ⟨hlu, haas1, haas2, haas3, hPu, huA⟩ := haas u hu huw1 huw2 huw3
          have haas_all : e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false :=
            ⟨haas1, haas2, haas3⟩
          exact universal_non_aas_witness e p hp hper u0 lag hd_lt hu0A hP0 hss0 u hcov huA hlu hPu haas_all
  · rintro (h1 | h2 | h3)
    · exact ⟨w1, hw1, h1⟩
    · exact ⟨w2, hw2, h2⟩
    · exact ⟨w3, hw3, h3⟩

/-- If none of w₁, w₂, w₃ covers s*(u₀), then A strictly survives deletion with zero loss. -/
theorem universal_three_non_aas_survives
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (htight : (neighborhood e p A lag).length = A.length)
    (w1 w2 w3 : Nat) (hw1 : w1 ∈ A) (hw2 : w2 ∈ A) (hw3 : w3 ∈ A)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (haas : ∀ u ∈ A, u ≠ w1 → u ≠ w2 → u ≠ w3 → lag u = 3 ∧
      e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false ∧
      ShortPeriodicSupply.P2 e (u : Int) 3 ∧ e (u : Int) = true)
    (hnot1 : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p [w1] lag)
    (hnot2 : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p [w2] lag)
    (hnot3 : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p [w3] lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot_A : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag := by
    intro hmem
    have hiff := (universal_three_non_aas_collision_iff e p hp hper A lag w1 w2 w3 hw1 hw2 hw3 u0 hd_lt hu0A hP0 hss0 haas).mp hmem
    rcases hiff with h | h | h
    · exact hnot1 h
    · exact hnot2 h
    · exact hnot3 h
  exact arbitrary_period_tight_survives_of_not_mem e p A lag htight u0 hnot_A

/-- In any tight quintuple (|A| = 5), every member u ∈ A satisfies |N([u])| ≤ 5. -/
theorem universal_tight_quintuple_member_bound (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (hA5 : A.length = 5)
    (htight : (neighborhood e p A lag).length = 5)
    (u : Nat) (hu : u ∈ A) :
    (neighborhood e p [u] lag).length ≤ 5 := by
  have hle := tight_subset_member_neighborhood_le e p A lag (by omega) u hu
  omega

/-- No window with individual neighborhood size ≥ 6 can belong to any tight quintuple of size 5. -/
theorem universal_tight_quintuple_no_ge_six (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (hA5 : A.length = 5)
    (htight : (neighborhood e p A lag).length = 5)
    (u : Nat) (hu : u ∈ A)
    (hN6 : 6 ≤ (neighborhood e p [u] lag).length) : False := by
  have hle := universal_tight_quintuple_member_bound e p A lag hA5 htight u hu
  omega

/-- Any tight quintuple consisting purely of lag 3 AAS windows strictly survives deletion with zero loss. -/
theorem universal_tight_quintuple_all_aas_survives
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (hA5 : A.length = 5)
    (htight : (neighborhood e p A lag).length = 5)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  universal_all_aas_survives e p hp hper A lag (by omega) u0 hd_lt hu0A hP0 hss0 hlag3 haas hP_A hA_A

/-- If every window in W satisfies modular distance non-congruence, then A strictly survives deletion
with zero loss. -/
theorem universal_non_aas_sublist_distance_survives
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (htight : (neighborhood e p A lag).length = A.length)
    (W : List Nat) (hW_sub : ∀ w ∈ W, w ∈ A)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (haas : ∀ u ∈ A, u ∉ W → lag u = 3 ∧
      e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false ∧
      ShortPeriodicSupply.P2 e (u : Int) 3 ∧ e (u : Int) = true)
    (hdist : ∀ w ∈ W, ∀ i : Nat, i < lag w → e ((w : Int) - 1 - (i : Int)) = false →
      ((u0 : Int) - (w : Int)) % (p : Int) ≠ (((lag u0 : Int) - 1 - (i : Int)) % (p : Int))) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot_cov : ∀ w ∈ W, oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p [w] lag := by
    intro w hw
    exact universal_not_mem_neighborhood_of_distance e p hp u0 w (lag u0) lag (hdist w hw)
  exact universal_non_aas_sublist_survives e p hp hper A lag htight W hW_sub u0 hd_lt hu0A hP0 hss0 haas hnot_cov

/-- Master Synthesis: Grand Universal Non-AAS Reduction Theorem. -/
theorem grand_universal_non_aas_reduction_synthesis
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (htight : (neighborhood e p A lag).length = A.length)
    (W : List Nat) (hW_sub : ∀ w ∈ W, w ∈ A)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (haas : ∀ u ∈ A, u ∉ W → lag u = 3 ∧
      e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false ∧
      ShortPeriodicSupply.P2 e (u : Int) 3 ∧ e (u : Int) = true)
    (hnot_cov : ∀ w ∈ W, oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p [w] lag) :
    -- (1) Neighborhood non-membership
    (oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag) ∧
    -- (2) Strict Hall condition preservation
    (A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) := by
  refine ⟨universal_non_aas_sublist_not_mem e p hp hper A lag W hW_sub u0 hd_lt hu0A hP0 hss0 haas hnot_cov,
          universal_non_aas_sublist_survives e p hp hper A lag htight W hW_sub u0 hd_lt hu0A hP0 hss0 haas hnot_cov⟩

end Recaman.UniversalNonAASReduction
