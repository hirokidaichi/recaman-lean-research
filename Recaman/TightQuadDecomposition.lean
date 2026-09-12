import Recaman.TightSubsetDecomposition
import Recaman.TightQuadRigidity

/-!
# TightQuadDecomposition: AAS and Non-AAS Collision Decomposition in Tight Quadruples

This module formalizes the structural decomposition of tight avoiding quadruples (size 4)
into AAS and non-AAS window components:

1. `tight_quad_member_neighborhood_le_four`: In any tight quadruple A (|A| = 4), every member u ∈ A
   satisfies `|N([u])| ≤ 4`.
2. `tight_quad_no_ge_five`: No window with individual neighborhood size ≥ 5 can belong to any
   tight quadruple of size 4.
3. `tight_quad_single_non_aas_collision_iff`: In a tight quadruple with 3 AAS windows and 1 non-AAS
   window w, `s*(u₀) ∈ N(A) ↔ s*(u₀) ∈ N([w])`.
4. `tight_quad_single_non_aas_survives_of_not_covers`: If `s*(u₀) ∉ N([w])`, then A strictly survives
   deletion with zero loss: `|A| ≤ |N(A) \ {s*(u₀)}|`.
5. `tight_quad_two_non_aas_collision_iff`: In a tight quadruple with 2 AAS windows and 2 non-AAS
   windows w₁, w₂, `s*(u₀) ∈ N(A) ↔ (s*(u₀) ∈ N([w₁]) ∨ s*(u₀) ∈ N([w₂]))`.
6. `tight_quad_two_non_aas_survives_of_neither_covers`: If neither w₁ nor w₂ covers s*(u₀), then A
   strictly survives deletion: `|A| ≤ |N(A) \ {s*(u₀)}|`.
7. `tight_quad_two_lag7_disjoint_impossible`: In any tight quadruple, two windows with individual
   neighborhoods of size ≥ 3 cannot have disjoint neighborhoods.
8. `tight_quad_two_lag7_not_disjoint`: In any tight quadruple, any two windows with individual
   neighborhoods of size ≥ 3 cannot be disjoint.
9. `tight_quad_all_aas_survives_unconditional`: Any tight quadruple of purely lag 3 AAS windows
   strictly avoids s*(u₀) and survives deletion with zero loss.
10. `grand_tight_quad_decomposition_synthesis`: Master synthesis theorem for tight quadruple decomposition.
-/

namespace Recaman.TightQuadDecomposition

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
open TightSubsetDecomposition

/-- In any tight quadruple A (|A| = 4), every member u ∈ A satisfies |N([u])| ≤ 4. -/
theorem tight_quad_member_neighborhood_le_four (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (hA4 : A.length = 4)
    (htight : (neighborhood e p A lag).length = 4)
    (u : Nat) (hu : u ∈ A) :
    (neighborhood e p [u] lag).length ≤ 4 := by
  have hle := tight_subset_member_neighborhood_le e p A lag (by omega) u hu
  omega

/-- No window with individual neighborhood size ≥ 5 can belong to any tight quadruple of size 4. -/
theorem tight_quad_no_ge_five (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (hA4 : A.length = 4)
    (htight : (neighborhood e p A lag).length = 4)
    (u : Nat) (hu : u ∈ A)
    (hN5 : 5 ≤ (neighborhood e p [u] lag).length) : False := by
  have hle := tight_quad_member_neighborhood_le_four e p A lag hA4 htight u hu
  omega

/-- In a tight quadruple with 3 AAS windows and 1 non-AAS window w, s*(u₀) ∈ N(A) ↔ s*(u₀) ∈ N([w]). -/
theorem tight_quad_single_non_aas_collision_iff (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (v1 v2 v3 w : Nat)
    (hA : A = [v1, v2, v3, w])
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hl1 : lag v1 = 3) (hl2 : lag v2 = 3) (hl3 : lag v3 = 3)
    (haas1 : e ((v1 : Int) - 1) = true ∧ e ((v1 : Int) - 2) = true ∧ e ((v1 : Int) - 3) = false)
    (haas2 : e ((v2 : Int) - 1) = true ∧ e ((v2 : Int) - 2) = true ∧ e ((v2 : Int) - 3) = false)
    (haas3 : e ((v3 : Int) - 1) = true ∧ e ((v3 : Int) - 2) = true ∧ e ((v3 : Int) - 3) = false)
    (hP1 : ShortPeriodicSupply.P2 e (v1 : Int) 3)
    (hP2 : ShortPeriodicSupply.P2 e (v2 : Int) 3)
    (hP3 : ShortPeriodicSupply.P2 e (v3 : Int) 3)
    (hv1A : e (v1 : Int) = true) (hv2A : e (v2 : Int) = true) (hv3A : e (v3 : Int) = true) :
    oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p A lag ↔
    oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p [w] lag := by
  rw [mem_neighborhood_iff_exists_singleton]
  constructor
  · rintro ⟨u, hu, hcov⟩
    rw [hA] at hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exfalso
      exact neighborhood_collision_forces_non_aas e p hp hper u0 lag hd_lt hu0A hP0 hss0 u hcov hv1A hl1 hP1 haas1
    · exfalso
      exact neighborhood_collision_forces_non_aas e p hp hper u0 lag hd_lt hu0A hP0 hss0 u hcov hv2A hl2 hP2 haas2
    · exfalso
      exact neighborhood_collision_forces_non_aas e p hp hper u0 lag hd_lt hu0A hP0 hss0 u hcov hv3A hl3 hP3 haas3
    · exact hcov
  · intro hcov
    refine ⟨w, by rw [hA]; simp, hcov⟩

/-- If s*(u₀) ∉ N([w]), then A strictly survives deletion with zero loss. -/
theorem tight_quad_single_non_aas_survives_of_not_covers
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (hA4 : A.length = 4)
    (htight : (neighborhood e p A lag).length = 4)
    (v1 v2 v3 w : Nat)
    (hA : A = [v1, v2, v3, w])
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hl1 : lag v1 = 3) (hl2 : lag v2 = 3) (hl3 : lag v3 = 3)
    (haas1 : e ((v1 : Int) - 1) = true ∧ e ((v1 : Int) - 2) = true ∧ e ((v1 : Int) - 3) = false)
    (haas2 : e ((v2 : Int) - 1) = true ∧ e ((v2 : Int) - 2) = true ∧ e ((v2 : Int) - 3) = false)
    (haas3 : e ((v3 : Int) - 1) = true ∧ e ((v3 : Int) - 2) = true ∧ e ((v3 : Int) - 3) = false)
    (hP1 : ShortPeriodicSupply.P2 e (v1 : Int) 3)
    (hP2 : ShortPeriodicSupply.P2 e (v2 : Int) 3)
    (hP3 : ShortPeriodicSupply.P2 e (v3 : Int) 3)
    (hv1A : e (v1 : Int) = true) (hv2A : e (v2 : Int) = true) (hv3A : e (v3 : Int) = true)
    (hnot : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p [w] lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot_A : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag := by
    intro hmem
    have hw_cov := (tight_quad_single_non_aas_collision_iff e p hp hper A lag v1 v2 v3 w hA u0 hd_lt hu0A hP0 hss0 hl1 hl2 hl3 haas1 haas2 haas3 hP1 hP2 hP3 hv1A hv2A hv3A).mp hmem
    exact hnot hw_cov
  exact tight_quad_survives_of_not_mem e p A lag hA4 htight u0 hnot_A

/-- In a tight quadruple with 2 AAS windows and 2 non-AAS windows w₁, w₂,
s*(u₀) ∈ N(A) ↔ (s*(u₀) ∈ N([w₁]) ∨ s*(u₀) ∈ N([w₂])). -/
theorem tight_quad_two_non_aas_collision_iff (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (v1 v2 w1 w2 : Nat)
    (hA : A = [v1, v2, w1, w2])
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hl1 : lag v1 = 3) (hl2 : lag v2 = 3)
    (haas1 : e ((v1 : Int) - 1) = true ∧ e ((v1 : Int) - 2) = true ∧ e ((v1 : Int) - 3) = false)
    (haas2 : e ((v2 : Int) - 1) = true ∧ e ((v2 : Int) - 2) = true ∧ e ((v2 : Int) - 3) = false)
    (hP1 : ShortPeriodicSupply.P2 e (v1 : Int) 3)
    (hP2 : ShortPeriodicSupply.P2 e (v2 : Int) 3)
    (hv1A : e (v1 : Int) = true) (hv2A : e (v2 : Int) = true) :
    oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p A lag ↔
    (oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p [w1] lag ∨
     oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p [w2] lag) := by
  rw [mem_neighborhood_iff_exists_singleton]
  constructor
  · rintro ⟨u, hu, hcov⟩
    rw [hA] at hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exfalso
      exact neighborhood_collision_forces_non_aas e p hp hper u0 lag hd_lt hu0A hP0 hss0 u hcov hv1A hl1 hP1 haas1
    · exfalso
      exact neighborhood_collision_forces_non_aas e p hp hper u0 lag hd_lt hu0A hP0 hss0 u hcov hv2A hl2 hP2 haas2
    · exact Or.inl hcov
    · exact Or.inr hcov
  · rintro (h1 | h2)
    · exact ⟨w1, by rw [hA]; simp, h1⟩
    · exact ⟨w2, by rw [hA]; simp, h2⟩

/-- If neither w₁ nor w₂ covers s*(u₀), then A strictly survives deletion with zero loss. -/
theorem tight_quad_two_non_aas_survives_of_neither_covers
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (hA4 : A.length = 4)
    (htight : (neighborhood e p A lag).length = 4)
    (v1 v2 w1 w2 : Nat)
    (hA : A = [v1, v2, w1, w2])
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hl1 : lag v1 = 3) (hl2 : lag v2 = 3)
    (haas1 : e ((v1 : Int) - 1) = true ∧ e ((v1 : Int) - 2) = true ∧ e ((v1 : Int) - 3) = false)
    (haas2 : e ((v2 : Int) - 1) = true ∧ e ((v2 : Int) - 2) = true ∧ e ((v2 : Int) - 3) = false)
    (hP1 : ShortPeriodicSupply.P2 e (v1 : Int) 3)
    (hP2 : ShortPeriodicSupply.P2 e (v2 : Int) 3)
    (hv1A : e (v1 : Int) = true) (hv2A : e (v2 : Int) = true)
    (hnot1 : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p [w1] lag)
    (hnot2 : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p [w2] lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot_A : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag := by
    intro hmem
    have h_or := (tight_quad_two_non_aas_collision_iff e p hp hper A lag v1 v2 w1 w2 hA u0 hd_lt hu0A hP0 hss0 hl1 hl2 haas1 haas2 hP1 hP2 hv1A hv2A).mp hmem
    rcases h_or with h1 | h2
    · exact hnot1 h1
    · exact hnot2 h2
  exact tight_quad_survives_of_not_mem e p A lag hA4 htight u0 hnot_A

/-- In any tight quadruple, two windows with individual neighborhoods of size ≥ 3 cannot have
disjoint neighborhoods. -/
theorem tight_quad_two_lag7_disjoint_impossible (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (hA4 : A.length = 4)
    (htight : (neighborhood e p A lag).length = 4)
    (u v : Nat) (hu : u ∈ A) (hv : v ∈ A)
    (hdisj : ∀ s, s ∈ neighborhood e p [u] lag → s ∉ neighborhood e p [v] lag)
    (hNu : 3 ≤ (neighborhood e p [u] lag).length)
    (hNv : 3 ≤ (neighborhood e p [v] lag).length) : False := by
  have hle5 : A.length ≤ 5 := by omega
  have htight_eq : (neighborhood e p A lag).length = A.length := by omega
  exact two_disjoint_ge_three_exceeds_tight_five e p A lag hle5 htight_eq u v hu hv hdisj hNu hNv

/-- In any tight quadruple, any two windows with individual neighborhoods of size ≥ 3 cannot be
disjoint. -/
theorem tight_quad_two_lag7_not_disjoint (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (hA4 : A.length = 4)
    (htight : (neighborhood e p A lag).length = 4)
    (u v : Nat) (hu : u ∈ A) (hv : v ∈ A)
    (hNu : 3 ≤ (neighborhood e p [u] lag).length)
    (hNv : 3 ≤ (neighborhood e p [v] lag).length) :
    ¬ (∀ s, s ∈ neighborhood e p [u] lag → s ∉ neighborhood e p [v] lag) := by
  intro hdisj
  exact tight_quad_two_lag7_disjoint_impossible e p A lag hA4 htight u v hu hv hdisj hNu hNv

/-- Any tight quadruple of purely lag 3 AAS windows strictly avoids s*(u₀) and survives deletion. -/
theorem tight_quad_all_aas_survives_unconditional (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (hA4 : A.length = 4)
    (htight : (neighborhood e p A lag).length = 4)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot := all_aas_subset_avoids_s_star e p hp hper A lag u0 hd_lt hu0A hP0 hss0 hlag3 haas hP_A hA_A
  exact tight_quad_survives_of_not_mem e p A lag hA4 htight u0 hnot

/-- Master Synthesis: Grand Tight Quadruple Decomposition Theorem. -/
theorem grand_tight_quad_decomposition_synthesis
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (hA4 : A.length = 4)
    (htight : (neighborhood e p A lag).length = 4)
    (v1 v2 v3 w : Nat)
    (hA : A = [v1, v2, v3, w])
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hl1 : lag v1 = 3) (hl2 : lag v2 = 3) (hl3 : lag v3 = 3)
    (haas1 : e ((v1 : Int) - 1) = true ∧ e ((v1 : Int) - 2) = true ∧ e ((v1 : Int) - 3) = false)
    (haas2 : e ((v2 : Int) - 1) = true ∧ e ((v2 : Int) - 2) = true ∧ e ((v2 : Int) - 3) = false)
    (haas3 : e ((v3 : Int) - 1) = true ∧ e ((v3 : Int) - 2) = true ∧ e ((v3 : Int) - 3) = false)
    (hP1 : ShortPeriodicSupply.P2 e (v1 : Int) 3)
    (hP2 : ShortPeriodicSupply.P2 e (v2 : Int) 3)
    (hP3 : ShortPeriodicSupply.P2 e (v3 : Int) 3)
    (hv1A : e (v1 : Int) = true) (hv2A : e (v2 : Int) = true) (hv3A : e (v3 : Int) = true) :
    -- (1) Bounded individual neighborhood
    (∀ u ∈ A, (neighborhood e p [u] lag).length ≤ 4) ∧
    -- (2) Impossibility of individual neighborhood ≥ 5
    (∀ u ∈ A, 5 ≤ (neighborhood e p [u] lag).length → False) ∧
    -- (3) Equivalence of collision with single non-AAS window
    (oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p A lag ↔
     oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p [w] lag) ∧
    -- (4) Preservation when w does not cover s*(u₀)
    (oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p [w] lag →
     A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) := by
  refine ⟨fun u hu => tight_quad_member_neighborhood_le_four e p A lag hA4 htight u hu,
          fun u hu h5 => tight_quad_no_ge_five e p A lag hA4 htight u hu h5,
          tight_quad_single_non_aas_collision_iff e p hp hper A lag v1 v2 v3 w hA u0 hd_lt hu0A hP0 hss0 hl1 hl2 hl3 haas1 haas2 haas3 hP1 hP2 hP3 hv1A hv2A hv3A,
          tight_quad_single_non_aas_survives_of_not_covers e p hp hper A lag hA4 htight v1 v2 v3 w hA u0 hd_lt hu0A hP0 hss0 hl1 hl2 hl3 haas1 haas2 haas3 hP1 hP2 hP3 hv1A hv2A hv3A⟩

end Recaman.TightQuadDecomposition
