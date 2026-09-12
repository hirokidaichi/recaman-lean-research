import Recaman.TightSubsetLagStructure
import Recaman.LagSevenNeighborhoodRigidity
import Recaman.TightTripleRigidity
import Recaman.ArbitraryPeriodGateT6Unconditional

/-!
# TightSubsetDecomposition: AAS and Non-AAS Collision Decomposition in Tight Subsets

This module establishes the exact decomposition of candidate collisions at Gate T6
into AAS and non-AAS window components:

1. `mem_of_subset_nodup_length_eq`: General list lemma: if `l1 ⊆ l2`, `l1.Nodup`, and
   `l1.length = l2.length`, then `l2 ⊆ l1`.
2. `mem_neighborhood_iff_exists_singleton`: A subtraction phase belongs to `N(A)` iff
   it belongs to `N([u])` for some `u ∈ A`.
3. `aas_window_avoids_s_star`: Any lag 3 AAS window strictly avoids the donated subtraction
   `s*(u₀)` of an SS=2 donor.
4. `neighborhood_collision_forces_non_aas`: Any witness window `w ∈ A` covering `s*(u₀)`
   cannot be a lag 3 AAS window.
5. `all_aas_subset_avoids_s_star`: If all members of `A` are lag 3 AAS, then `s*(u₀) ∉ N(A)`.
6. `tight_triple_lag7_spans_neighborhood`: In any tight triple `A` (|A| = 3), any member `w`
   with individual neighborhood size 3 spans the entire collective neighborhood `N(A)`.
7. `tight_triple_lag7_covers_aas_endpoints`: In a tight triple `A = [v₁, v₂, w]` with `v₁, v₂` AAS
   and `w` lag 7, `w` covers both AAS endpoints `s*(v₁)` and `s*(v₂)`.
8. `tight_triple_collision_iff_lag7_covers`: In such a tight triple, `s*(u₀) ∈ N(A)` iff `s*(u₀) ∈ N([w])`.
9. `tight_triple_collision_forces_triple_endpoint_coverage`: If `s*(u₀) ∈ N(A)`, then `w`
   simultaneously covers `s*(u₀)`, `s*(v₁)`, and `s*(v₂)`.
10. `tight_triple_survives_of_lag7_not_covers`: If `s*(u₀) ∉ N([w])`, then `A` strictly survives
    deletion with zero loss: `|A| ≤ |N(A) \ {s*(u₀)}|`.
11. `grand_tight_subset_decomposition_synthesis`: Master synthesis theorem.
-/

namespace Recaman.TightSubsetDecomposition

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

/-- General list lemma: if `l1 ⊆ l2`, `l1.Nodup`, and `l1.length = l2.length`, then `l2 ⊆ l1`. -/
theorem mem_of_subset_nodup_length_eq {α : Type} {l1 l2 : List α}
    (hsub : l1 ⊆ l2) (hnodup : l1.Nodup) (hlen : l1.length = l2.length)
    {x : α} (hx : x ∈ l2) : x ∈ l1 := by
  classical
  by_cases hx1 : x ∈ l1
  · exact hx1
  · exfalso
    have hsub' : (x :: l1) ⊆ l2 := by
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hyl1
      · exact hx
      · exact hsub hyl1
    have hnodup' : (x :: l1).Nodup := List.nodup_cons.mpr ⟨hx1, hnodup⟩
    have hle := hnodup'.length_le_of_subset hsub'
    simp only [List.length_cons] at hle
    omega

/-- Membership in the neighborhood of a subset is equivalent to membership in the individual
neighborhood of some member. -/
theorem mem_neighborhood_iff_exists_singleton (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat) (s : Nat) :
    s ∈ neighborhood e p A lag ↔ ∃ u ∈ A, s ∈ neighborhood e p [u] lag := by
  constructor
  · intro hs
    rw [mem_neighborhood_iff] at hs
    obtain ⟨hsub_phase, hcov⟩ := hs
    rw [isCoveredBySubset_iff] at hcov
    obtain ⟨u, hu, i, hi, he, hmod⟩ := hcov
    refine ⟨u, hu, ?_⟩
    rw [mem_neighborhood_iff]
    refine ⟨hsub_phase, ?_⟩
    rw [isCoveredBySubset_iff]
    exact ⟨u, by simp, i, hi, he, hmod⟩
  · rintro ⟨u, hu, hs⟩
    have hsub := singleton_neighborhood_subset e p A lag u hu
    exact hsub hs

/-- Any lag 3 AAS window strictly avoids the donated subtraction s*(u₀) of an SS=2 donor. -/
theorem aas_window_avoids_s_star (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (u0 u : Nat) (lag : Nat → Nat)
    (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (huA : e (u : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hlu : lag u = 3)
    (hPu : ShortPeriodicSupply.P2 e (u : Int) 3)
    (haas : e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false) :
    oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p [u] lag := by
  intro hmem
  rw [mem_neighborhood_iff] at hmem
  obtain ⟨_, hcov⟩ := hmem
  rw [isCoveredBySubset_iff] at hcov
  obtain ⟨w, hw, i, hi, he, hmod⟩ := hcov
  simp only [List.mem_singleton] at hw
  subst w
  rw [hlu] at hi
  have hcov_win : WindowCoversSubtraction e p (u : Int) 3 (oldestSubtractionPhase p u0 (lag u0)) := by
    unfold WindowCoversSubtraction
    exact ⟨i, hi, he, hmod⟩
  have h_endpoint := (lag_three_covers_iff e p hp (u : Int) haas.1 haas.2.1 haas.2.2 _).mp hcov_win
  have h_ne := ss2_donor_disjoint_from_aas_endpoint e p hp hper u0 u lag hd_lt hu0A huA hP0 hss0 hPu haas
  exact h_ne h_endpoint

/-- Any witness window covering s*(u₀) cannot be a lag 3 AAS window. -/
theorem neighborhood_collision_forces_non_aas (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    False := by
  have hav := aas_window_avoids_s_star e p hp hper u0 w lag hd_lt hu0A hwA hP0 hss0 hlw hPw haas
  exact hav hw_cov

/-- If all members of A are lag 3 AAS, then s*(u₀) does not belong to N(A). -/
theorem all_aas_subset_avoids_s_star (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag := by
  rw [mem_neighborhood_iff_exists_singleton]
  rintro ⟨u, hu, hcov⟩
  have hlu := hlag3 u hu
  have haasu := haas u hu
  have hPu : ShortPeriodicSupply.P2 e (u : Int) 3 := by
    have := hP_A u hu
    rwa [hlu] at this
  have huA := hA_A u hu
  exact neighborhood_collision_forces_non_aas e p hp hper u0 lag hd_lt hu0A hP0 hss0 u hcov huA hlu hPu haasu

/-- In any tight triple A of size 3, any member w with individual neighborhood size 3
spans the entire collective neighborhood N(A). -/
theorem tight_triple_lag7_spans_neighborhood (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (_hA3 : A.length = 3)
    (htight : (neighborhood e p A lag).length = 3)
    (w : Nat) (hw : w ∈ A)
    (hNw : (neighborhood e p [w] lag).length = 3) :
    ∀ s, s ∈ neighborhood e p A lag ↔ s ∈ neighborhood e p [w] lag := by
  intro s
  constructor
  · intro hs
    have hsub := singleton_neighborhood_subset e p A lag w hw
    have hnodup := neighborhood_nodup e p [w] lag
    have hlen : (neighborhood e p [w] lag).length = (neighborhood e p A lag).length := by
      omega
    exact mem_of_subset_nodup_length_eq hsub hnodup hlen hs
  · intro hs
    exact singleton_neighborhood_subset e p A lag w hw hs

/-- In a tight triple A = [v₁, v₂, w] with v₁, v₂ AAS and w of individual neighborhood size 3,
w covers both AAS endpoints s*(v₁) and s*(v₂). -/
theorem tight_triple_lag7_covers_aas_endpoints (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (hA3 : A.length = 3)
    (htight : (neighborhood e p A lag).length = 3)
    (v1 v2 w : Nat)
    (hv1 : v1 ∈ A) (hv2 : v2 ∈ A) (hw : w ∈ A)
    (hl1 : lag v1 = 3) (hl2 : lag v2 = 3)
    (haas1 : e ((v1 : Int) - 1) = true ∧ e ((v1 : Int) - 2) = true ∧ e ((v1 : Int) - 3) = false)
    (haas2 : e ((v2 : Int) - 1) = true ∧ e ((v2 : Int) - 2) = true ∧ e ((v2 : Int) - 3) = false)
    (hNw : (neighborhood e p [w] lag).length = 3) :
    endpointPhase p (v1 : Int) 3 ∈ neighborhood e p [w] lag ∧
    endpointPhase p (v2 : Int) 3 ∈ neighborhood e p [w] lag := by
  have he1 := aas_endpoint_mem_neighborhood e p hp hper A lag v1 hv1 hl1 haas1
  have he2 := aas_endpoint_mem_neighborhood e p hp hper A lag v2 hv2 hl2 haas2
  have hspan := tight_triple_lag7_spans_neighborhood e p A lag hA3 htight w hw hNw
  exact ⟨(hspan _).mp he1, (hspan _).mp he2⟩

/-- In such a tight triple, s*(u₀) belongs to N(A) iff it belongs to N([w]). -/
theorem tight_triple_collision_iff_lag7_covers (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (hA3 : A.length = 3)
    (htight : (neighborhood e p A lag).length = 3)
    (w : Nat) (hw : w ∈ A)
    (hNw : (neighborhood e p [w] lag).length = 3)
    (u0 : Nat) :
    oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p A lag ↔
    oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p [w] lag :=
  tight_triple_lag7_spans_neighborhood e p A lag hA3 htight w hw hNw (oldestSubtractionPhase p u0 (lag u0))

/-- If s*(u₀) ∈ N(A), then w simultaneously covers s*(u₀), s*(v₁), and s*(v₂). -/
theorem tight_triple_collision_forces_triple_endpoint_coverage
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (hA3 : A.length = 3)
    (htight : (neighborhood e p A lag).length = 3)
    (v1 v2 w : Nat)
    (hv1 : v1 ∈ A) (hv2 : v2 ∈ A) (hw : w ∈ A)
    (hl1 : lag v1 = 3) (hl2 : lag v2 = 3)
    (haas1 : e ((v1 : Int) - 1) = true ∧ e ((v1 : Int) - 2) = true ∧ e ((v1 : Int) - 3) = false)
    (haas2 : e ((v2 : Int) - 1) = true ∧ e ((v2 : Int) - 2) = true ∧ e ((v2 : Int) - 3) = false)
    (hNw : (neighborhood e p [w] lag).length = 3)
    (u0 : Nat)
    (hcoll : oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p A lag) :
    oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p [w] lag ∧
    endpointPhase p (v1 : Int) 3 ∈ neighborhood e p [w] lag ∧
    endpointPhase p (v2 : Int) 3 ∈ neighborhood e p [w] lag := by
  have hcov_w := (tight_triple_collision_iff_lag7_covers e p A lag hA3 htight w hw hNw u0).mp hcoll
  have ⟨he1, he2⟩ := tight_triple_lag7_covers_aas_endpoints e p hp hper A lag hA3 htight v1 v2 w hv1 hv2 hw hl1 hl2 haas1 haas2 hNw
  exact ⟨hcov_w, he1, he2⟩

/-- If s*(u₀) ∉ N([w]), then A strictly survives deletion with zero loss. -/
theorem tight_triple_survives_of_lag7_not_covers
    (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (hA3 : A.length = 3)
    (htight : (neighborhood e p A lag).length = 3)
    (w : Nat) (hw : w ∈ A)
    (hNw : (neighborhood e p [w] lag).length = 3)
    (u0 : Nat)
    (hnot : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p [w] lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot_A : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag := by
    intro hmem
    have h_w := (tight_triple_collision_iff_lag7_covers e p A lag hA3 htight w hw hNw u0).mp hmem
    exact hnot h_w
  exact tight_triple_survives_of_s_not_mem e p A lag u0 (by omega) hnot_A

/-- Master Synthesis: Grand Tight Subset Decomposition Theorem. -/
theorem grand_tight_subset_decomposition_synthesis
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (hA3 : A.length = 3)
    (htight : (neighborhood e p A lag).length = 3)
    (v1 v2 w : Nat)
    (hv1 : v1 ∈ A) (hv2 : v2 ∈ A) (hw : w ∈ A)
    (hl1 : lag v1 = 3) (hl2 : lag v2 = 3)
    (haas1 : e ((v1 : Int) - 1) = true ∧ e ((v1 : Int) - 2) = true ∧ e ((v1 : Int) - 3) = false)
    (haas2 : e ((v2 : Int) - 1) = true ∧ e ((v2 : Int) - 2) = true ∧ e ((v2 : Int) - 3) = false)
    (hNw : (neighborhood e p [w] lag).length = 3)
    (u0 : Nat) :
    -- (1) Equivalence of collective collision and lag 7 window collision
    (oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p A lag ↔
     oldestSubtractionPhase p u0 (lag u0) ∈ neighborhood e p [w] lag) ∧
    -- (2) Saturation: w covers both AAS endpoints
    (endpointPhase p (v1 : Int) 3 ∈ neighborhood e p [w] lag ∧
     endpointPhase p (v2 : Int) 3 ∈ neighborhood e p [w] lag) ∧
    -- (3) Preservation when w does not cover s*(u₀)
    (oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p [w] lag →
     A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) := by
  refine ⟨tight_triple_collision_iff_lag7_covers e p A lag hA3 htight w hw hNw u0,
          tight_triple_lag7_covers_aas_endpoints e p hp hper A lag hA3 htight v1 v2 w hv1 hv2 hw hl1 hl2 haas1 haas2 hNw,
          tight_triple_survives_of_lag7_not_covers e p A lag hA3 htight w hw hNw u0⟩

end Recaman.TightSubsetDecomposition
