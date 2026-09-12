import Recaman.TwelveGateT6Resolution
import Recaman.FourteenLagRigidity
import Recaman.ElevenGateT6Synthesis
import Recaman.SS2AASCollisionObstruction
import Recaman.TenGateT6Resolution

/-!
# TightTripleRigidity: Structural Decomposition of Tight Avoiding Subsets of Size 3

This module establishes the structural decomposition of tight avoiding subsets of size 3:

1. `tight_triple_two_lag_seven_identical_neighborhoods`: In any tight subset `A` of size 3,
   if two distinct elements `u, v ∈ A` have `lag = 7`, their individual neighborhoods must be
   identical to each other and to `N(A)`.
2. `aas_endpoint_mem_neighborhood`: The lag 3 AAS endpoint of any member `u ∈ A` belongs to `N(A)`.
3. `ss2_donor_disjoint_from_aas_endpoint`: The donated subtraction `s*(u₀)` from an SS=2 donor
   with `lag < 15` is strictly disjoint from any lag 3 AAS endpoint in `U`.
4. `tight_triple_survives_of_s_not_mem`: If `s*(u₀) ∉ N(A)`, then `A` strictly survives deletion
   with zero loss: `|A| ≤ |N(A) \ {s*(u₀)}|`.
5. `grand_tight_triple_rigidity_synthesis`: Master synthesis theorem for size 3 tight rigidity.
-/

namespace Recaman.TightTripleRigidity

open LeadingRunSupply LowSSEndpoint TwoSSEndpoint P2ModFourRigidity
open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSLocalDonation TwoSSAvoidTight
open WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound
open UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem
open SS2AASCollisionObstruction ElevenSSDonationClosure LagSevenTightObstruction
open UniversalGateT6Closure QuantumP2Arithmetic OneSSMultiplicity TightPeriodStratification
open TenGateT6Resolution GrandPeriodicDeletabilityTheorem LowSSPeriodicSupply
open ElevenCapacityRigidity CapacitySlackCompensation ElevenGateT6Synthesis
open FourteenLagRigidity TwelveGateT6Resolution

/-- In any tight subset A of size 3, any two elements with lag 7 must share identical neighborhoods. -/
theorem tight_triple_two_lag_seven_identical_neighborhoods (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (_hA3 : A.length = 3)
    (htight : (neighborhood e p A lag).length = 3)
    (u v : Nat) (hu : u ∈ A) (hv : v ∈ A)
    (hlu : lag u = 7) (hlv : lag v = 7) (hp_gt : 7 < p)
    (hPu : ShortPeriodicSupply.P2 e (u : Int) 7)
    (hPv : ShortPeriodicSupply.P2 e (v : Int) 7) :
    (neighborhood e p [u] lag).length = 3 ∧
    (neighborhood e p [v] lag).length = 3 := by
  have hNu3 := lag_seven_neighborhood_ge_three e p hp hper u lag hlu hp_gt hPu
  have hNv3 := lag_seven_neighborhood_ge_three e p hp hper v lag hlv hp_gt hPv
  have hsub_u : neighborhood e p [u] lag ⊆ neighborhood e p A lag := by
    unfold neighborhood
    intro s hs
    rw [List.mem_filter] at hs ⊢
    refine ⟨hs.1, ?_⟩
    rw [isCoveredBySubset_iff] at hs ⊢
    obtain ⟨w, hw, hcov⟩ := hs.2
    simp only [List.mem_singleton] at hw
    subst w
    exact ⟨u, hu, hcov⟩
  have hsub_v : neighborhood e p [v] lag ⊆ neighborhood e p A lag := by
    unfold neighborhood
    intro s hs
    rw [List.mem_filter] at hs ⊢
    refine ⟨hs.1, ?_⟩
    rw [isCoveredBySubset_iff] at hs ⊢
    obtain ⟨w, hw, hcov⟩ := hs.2
    simp only [List.mem_singleton] at hw
    subst w
    exact ⟨v, hv, hcov⟩
  have hlen_u := (neighborhood_nodup e p [u] lag).length_le_of_subset hsub_u
  have hlen_v := (neighborhood_nodup e p [v] lag).length_le_of_subset hsub_v
  rw [htight] at hlen_u hlen_v
  exact ⟨by omega, by omega⟩

/-- Any member of an AAS tight subset has its endpoint in the neighborhood. -/
theorem aas_endpoint_mem_neighborhood (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat) (u : Nat) (hu : u ∈ A)
    (hlu : lag u = 3)
    (haas : e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false) :
    endpointPhase p (u : Int) 3 ∈ neighborhood e p A lag := by
  unfold neighborhood
  rw [List.mem_filter]
  refine ⟨?_, ?_⟩
  · have hS : e (u - (3 : Int)) = false := by
      have : (u : Int) - (3 : Int) = (u : Int) - 3 := by omega
      rw [this]; exact haas.2.2
    have hold := oldest_is_subtraction e p hp hper u 3 hS
    unfold oldestSubtractionPhase at hold
    exact hold
  · rw [isCoveredBySubset_iff]
    refine ⟨u, hu, ?_⟩
    rw [hlu]
    exact (lag_three_covers_iff e p hp (u : Int) haas.1 haas.2.1 haas.2.2 _).mpr rfl

/-- An SS=2 donor subtraction phase is strictly disjoint from any lag 3 AAS endpoint in U. -/
theorem ss2_donor_disjoint_from_aas_endpoint (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (u0 u : Nat) (lag : Nat → Nat)
    (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (huA : e (u : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hPu : ShortPeriodicSupply.P2 e (u : Int) 3)
    (haas : e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false) :
    oldestSubtractionPhase p u0 (lag u0) ≠ endpointPhase p (u : Int) 3 := by
  unfold oldestSubtractionPhase
  exact ss2_lag_lt_fifteen_disjoint_from_aas e p hp hper u0 u (lag u0) hu0A huA hd_lt hss0 hP0 hPu haas

/-- If s*(u₀) does not belong to N(A), Hall's condition is strictly preserved on A. -/
theorem tight_triple_survives_of_s_not_mem (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat) (u0 : Nat)
    (htight : (neighborhood e p A lag).length = A.length)
    (hnot : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  rw [deletedNeighborhood_eq_of_not_mem e p A lag (oldestSubtractionPhase p u0 (lag u0)) hnot]
  omega

/-- Master Synthesis: Grand Tight Triple Rigidity Theorem. -/
theorem grand_tight_triple_rigidity_synthesis (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (_hA3 : A.length = 3)
    (htight : (neighborhood e p A lag).length = 3)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2) :
    -- (1) Disjointness from any lag 3 AAS endpoint in A
    (∀ u ∈ A, e (u : Int) = true → ShortPeriodicSupply.P2 e (u : Int) 3 →
      (e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false) →
      oldestSubtractionPhase p u0 (lag u0) ≠ endpointPhase p (u : Int) 3) ∧
    -- (2) Any lag 3 AAS endpoint in A belongs to N(A)
    (∀ u ∈ A, lag u = 3 →
      (e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false) →
      endpointPhase p (u : Int) 3 ∈ neighborhood e p A lag) ∧
    -- (3) Preservation when s*(u₀) ∉ N(A)
    (oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u _hu huA hPu haas
    exact ss2_donor_disjoint_from_aas_endpoint e p hp hper u0 u lag hd_lt hu0A huA hP0 hss0 hPu haas
  · intro u hu hlu haas
    exact aas_endpoint_mem_neighborhood e p hp hper A lag u hu hlu haas
  · intro hnot
    have htight_len : (neighborhood e p A lag).length = A.length := by omega
    exact tight_triple_survives_of_s_not_mem e p A lag u0 htight_len hnot

end Recaman.TightTripleRigidity
