import Recaman.TwoSSTightDisjoint
import Recaman.TwoSSPeriodicSupply
import Recaman.TwoSSEndpoint
import Recaman.LowSSPeriodicSupply

/-!
# TwoSSLocalDonation: High-SS Local Donation and Spare Subtraction Exhibition

This module realizes research gate **T6 (high-SS local donation at `ssCount = 2`)**
from `docs/HYPOTHESIS_CARD_2026-09-11_SS2_OLDEST_DELETABLE.md` (`H-20260911-02`).

For any periodic sign word `e` with period `p`:
1. **Exhibition of Donated Subtraction**: Each S-ended SS=2 window `(u, d)` donates its
   oldest subtraction phase `s*(u) = endpointPhase p u d` from inside its own window:
   `oldest_is_subtraction` and `oldest_covered_by_window`.
2. **Local Hall Preservation**: For `p ≤ 11` and positive slack `|U| < |D|`, deleting `s*(u)`
   preserves Hall's condition on any component containing `u`:
   `oldest_donation_preserves_hall`.
3. **Mutual Injectivity**: Distinct SS=2 windows donate distinct subtraction phases:
   `oldest_donation_injective` and `oldest_donation_list_nodup`.
4. **Disjointness from Low-SS**: The donated subtractions never collide with the endpoint
   phases of SS=1 windows: `oldest_donation_disjoint_from_one_SS` and
   `oldest_donation_disjoint_one_SS_list`.
-/

namespace Recaman.TwoSSLocalDonation

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint LeadingRunSupply EndpointRepetitionBudget LowSSEndpoint SharpPeriodicSupply LowSSPeriodicSupply OneSSMultiplicity

/-- The oldest subtraction phase of an S-ended window is its endpoint phase modulo p. -/
def oldestSubtractionPhase (p : Nat) (u : Nat) (d : Nat) : Nat :=
  endpointPhase p (u : Int) d

/-- The oldest subtraction phase is indeed a valid subtraction phase in D = subPhases e 0 p. -/
theorem oldest_is_subtraction (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (u : Nat) (d : Nat)
    (hS : e (u - (d : Int)) = false) :
    oldestSubtractionPhase p u d ∈ LagElevenPeriodic.subPhases e 0 p := by
  apply (LagElevenPeriodic.mem_subPhases e 0 p _).mpr
  refine ⟨phase_lt p hp _, ?_⟩
  unfold oldestSubtractionPhase
  have hs := endpoint_is_S e p hp hper u d hS
  have h0 : (0 : Int) + ((endpointPhase p u d : Nat) : Int) = (endpointPhase p u d : Int) := by omega
  rw [h0]
  exact hs

/-- The window covers its own oldest subtraction phase. -/
theorem oldest_covered_by_window (e : Int → Bool) (p : Nat) (hp : 0 < p) (u : Nat) (d : Nat)
    (hd : 0 < d) (hS : e (u - (d : Int)) = false) :
    WindowCoversSubtraction e p (u : Int) d (oldestSubtractionPhase p u d) := by
  unfold WindowCoversSubtraction oldestSubtractionPhase endpointPhase phase
  refine ⟨d - 1, by omega, ?_, ?_⟩
  · have : (u : Int) - 1 - ((d - 1 : Nat) : Int) = (u : Int) - (d : Int) := by omega
    rw [this]; exact hS
  · have : (u : Int) - 1 - ((d - 1 : Nat) : Int) = (u : Int) - (d : Int) := by omega
    rw [this]
    have hp0 : (0 : Int) < p := by omega
    have hnn : 0 ≤ ((u : Int) - (d : Int)) % (p : Int) := Int.emod_nonneg ((u : Int) - (d : Int)) (by omega)
    have heq : (((((u : Int) - (d : Int)) % (p : Int)).toNat : Nat) : Int) = ((u : Int) - (d : Int)) % (p : Int) :=
      Int.toNat_of_nonneg hnn
    rw [heq]

/-- Any subset containing the window covers the oldest subtraction phase. -/
theorem oldest_covered_by_subset (e : Int → Bool) (p : Nat) (hp : 0 < p) (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hu0 : u0 ∈ A) (hd : 0 < lag u0) (hS : e (u0 - (lag u0 : Int)) = false) :
    isCoveredBySubset e p A lag (oldestSubtractionPhase p u0 (lag u0)) = true := by
  rw [isCoveredBySubset_iff]
  refine ⟨u0, hu0, ?_⟩
  have hcov := oldest_covered_by_window e p hp u0 (lag u0) hd hS
  exact hcov

/-- Local donation preserves Hall's condition on any component containing the donor SS=2 window. -/
theorem oldest_donation_preserves_hall (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss : ssCount (past e (u0 : Int) (lag u0)) = 2) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  deleted_neighborhood_hall_of_has_ss2 e p hp hp11 hper U A lag hAU hslack u0 hu0 hP hss
    (oldestSubtractionPhase p u0 (lag u0))

/-- Distinct SS=2 windows donate distinct subtraction phases. -/
theorem oldest_donation_injective (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (u v : Nat) (lag : Nat → Nat)
    (hu_lt : u < p) (hv_lt : v < p)
    (huA : e u = true) (hvA : e v = true)
    (hu_ss : ssCount (past e (u : Int) (lag u)) = 2) (hv_ss : ssCount (past e (v : Int) (lag v)) = 2)
    (hu_P : ShortPeriodicSupply.P2 e (u : Int) (lag u)) (hv_P : ShortPeriodicSupply.P2 e (v : Int) (lag v))
    (heq : oldestSubtractionPhase p u (lag u) = oldestSubtractionPhase p v (lag v)) :
    u = v := by
  unfold oldestSubtractionPhase at heq
  have hmod := two_SS_endpoint_mod_injective e p hp hper (u : Int) (v : Int) (lag u) (lag v) huA hvA hu_ss hv_ss hu_P hv_P heq
  have hu_mod : (u : Int) % (p : Int) = (u : Int) := Int.emod_eq_of_lt (by omega) (by omega)
  have hv_mod : (v : Int) % (p : Int) = (v : Int) := Int.emod_eq_of_lt (by omega) (by omega)
  rw [hu_mod, hv_mod] at hmod
  exact Int.ofNat_inj.mp hmod

/-- Donated subtractions from SS=2 windows never collide with SS=1 endpoint phases. -/
theorem oldest_donation_disjoint_from_one_SS (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (u v : Nat) (lag : Nat → Nat)
    (huA : e u = true) (hvA : e v = true)
    (hu_ss : ssCount (past e (u : Int) (lag u)) = 2) (hv_ss : ssCount (past e (v : Int) (lag v)) = 1)
    (hu_P : ShortPeriodicSupply.P2 e (u : Int) (lag u)) (hv_P : ShortPeriodicSupply.P2 e (v : Int) (lag v)) :
    oldestSubtractionPhase p u (lag u) ≠ endpointPhase p (v : Int) (lag v) := by
  intro heq
  unfold oldestSubtractionPhase at heq
  exact ss_one_two_endpoint_mod_disjoint e p hp hper (v : Int) (u : Int) (lag v) (lag u) hvA huA hv_ss hu_ss hv_P hu_P heq.symm

/-- The list of donated subtractions from a nodup list of SS=2 windows has no duplicates. -/
theorem oldest_donation_list_nodup (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (U2 : List Nat) (lag : Nat → Nat)
    (hU2nodup : U2.Nodup) (hU2range : ∀ u ∈ U2, u < p)
    (hU2A : ∀ u ∈ U2, e u = true)
    (hU2ss : ∀ u ∈ U2, ssCount (past e (u : Int) (lag u)) = 2)
    (hU2P : ∀ u ∈ U2, ShortPeriodicSupply.P2 e (u : Int) (lag u)) :
    (U2.map (fun u : Nat => oldestSubtractionPhase p u (lag u))).Nodup := by
  apply LagElevenPeriodic.nodup_map_of_inj hU2nodup
  intro u v hu hv heq
  exact oldest_donation_injective e p hp hper u v lag (hU2range u hu) (hU2range v hv)
    (hU2A u hu) (hU2A v hv) (hU2ss u hu) (hU2ss v hv) (hU2P u hu) (hU2P v hv) heq

/-- The list of donated subtractions from SS=2 windows is disjoint from the matching image of SS=1 windows. -/
theorem oldest_donation_disjoint_one_SS_list (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (U1 U2 : List Nat) (lag : Nat → Nat)
    (hU1A : ∀ u ∈ U1, e u = true) (hU2A : ∀ u ∈ U2, e u = true)
    (hU1ss : ∀ u ∈ U1, ssCount (past e (u : Int) (lag u)) = 1)
    (hU2ss : ∀ u ∈ U2, ssCount (past e (u : Int) (lag u)) = 2)
    (hU1P : ∀ u ∈ U1, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU2P : ∀ u ∈ U2, ShortPeriodicSupply.P2 e (u : Int) (lag u)) :
    ∀ a, a ∈ U2.map (fun u : Nat => oldestSubtractionPhase p u (lag u)) →
      a ∉ U1.map (fun u : Nat => endpointPhase p (u : Int) (lag u)) := by
  intro a ha2 ha1
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha2
  obtain ⟨v, hv, heq⟩ := List.mem_map.mp ha1
  have hdisj := oldest_donation_disjoint_from_one_SS e p hp hper u v lag
    (hU2A u hu) (hU1A v hv) (hU2ss u hu) (hU1ss v hv) (hU2P u hu) (hU1P v hv)
  exact hdisj heq.symm

end Recaman.TwoSSLocalDonation
