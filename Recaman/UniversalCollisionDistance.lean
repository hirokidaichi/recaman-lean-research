import Recaman.LagSevenCollisionDistance

/-!
# UniversalCollisionDistance: Universal Modular Distance Obstruction for Window Collisions

This module establishes the universal modular distance obstruction for candidate collisions
between a donor subtraction s*(u₀) and arbitrary windows of any lag d:

1. `universal_collision_residue_cases`: Any window w covering s*(u₀) at subtraction offset 1 + i
   forces `(u₀ - w) % p = (d₀ - 1 - i) % p`.
2. `universal_avoids_of_not_in_residues`: If `(u₀ - w) % p` does not equal `(d₀ - 1 - i) % p`
   for any subtraction offset i of w, then w strictly avoids s*(u₀).
3. `universal_not_mem_neighborhood_of_distance`: Under the distance non-congruence condition,
   `s*(u₀) ∉ N([w])` for arbitrary windows w.
4. `universal_tight_subset_not_mem_of_distance`: In any subset A, if every window w ∈ A satisfies
   either distance non-congruence or is a lag 3 AAS window, then `s*(u₀) ∉ N(A)`.
5. `universal_tight_subset_survives_of_distance`: Any tight subset A of arbitrary size where every
   window is either distance non-congruent or lag 3 AAS strictly survives deletion with zero loss:
   `|A| ≤ |N(A) \ {s*(u₀)}|`.
6. `grand_universal_collision_distance_synthesis`: Master synthesis theorem for universal distance obstruction.
-/

namespace Recaman.UniversalCollisionDistance

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
open SharpPeriodicSupply LagSevenCollisionDistance

/-- Any window w covering s*(u₀) at subtraction offset 1 + i forces (u₀ - w) % p = (d₀ - 1 - i) % p. -/
theorem universal_collision_residue_cases (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (u0 w : Nat) (d0 d : Nat)
    (hcov : WindowCoversSubtraction e p (w : Int) d (oldestSubtractionPhase p u0 d0)) :
    ∃ i : Nat, i < d ∧ e ((w : Int) - 1 - (i : Int)) = false ∧
      ((u0 : Int) - (w : Int)) % (p : Int) = ((d0 : Int) - 1 - (i : Int)) % (p : Int) := by
  obtain ⟨i, hi, he, hmod⟩ := hcov
  unfold oldestSubtractionPhase endpointPhase at hmod
  have hcast := phase_cast p hp ((u0 : Int) - (d0 : Int))
  rw [hcast] at hmod
  refine ⟨i, hi, he, ?_⟩
  exact collision_mod_residue_eq p (u0 : Int) (w : Int) d0 i hmod

/-- If (u₀ - w) % p does not equal (d₀ - 1 - i) % p for any subtraction offset i of w,
then w strictly avoids s*(u₀). -/
theorem universal_avoids_of_not_in_residues (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (u0 w : Nat) (d0 d : Nat)
    (hnot : ∀ i : Nat, i < d → e ((w : Int) - 1 - (i : Int)) = false →
      ((u0 : Int) - (w : Int)) % (p : Int) ≠ ((d0 : Int) - 1 - (i : Int)) % (p : Int)) :
    ¬ WindowCoversSubtraction e p (w : Int) d (oldestSubtractionPhase p u0 d0) := by
  intro hcov
  obtain ⟨i, hi, he, heq⟩ := universal_collision_residue_cases e p hp u0 w d0 d hcov
  exact hnot i hi he heq

/-- Under the distance non-congruence condition, s*(u₀) ∉ N([w]) for arbitrary windows w. -/
theorem universal_not_mem_neighborhood_of_distance (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (u0 w : Nat) (d0 : Nat) (lag : Nat → Nat)
    (hnot : ∀ i : Nat, i < lag w → e ((w : Int) - 1 - (i : Int)) = false →
      ((u0 : Int) - (w : Int)) % (p : Int) ≠ ((d0 : Int) - 1 - (i : Int)) % (p : Int)) :
    oldestSubtractionPhase p u0 d0 ∉ neighborhood e p [w] lag := by
  intro hmem
  rw [mem_neighborhood_iff] at hmem
  obtain ⟨_, hcov⟩ := hmem
  rw [isCoveredBySubset_iff] at hcov
  obtain ⟨x, hx, i, hi, he, hmod⟩ := hcov
  simp only [List.mem_singleton] at hx
  subst x
  have hwin : WindowCoversSubtraction e p (w : Int) (lag w) (oldestSubtractionPhase p u0 d0) := by
    unfold WindowCoversSubtraction
    exact ⟨i, hi, he, hmod⟩
  exact universal_avoids_of_not_in_residues e p hp u0 w d0 (lag w) hnot hwin

/-- In any subset A, if every window w ∈ A satisfies either distance non-congruence or is a lag 3 AAS
window, then s*(u₀) ∉ N(A). -/
theorem universal_tight_subset_not_mem_of_distance
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hdist : ∀ w ∈ A, (∃ i : Nat, i < lag w ∧ e ((w : Int) - 1 - (i : Int)) = false ∧
      ((u0 : Int) - (w : Int)) % (p : Int) = (((lag u0 : Int) - 1 - (i : Int)) % (p : Int))) →
      (lag w = 3 ∧ e ((w : Int) - 1) = true ∧ e ((w : Int) - 2) = true ∧ e ((w : Int) - 3) = false ∧
       ShortPeriodicSupply.P2 e (w : Int) 3 ∧ e (w : Int) = true)) :
    oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag := by
  rw [universal_mem_neighborhood_iff]
  rintro ⟨w, hw, hcov⟩
  have hcov_w := hcov
  rw [mem_neighborhood_iff] at hcov
  obtain ⟨_, hcov'⟩ := hcov
  rw [isCoveredBySubset_iff] at hcov'
  obtain ⟨x, hx, i, hi, he, hmod⟩ := hcov'
  simp only [List.mem_singleton] at hx
  subst x
  have hwin : WindowCoversSubtraction e p (w : Int) (lag w) (oldestSubtractionPhase p u0 (lag u0)) :=
    ⟨i, hi, he, hmod⟩
  obtain ⟨i', hi', he', heq⟩ := universal_collision_residue_cases e p hp u0 w (lag u0) (lag w) hwin
  have hcand : ∃ i : Nat, i < lag w ∧ e ((w : Int) - 1 - (i : Int)) = false ∧
      ((u0 : Int) - (w : Int)) % (p : Int) = (((lag u0 : Int) - 1 - (i : Int)) % (p : Int)) :=
    ⟨i', hi', he', heq⟩
  obtain ⟨hlw, haas1, haas2, haas3, hPw, hwA⟩ := hdist w hw hcand
  have haas : e ((w : Int) - 1) = true ∧ e ((w : Int) - 2) = true ∧ e ((w : Int) - 3) = false :=
    ⟨haas1, haas2, haas3⟩
  exact universal_non_aas_witness e p hp hper u0 lag hd_lt hu0A hP0 hss0 w hcov_w hwA hlw hPw haas

/-- Any tight subset A of arbitrary size where every window is either distance non-congruent or lag 3 AAS
strictly survives deletion with zero loss. -/
theorem universal_tight_subset_survives_of_distance
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (htight : (neighborhood e p A lag).length = A.length)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hdist : ∀ w ∈ A, (∃ i : Nat, i < lag w ∧ e ((w : Int) - 1 - (i : Int)) = false ∧
      ((u0 : Int) - (w : Int)) % (p : Int) = (((lag u0 : Int) - 1 - (i : Int)) % (p : Int))) →
      (lag w = 3 ∧ e ((w : Int) - 1) = true ∧ e ((w : Int) - 2) = true ∧ e ((w : Int) - 3) = false ∧
       ShortPeriodicSupply.P2 e (w : Int) 3 ∧ e (w : Int) = true)) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot := universal_tight_subset_not_mem_of_distance e p hp hper A lag u0 hd_lt hu0A hP0 hss0 hdist
  exact arbitrary_period_tight_survives_of_not_mem e p A lag htight u0 hnot

/-- Master Synthesis: Grand Universal Collision Distance Theorem. -/
theorem grand_universal_collision_distance_synthesis
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (htight : (neighborhood e p A lag).length = A.length)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hdist : ∀ w ∈ A, (∃ i : Nat, i < lag w ∧ e ((w : Int) - 1 - (i : Int)) = false ∧
      ((u0 : Int) - (w : Int)) % (p : Int) = (((lag u0 : Int) - 1 - (i : Int)) % (p : Int))) →
      (lag w = 3 ∧ e ((w : Int) - 1) = true ∧ e ((w : Int) - 2) = true ∧ e ((w : Int) - 3) = false ∧
       ShortPeriodicSupply.P2 e (w : Int) 3 ∧ e (w : Int) = true)) :
    -- (1) Neighborhood avoidance
    (oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag) ∧
    -- (2) Strict Hall condition preservation
    (A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) := by
  refine ⟨universal_tight_subset_not_mem_of_distance e p hp hper A lag u0 hd_lt hu0A hP0 hss0 hdist,
          universal_tight_subset_survives_of_distance e p hp hper A lag htight u0 hd_lt hu0A hP0 hss0 hdist⟩

end Recaman.UniversalCollisionDistance
