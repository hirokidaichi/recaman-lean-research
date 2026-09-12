import Recaman.UniversalTightDecomposition

/-!
# LagSevenCollisionDistance: Modular Distance Obstruction for Lag 7 Window Collisions

This module formalizes the modular distance obstruction governing candidate collisions
between a donor subtraction s*(u₀) and a lag 7 window w:

1. `collision_implies_offset_congruence`: Any subtraction covered by a window at w at offset
   `1 + i` satisfies `(u₀ - w) ≡ (d₀ - 1 - i) [MOD p]`.
2. `mod_eq_of_sub_mod_zero`: Fundamental modular lemma: `(x - y) % p = 0 → x % p = y % p`.
3. `collision_mod_residue_eq`: If w covers s*(u₀) at offset `1 + i`, then `(u₀ - w) % p = (d₀ - 1 - i) % p`.
4. `lag7_collision_residue_cases`: If a lag 7 window w covers s*(u₀), then `(u₀ - w) % p` must
   equal `(d₀ - 1 - i) % p` for some `i ∈ {0, 1, 2, 3, 4, 5, 6}`.
5. `lag7_avoids_of_not_in_residues`: If `(u₀ - w) % p` does not equal `(d₀ - 1 - i) % p` for any `i < 7`,
   then w strictly avoids s*(u₀).
6. `lag7_not_mem_neighborhood_of_distance`: Under the distance non-congruence condition,
   `s*(u₀) ∉ N([w])`.
7. `tight_triple_survives_of_distance`: Any tight triple containing a lag 7 window w satisfying
   the distance non-congruence condition strictly survives deletion with zero loss.
8. `tight_quad_single_survives_of_distance`: Any tight quadruple containing a single lag 7 window w
   satisfying the distance condition strictly survives deletion with zero loss.
9. `grand_lag_seven_collision_distance_synthesis`: Master synthesis theorem for modular distance obstruction.
-/

namespace Recaman.LagSevenCollisionDistance

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
open SharpPeriodicSupply

/-- Fundamental modular lemma: (x - y) % p = 0 implies x % p = y % p. -/
theorem mod_eq_of_sub_mod_zero (p : Nat) (x y : Int)
    (h : (x - y) % (p : Int) = 0) :
    x % (p : Int) = y % (p : Int) := by
  have hxy : x = (x - y) + y := by omega
  have hmod : x % (p : Int) = ((x - y) + y) % (p : Int) := congrArg (· % (p : Int)) hxy
  rw [hmod, Int.add_emod, h, Int.zero_add, Int.emod_emod]

/-- Any subtraction covered by a window at w at offset 1 + i satisfies (u₀ - w) ≡ (d₀ - 1 - i) [MOD p]. -/
theorem collision_implies_offset_congruence (p : Nat)
    (u0 w : Int) (d0 : Nat)
    (i : Nat)
    (hcov : (w - 1 - (i : Int)) % (p : Int) = (u0 - (d0 : Int)) % (p : Int)) :
    ((u0 - w) - ((d0 : Int) - 1 - (i : Int))) % (p : Int) = 0 := by
  have : (u0 - (d0 : Int)) - (w - 1 - (i : Int)) = (u0 - w) - ((d0 : Int) - 1 - (i : Int)) := by omega
  rw [← this]
  rw [Int.sub_emod, hcov, Int.sub_self, Int.zero_emod]

/-- If w covers s*(u₀) at offset 1 + i, then (u₀ - w) % p = (d₀ - 1 - i) % p. -/
theorem collision_mod_residue_eq (p : Nat)
    (u0 w : Int) (d0 : Nat)
    (i : Nat)
    (hcov : (w - 1 - (i : Int)) % (p : Int) = (u0 - (d0 : Int)) % (p : Int)) :
    (u0 - w) % (p : Int) = ((d0 : Int) - 1 - (i : Int)) % (p : Int) :=
  mod_eq_of_sub_mod_zero p (u0 - w) ((d0 : Int) - 1 - (i : Int))
    (collision_implies_offset_congruence p u0 w d0 i hcov)

/-- If a lag 7 window w covers s*(u₀), then (u₀ - w) % p must equal (d₀ - 1 - i) % p for some i < 7. -/
theorem lag7_collision_residue_cases (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (u0 w : Nat) (d0 : Nat)
    (hcov : WindowCoversSubtraction e p (w : Int) 7 (oldestSubtractionPhase p u0 d0)) :
    ∃ i : Nat, i < 7 ∧ ((u0 : Int) - (w : Int)) % (p : Int) = ((d0 : Int) - 1 - (i : Int)) % (p : Int) := by
  obtain ⟨i, hi, _, hmod⟩ := hcov
  unfold oldestSubtractionPhase endpointPhase at hmod
  have hcast := phase_cast p hp ((u0 : Int) - (d0 : Int))
  rw [hcast] at hmod
  refine ⟨i, hi, ?_⟩
  exact collision_mod_residue_eq p (u0 : Int) (w : Int) d0 i hmod

/-- If (u₀ - w) % p does not equal (d₀ - 1 - i) % p for any i < 7, then w strictly avoids s*(u₀). -/
theorem lag7_avoids_of_not_in_residues (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (u0 w : Nat) (d0 : Nat)
    (hnot : ∀ i : Nat, i < 7 → ((u0 : Int) - (w : Int)) % (p : Int) ≠ ((d0 : Int) - 1 - (i : Int)) % (p : Int)) :
    ¬ WindowCoversSubtraction e p (w : Int) 7 (oldestSubtractionPhase p u0 d0) := by
  intro hcov
  obtain ⟨i, hi, heq⟩ := lag7_collision_residue_cases e p hp u0 w d0 hcov
  exact hnot i hi heq

/-- Under the distance non-congruence condition, s*(u₀) ∉ N([w]). -/
theorem lag7_not_mem_neighborhood_of_distance (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (u0 w : Nat) (d0 : Nat) (lag : Nat → Nat)
    (hlw : lag w = 7)
    (hnot : ∀ i : Nat, i < 7 → ((u0 : Int) - (w : Int)) % (p : Int) ≠ ((d0 : Int) - 1 - (i : Int)) % (p : Int)) :
    oldestSubtractionPhase p u0 d0 ∉ neighborhood e p [w] lag := by
  intro hmem
  rw [mem_neighborhood_iff] at hmem
  obtain ⟨_, hcov⟩ := hmem
  rw [isCoveredBySubset_iff] at hcov
  obtain ⟨x, hx, i, hi, he, hmod⟩ := hcov
  simp only [List.mem_singleton] at hx
  subst x
  rw [hlw] at hi
  have hwin : WindowCoversSubtraction e p (w : Int) 7 (oldestSubtractionPhase p u0 d0) := by
    unfold WindowCoversSubtraction
    exact ⟨i, hi, he, hmod⟩
  exact lag7_avoids_of_not_in_residues e p hp u0 w d0 hnot hwin

/-- Any tight triple containing a lag 7 window w satisfying the distance non-congruence condition
strictly survives deletion with zero loss. -/
theorem tight_triple_survives_of_distance
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (_hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (hA3 : A.length = 3)
    (htight : (neighborhood e p A lag).length = 3)
    (v1 v2 w : Nat)
    (_hv1 : v1 ∈ A) (_hv2 : v2 ∈ A) (hw : w ∈ A)
    (_hl1 : lag v1 = 3) (_hl2 : lag v2 = 3) (hlw : lag w = 7)
    (_haas1 : e ((v1 : Int) - 1) = true ∧ e ((v1 : Int) - 2) = true ∧ e ((v1 : Int) - 3) = false)
    (_haas2 : e ((v2 : Int) - 1) = true ∧ e ((v2 : Int) - 2) = true ∧ e ((v2 : Int) - 3) = false)
    (hNw : (neighborhood e p [w] lag).length = 3)
    (u0 : Nat)
    (hnot : ∀ i : Nat, i < 7 → ((u0 : Int) - (w : Int)) % (p : Int) ≠ (((lag u0 : Int) - 1 - (i : Int)) % (p : Int))) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot_w := lag7_not_mem_neighborhood_of_distance e p hp u0 w (lag u0) lag hlw hnot
  exact tight_triple_survives_of_lag7_not_covers e p A lag hA3 htight w hw hNw u0 hnot_w

/-- Any tight quadruple containing a single lag 7 window w satisfying the distance condition
strictly survives deletion with zero loss. -/
theorem tight_quad_single_survives_of_distance
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
    (hlw : lag w = 7)
    (haas1 : e ((v1 : Int) - 1) = true ∧ e ((v1 : Int) - 2) = true ∧ e ((v1 : Int) - 3) = false)
    (haas2 : e ((v2 : Int) - 1) = true ∧ e ((v2 : Int) - 2) = true ∧ e ((v2 : Int) - 3) = false)
    (haas3 : e ((v3 : Int) - 1) = true ∧ e ((v3 : Int) - 2) = true ∧ e ((v3 : Int) - 3) = false)
    (hP1 : ShortPeriodicSupply.P2 e (v1 : Int) 3)
    (hP2 : ShortPeriodicSupply.P2 e (v2 : Int) 3)
    (hP3 : ShortPeriodicSupply.P2 e (v3 : Int) 3)
    (hv1A : e (v1 : Int) = true) (hv2A : e (v2 : Int) = true) (hv3A : e (v3 : Int) = true)
    (hnot : ∀ i : Nat, i < 7 → ((u0 : Int) - (w : Int)) % (p : Int) ≠ (((lag u0 : Int) - 1 - (i : Int)) % (p : Int))) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot_w := lag7_not_mem_neighborhood_of_distance e p hp u0 w (lag u0) lag hlw hnot
  exact tight_quad_single_non_aas_survives_of_not_covers e p hp hper A lag hA4 htight v1 v2 v3 w hA u0 hd_lt hu0A hP0 hss0 hl1 hl2 hl3 haas1 haas2 haas3 hP1 hP2 hP3 hv1A hv2A hv3A hnot_w

/-- Master Synthesis: Grand Lag 7 Collision Distance Theorem. -/
theorem grand_lag_seven_collision_distance_synthesis
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (u0 w : Nat) (d0 : Nat) (lag : Nat → Nat)
    (hlw : lag w = 7)
    (hnot : ∀ i : Nat, i < 7 → ((u0 : Int) - (w : Int)) % (p : Int) ≠ ((d0 : Int) - 1 - (i : Int)) % (p : Int)) :
    -- (1) Avoidance of window coverage
    (¬ WindowCoversSubtraction e p (w : Int) 7 (oldestSubtractionPhase p u0 d0)) ∧
    -- (2) Avoidance of individual neighborhood
    (oldestSubtractionPhase p u0 d0 ∉ neighborhood e p [w] lag) := by
  refine ⟨lag7_avoids_of_not_in_residues e p hp u0 w d0 hnot,
          lag7_not_mem_neighborhood_of_distance e p hp u0 w d0 lag hlw hnot⟩

end Recaman.LagSevenCollisionDistance
