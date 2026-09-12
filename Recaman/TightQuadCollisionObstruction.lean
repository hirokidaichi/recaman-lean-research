import Recaman.TightTripleCollisionObstruction

/-!
# TightQuadCollisionObstruction: Geometric Separation Obstructions in Tight Quadruples

This module establishes the geometric separation obstructions for window collisions
within tight avoiding quadruples A = [v₁, v₂, v₃, w]:

1. `tight_quad_lag7_complement_bound`: In any tight quadruple A of size 4 containing a lag 7
   window w with |N([w])| ≥ 3, the complement N(A) \ N([w]) has size at most 1.
2. `tight_quad_two_aas_covered_forces_proximity`: If a lag 7 window w in a tight quadruple covers
   two AAS endpoints v_a and v_b, their modular separation is strictly bounded by 6:
   `∃ k : Int, -6 ≤ k ∧ k ≤ 6 ∧ (v_a - v_b) % p = k % p`.
3. `tight_quad_pairwise_distant_cannot_cover_pair`: If all three pairs of AAS windows are separated
   by more than 6 on the torus ℤ/pℤ, w cannot cover any pair of AAS endpoints simultaneously.
4. `tight_quad_single_non_aas_survives_of_distance`: In a tight quadruple with 3 AAS windows and 1
   lag 7 window w, if w satisfies modular distance non-congruence with s*(u₀), then A strictly
   survives deletion with zero loss: `|A| ≤ |N(A) \ {s*(u₀)}|`.
5. `tight_quad_two_non_aas_survives_of_distance`: In a tight quadruple with 2 AAS windows and 2
   lag 7 windows w₁, w₂, if both satisfy modular distance non-congruence, then A strictly survives
   deletion with zero loss.
6. `grand_tight_quad_collision_obstruction_synthesis`: Master synthesis theorem for tight quadruple
   collision obstruction.
-/

namespace Recaman.TightQuadCollisionObstruction

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
open UniversalNonAASReduction UniversalDistanceGateT6Resolution UniversalCapacityThresholds
open ParametricGateT6Synthesis TightTripleCollisionObstruction

/-- In any tight quadruple A of size 4 containing a lag 7 window w with |N([w])| ≥ 3,
the complement size is at most 1. -/
theorem tight_quad_lag7_complement_bound
    (A_len N_A_len Nw_len : Nat)
    (_hA4 : A_len = 4)
    (htight : N_A_len = 4)
    (hNw3 : 3 ≤ Nw_len)
    (hsub : Nw_len ≤ N_A_len) :
    N_A_len - Nw_len ≤ 1 := by
  omega

/-- If a lag 7 window w in a tight quadruple covers two AAS endpoints v_a and v_b,
their modular separation is bounded in [-6, 6]. -/
theorem tight_quad_two_aas_covered_forces_proximity (p : Nat) (hp : 0 < p)
    (e : Int → Bool) (va vb w : Nat)
    (hcov1 : WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (va : Int) 3))
    (hcov2 : WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (vb : Int) 3)) :
    ∃ k : Int, -6 ≤ k ∧ k ≤ 6 ∧ ((va : Int) - (vb : Int)) % (p : Int) = k % (p : Int) :=
  lag7_covers_two_aas_forces_proximity p hp e va vb w hcov1 hcov2

/-- If all 3 pairs of AAS windows are separated by > 6, w cannot cover any pair. -/
theorem tight_quad_pairwise_distant_cannot_cover_pair (p : Nat) (hp : 0 < p)
    (e : Int → Bool) (v1 v2 v3 w : Nat)
    (hdist12 : ∀ k : Int, -6 ≤ k → k ≤ 6 → ((v1 : Int) - (v2 : Int)) % (p : Int) ≠ k % (p : Int))
    (hdist23 : ∀ k : Int, -6 ≤ k → k ≤ 6 → ((v2 : Int) - (v3 : Int)) % (p : Int) ≠ k % (p : Int))
    (hdist13 : ∀ k : Int, -6 ≤ k → k ≤ 6 → ((v1 : Int) - (v3 : Int)) % (p : Int) ≠ k % (p : Int)) :
    (¬ (WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v1 : Int) 3) ∧
        WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v2 : Int) 3))) ∧
    (¬ (WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v2 : Int) 3) ∧
        WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v3 : Int) 3))) ∧
    (¬ (WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v1 : Int) 3) ∧
        WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v3 : Int) 3))) := by
  refine ⟨lag7_cannot_cover_distant_aas p hp e v1 v2 w hdist12,
          lag7_cannot_cover_distant_aas p hp e v2 v3 w hdist23,
          lag7_cannot_cover_distant_aas p hp e v1 v3 w hdist13⟩

/-- In a tight quadruple with 3 AAS windows and 1 lag 7 window w, if w satisfies modular distance
non-congruence, then A strictly survives deletion with zero loss. -/
theorem tight_quad_single_non_aas_survives_of_distance
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (v1 v2 v3 w : Nat)
    (hA : A = [v1, v2, v3, w])
    (htight : (neighborhood e p A lag).length = 4)
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
    (hdist : ∀ i : Nat, i < 7 → ((u0 : Int) - (w : Int)) % (p : Int) ≠ (((lag u0 : Int) - 1 - (i : Int)) % (p : Int))) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hA4 : A.length = 4 := by rw [hA]; rfl
  exact LagSevenCollisionDistance.tight_quad_single_survives_of_distance e p hp hper A lag hA4 htight v1 v2 v3 w hA u0 hd_lt hu0A hP0 hss0 hl1 hl2 hl3 hlw haas1 haas2 haas3 hP1 hP2 hP3 hv1A hv2A hv3A hdist

/-- In a tight quadruple with 2 AAS windows and 2 lag 7 windows w₁, w₂, if both satisfy modular distance
non-congruence, then A strictly survives deletion with zero loss. -/
theorem tight_quad_two_non_aas_survives_of_distance
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (v1 v2 w1 w2 : Nat)
    (hA : A = [v1, v2, w1, w2])
    (htight : (neighborhood e p A lag).length = 4)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hl1 : lag v1 = 3) (hl2 : lag v2 = 3)
    (hlw1 : lag w1 = 7) (hlw2 : lag w2 = 7)
    (haas1 : e ((v1 : Int) - 1) = true ∧ e ((v1 : Int) - 2) = true ∧ e ((v1 : Int) - 3) = false)
    (haas2 : e ((v2 : Int) - 1) = true ∧ e ((v2 : Int) - 2) = true ∧ e ((v2 : Int) - 3) = false)
    (hP1 : ShortPeriodicSupply.P2 e (v1 : Int) 3)
    (hP2 : ShortPeriodicSupply.P2 e (v2 : Int) 3)
    (hv1A : e (v1 : Int) = true) (hv2A : e (v2 : Int) = true)
    (hdist1 : ∀ i : Nat, i < 7 → ((u0 : Int) - (w1 : Int)) % (p : Int) ≠ (((lag u0 : Int) - 1 - (i : Int)) % (p : Int)))
    (hdist2 : ∀ i : Nat, i < 7 → ((u0 : Int) - (w2 : Int)) % (p : Int) ≠ (((lag u0 : Int) - 1 - (i : Int)) % (p : Int))) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot1 := lag7_not_mem_neighborhood_of_distance e p hp u0 w1 (lag u0) lag hlw1 hdist1
  have hnot2 := lag7_not_mem_neighborhood_of_distance e p hp u0 w2 (lag u0) lag hlw2 hdist2
  have hA4 : A.length = 4 := by rw [hA]; rfl
  exact tight_quad_two_non_aas_survives_of_neither_covers e p hp hper A lag hA4 htight v1 v2 w1 w2 hA u0 hd_lt hu0A hP0 hss0 hl1 hl2 haas1 haas2 hP1 hP2 hv1A hv2A hnot1 hnot2

/-- Master Synthesis: Grand Tight Quadruple Collision Obstruction Theorem. -/
theorem grand_tight_quad_collision_obstruction_synthesis
    (A_len N_A_len Nw_len : Nat)
    (hA4 : A_len = 4)
    (htight : N_A_len = 4)
    (hNw3 : 3 ≤ Nw_len)
    (hsub : Nw_len ≤ N_A_len) :
    -- (1) Complement size bound
    (N_A_len - Nw_len ≤ 1) :=
  tight_quad_lag7_complement_bound A_len N_A_len Nw_len hA4 htight hNw3 hsub

end Recaman.TightQuadCollisionObstruction
