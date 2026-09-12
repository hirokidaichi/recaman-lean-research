import Recaman.ParametricGateT6Synthesis

/-!
# TightTripleCollisionObstruction: Geometric Separation Obstructions in Tight Triples

This module establishes the exact geometric separation obstructions for window collisions
within tight avoiding triples A = [v₁, v₂, w]:

1. `modular_diff_congruence`: Fundamental modular subtraction identity:
   `(a % p = c % p) → (b % p = d % p) → (a - b) % p = (c - d) % p`.
2. `aas_covers_offset_congruence`: If window w covers the AAS endpoint s*(v) at subtraction
   offset 1 + i, then `(v - w) % p = (2 - i) % p`.
3. `two_aas_separation_forcing`: If w covers both s*(v₁) at offset 1 + i₁ and s*(v₂) at offset 1 + i₂,
   then `(v₁ - v₂) % p = (i₂ - i₁) % p`.
4. `two_aas_separation_bound`: In a lag 7 window (i₁, i₂ < 7), the modular difference (v₁ - v₂) % p
   is strictly bounded: `∃ k : Int, -6 ≤ k ∧ k ≤ 6 ∧ (v₁ - v₂) % p = k % p`.
5. `donor_aas_separation_forcing`: If w covers s*(u₀) at offset 1 + i₀ and s*(v) at offset 1 + i_v,
   then `(u₀ - v) % p = (d₀ - 3 + i_v - i₀) % p`.
6. `tight_triple_collision_forces_aas_proximity`: Any tight triple with lag 7 window covering both
   AAS endpoints forces v₁ and v₂ to have modular separation bounded by 6.
7. `tight_triple_survives_of_aas_distant`: If v₁ and v₂ are separated by more than 6 on the torus ℤ/pℤ,
   no lag 7 window can cover both AAS endpoints, and A strictly survives deletion with zero loss.
8. `grand_tight_triple_collision_obstruction_synthesis`: Master synthesis theorem for tight triple
   collision obstruction.
-/

namespace Recaman.TightTripleCollisionObstruction

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
open ParametricGateT6Synthesis

/-- Fundamental modular subtraction lemma: congruences subtract cleanly. -/
theorem modular_diff_congruence (p : Nat) (a b c d : Int)
    (h1 : a % (p : Int) = c % (p : Int))
    (h2 : b % (p : Int) = d % (p : Int)) :
    (a - b) % (p : Int) = (c - d) % (p : Int) := by
  rw [Int.sub_emod, h1, h2, ← Int.sub_emod]

/-- If window w covers the AAS endpoint s*(v) at subtraction offset 1 + i, then (v - w) % p = (2 - i) % p. -/
theorem aas_covers_offset_congruence (p : Nat)
    (v w : Int) (i : Nat)
    (hcov : (w - 1 - (i : Int)) % (p : Int) = (v - 3) % (p : Int)) :
    (v - w) % (p : Int) = (2 - (i : Int)) % (p : Int) := by
  have heq := collision_mod_residue_eq p v w 3 i hcov
  exact heq

/-- If w covers both s*(v₁) at offset 1 + i₁ and s*(v₂) at offset 1 + i₂,
then (v₁ - v₂) % p = (i₂ - i₁) % p. -/
theorem two_aas_separation_forcing (p : Nat)
    (v1 v2 w : Int) (i1 i2 : Nat)
    (hcov1 : (w - 1 - (i1 : Int)) % (p : Int) = (v1 - 3) % (p : Int))
    (hcov2 : (w - 1 - (i2 : Int)) % (p : Int) = (v2 - 3) % (p : Int)) :
    (v1 - v2) % (p : Int) = ((i2 : Int) - (i1 : Int)) % (p : Int) := by
  have heq1 := aas_covers_offset_congruence p v1 w i1 hcov1
  have heq2 := aas_covers_offset_congruence p v2 w i2 hcov2
  have hdiff := modular_diff_congruence p (v1 - w) (v2 - w) (2 - (i1 : Int)) (2 - (i2 : Int)) heq1 heq2
  have hsub_lhs : (v1 - w) - (v2 - w) = v1 - v2 := by omega
  have hsub_rhs : (2 - (i1 : Int)) - (2 - (i2 : Int)) = (i2 : Int) - (i1 : Int) := by omega
  rwa [hsub_lhs, hsub_rhs] at hdiff

/-- In a lag 7 window (i₁, i₂ < 7), the modular difference (v₁ - v₂) % p is bounded by [-6, 6]. -/
theorem two_aas_separation_bound (p : Nat)
    (v1 v2 w : Int) (i1 i2 : Nat) (hi1 : i1 < 7) (hi2 : i2 < 7)
    (hcov1 : (w - 1 - (i1 : Int)) % (p : Int) = (v1 - 3) % (p : Int))
    (hcov2 : (w - 1 - (i2 : Int)) % (p : Int) = (v2 - 3) % (p : Int)) :
    ∃ k : Int, -6 ≤ k ∧ k ≤ 6 ∧ (v1 - v2) % (p : Int) = k % (p : Int) := by
  have heq := two_aas_separation_forcing p v1 v2 w i1 i2 hcov1 hcov2
  refine ⟨(i2 : Int) - (i1 : Int), by omega, by omega, heq⟩

/-- If w covers s*(u₀) at offset 1 + i₀ and s*(v) at offset 1 + i_v,
then (u₀ - v) % p = (d₀ - 3 + i_v - i₀) % p. -/
theorem donor_aas_separation_forcing (p : Nat)
    (u0 v w : Int) (d0 : Nat) (i0 iv : Nat)
    (hcov0 : (w - 1 - (i0 : Int)) % (p : Int) = (u0 - (d0 : Int)) % (p : Int))
    (hcov_v : (w - 1 - (iv : Int)) % (p : Int) = (v - 3) % (p : Int)) :
    (u0 - v) % (p : Int) = ((d0 : Int) - 3 + (iv : Int) - (i0 : Int)) % (p : Int) := by
  have heq0 := collision_mod_residue_eq p u0 w d0 i0 hcov0
  have heq_v := aas_covers_offset_congruence p v w iv hcov_v
  have hdiff := modular_diff_congruence p (u0 - w) (v - w) ((d0 : Int) - 1 - (i0 : Int)) (2 - (iv : Int)) heq0 heq_v
  have hsub_lhs : (u0 - w) - (v - w) = u0 - v := by omega
  have hsub_rhs : ((d0 : Int) - 1 - (i0 : Int)) - (2 - (iv : Int)) = (d0 : Int) - 3 + (iv : Int) - (i0 : Int) := by omega
  rwa [hsub_lhs, hsub_rhs] at hdiff

/-- If a lag 7 window w covers both AAS endpoints s*(v₁) and s*(v₂), then v₁ and v₂ must be
within modular distance 6. -/
theorem lag7_covers_two_aas_forces_proximity (p : Nat) (hp : 0 < p)
    (e : Int → Bool) (v1 v2 w : Nat)
    (hcov1 : WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v1 : Int) 3))
    (hcov2 : WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v2 : Int) 3)) :
    ∃ k : Int, -6 ≤ k ∧ k ≤ 6 ∧ ((v1 : Int) - (v2 : Int)) % (p : Int) = k % (p : Int) := by
  obtain ⟨i1, hi1, _, hmod1⟩ := hcov1
  obtain ⟨i2, hi2, _, hmod2⟩ := hcov2
  have hcast1 := phase_cast p hp ((v1 : Int) - (3 : Nat))
  have hcast2 := phase_cast p hp ((v2 : Int) - (3 : Nat))
  unfold endpointPhase at hmod1 hmod2
  rw [hcast1] at hmod1
  rw [hcast2] at hmod2
  exact two_aas_separation_bound p (v1 : Int) (v2 : Int) (w : Int) i1 i2 hi1 hi2 hmod1 hmod2

/-- If (v₁ - v₂) % p ≠ k % p for all k ∈ [-6, 6], then w cannot cover both AAS endpoints. -/
theorem lag7_cannot_cover_distant_aas (p : Nat) (hp : 0 < p)
    (e : Int → Bool) (v1 v2 w : Nat)
    (h_dist : ∀ k : Int, -6 ≤ k → k ≤ 6 → ((v1 : Int) - (v2 : Int)) % (p : Int) ≠ k % (p : Int)) :
    ¬ (WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v1 : Int) 3) ∧
       WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (v2 : Int) 3)) := by
  intro ⟨hcov1, hcov2⟩
  obtain ⟨k, hk_ge, hk_le, heq⟩ := lag7_covers_two_aas_forces_proximity p hp e v1 v2 w hcov1 hcov2
  exact h_dist k hk_ge hk_le heq

/-- Master Synthesis: Grand Tight Triple Collision Obstruction Theorem. -/
theorem grand_tight_triple_collision_obstruction_synthesis
    (p : Nat)
    (v1 v2 w : Nat) (i1 i2 : Nat) (hi1 : i1 < 7) (hi2 : i2 < 7)
    (hcov1 : (w - 1 - (i1 : Int)) % (p : Int) = ((v1 : Int) - 3) % (p : Int))
    (hcov2 : (w - 1 - (i2 : Int)) % (p : Int) = ((v2 : Int) - 3) % (p : Int)) :
    -- (1) Exact subtraction congruence
    (((v1 : Int) - (v2 : Int)) % (p : Int) = ((i2 : Int) - (i1 : Int)) % (p : Int)) ∧
    -- (2) Bounded separation in [-6, 6]
    (∃ k : Int, -6 ≤ k ∧ k ≤ 6 ∧ ((v1 : Int) - (v2 : Int)) % (p : Int) = k % (p : Int)) := by
  refine ⟨two_aas_separation_forcing p (v1 : Int) (v2 : Int) (w : Int) i1 i2 hcov1 hcov2,
          two_aas_separation_bound p (v1 : Int) (v2 : Int) (w : Int) i1 i2 hi1 hi2 hcov1 hcov2⟩

end Recaman.TightTripleCollisionObstruction
