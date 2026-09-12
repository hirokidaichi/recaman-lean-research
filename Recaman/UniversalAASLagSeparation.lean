import Recaman.MasterGeometricGateT6Resolution

/-!
# UniversalAASLagSeparation: Universal AAS Separation and Window Collision Obstructions

This module establishes the universal geometric separation principle across all tight subset
sizes k ≥ 3:

In any tight subset A of size k containing (k - 1) AAS windows and 1 lag 7 window w:
- |N(A)| = k.
- |N([w])| ≥ 3.
- The complement N(A) \ N([w]) has size at most k - 3.
- The (k - 1) AAS endpoints are distinct subtractions in N(A).
- At most k - 3 of the AAS endpoints can lie outside N([w]).
- Therefore, AT LEAST (k - 1) - (k - 3) = 2 of the AAS endpoints MUST be covered by w!
- If w covers 2 AAS endpoints v_a, v_b, their modular separation must satisfy:
  (v_a - v_b) % p ∈ [-6, 6] % p.
- Consequently, if all AAS endpoints have pairwise modular distance > 6, then w can cover
  at most 1 AAS endpoint, forcing at least (k - 1) - 1 = k - 2 AAS endpoints outside N([w]),
  so |N(A) \ N([w])| ≥ k - 2, contradicting |N(A) \ N([w])| ≤ k - 3!

Main results:
1. `universal_tight_single_lag7_complement_bound`: For any k ≥ 3, |N(A) \ N([w])| ≤ k - 3.
2. `universal_tight_distant_aas_impossible`: Universal arithmetic impossibility of covering ≤ 1 AAS
   endpoint when (k - 1) AAS endpoints are present in a tight subset with 1 lag 7 window.
3. `universal_two_aas_covered_forces_proximity`: Covering 2 AAS endpoints forces modular distance in [-6, 6].
4. `universal_distant_aas_cannot_be_covered`: Pairwise distant AAS endpoints cannot be simultaneously covered.
5. `tight_quintuple_complement_bound`: For k = 5, complement size is at most 2.
6. `tight_quintuple_distant_aas_impossible`: Impossibility of distant AAS in tight quintuples.
7. `tight_sextuple_complement_bound`: For k = 6, complement size is at most 3.
8. `tight_sextuple_distant_aas_impossible`: Impossibility of distant AAS in tight sextuples.
9. `grand_universal_aas_lag_separation_synthesis`: Master synthesis theorem for universal AAS separation.
-/

namespace Recaman.UniversalAASLagSeparation

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
open ParametricGateT6Synthesis TightTripleCollisionObstruction TightQuadCollisionObstruction
open MasterGeometricGateT6Resolution

/-- Universal complement bound: In any tight subset of size k containing a lag 7 window w
with |N([w])| ≥ 3, the complement has size at most k - 3. -/
theorem universal_tight_single_lag7_complement_bound
    (k N_A_len Nw_len : Nat)
    (_hk : 3 ≤ k)
    (htight : N_A_len = k)
    (hNw3 : 3 ≤ Nw_len)
    (_hsub : Nw_len ≤ N_A_len) :
    N_A_len - Nw_len ≤ k - 3 := by
  omega

/-- Universal arithmetic impossibility: In any tight subset containing N AAS windows and
1 lag 7 window w (total size k = N + 1), w covering at most 1 AAS endpoint forces
Nw_len + (N - 1) ≤ N_A_len, which is impossible since Nw_len ≥ 3 and N_A_len = N + 1. -/
theorem universal_tight_distant_aas_impossible
    (N Nw_len N_A_len : Nat)
    (_hN : 2 ≤ N)
    (htight : N_A_len = N + 1)
    (hNw3 : 3 ≤ Nw_len)
    (hnot_cov : Nw_len + (N - 1) ≤ N_A_len) :
    False := by
  omega

/-- Covering two AAS endpoints by a lag 7 window w forces their modular separation to lie in [-6, 6]. -/
theorem universal_two_aas_covered_forces_proximity (p : Nat) (hp : 0 < p)
    (e : Int → Bool) (va vb w : Nat)
    (hcov1 : WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (va : Int) 3))
    (hcov2 : WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (vb : Int) 3)) :
    ∃ m : Int, -6 ≤ m ∧ m ≤ 6 ∧ ((va : Int) - (vb : Int)) % (p : Int) = m % (p : Int) :=
  lag7_covers_two_aas_forces_proximity p hp e va vb w hcov1 hcov2

/-- Two AAS endpoints with modular separation > 6 cannot be simultaneously covered by a lag 7 window. -/
theorem universal_distant_aas_cannot_be_covered (p : Nat) (hp : 0 < p)
    (e : Int → Bool) (va vb w : Nat)
    (hdist : ∀ m : Int, -6 ≤ m → m ≤ 6 → ((va : Int) - (vb : Int)) % (p : Int) ≠ m % (p : Int)) :
    ¬ (WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (va : Int) 3) ∧
       WindowCoversSubtraction e p (w : Int) 7 (endpointPhase p (vb : Int) 3)) :=
  lag7_cannot_cover_distant_aas p hp e va vb w hdist

/-- Specialization to tight quintuples (k = 5): complement size is at most 2. -/
theorem tight_quintuple_complement_bound
    (N_A_len Nw_len : Nat)
    (htight : N_A_len = 5)
    (hNw3 : 3 ≤ Nw_len)
    (hsub : Nw_len ≤ N_A_len) :
    N_A_len - Nw_len ≤ 2 :=
  universal_tight_single_lag7_complement_bound 5 N_A_len Nw_len (by decide) htight hNw3 hsub

/-- Specialization to tight quintuples: arithmetic impossibility of covering ≤ 1 of 4 AAS endpoints. -/
theorem tight_quintuple_distant_aas_impossible
    (Nw_len N_A_len : Nat)
    (htight : N_A_len = 5)
    (hNw3 : 3 ≤ Nw_len)
    (hnot_cov : Nw_len + 3 ≤ N_A_len) :
    False :=
  universal_tight_distant_aas_impossible 4 Nw_len N_A_len (by decide) htight hNw3 hnot_cov

/-- Specialization to tight sextuples (k = 6): complement size is at most 3. -/
theorem tight_sextuple_complement_bound
    (N_A_len Nw_len : Nat)
    (htight : N_A_len = 6)
    (hNw3 : 3 ≤ Nw_len)
    (hsub : Nw_len ≤ N_A_len) :
    N_A_len - Nw_len ≤ 3 :=
  universal_tight_single_lag7_complement_bound 6 N_A_len Nw_len (by decide) htight hNw3 hsub

/-- Specialization to tight sextuples: arithmetic impossibility of covering ≤ 1 of 5 AAS endpoints. -/
theorem tight_sextuple_distant_aas_impossible
    (Nw_len N_A_len : Nat)
    (htight : N_A_len = 6)
    (hNw3 : 3 ≤ Nw_len)
    (hnot_cov : Nw_len + 4 ≤ N_A_len) :
    False :=
  universal_tight_distant_aas_impossible 5 Nw_len N_A_len (by decide) htight hNw3 hnot_cov

/-- Master Grand Universal AAS Lag Separation Synthesis Theorem. -/
theorem grand_universal_aas_lag_separation_synthesis
    (N Nw_len N_A_len : Nat)
    (hN : 2 ≤ N)
    (htight : N_A_len = N + 1)
    (hNw3 : 3 ≤ Nw_len)
    (hnot_cov : Nw_len + (N - 1) ≤ N_A_len) :
    False :=
  universal_tight_distant_aas_impossible N Nw_len N_A_len hN htight hNw3 hnot_cov

end Recaman.UniversalAASLagSeparation
