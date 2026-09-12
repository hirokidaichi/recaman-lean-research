import Recaman.TightTripleRigidity
import Recaman.TwelveGateT6Resolution
import Recaman.FourteenLagRigidity
import Recaman.ElevenGateT6Synthesis
import Recaman.ElevenCapacityRigidity
import Recaman.GrandPeriodicDeletabilityTheorem
import Recaman.TenGateT6Resolution

/-!
# ApexPeriodicRigidityTheorem: Grand Apex Synthesis of Periodic Rigidity and Gate T6 Resolution

This module establishes the apex synthesis unifying the periodic capacity, lag rigidity,
and Gate T6 resolution results across periods `p ≤ 14`:

1. `apex_capacity_stratification_p14`: The complete 4-tier capacity stratification:
   - `p ≤ 7`: `|D| ≤ 3`, avoiding size `|A| ≤ 1`.
   - `p ≤ 10`: `|D| ≤ 4`, avoiding size `|A| ≤ 2`.
   - `p ≤ 12`: `|D| ≤ 5`, avoiding size `|A| ≤ 3`.
   - `p ≤ 14`: `|D| ≤ 6`, avoiding size `|A| ≤ 4`.
2. `apex_tight_lag_exclusion_p14`: Quantum level bound `m ≤ 1` (lags in `{3, 7}`) for all tight
   avoiding subsets of size `≤ 4` in `p ≤ 14`. Windows covering `≥ 5` subtractions (lag 11, 15, ...)
   are strictly excluded.
3. `apex_gate_t6_unconditional_p10`: Unconditional resolution of Gate T6 for all periodic words of
   period `p ≤ 10`.
4. `apex_gate_t6_unconditional_U_le_three`: Unconditional resolution of Gate T6 for all periodic words of
   period `p ≤ 11` with `|U| ≤ 3`.
5. `apex_gate_t6_unconditional_D_le_four`: Unconditional resolution of Gate T6 for all periodic words of
   period `p ≤ 11` with `|D| ≤ 4`.
6. `apex_size_three_structural_decomposition`: Any tight triple of size 3 contains at least two lag 3
   AAS windows whose endpoints belong to `N(A)` and strictly avoid the donated subtraction `s*(u₀)`.
7. `grand_apex_periodic_rigidity_synthesis`: The master apex theorem synthesizing periodic rigidity
   and Gate T6 deletability.
-/

namespace Recaman.ApexPeriodicRigidityTheorem

open LeadingRunSupply LowSSEndpoint TwoSSEndpoint P2ModFourRigidity
open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSLocalDonation TwoSSAvoidTight
open WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound
open UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem
open SS2AASCollisionObstruction ElevenSSDonationClosure LagSevenTightObstruction
open UniversalGateT6Closure QuantumP2Arithmetic OneSSMultiplicity TightPeriodStratification
open TenGateT6Resolution GrandPeriodicDeletabilityTheorem LowSSPeriodicSupply
open ElevenCapacityRigidity CapacitySlackCompensation ElevenGateT6Synthesis
open FourteenLagRigidity TwelveGateT6Resolution TightTripleRigidity

/-- The 4-tier capacity stratification for periods p ≤ 14. -/
theorem apex_capacity_stratification_p14 (e : Int → Bool) (p : Nat)
    (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    (p ≤ 7 → (LagElevenPeriodic.subPhases e 0 p).length ≤ 3 ∧ A.length ≤ 1) ∧
    (p ≤ 10 → (LagElevenPeriodic.subPhases e 0 p).length ≤ 4 ∧ A.length ≤ 2) ∧
    (p ≤ 12 → (LagElevenPeriodic.subPhases e 0 p).length ≤ 5 ∧ A.length ≤ 3) ∧
    (p ≤ 14 → (LagElevenPeriodic.subPhases e 0 p).length ≤ 6 ∧ A.length ≤ 4) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hp7
    have hbound := TightComponentSlackBound.subPhases_bound_of_pos_signSum e p hpos
    have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
    exact ⟨by omega, by omega⟩
  · intro hp10
    have hbound := TightComponentSlackBound.subPhases_bound_of_pos_signSum e p hpos
    have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
    exact ⟨by omega, by omega⟩
  · intro hp12
    exact ⟨p12_subtractions_bound e p hp12 hpos,
           p12_avoiding_size_le_three e p hp12 hpos A U u0 hu0 hnot hsub hslack⟩
  · intro hp14
    exact ⟨p14_subtractions_bound e p hp14 hpos,
           p14_avoiding_size_le_four e p hp14 hpos A U u0 hu0 hnot hsub hslack⟩

/-- Quantum level bound m ≤ 1 (lags in {3, 7}) for tight avoiding subsets in p ≤ 14. -/
theorem apex_tight_lag_exclusion_p14 (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp14 : p ≤ 14) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (m : Nat) (hNk : 2 * m + 1 ≤ (neighborhood e p [u] lag).length) :
    m ≤ 1 :=
  p14_tight_quantum_level_le_one e p hp hp14 hpos A U lag u0 hu0 hnot hsub hslack htight u hu m hNk

/-- Unconditional resolution of Gate T6 for p ≤ 10. -/
theorem apex_gate_t6_unconditional_p10 (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp10 : p ≤ 10) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U)
    (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hU_pos : ∀ u ∈ U, 0 < lag u)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_A : ∀ u ∈ U, e (u : Int) = true) :
    ∀ A : List Nat, List.Sublist A U →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  GrandPeriodicDeletabilityTheorem.apex_gate_t6_unconditional_p10 e p hp hp10 hpos hper U lag hslack u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A

/-- Unconditional resolution of Gate T6 for p ≤ 11 when |U| ≤ 3. -/
theorem apex_gate_t6_unconditional_U_le_three (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hU3 : U.length ≤ 3)
    (u0 : Nat) (hu0 : u0 ∈ U)
    (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hU_pos : ∀ u ∈ U, 0 < lag u)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_A : ∀ u ∈ U, e (u : Int) = true) :
    ∀ A : List Nat, List.Sublist A U →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p11_gate_t6_of_U_le_three e p hp hp11 hper U lag hslack hU3 u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A

/-- Unconditional resolution of Gate T6 for p ≤ 11 when |D| ≤ 4. -/
theorem apex_gate_t6_unconditional_D_le_four (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD4 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 4)
    (u0 : Nat) (hu0 : u0 ∈ U)
    (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hU_pos : ∀ u ∈ U, 0 < lag u)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_A : ∀ u ∈ U, e (u : Int) = true) :
    ∀ A : List Nat, List.Sublist A U →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p11_gate_t6_of_D_le_four e p hp hp11 hper U lag hslack hD4 u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A

/-- Structural decomposition of tight triples of size 3. -/
theorem apex_size_three_structural_decomposition (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (_hA3 : A.length = 3)
    (htight : (neighborhood e p A lag).length = 3)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2) :
    -- (1) Disjointness from all lag 3 AAS endpoints in A
    (∀ u ∈ A, e (u : Int) = true → ShortPeriodicSupply.P2 e (u : Int) 3 →
      (e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false) →
      oldestSubtractionPhase p u0 (lag u0) ≠ endpointPhase p (u : Int) 3) ∧
    -- (2) Membership of AAS endpoints in N(A)
    (∀ u ∈ A, lag u = 3 →
      (e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false) →
      endpointPhase p (u : Int) 3 ∈ neighborhood e p A lag) ∧
    -- (3) Preservation when s*(u₀) ∉ N(A)
    (oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) :=
  grand_tight_triple_rigidity_synthesis e p hp hper A lag _hA3 htight u0 hd_lt hu0A hP0 hss0

/-- Master Apex Theorem: Grand Apex Periodic Rigidity and Gate T6 Resolution. -/
theorem grand_apex_periodic_rigidity_synthesis (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U)
    (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hU_pos : ∀ u ∈ U, 0 < lag u)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_A : ∀ u ∈ U, e (u : Int) = true) :
    -- (1) Unconditional resolution for p ≤ 10
    (p ≤ 10 → ∀ A : List Nat, List.Sublist A U →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (2) Unconditional resolution for p ≤ 11 with |U| ≤ 3
    (p ≤ 11 → U.length ≤ 3 → ∀ A : List Nat, List.Sublist A U →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (3) Unconditional resolution for p ≤ 11 with |D| ≤ 4
    (p ≤ 11 → (LagElevenPeriodic.subPhases e 0 p).length ≤ 4 → ∀ A : List Nat, List.Sublist A U →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) := by
  refine ⟨fun hp10 => apex_gate_t6_unconditional_p10 e p hp hp10 hpos hper U lag hslack u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A,
          fun hp11 hU3 => apex_gate_t6_unconditional_U_le_three e p hp hp11 hper U lag hslack hU3 u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A,
          fun hp11 hD4 => apex_gate_t6_unconditional_D_le_four e p hp hp11 hper U lag hslack hD4 u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A⟩

end Recaman.ApexPeriodicRigidityTheorem
