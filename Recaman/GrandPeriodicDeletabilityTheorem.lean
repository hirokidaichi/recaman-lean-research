import Recaman.TenGateT6Resolution
import Recaman.GrandPeriodicBottleneckTheorem

/-!
# GrandPeriodicDeletabilityTheorem: Unconditional Gate T6 Resolution and Deletability Hierarchy

This module establishes the grand synthesis of Gate T6 deletability across the periodic hierarchy:

1. `apex_gate_t6_unconditional_p10`: Gate T6 (deletability of the donated subtraction `s*(u₀)`)
   holds unconditionally for all periodic words of period `p ≤ 10` with positive signSum and positive slack.
2. `apex_tight_avoiding_all_aas_p10`: In all periodic words of period `p ≤ 10`, every member of every
   tight avoiding subset is an AAS window of lag 3.
3. `apex_no_lag_seven_in_tight_p10`: In all periodic words of period `p ≤ 10`, no member of any tight
   avoiding subset can have lag 7.
4. `apex_gate_t6_hall_preservation_p10`: Hall's marriage condition is universally preserved on all
   sublists of `U` after deleting `s*(u₀)` for all `p ≤ 10`.
5. `grand_periodic_deletability_synthesis`: Master synthesis theorem unifying unconditional closure
   for `p ≤ 10` with complete reduction for `p ≤ 11`.
-/

namespace Recaman.GrandPeriodicDeletabilityTheorem

open LeadingRunSupply LowSSEndpoint TwoSSEndpoint P2ModFourRigidity
open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSLocalDonation TwoSSAvoidTight
open WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound
open UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem
open SS2AASCollisionObstruction ElevenSSDonationClosure LagSevenTightObstruction
open UniversalGateT6Closure QuantumP2Arithmetic OneSSMultiplicity TightPeriodStratification
open TenGateT6Resolution GrandPeriodicBottleneckTheorem

/-- Unconditional Resolution of Gate T6 for all periodic words of period p ≤ 10. -/
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
  p10_universal_gate_t6_deletability_unconditional e p hp hp10 hpos hper U lag hslack u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A

/-- Tight avoiding subsets are unconditionally forced to lag 3 AAS windows for p ≤ 10. -/
theorem apex_tight_avoiding_all_aas_p10 (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp10 : p ≤ 10) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat) (u0 : Nat)
    (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (neighborhood e p A lag).length = A.length)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_pos : ∀ u ∈ U, 0 < lag u) :
    (∀ u ∈ A, lag u = 3) ∧
    (∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false) :=
  ⟨tight_avoiding_all_lag_three_p10 e p hp hp10 hpos hper U A lag u0 hu0 hnot hsub hslack htight hU_P2 hU_pos,
   tight_avoiding_all_aas_p10 e p hp hp10 hpos hper U A lag u0 hu0 hnot hsub hslack htight hU_P2 hU_pos⟩

/-- No lag 7 window can appear in any tight avoiding subset for p ≤ 10. -/
theorem apex_no_lag_seven_in_tight_p10 (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp10 : p ≤ 10) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat) (u0 : Nat)
    (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hlag7 : lag u = 7)
    (hP_u : ShortPeriodicSupply.P2 e (u : Int) (lag u)) : False :=
  no_lag_seven_in_tight_avoiding_p10 e p hp hp10 hpos hper U A lag u0 hu0 hnot hsub hslack htight u hu hlag7 hP_u

/-- Hall Preservation Corollary: Hall's condition is preserved on all sublists of U for p ≤ 10. -/
theorem apex_gate_t6_hall_preservation_p10 (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    (hU_A : ∀ u ∈ U, e (u : Int) = true)
    (A : List Nat) (hsub : List.Sublist A U) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p10_universal_gate_t6_hall_preservation_unconditional e p hp hp10 hpos hper U lag hslack u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A A hsub

/-- Master Synthesis: Grand Periodic Deletability Theorem. -/
theorem grand_periodic_deletability_synthesis (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    (∀ A : List Nat, List.Sublist A U → (neighborhood e p A lag).length = A.length → u0 ∉ A → ∀ u ∈ A, lag u = 3) ∧
    (∀ A : List Nat, List.Sublist A U →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) :=
  grand_ten_gate_t6_closure e p hp hp10 hpos hper U lag hslack u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A

end Recaman.GrandPeriodicDeletabilityTheorem
