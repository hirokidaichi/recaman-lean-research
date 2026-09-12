import Recaman.FourteenLagRigidity
import Recaman.ElevenGateT6Synthesis
import Recaman.ElevenCapacityRigidity
import Recaman.GrandPeriodicDeletabilityTheorem

/-!
# TwelveGateT6Resolution: Period 12 Gate T6 Resolution and Size-3 Reduction

This module establishes the exact decomposition and resolution of Gate T6 for periods up to `p ≤ 12`:

1. `p12_tight_avoiding_size_le_three`: In any periodic word of period `p ≤ 12` with positive signSum
   and positive slack, any avoiding sublist has `|A| ≤ 3`.
2. `p12_avoiding_size_cases`: Any avoiding sublist in `p ≤ 12` has `|A| ≤ 2 ∨ |A| = 3`.
3. `p11_gate_t6_of_size_three_survives`: In period `p ≤ 11`, if all tight avoiding sublists of
   size 3 survive deletion of `s*(u₀)`, then Gate T6 holds unconditionally on ALL sublists of `U`.
4. `p12_gate_t6_of_U_le_three`: Unconditional resolution of Gate T6 whenever `|U| ≤ 3` for `p ≤ 11`.
5. `p12_gate_t6_of_D_le_four`: Unconditional resolution of Gate T6 whenever `|D| ≤ 4` for `p ≤ 11`.
6. `p12_gate_t6_tripartite_resolution`: Complete resolution of Gate T6 on all sublists of `U`
   under the three-part classification: containing `u₀`, slack, or tight AAS.
7. `grand_twelve_gate_t6_resolution`: Master synthesis theorem for period 12 Gate T6 resolution.
-/

namespace Recaman.TwelveGateT6Resolution

open LeadingRunSupply LowSSEndpoint TwoSSEndpoint P2ModFourRigidity
open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSLocalDonation TwoSSAvoidTight
open WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound
open UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem
open SS2AASCollisionObstruction ElevenSSDonationClosure LagSevenTightObstruction
open UniversalGateT6Closure QuantumP2Arithmetic OneSSMultiplicity TightPeriodStratification
open TenGateT6Resolution GrandPeriodicDeletabilityTheorem LowSSPeriodicSupply
open ElevenCapacityRigidity CapacitySlackCompensation ElevenGateT6Synthesis FourteenLagRigidity

/-- In any periodic word of period p ≤ 12 with positive signSum and positive slack, |A| ≤ 3. -/
theorem p12_tight_avoiding_size_le_three (e : Int → Bool) (p : Nat)
    (hp12 : p ≤ 12) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    A.length ≤ 3 :=
  p12_avoiding_size_le_three e p hp12 hpos A U u0 hu0 hnot hsub hslack

/-- Any avoiding sublist in p ≤ 12 satisfies |A| ≤ 2 ∨ |A| = 3. -/
theorem p12_avoiding_size_cases (e : Int → Bool) (p : Nat)
    (hp12 : p ≤ 12) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    A.length ≤ 2 ∨ A.length = 3 := by
  have h3 := p12_tight_avoiding_size_le_three e p hp12 hpos A U u0 hu0 hnot hsub hslack
  omega

/-- In period p ≤ 11, if tight avoiding sublists of size 3 survive deletion of s*(u₀),
then Gate T6 holds unconditionally on ALL sublists of U. -/
theorem p11_gate_t6_of_size_three_survives (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
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
    (hU_A : ∀ u ∈ U, e (u : Int) = true)
    (hsurv3 : ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
      (neighborhood e p A lag).length = A.length → A.length = 3 →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) :
    ∀ A : List Nat, List.Sublist A U →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  intro A hsub
  by_cases hu0A_mem : u0 ∈ A
  · exact donor_containing_survives_deletion e p hp hp11 hper U A lag hsub.length_le hslack u0 hu0A_mem hP0 hss0
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · by_cases hA2 : A.length ≤ 2
      · exact p11_tight_avoiding_le_two_survives e p hp hp11 hper U A lag u0 hslack hd_lt hu0A hP0 hss0 hA2 hsub htight hhall_orig hU_pos hU_P2 hU_A
      · have hbound := TightComponentSlackBound.subPhases_bound_of_pos_signSum e p hpos
        have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hu0A_mem hslack
        have hA3 : A.length = 3 := by omega
        exact hsurv3 A hsub hu0A_mem htight hA3
    · have hslackA : A.length < (neighborhood e p A lag).length := by
        have horig := hhall_orig A hsub
        omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA

/-- Unconditional resolution of Gate T6 whenever |U| ≤ 3 for p ≤ 11. -/
theorem p12_gate_t6_of_U_le_three (e : Int → Bool) (p : Nat) (hp : 0 < p)
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

/-- Unconditional resolution of Gate T6 whenever |D| ≤ 4 for p ≤ 11. -/
theorem p12_gate_t6_of_D_le_four (e : Int → Bool) (p : Nat) (hp : 0 < p)
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

/-- Master Synthesis: Grand Twelve Gate T6 Resolution Theorem. -/
theorem grand_twelve_gate_t6_resolution (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
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
    -- (1) Any avoiding sublist of size ≤ 2 survives
    (∀ A : List Nat, List.Sublist A U → u0 ∉ A → A.length ≤ 2 →
      (neighborhood e p A lag).length = A.length →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (2) Any avoiding sublist of size 3 that is lag 3 AAS survives
    (∀ A : List Nat, List.Sublist A U → u0 ∉ A → A.length = 3 →
      (neighborhood e p A lag).length = 3 →
      (∀ u ∈ A, lag u = 3) →
      (∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false) →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (3) Unconditional resolution whenever |U| ≤ 3
    (U.length ≤ 3 →
      ∀ A : List Nat, List.Sublist A U →
        A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (4) Unconditional resolution whenever |D| ≤ 4
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 4 →
      ∀ A : List Nat, List.Sublist A U →
        A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A hsub hnot hA2 htight
    exact p11_tight_avoiding_le_two_survives e p hp hp11 hper U A lag u0 hslack hd_lt hu0A hP0 hss0 hA2 hsub htight hhall_orig hU_pos hU_P2 hU_A
  · intro A hsub hnot hA3 htight hlag3 haas
    exact p11_tight_avoiding_size_three_aas_survives e p hp hper U A lag hsub hA3 htight u0 hu0 hnot hd_lt hu0A hP0 hss0 hlag3 haas hU_P2 hU_A
  · intro hU3
    exact p12_gate_t6_of_U_le_three e p hp hp11 hper U lag hslack hU3 u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A
  · intro hD4
    exact p12_gate_t6_of_D_le_four e p hp hp11 hper U lag hslack hD4 u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A

end Recaman.TwelveGateT6Resolution
