import Recaman.TwelveGateT6Unconditional
import Recaman.LagSevenNeighborhoodRigidity
import Recaman.FourteenLagRigidity
import Recaman.TightTripleRigidity
import Recaman.SS2LagElevenForcing

/-!
# FourteenGateT6Resolution: Gate T6 Resolution and Multi-Tier Avoiding Reduction for p ≤ 14

This module establishes the comprehensive reduction and resolution of Gate T6 for periods up to p ≤ 14:

1. `p14_avoiding_size_cases`: In any periodic word of period p ≤ 14 with positive signSum and slack,
   any avoiding sublist A satisfies `|A| ≤ 2 ∨ |A| = 3 ∨ |A| = 4`.
2. `p14_tight_size_two_survives`: Any tight avoiding sublist of size ≤ 2 strictly survives deletion
   of s*(u₀) unconditionally.
3. `p14_tight_triple_survives_of_not_mem`: Any tight avoiding sublist of size 3 strictly survives
   deletion of s*(u₀) whenever s*(u₀) ∉ N(A).
4. `p14_tight_quad_survives_of_not_mem`: Any tight avoiding sublist of size 4 strictly survives
   deletion of s*(u₀) whenever s*(u₀) ∉ N(A).
5. `p14_avoiding_sublist_survives_of_tight_avoidance`: If all tight avoiding sublists of size 3 and 4
   avoid s*(u₀), then every avoiding sublist of U strictly survives deletion of s*(u₀).
6. `p14_avoiding_size_le_three_of_D_le_five`: If |D| ≤ 5, avoiding size is bounded by 3 (|A| ≤ 3).
7. `p14_avoiding_size_le_two_of_D_le_four`: If |D| ≤ 4, avoiding size is bounded by 2 (|A| ≤ 2).
8. `p14_avoiding_sublists_survive_unconditional_of_D_le_four`: If |D| ≤ 4, all avoiding sublists
   survive deletion unconditionally.
9. `p14_avoiding_sublists_survive_unconditional_of_U_le_three`: If |U| ≤ 3, all avoiding sublists
   survive deletion unconditionally.
10. `grand_fourteen_gate_t6_resolution_synthesis`: Master synthesis theorem for period 14 Gate T6.
-/

namespace Recaman.FourteenGateT6Resolution

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

/-- In any periodic word of period p ≤ 14 with positive signSum and positive slack,
any avoiding sublist satisfies |A| ≤ 2 ∨ |A| = 3 ∨ |A| = 4. -/
theorem p14_avoiding_size_cases (e : Int → Bool) (p : Nat)
    (hp14 : p ≤ 14) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    A.length ≤ 2 ∨ A.length = 3 ∨ A.length = 4 := by
  have h4 := p14_avoiding_size_le_four e p hp14 hpos A U u0 hu0 hnot hsub hslack
  omega

/-- For p ≤ 14, any tight avoiding sublist of size ≤ 2 strictly survives deletion of s*(u₀) unconditionally. -/
theorem p14_tight_size_two_survives (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (hA2 : A.length ≤ 2)
    (htight : (neighborhood e p A lag).length = A.length)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  tight_avoiding_le_two_survives_general e p hp hper A lag hA2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A

/-- Any tight avoiding sublist of size 3 strictly survives deletion of s*(u₀) whenever s*(u₀) ∉ N(A). -/
theorem p14_tight_triple_survives_of_not_mem (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (hA3 : A.length = 3)
    (htight : (neighborhood e p A lag).length = 3)
    (u0 : Nat)
    (hnot : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have htight' : (neighborhood e p A lag).length = A.length := by omega
  exact tight_triple_survives_of_s_not_mem e p A lag u0 htight' hnot

/-- Any tight avoiding sublist of size 4 strictly survives deletion of s*(u₀) whenever s*(u₀) ∉ N(A). -/
theorem p14_tight_quad_survives_of_not_mem (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (hA4 : A.length = 4)
    (htight : (neighborhood e p A lag).length = 4)
    (u0 : Nat)
    (hnot : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have htight' : (neighborhood e p A lag).length = A.length := by omega
  exact tight_triple_survives_of_s_not_mem e p A lag u0 htight' hnot

/-- In period p ≤ 14, every avoiding sublist strictly survives deletion of s*(u₀) provided that
all tight avoiding sublists of size 3 and 4 avoid s*(u₀). -/
theorem p14_avoiding_sublist_survives_of_tight_avoidance (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp14 : p ≤ 14) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hA_A : ∀ u ∈ A, e (u : Int) = true)
    (h_tight_avoid : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      (B.length = 3 ∨ B.length = 4) →
      (neighborhood e p B lag).length = B.length →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hcases := p14_avoiding_size_cases e p hp14 hpos A U u0 hu0 hnot hsub hslack
  rcases hcases with hle2 | heq3 | heq4
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · exact p14_tight_size_two_survives e p hp hper A lag hle2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inl heq3) htight
      have htight3 : (neighborhood e p A lag).length = 3 := by omega
      exact p14_tight_triple_survives_of_not_mem e p A lag heq3 htight3 u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inr heq4) htight
      have htight4 : (neighborhood e p A lag).length = 4 := by omega
      exact p14_tight_quad_survives_of_not_mem e p A lag heq4 htight4 u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA

/-- If |D| ≤ 5, avoiding size is bounded by 3 (|A| ≤ 3). -/
theorem p14_avoiding_size_le_three_of_D_le_five (e : Int → Bool) (p : Nat)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD5 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 5) :
    A.length ≤ 3 := by
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- If |D| ≤ 4, avoiding size is bounded by 2 (|A| ≤ 2). -/
theorem p14_avoiding_size_le_two_of_D_le_four (e : Int → Bool) (p : Nat)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD4 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 4) :
    A.length ≤ 2 := by
  have hdef := UniversalTightLagBound.sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- If |D| ≤ 4, all avoiding sublists strictly survive deletion of s*(u₀) unconditionally. -/
theorem p14_avoiding_sublists_survive_unconditional_of_D_le_four (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD4 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 4)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hA2 := p14_avoiding_size_le_two_of_D_le_four e p A U u0 hu0 hnot hsub hslack hD4
  by_cases htight : (neighborhood e p A lag).length = A.length
  · exact p14_tight_size_two_survives e p hp hper A lag hA2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A
  · have hhallA := hhall_orig A hsub
    have hslackA : A.length < (neighborhood e p A lag).length := by omega
    exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA

/-- If |U| ≤ 3, all avoiding sublists strictly survive deletion of s*(u₀) unconditionally. -/
theorem p14_avoiding_sublists_survive_unconditional_of_U_le_three (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hU3 : U.length ≤ 3)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hA2 : A.length ≤ 2 := by
    have hle := sublist_length_le_sub_one_of_mem_not_mem hsub hu0 hnot
    omega
  by_cases htight : (neighborhood e p A lag).length = A.length
  · exact p14_tight_size_two_survives e p hp hper A lag hA2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A
  · have hhallA := hhall_orig A hsub
    have hslackA : A.length < (neighborhood e p A lag).length := by omega
    exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA

/-- Master Synthesis: Grand Fourteen Gate T6 Resolution Theorem. -/
theorem grand_fourteen_gate_t6_resolution_synthesis
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp14 : p ≤ 14) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_lags : ∀ u ∈ U, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hU_A : ∀ u ∈ U, e (u : Int) = true) :
    -- (1) Avoiding sublists of size ≤ 2 survive unconditionally
    (∀ A : List Nat, List.Sublist A U → u0 ∉ A → A.length ≤ 2 →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (2) Unconditional survival of all avoiding sublists when |U| ≤ 3
    (U.length ≤ 3 → ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (3) Unconditional survival of all avoiding sublists when |D| ≤ 4
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 4 → ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (4) Complete reduction of avoiding sublists to tight avoidance of size 3 and 4
    ((∀ B : List Nat, List.Sublist B U → u0 ∉ B →
        (B.length = 3 ∨ B.length = 4) →
        (neighborhood e p B lag).length = B.length →
        oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) →
      ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
        A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A hsub _hnot hA2
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    by_cases htight : (neighborhood e p A lag).length = A.length
    · exact p14_tight_size_two_survives e p hp hper A lag hA2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · intro hU3 A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact p14_avoiding_sublists_survive_unconditional_of_U_le_three e p hp hper U A lag hU3 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A
  · intro hD4 A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact p14_avoiding_sublists_survive_unconditional_of_D_le_four e p hp hper U A lag hslack hD4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A
  · intro h_tight A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact p14_avoiding_sublist_survives_of_tight_avoidance e p hp hp14 hpos hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_tight

end Recaman.FourteenGateT6Resolution
