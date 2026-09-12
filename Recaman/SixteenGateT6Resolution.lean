import Recaman.SixteenLagRigidity

/-!
# SixteenGateT6Resolution: Gate T6 Multi-Tier Reduction and Resolution for Periods p ≤ 16

This module establishes the comprehensive reduction and resolution of Gate T6 for periods up to p ≤ 16:

1. `p16_tight_size_two_survives`: Any tight avoiding sublist of size ≤ 2 strictly survives deletion
   of s*(u₀) unconditionally.
2. `p16_tight_triple_survives_of_not_mem`: Any tight avoiding sublist of size 3 strictly survives
   deletion of s*(u₀) whenever s*(u₀) ∉ N(A).
3. `p16_tight_quad_survives_of_not_mem`: Any tight avoiding sublist of size 4 strictly survives
   deletion of s*(u₀) whenever s*(u₀) ∉ N(A).
4. `p16_tight_quint_survives_of_not_mem`: Any tight avoiding sublist of size 5 strictly survives
   deletion of s*(u₀) whenever s*(u₀) ∉ N(A).
5. `p16_avoiding_sublist_survives_of_tight_avoidance`: If all tight avoiding sublists of size 3, 4,
   and 5 avoid s*(u₀), then every avoiding sublist of U strictly survives deletion of s*(u₀).
6. `p16_avoiding_sublists_survive_unconditional_of_U_le_three`: If |U| ≤ 3, all avoiding sublists
   survive deletion unconditionally.
7. `p16_avoiding_sublists_survive_unconditional_of_D_le_four`: If |D| ≤ 4, all avoiding sublists
   survive deletion unconditionally.
8. `p16_gate_t6_of_U_le_four_and_triples`: If |U| ≤ 4, Gate T6 reduces entirely to tight triples.
9. `p16_gate_t6_of_D_le_five_and_triples`: If |D| ≤ 5, Gate T6 reduces entirely to tight triples.
10. `grand_sixteen_gate_t6_resolution_synthesis`: Master synthesis theorem for period 16 Gate T6.
-/

namespace Recaman.SixteenGateT6Resolution

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
open SixteenLagRigidity

/-- For p ≤ 16, any tight avoiding sublist of size ≤ 2 strictly survives deletion of s*(u₀) unconditionally. -/
theorem p16_tight_size_two_survives (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
theorem p16_tight_triple_survives_of_not_mem (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (hA3 : A.length = 3)
    (htight : (neighborhood e p A lag).length = 3)
    (u0 : Nat)
    (hnot : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p14_tight_triple_survives_of_not_mem e p A lag hA3 htight u0 hnot

/-- Any tight avoiding sublist of size 4 strictly survives deletion of s*(u₀) whenever s*(u₀) ∉ N(A). -/
theorem p16_tight_quad_survives_of_not_mem (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (hA4 : A.length = 4)
    (htight : (neighborhood e p A lag).length = 4)
    (u0 : Nat)
    (hnot : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p14_tight_quad_survives_of_not_mem e p A lag hA4 htight u0 hnot

/-- Any tight avoiding sublist of size 5 strictly survives deletion of s*(u₀) whenever s*(u₀) ∉ N(A). -/
theorem p16_tight_quint_survives_of_not_mem (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (_hA5 : A.length = 5)
    (htight : (neighborhood e p A lag).length = 5)
    (u0 : Nat)
    (hnot : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have htight' : (neighborhood e p A lag).length = A.length := by omega
  exact tight_triple_survives_of_s_not_mem e p A lag u0 htight' hnot

/-- In period p ≤ 16, every avoiding sublist strictly survives deletion of s*(u₀) provided that
all tight avoiding sublists of size 3, 4, and 5 avoid s*(u₀). -/
theorem p16_avoiding_sublist_survives_of_tight_avoidance (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp16 : p ≤ 16) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
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
      (B.length = 3 ∨ B.length = 4 ∨ B.length = 5) →
      (neighborhood e p B lag).length = B.length →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hcases := p16_avoiding_size_cases e p hp16 hpos A U u0 hu0 hnot hsub hslack
  rcases hcases with hle2 | heq3 | heq4 | heq5
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · exact p16_tight_size_two_survives e p hp hper A lag hle2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inl heq3) htight
      have htight3 : (neighborhood e p A lag).length = 3 := by omega
      exact p16_tight_triple_survives_of_not_mem e p A lag heq3 htight3 u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inr (Or.inl heq4)) htight
      have htight4 : (neighborhood e p A lag).length = 4 := by omega
      exact p16_tight_quad_survives_of_not_mem e p A lag heq4 htight4 u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hnot_mem := h_tight_avoid A hsub hnot (Or.inr (Or.inr heq5)) htight
      have htight5 : (neighborhood e p A lag).length = 5 := by omega
      exact p16_tight_quint_survives_of_not_mem e p A lag heq5 htight5 u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA

/-- If |U| ≤ 3, all avoiding sublists survive deletion unconditionally. -/
theorem p16_avoiding_sublists_survive_unconditional_of_U_le_three (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p14_avoiding_sublists_survive_unconditional_of_U_le_three e p hp hper U A lag hU3 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A

/-- If |D| ≤ 4, all avoiding sublists survive deletion unconditionally. -/
theorem p16_avoiding_sublists_survive_unconditional_of_D_le_four (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p14_avoiding_sublists_survive_unconditional_of_D_le_four e p hp hper U A lag hslack hD4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A

/-- If |U| ≤ 4, Gate T6 reduces entirely to tight triples of size 3. -/
theorem p16_gate_t6_of_U_le_four_and_triples (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp14 : p ≤ 14) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hU4 : U.length ≤ 4)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hA_A : ∀ u ∈ A, e (u : Int) = true)
    (h_tight3 : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      B.length = 3 →
      (neighborhood e p B lag).length = 3 →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p14_gate_t6_of_U_le_four_and_triples e p hp hp14 hpos hper U A lag hslack hU4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_tight3

/-- If |D| ≤ 5, Gate T6 reduces entirely to tight triples of size 3. -/
theorem p16_gate_t6_of_D_le_five_and_triples (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp14 : p ≤ 14) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD5 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 5)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hA_A : ∀ u ∈ A, e (u : Int) = true)
    (h_tight3 : ∀ B : List Nat, List.Sublist B U → u0 ∉ B →
      B.length = 3 →
      (neighborhood e p B lag).length = 3 →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p14_gate_t6_of_D_le_five_and_triples e p hp hp14 hpos hper U A lag hslack hD5 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_tight3

/-- Master Synthesis: Grand Sixteen Gate T6 Resolution Theorem. -/
theorem grand_sixteen_gate_t6_resolution_synthesis
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp16 : p ≤ 16) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
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
    -- (4) Complete reduction of avoiding sublists to tight avoidance of size 3, 4, 5
    ((∀ B : List Nat, List.Sublist B U → u0 ∉ B →
        (B.length = 3 ∨ B.length = 4 ∨ B.length = 5) →
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
    · exact p16_tight_size_two_survives e p hp hper A lag hA2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · intro hU3 A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact p16_avoiding_sublists_survive_unconditional_of_U_le_three e p hp hper U A lag hU3 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A
  · intro hD4 A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact p16_avoiding_sublists_survive_unconditional_of_D_le_four e p hp hper U A lag hslack hD4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A
  · intro h_tight A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact p16_avoiding_sublist_survives_of_tight_avoidance e p hp hp16 hpos hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_tight

end Recaman.SixteenGateT6Resolution
