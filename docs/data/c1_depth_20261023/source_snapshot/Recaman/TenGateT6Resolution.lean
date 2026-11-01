import Recaman.UniversalGateT6Closure
import Recaman.QuantumP2Arithmetic

/-!
# TenGateT6Resolution: Unconditional Resolution of Gate T6 for all Periods p ≤ 10

This module proves that Gate T6 (deletability of the donated subtraction `s*(u₀)`)
holds unconditionally for all periodic words of period `p ≤ 10`:

1. `lag_seven_neighborhood_ge_three`: Any non-wrapping lag 7 window (`7 < p`) has at least
   3 distinct subtractions in its neighborhood: `3 ≤ (neighborhood e p [u] lag).length`.
2. `no_lag_seven_in_tight_avoiding_p10`: For all `p ≤ 10`, no member of any tight avoiding
   subset can have `lag u = 7`.
3. `tight_avoiding_lags_le_five_p10`: For all `p ≤ 10`, every member of every tight avoiding
   subset satisfies `lag u ≤ 5`.
4. `tight_avoiding_all_lag_three_p10`: For all `p ≤ 10`, every member of every tight avoiding
   subset has `lag u = 3`.
5. `tight_avoiding_all_aas_p10`: For all `p ≤ 10`, every member of every tight avoiding
   subset is an AAS window.
6. `p10_universal_gate_t6_deletability_unconditional`: The donated subtraction `s*(u₀)`
   is universally deletable for all `p ≤ 10` without any lag hypotheses.
7. `p10_universal_gate_t6_hall_preservation_unconditional`: Hall's condition is universally
   preserved on all sublists of `U` after deleting `s*(u₀)` for all `p ≤ 10`.
8. `grand_ten_gate_t6_closure`: Master synthesis theorem for period `p ≤ 10` closure.
-/

namespace Recaman.TenGateT6Resolution

open LeadingRunSupply LowSSEndpoint TwoSSEndpoint P2ModFourRigidity
open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSLocalDonation TwoSSAvoidTight
open WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound
open UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem
open SS2AASCollisionObstruction ElevenSSDonationClosure LagSevenTightObstruction
open UniversalGateT6Closure QuantumP2Arithmetic OneSSMultiplicity TightPeriodStratification

theorem past_seven (e : Int → Bool) (u : Int) :
    past e u 7 = [e (u - 1), e (u - 2), e (u - 3), e (u - 4), e (u - 5), e (u - 6), e (u - 7)] := by
  unfold past
  rfl

/-- Any length 7 P2 window has at least 3 subtraction positions. -/
theorem p2_lag_seven_three_subtractions (e : Int → Bool) (u : Int)
    (hP : ShortPeriodicSupply.P2 e u 7) :
    ∃ i1 i2 i3 : Nat, i1 < i2 ∧ i2 < i3 ∧ i3 < 7 ∧
      e (u - 1 - (i1 : Int)) = false ∧
      e (u - 1 - (i2 : Int)) = false ∧
      e (u - 1 - (i3 : Int)) = false := by
  have hP_past : P2 (past e u 7) := (past_p2_iff e u 7).mpr hP
  have hlen : (past e u 7).length = 7 := past_length e u 7
  have hcases := p2_length_seven_cases (past e u 7) hP_past hlen
  have hp7 := past_seven e u
  rcases hcases with h1 | h2 | h3 | h4
  · rw [hp7] at h1
    injection h1 with e0 rest1
    injection rest1 with e1 rest2
    injection rest2 with e2 rest3
    injection rest3 with e3 rest4
    injection rest4 with e4 rest5
    injection rest5 with e5 rest6
    injection rest6 with e6 _
    refine ⟨0, 5, 6, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · rw [show (u - 1 - (0 : Nat) : Int) = u - 1 by omega]; exact e0
    · rw [show (u - 1 - (5 : Nat) : Int) = u - 6 by omega]; exact e5
    · rw [show (u - 1 - (6 : Nat) : Int) = u - 7 by omega]; exact e6
  · rw [hp7] at h2
    injection h2 with e0 rest1
    injection rest1 with e1 rest2
    injection rest2 with e2 rest3
    injection rest3 with e3 rest4
    injection rest4 with e4 rest5
    injection rest5 with e5 rest6
    injection rest6 with e6 _
    refine ⟨1, 4, 6, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · rw [show (u - 1 - (1 : Nat) : Int) = u - 2 by omega]; exact e1
    · rw [show (u - 1 - (4 : Nat) : Int) = u - 5 by omega]; exact e4
    · rw [show (u - 1 - (6 : Nat) : Int) = u - 7 by omega]; exact e6
  · rw [hp7] at h3
    injection h3 with e0 rest1
    injection rest1 with e1 rest2
    injection rest2 with e2 rest3
    injection rest3 with e3 rest4
    injection rest4 with e4 rest5
    injection rest5 with e5 rest6
    injection rest6 with e6 _
    refine ⟨2, 3, 6, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · rw [show (u - 1 - (2 : Nat) : Int) = u - 3 by omega]; exact e2
    · rw [show (u - 1 - (3 : Nat) : Int) = u - 4 by omega]; exact e3
    · rw [show (u - 1 - (6 : Nat) : Int) = u - 7 by omega]; exact e6
  · rw [hp7] at h4
    injection h4 with e0 rest1
    injection rest1 with e1 rest2
    injection rest2 with e2 rest3
    injection rest3 with e3 rest4
    injection rest4 with e4 rest5
    injection rest5 with e5 rest6
    injection rest6 with e6 _
    refine ⟨2, 4, 5, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · rw [show (u - 1 - (2 : Nat) : Int) = u - 3 by omega]; exact e2
    · rw [show (u - 1 - (4 : Nat) : Int) = u - 5 by omega]; exact e4
    · rw [show (u - 1 - (5 : Nat) : Int) = u - 6 by omega]; exact e5

/-- Canonical subtraction phase of a window index modulo p. -/
def subPhaseOfIndex (p : Nat) (u : Int) (i : Nat) : Nat :=
  ((u - 1 - (i : Int)) % (p : Int)).toNat

theorem subPhaseOfIndex_eq (p : Nat) (_hp : 0 < p) (u : Int) (i : Nat) :
    (subPhaseOfIndex p u i : Int) = (u - 1 - (i : Int)) % (p : Int) := by
  unfold subPhaseOfIndex
  have hnn : 0 ≤ (u - 1 - (i : Int)) % (p : Int) := Int.emod_nonneg (u - 1 - (i : Int)) (by omega)
  exact Int.toNat_of_nonneg hnn

theorem subPhaseOfIndex_lt (p : Nat) (hp : 0 < p) (u : Int) (i : Nat) :
    subPhaseOfIndex p u i < p := by
  have heq := subPhaseOfIndex_eq p hp u i
  have hmod := Int.emod_lt_of_pos (u - 1 - (i : Int)) (show (0 : Int) < (p : Int) by omega)
  omega

theorem subPhaseOfIndex_inj (p : Nat) (hp : 0 < p) (u : Int) (i j : Nat)
    (hij : i < j) (hjp : j < p) :
    subPhaseOfIndex p u i ≠ subPhaseOfIndex p u j := by
  intro heq
  have h1 := subPhaseOfIndex_eq p hp u i
  have h2 := subPhaseOfIndex_eq p hp u j
  have h_contra := subtraction_residue_injective_of_lt_p p hp u i j hij hjp
  rw [← h1, ← h2] at h_contra
  exact h_contra (by rw [heq])

theorem subPhaseOfIndex_mem_neighborhood (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (u : Nat) (lag : Nat → Nat)
    (hlag : lag u = 7) (i : Nat) (hi : i < 7) (he : e ((u : Int) - 1 - (i : Int)) = false) :
    subPhaseOfIndex p (u : Int) i ∈ neighborhood e p [u] lag := by
  unfold neighborhood
  rw [List.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [LagElevenPeriodic.mem_subPhases]
    refine ⟨subPhaseOfIndex_lt p hp (u : Int) i, ?_⟩
    simp only [Int.zero_add]
    have heq := subPhaseOfIndex_eq p hp (u : Int) i
    have he_eval := TwoSSPeriodicSupply.emod_eq_shift e p hp hper (subPhaseOfIndex p (u : Int) i) (u - 1 - (i : Int))
    have hmod_id : ((subPhaseOfIndex p (u : Int) i : Int) % (p : Int)) = (subPhaseOfIndex p (u : Int) i : Int) := by
      apply Int.emod_eq_of_lt (by omega)
      have hlt := subPhaseOfIndex_lt p hp (u : Int) i
      omega
    rw [hmod_id, heq] at he_eval
    rw [heq]
    rw [he_eval rfl]
    exact he
  · rw [isCoveredBySubset_iff]
    refine ⟨u, List.mem_singleton_self u, i, ?_, he, ?_⟩
    · omega
    · have heq := subPhaseOfIndex_eq p hp (u : Int) i
      exact heq.symm

/-- Any non-wrapping lag 7 window has at least 3 distinct subtractions in its neighborhood. -/
theorem lag_seven_neighborhood_ge_three (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x) (u : Nat) (lag : Nat → Nat)
    (hlag : lag u = 7) (hp_gt : 7 < p)
    (hP : ShortPeriodicSupply.P2 e (u : Int) 7) :
    3 ≤ (neighborhood e p [u] lag).length := by
  obtain ⟨i1, i2, i3, h12, h23, _h37, he1, he2, he3⟩ := p2_lag_seven_three_subtractions e (u : Int) hP
  have hi1_lt : i1 < 7 := by omega
  have hi2_lt : i2 < 7 := by omega
  have hi3_lt : i3 < 7 := by omega
  have hj2 : i2 < p := by omega
  have hj3 : i3 < p := by omega
  let s1 := subPhaseOfIndex p (u : Int) i1
  let s2 := subPhaseOfIndex p (u : Int) i2
  let s3 := subPhaseOfIndex p (u : Int) i3
  have hs1 : s1 ∈ neighborhood e p [u] lag := subPhaseOfIndex_mem_neighborhood e p hp hper u lag hlag i1 hi1_lt he1
  have hs2 : s2 ∈ neighborhood e p [u] lag := subPhaseOfIndex_mem_neighborhood e p hp hper u lag hlag i2 hi2_lt he2
  have hs3 : s3 ∈ neighborhood e p [u] lag := subPhaseOfIndex_mem_neighborhood e p hp hper u lag hlag i3 hi3_lt he3
  have h12_ne : s1 ≠ s2 := subPhaseOfIndex_inj p hp (u : Int) i1 i2 h12 hj2
  have h23_ne : s2 ≠ s3 := subPhaseOfIndex_inj p hp (u : Int) i2 i3 h23 hj3
  have h13_ne : s1 ≠ s3 := subPhaseOfIndex_inj p hp (u : Int) i1 i3 (by omega) hj3
  have hsub : [s1, s2, s3] ⊆ neighborhood e p [u] lag := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hs1
    · exact hs2
    · exact hs3
  have hnodup : [s1, s2, s3].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, not_false_iff, List.nodup_nil, and_true]
    exact ⟨⟨h12_ne, h13_ne⟩, h23_ne⟩
  have hlen := hnodup.length_le_of_subset hsub
  simp only [List.length_cons, List.length_nil] at hlen
  omega

/-- For all p ≤ 10, no member of any tight avoiding subset can have lag 7. -/
theorem no_lag_seven_in_tight_avoiding_p10 (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp10 : p ≤ 10) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat) (u0 : Nat)
    (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hlag7 : lag u = 7)
    (hP_u : ShortPeriodicSupply.P2 e (u : Int) (lag u)) : False := by
  have hA2 : A.length ≤ 2 :=
    tight_avoiding_size_le_two_of_p10 e p hp10 hpos U A u0 hu0 hnot hsub hslack
  have hnowrap : lag u < p := by
    apply Classical.byContradiction
    intro hwrap
    have hge : p ≤ lag u := by omega
    have hne := tight_excludes_wrapping_window_ne e p hp hper U A lag hsub.length_le hslack u hu hge
    contradiction
  have hp_gt : 7 < p := by omega
  have hP7 : ShortPeriodicSupply.P2 e (u : Int) 7 := by rwa [hlag7] at hP_u
  have hN3 : 3 ≤ (neighborhood e p [u] lag).length :=
    lag_seven_neighborhood_ge_three e p hp hper u lag hlag7 hp_gt hP7
  exact tight_subset_le_two_no_ge_three p hp A lag hA2 htight u hu hN3

/-- For all p ≤ 10, every member of any tight avoiding subset has lag ≤ 5. -/
theorem tight_avoiding_lags_le_five_p10 (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp10 : p ≤ 10) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat) (u0 : Nat)
    (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (neighborhood e p A lag).length = A.length)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u)) :
    ∀ u ∈ A, lag u ≤ 5 := by
  intro u hu
  have huU := hsub.subset hu
  have hPu := hU_P2 u huU
  have hnowrap : lag u < p := by
    apply Classical.byContradiction
    intro hwrap
    have hge : p ≤ lag u := by omega
    have hne := tight_excludes_wrapping_window_ne e p hp hper U A lag hsub.length_le hslack u hu hge
    contradiction
  have hlt11 : lag u < 11 := by omega
  have hP2_past : P2 (past e (u : Int) (lag u)) := (past_p2_iff e (u : Int) (lag u)).mpr hPu
  have hlen_lt : (past e (u : Int) (lag u)).length < 11 := by rw [past_length]; exact hlt11
  have hlags := p2_length_lt_eleven_cases (past e (u : Int) (lag u)) hlen_lt hP2_past
  rw [past_length] at hlags
  rcases hlags with h3 | h7
  · omega
  · exfalso
    exact no_lag_seven_in_tight_avoiding_p10 e p hp hp10 hpos hper U A lag u0 hu0 hnot hsub hslack htight u hu h7 hPu

/-- For all p ≤ 10, every member of any tight avoiding subset has lag 3. -/
theorem tight_avoiding_all_lag_three_p10 (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp10 : p ≤ 10) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat) (u0 : Nat)
    (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (neighborhood e p A lag).length = A.length)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_pos : ∀ u ∈ U, 0 < lag u) :
    ∀ u ∈ A, lag u = 3 := by
  have hle5 := tight_avoiding_lags_le_five_p10 e p hp hp10 hpos hper U A lag u0 hu0 hnot hsub hslack htight hU_P2
  intro u hu
  have huU := hsub.subset hu
  exact p2_lag_le_five_forces_three e (u : Int) (lag u) (hU_pos u huU) (hle5 u hu) (hU_P2 u huU)

/-- For all p ≤ 10, every member of any tight avoiding subset is an AAS window. -/
theorem tight_avoiding_all_aas_p10 (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp10 : p ≤ 10) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat) (u0 : Nat)
    (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (neighborhood e p A lag).length = A.length)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_pos : ∀ u ∈ U, 0 < lag u) :
    ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false := by
  have hle5 := tight_avoiding_lags_le_five_p10 e p hp hp10 hpos hper U A lag u0 hu0 hnot hsub hslack htight hU_P2
  intro u hu
  have huU := hsub.subset hu
  exact p2_lag_le_five_forces_aas e (u : Int) (lag u) (hU_pos u huU) (hle5 u hu) (hU_P2 u huU)

/-- Unconditional Resolution of Gate T6 Deletability for all p ≤ 10:
For any periodic word of period p ≤ 10 with positive signSum and positive slack,
the donated subtraction s*(u0) is universally deletable from D without any lag hypotheses. -/
theorem p10_universal_gate_t6_deletability_unconditional (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hle5 : ∀ A : List Nat, List.Sublist A U → (neighborhood e p A lag).length = A.length → u0 ∉ A → ∀ u ∈ A, lag u ≤ 5 := by
    intro A hsub htight hnot u hu
    exact tight_avoiding_lags_le_five_p10 e p hp hp10 hpos hper U A lag u0 hu0 hnot hsub hslack htight hU_P2 u hu
  exact p10_universal_gate_t6_deletability_of_lag_le_five e p hp hp10 hper U lag hslack u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A hle5

/-- Unconditional Hall Preservation after Gate T6 donation for all p ≤ 10:
Hall's condition is universally preserved on all sublists of U. -/
theorem p10_universal_gate_t6_hall_preservation_unconditional (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
  p10_universal_gate_t6_deletability_unconditional e p hp hp10 hpos hper U lag hslack u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A A hsub

/-- Master Synthesis: Grand Ten Gate T6 Closure Theorem. -/
theorem grand_ten_gate_t6_closure (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
  ⟨fun A hsub htight hnot =>
     tight_avoiding_all_lag_three_p10 e p hp hp10 hpos hper U A lag u0 hu0 hnot hsub hslack htight hU_P2 hU_pos,
   p10_universal_gate_t6_deletability_unconditional e p hp hp10 hpos hper U lag hslack u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A⟩

end Recaman.TenGateT6Resolution
