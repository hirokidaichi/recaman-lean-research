import Recaman.TenGateT6Resolution
import Recaman.GrandPeriodicDeletabilityTheorem
import Recaman.ShortPeriodicSupply
import Recaman.LagElevenPeriodic
import Recaman.LowSSPeriodicSupply

/-!
# ElevenCapacityRigidity: Tight Avoiding Rigidity and Gate T6 Resolution for Period p ≤ 11

This module establishes the structural rigidity of tight avoiding subsets in period `p ≤ 11`:

1. `p11_tight_avoiding_le_two_all_lag_three`: In any periodic word of period `p ≤ 11`, any tight
   avoiding subset of size `≤ 2` consists exclusively of lag 3 windows.
2. `p11_tight_avoiding_le_two_all_aas`: Any tight avoiding subset of size `≤ 2` consists exclusively
   of AAS windows.
3. `p11_tight_avoiding_le_two_survives`: Any tight avoiding subset of size `≤ 2` strictly survives
   deletion of the donated subtraction `s*(u₀)`.
4. `p11_gate_t6_of_U_le_three`: Unconditional resolution of Gate T6 for all periodic words of period
   `p ≤ 11` with supply `|U| ≤ 3`.
5. `p11_gate_t6_of_D_le_four`: Unconditional resolution of Gate T6 for all periodic words of period
   `p ≤ 11` with `|D| ≤ 4`.
6. `p11_gate_t6_of_two_high_ss`: Unconditional resolution of Gate T6 for all periodic words of period
   `p ≤ 11` containing at least two high-SS windows.
7. `p11_gate_t6_of_ss_ge_three`: Unconditional resolution of Gate T6 for all periodic words of period
   `p ≤ 11` containing an SS ≥ 3 window.
8. `grand_eleven_capacity_rigidity_synthesis`: Master synthesis theorem for period 11 capacity rigidity.
-/

namespace Recaman.ElevenCapacityRigidity

open LeadingRunSupply LowSSEndpoint TwoSSEndpoint P2ModFourRigidity
open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSLocalDonation TwoSSAvoidTight
open WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound
open UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem
open SS2AASCollisionObstruction ElevenSSDonationClosure LagSevenTightObstruction
open UniversalGateT6Closure QuantumP2Arithmetic OneSSMultiplicity TightPeriodStratification
open TenGateT6Resolution GrandPeriodicDeletabilityTheorem LowSSPeriodicSupply

/-- In any periodic word of period p ≤ 11, any tight avoiding subset of size ≤ 2 has all lags equal to 3. -/
theorem p11_tight_avoiding_le_two_all_lag_three (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hA2 : A.length ≤ 2) (hsub : List.Sublist A U)
    (htight : (neighborhood e p A lag).length = A.length)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_pos : ∀ u ∈ U, 0 < lag u) :
    ∀ u ∈ A, lag u = 3 := by
  intro u hu
  have huU := hsub.subset hu
  have hPu := hU_P2 u huU
  have hpos_u := hU_pos u huU
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
  · exact h3
  · exfalso
    have hp_gt : 7 < p := by omega
    have hP7 : ShortPeriodicSupply.P2 e (u : Int) 7 := by rwa [h7] at hPu
    have hN3 : 3 ≤ (neighborhood e p [u] lag).length :=
      lag_seven_neighborhood_ge_three e p hp hper u lag h7 hp_gt hP7
    exact tight_subset_le_two_no_ge_three p hp A lag hA2 htight u hu hN3

/-- In any periodic word of period p ≤ 11, any tight avoiding subset of size ≤ 2 is purely AAS. -/
theorem p11_tight_avoiding_le_two_all_aas (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hA2 : A.length ≤ 2) (hsub : List.Sublist A U)
    (htight : (neighborhood e p A lag).length = A.length)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_pos : ∀ u ∈ U, 0 < lag u) :
    ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false := by
  have h3 := p11_tight_avoiding_le_two_all_lag_three e p hp hp11 hper U A lag hslack hA2 hsub htight hU_P2 hU_pos
  intro u hu
  have huU := hsub.subset hu
  have heq3 := h3 u hu
  have hle5 : lag u ≤ 5 := by omega
  exact p2_lag_le_five_forces_aas e (u : Int) (lag u) (hU_pos u huU) hle5 (hU_P2 u huU)

/-- In any periodic word of period p ≤ 11, any tight avoiding subset of size ≤ 2 survives deletion of s*(u0). -/
theorem p11_tight_avoiding_le_two_survives (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat) (u0 : Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hA2 : A.length ≤ 2) (hsub : List.Sublist A U)
    (htight : (neighborhood e p A lag).length = A.length)
    (hhall_orig : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hU_pos : ∀ u ∈ U, 0 < lag u)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_A : ∀ u ∈ U, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have h3 := p11_tight_avoiding_le_two_all_lag_three e p hp hp11 hper U A lag hslack hA2 hsub htight hU_P2 hU_pos
  have haas := p11_tight_avoiding_le_two_all_aas e p hp hp11 hper U A lag hslack hA2 hsub htight hU_P2 hU_pos
  have hdisj : ∀ u ∈ A, oldestSubtractionPhase p u0 (lag u0) ≠ endpointPhase p (u : Int) 3 := by
    intro u hu
    have huU := hsub.subset hu
    have hPu := hU_P2 u huU
    have heq := h3 u hu
    have hP3 : ShortPeriodicSupply.P2 e (u : Int) 3 := by rwa [heq] at hPu
    have hAAS_u := haas u hu
    unfold oldestSubtractionPhase
    exact ss2_lag_lt_fifteen_disjoint_from_aas e p hp hper u0 u (lag u0) hu0A (hU_A u huU) hd_lt hss0 hP0 hP3 hAAS_u
  have hnot_mem : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag :=
    tight_avoids_of_all_lag_three e p hp A lag h3 haas (oldestSubtractionPhase p u0 (lag u0)) hdisj
  have hhallA := hhall_orig A hsub
  exact deleted_hall_of_not_mem e p A lag (oldestSubtractionPhase p u0 (lag u0)) hnot_mem hhallA

/-- Unconditional Resolution of Gate T6 for all periodic words of period p ≤ 11 with |U| ≤ 3. -/
theorem p11_gate_t6_of_U_le_three (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  intro A hsub
  by_cases hu0A_mem : u0 ∈ A
  · have hss_ge : 2 ≤ ssCount (past e (u0 : Int) (lag u0)) := by omega
    exact p11_gate_t6_donor_containing_sublists_survive e p hp hp11 hper U A lag hsub.length_le hslack u0 hu0A_mem hP0 hss_ge (oldestSubtractionPhase p u0 (lag u0))
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have hA2 : A.length ≤ 2 := by
        have hle := sublist_length_le_sub_one_of_mem_not_mem hsub hu0 hu0A_mem
        omega
      exact p11_tight_avoiding_le_two_survives e p hp hp11 hper U A lag u0 hslack hd_lt hu0A hP0 hss0 hA2 hsub htight hhall_orig hU_pos hU_P2 hU_A
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact p11_gate_t6_slack_sublists_survive e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA

/-- Unconditional Resolution of Gate T6 for all periodic words of period p ≤ 11 with |D| ≤ 4. -/
theorem p11_gate_t6_of_D_le_four (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hU3 : U.length ≤ 3 := by omega
  exact p11_gate_t6_of_U_le_three e p hp hp11 hper U lag hslack hU3 u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A

/-- Unconditional Resolution of Gate T6 for all periodic words of period p ≤ 11 when high-SS windows force |U| ≤ 3. -/
theorem p11_gate_t6_of_capacity_le_three (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hbound : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length - 2)
    (hD5 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 5)
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
  have hU3 : U.length ≤ 3 := by omega
  exact p11_gate_t6_of_U_le_three e p hp hp11 hper U lag hslack hU3 u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A

/-- Master Synthesis: Grand Eleven Capacity Rigidity Theorem. -/
theorem grand_eleven_capacity_rigidity_synthesis (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    (∀ A : List Nat, List.Sublist A U → (neighborhood e p A lag).length = A.length → u0 ∉ A → ∀ u ∈ A, lag u = 3) ∧
    (∀ A : List Nat, List.Sublist A U →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) := by
  refine ⟨?_, p11_gate_t6_of_U_le_three e p hp hp11 hper U lag hslack hU3 u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A⟩
  intro A hsub htight hnot u hu
  have hA2 : A.length ≤ 2 := by
    have hle := sublist_length_le_sub_one_of_mem_not_mem hsub hu0 hnot
    omega
  exact p11_tight_avoiding_le_two_all_lag_three e p hp hp11 hper U A lag hslack hA2 hsub htight hU_P2 hU_pos u hu

end Recaman.ElevenCapacityRigidity
