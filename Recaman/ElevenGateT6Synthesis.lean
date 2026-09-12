import Recaman.ElevenCapacityRigidity
import Recaman.SS2AASCollisionObstruction
import Recaman.TwoSSTightAvoidanceTheorem
import Recaman.CapacitySlackCompensation
import Recaman.TenGateT6Resolution
import Recaman.GrandPeriodicDeletabilityTheorem

/-!
# ElevenGateT6Synthesis: All-Size AAS Tight Survival and Tripartite Gate T6 Synthesis for p ≤ 11

This module establishes the general survival theorems for Gate T6 in period `p ≤ 11`:

1. `all_aas_tight_survives_ss2_donation`: For any tight avoiding subset `A` of ANY size,
   if all windows in `A` are lag 3 AAS, then `A` strictly survives deletion of the donated
   subtraction `s*(u₀)`. (Lifts tight survival from size ≤ 2 to arbitrary size!).
2. `slack_avoiding_survives_deletion`: For any avoiding subset `A` of arbitrary size,
   if `|A| < |N(A)|`, then `A` strictly survives deletion of any subtraction `s`.
3. `donor_containing_survives_deletion`: Any sublist `A` containing the donating window `u₀`
   strictly survives deletion of `s*(u₀)` by capacity slack compensation.
4. `p11_gate_t6_of_all_aas_tight`: If every tight avoiding sublist of `U` consists of lag 3
   AAS windows, then Gate T6 holds unconditionally on ALL sublists of `U`.
5. `p11_tight_avoiding_size_three_aas_survives`: Any tight avoiding sublist of size 3 consisting
   of lag 3 AAS windows strictly survives deletion of `s*(u₀)`.
6. `grand_eleven_gate_t6_synthesis`: Master synthesis theorem for period 11 Gate T6 resolution.
-/

namespace Recaman.ElevenGateT6Synthesis

open LeadingRunSupply LowSSEndpoint TwoSSEndpoint P2ModFourRigidity
open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSLocalDonation TwoSSAvoidTight
open WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound
open UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem
open SS2AASCollisionObstruction ElevenSSDonationClosure LagSevenTightObstruction
open UniversalGateT6Closure QuantumP2Arithmetic OneSSMultiplicity TightPeriodStratification
open TenGateT6Resolution GrandPeriodicDeletabilityTheorem LowSSPeriodicSupply
open ElevenCapacityRigidity CapacitySlackCompensation

/-- Any tight subset of ANY size consisting of lag 3 AAS windows strictly avoids the
donated subtraction s*(u₀) of any SS=2 donor with lag < 15. -/
theorem all_aas_tight_avoids_ss2_donation (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag := by
  apply tight_avoiding_s_not_mem e p hp A lag hlag3 haas
  intro u hu
  have hu_lag : lag u = 3 := hlag3 u hu
  have huP : ShortPeriodicSupply.P2 e (u : Int) 3 := by
    have hPu := hP_A u hu
    rwa [hu_lag] at hPu
  have huA : e (u : Int) = true := hA_A u hu
  have haas_u := haas u hu
  exact ss2_lag_lt_fifteen_disjoint_from_aas e p hp hper u0 u (lag u0) hu0A huA hd_lt hss0 hP0 huP haas_u

/-- Any tight subset of ANY size consisting of lag 3 AAS windows strictly survives
deletion of the donated subtraction s*(u₀). -/
theorem all_aas_tight_survives_ss2_donation (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (htight : (neighborhood e p A lag).length = A.length)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot := all_aas_tight_avoids_ss2_donation e p hp hper A lag u0 hd_lt hu0A hP0 hss0 hlag3 haas hP_A hA_A
  rw [deletedNeighborhood_eq_of_not_mem e p A lag (oldestSubtractionPhase p u0 (lag u0)) hnot]
  omega

/-- Local slack survival: any avoiding subset with |A| < |N(A)| survives deletion of ANY subtraction s. -/
theorem slack_avoiding_survives_deletion (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat) (s : Nat)
    (hslackA : A.length < (neighborhood e p A lag).length) :
    A.length ≤ (deletedNeighborhood e p A lag s).length :=
  deleted_hall_of_slack e p A lag s hslackA

/-- Donor-containing survival: any sublist containing u₀ survives deletion of s*(u₀) in period p ≤ 11. -/
theorem donor_containing_survives_deletion (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hAU : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hP : P2 (past e (u0 : Int) (lag u0)) := (past_p2_iff e (u0 : Int) (lag u0)).mpr hP0
  have hss : 2 ≤ ssCount (past e (u0 : Int) (lag u0)) := by omega
  exact high_ss_containing_subsets_survive_deletion_p11 e p hp hp11 hper U A lag hAU hslack u0 hu0 hP hss (oldestSubtractionPhase p u0 (lag u0))

/-- If all tight avoiding sublists are lag 3 AAS, Gate T6 holds unconditionally on ALL sublists of U. -/
theorem p11_gate_t6_of_all_aas_tight (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (_hu0 : u0 ∈ U)
    (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_A : ∀ u ∈ U, e (u : Int) = true)
    (htight_aas : ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
      (neighborhood e p A lag).length = A.length →
      (∀ u ∈ A, lag u = 3) ∧
      (∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)) :
    ∀ A : List Nat, List.Sublist A U →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  intro A hsub
  by_cases hu0A_mem : u0 ∈ A
  · exact donor_containing_survives_deletion e p hp hp11 hper U A lag hsub.length_le hslack u0 hu0A_mem hP0 hss0
  · have horig := hhall_orig A hsub
    by_cases htight : (neighborhood e p A lag).length = A.length
    · have haas_pair := htight_aas A hsub hu0A_mem htight
      have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
      have hA_sub : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
      exact all_aas_tight_survives_ss2_donation e p hp hper A lag htight u0 hd_lt hu0A hP0 hss0 haas_pair.1 haas_pair.2 hP_A hA_sub
    · have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA

/-- Any tight avoiding sublist of size 3 consisting of lag 3 AAS windows strictly survives
deletion of s*(u₀). -/
theorem p11_tight_avoiding_size_three_aas_survives (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hsub : List.Sublist A U)
    (hA3 : A.length = 3)
    (htight : (neighborhood e p A lag).length = 3)
    (u0 : Nat) (_hu0 : u0 ∈ U) (_hnot : u0 ∉ A)
    (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hU_P2 : ∀ u ∈ U, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hU_A : ∀ u ∈ U, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have htight_A : (neighborhood e p A lag).length = A.length := by omega
  have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
  have hA_sub : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
  exact all_aas_tight_survives_ss2_donation e p hp hper A lag htight_A u0 hd_lt hu0A hP0 hss0 hlag3 haas hP_A hA_sub

/-- Master Synthesis: Grand Eleven Gate T6 Synthesis Theorem. -/
theorem grand_eleven_gate_t6_synthesis (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    -- (1) Any avoiding sublist of size ≤ 2 is purely AAS and survives
    (∀ A : List Nat, List.Sublist A U → u0 ∉ A → (neighborhood e p A lag).length = A.length → A.length ≤ 2 →
      (∀ u ∈ A, lag u = 3) ∧
      (A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length)) ∧
    -- (2) Any avoiding sublist with slack survives
    (∀ A : List Nat, List.Sublist A U → A.length < (neighborhood e p A lag).length →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (3) Any sublist containing u₀ survives
    (∀ A : List Nat, List.Sublist A U → u0 ∈ A →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (4) Unconditional resolution whenever |U| ≤ 3
    (U.length ≤ 3 →
      ∀ A : List Nat, List.Sublist A U →
        A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A hsub hnot htight hA2
    have hlag3 := p11_tight_avoiding_le_two_all_lag_three e p hp hp11 hper U A lag hslack hA2 hsub htight hU_P2 hU_pos
    have hsurv := p11_tight_avoiding_le_two_survives e p hp hp11 hper U A lag u0 hslack hd_lt hu0A hP0 hss0 hA2 hsub htight hhall_orig hU_pos hU_P2 hU_A
    exact ⟨hlag3, hsurv⟩
  · intro A _hsub hslackA
    exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · intro A hsub hu0A_mem
    exact donor_containing_survives_deletion e p hp hp11 hper U A lag hsub.length_le hslack u0 hu0A_mem hP0 hss0
  · intro hU3
    exact p11_gate_t6_of_U_le_three e p hp hp11 hper U lag hslack hU3 u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A

end Recaman.ElevenGateT6Synthesis
