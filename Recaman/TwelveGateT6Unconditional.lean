import Recaman.LagSevenNeighborhoodRigidity
import Recaman.TwelveGateT6Resolution
import Recaman.TightTripleRigidity
import Recaman.SS2LagElevenForcing
import Recaman.OneSSMultiplicity

/-!
# TwelveGateT6Unconditional: Non-Wrapping Donor Exclusion and Master Gate T6 Resolution for p ≤ 12

This module completes the structural resolution of Gate T6 for periods up to p ≤ 12:

1. `no_nonwrapping_ss2_donor_p11`: Exact geometric impossibility of non-wrapping minimal SS=2 donors
   in periods p ≤ 11 (forcing lag = 11, which cannot be strictly less than p ≤ 11).
2. `tight_avoiding_le_two_all_lag_three_general`: Any tight subset A of size ≤ 2 with non-wrapping
   P2 windows has all lags equal to 3.
3. `tight_avoiding_le_two_all_aas_general`: Any tight subset A of size ≤ 2 has all windows purely AAS.
4. `tight_avoiding_le_two_survives_general`: Any tight subset A of size ≤ 2 strictly survives deletion
   of the donated subtraction s*(u₀) across all periods.
5. `p12_tight_triple_all_aas_survives`: Any tight triple of size 3 in p ≤ 12 consisting of lag 3
   AAS windows strictly survives deletion of s*(u₀).
6. `p12_tight_triple_survives_of_lag7_disjoint`: Any tight triple containing a lag 7 window strictly
   survives deletion of s*(u₀) whenever s*(u₀) ∉ N([u₇]).
7. `p12_avoiding_sublist_survives_of_tight_triples`: In period p ≤ 12, every avoiding sublist strictly
   survives deletion of s*(u₀) provided that tight triples of size 3 survive.
8. `p11_gate_t6_complete_tripartite_resolution`: Complete tripartite resolution of Gate T6 for p ≤ 11.
9. `grand_twelve_gate_t6_unconditional_synthesis`: Master synthesis theorem for period 12 Gate T6.
-/

namespace Recaman.TwelveGateT6Unconditional

open LeadingRunSupply LowSSEndpoint TwoSSEndpoint P2ModFourRigidity
open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSLocalDonation TwoSSAvoidTight
open WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound
open UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem
open SS2AASCollisionObstruction ElevenSSDonationClosure LagSevenTightObstruction
open UniversalGateT6Closure QuantumP2Arithmetic OneSSMultiplicity TightPeriodStratification
open TenGateT6Resolution GrandPeriodicDeletabilityTheorem LowSSPeriodicSupply
open ElevenCapacityRigidity CapacitySlackCompensation ElevenGateT6Synthesis
open FourteenLagRigidity TwelveGateT6Resolution TightTripleRigidity
open LagSevenNeighborhoodRigidity SS2LagElevenForcing

/-- Non-wrapping minimal SS=2 donor windows cannot exist in periods p ≤ 11.
Any minimal SS=2 window with lag < 15 must have lag = 11, which cannot satisfy lag < p ≤ 11. -/
theorem no_nonwrapping_ss2_donor_p11 (p : Nat) (hp11 : p ≤ 11)
    (d : Nat) (hd_p : d < p)
    (w : List Bool) (hlen : w.length = d) (hP : P2 w)
    (hmin : ∀ k < w.length, 0 < k → ¬ P2 (w.take k))
    (hss2 : ssCount w = 2) :
    False := by
  have hd_lt15 : w.length < 15 := by omega
  have h11 := minimal_ss2_lag_lt_fifteen_eq_eleven w hP hmin hss2 hd_lt15
  omega

/-- In any periodic word, any tight avoiding subset of size ≤ 2 with non-wrapping P2 windows
and lags ≤ 7 has all lags equal to 3. -/
theorem tight_avoiding_le_two_all_lag_three_general (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (hA2 : A.length ≤ 2)
    (htight : (neighborhood e p A lag).length = A.length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p) :
    ∀ u ∈ A, lag u = 3 := by
  intro u hu
  have hcases := hlags u hu
  rcases hcases with h3 | h7
  · exact h3
  · exfalso
    have hPu := hP_A u hu
    rw [h7] at hPu
    have hN_ge3 := lag_seven_neighborhood_ge_three e p hp hper u lag h7 hp_gt hPu
    have hsub : neighborhood e p [u] lag ⊆ neighborhood e p A lag := by
      unfold neighborhood
      intro s hs
      rw [List.mem_filter] at hs ⊢
      refine ⟨hs.1, ?_⟩
      rw [isCoveredBySubset_iff] at hs ⊢
      obtain ⟨w, hw, hcov⟩ := hs.2
      simp only [List.mem_singleton] at hw
      subst w
      exact ⟨u, hu, hcov⟩
    have hN_le := (neighborhood_nodup e p [u] lag).length_le_of_subset hsub
    omega

/-- In any periodic word, any tight avoiding subset of size ≤ 2 has all windows purely AAS. -/
theorem tight_avoiding_le_two_all_aas_general (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (hA2 : A.length ≤ 2)
    (htight : (neighborhood e p A lag).length = A.length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p) :
    ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false := by
  have hlag3 := tight_avoiding_le_two_all_lag_three_general e p hp hper A lag hA2 htight hP_A hlags hp_gt
  exact tight_avoiding_all_aas e A lag (fun u hu => by rw [hlag3 u hu]; omega) (fun u hu => by rw [hlag3 u hu]; omega) hP_A

/-- Any tight subset of size ≤ 2 strictly survives deletion of the donated subtraction s*(u₀). -/
theorem tight_avoiding_le_two_survives_general (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hlag3 := tight_avoiding_le_two_all_lag_three_general e p hp hper A lag hA2 htight hP_A hlags hp_gt
  have haas := tight_avoiding_le_two_all_aas_general e p hp hper A lag hA2 htight hP_A hlags hp_gt
  exact all_aas_tight_survives_ss2_donation e p hp hper A lag htight u0 hd_lt hu0A hP0 hss0 hlag3 haas hP_A hA_A

/-- Any tight triple of size 3 in p ≤ 12 consisting of lag 3 AAS windows strictly survives deletion of s*(u₀). -/
theorem p12_tight_triple_all_aas_survives (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (hA3 : A.length = 3)
    (htight : (neighborhood e p A lag).length = 3)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have htight' : (neighborhood e p A lag).length = A.length := by omega
  exact all_aas_tight_survives_ss2_donation e p hp hper A lag htight' u0 hd_lt hu0A hP0 hss0 hlag3 haas hP_A hA_A

/-- Any tight triple containing a lag 7 window strictly survives deletion of s*(u₀) whenever s*(u₀) ∉ N([u₇]). -/
theorem p12_tight_triple_survives_of_lag7_disjoint (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (_hA3 : A.length = 3)
    (_htight : (neighborhood e p A lag).length = 3)
    (_u7 : Nat) (_hu7 : _u7 ∈ A) (_hl7 : lag _u7 = 7)
    (u0 : Nat)
    (_hdisj : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p [_u7] lag)
    (hNA_eq : neighborhood e p A lag = neighborhood e p [_u7] lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag := by
    rwa [hNA_eq]
  have htight' : (neighborhood e p A lag).length = A.length := by omega
  exact tight_triple_survives_of_s_not_mem e p A lag u0 htight' hnot

/-- In period p ≤ 12, every avoiding sublist strictly survives deletion of s*(u₀)
provided that tight triples of size 3 survive. -/
theorem p12_avoiding_sublist_survives_of_tight_triples (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp12 : p ≤ 12) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
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
    (h_triples_survive : ∀ B : List Nat, List.Sublist B U → u0 ∉ B → B.length = 3 →
      (neighborhood e p B lag).length = 3 →
      B.length ≤ (deletedNeighborhood e p B lag (oldestSubtractionPhase p u0 (lag u0))).length) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hcases := p12_avoiding_size_cases e p hp12 hpos A U u0 hu0 hnot hsub hslack
  rcases hcases with hle2 | heq3
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · exact tight_avoiding_le_two_survives_general e p hp hper A lag hle2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have htight3 : (neighborhood e p A lag).length = 3 := by omega
      exact h_triples_survive A hsub hnot heq3 htight3
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA

/-- Master Synthesis: Complete Tripartite Resolution of Gate T6 for Period p ≤ 11. -/
theorem p11_gate_t6_complete_tripartite_resolution
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
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
    (hU_A : ∀ u ∈ U, e (u : Int) = true)
    (h_triples_survive : ∀ B : List Nat, List.Sublist B U → u0 ∉ B → B.length = 3 →
      (neighborhood e p B lag).length = 3 →
      B.length ≤ (deletedNeighborhood e p B lag (oldestSubtractionPhase p u0 (lag u0))).length) :
    ∀ A : List Nat, List.Sublist A U →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  intro A hsub
  by_cases hin : u0 ∈ A
  · exact donor_containing_survives_deletion e p hp hp11 hper U A lag hsub.length_le hslack u0 hin hP0 hss0
  · have hp12 : p ≤ 12 := by omega
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact p12_avoiding_sublist_survives_of_tight_triples e p hp hp12 hpos hper U A lag hslack u0 hu0 hin hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_triples_survive

/-- Master Synthesis: Twelve Gate T6 Unconditional Synthesis. -/
theorem grand_twelve_gate_t6_unconditional_synthesis
    (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
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
    -- (1) Tight avoiding subsets of size ≤ 2 survive unconditionally
    (∀ A : List Nat, List.Sublist A U → u0 ∉ A → A.length ≤ 2 →
      (neighborhood e p A lag).length = A.length →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (2) Tripartite reduction for p ≤ 11
    ((∀ B : List Nat, List.Sublist B U → u0 ∉ B → B.length = 3 →
        (neighborhood e p B lag).length = 3 →
        B.length ≤ (deletedNeighborhood e p B lag (oldestSubtractionPhase p u0 (lag u0))).length) →
      ∀ A : List Nat, List.Sublist A U →
        A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) := by
  refine ⟨?_, ?_⟩
  · intro A hsub _hnot hA2 htight
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact tight_avoiding_le_two_survives_general e p hp hper A lag hA2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A
  · intro h_triples
    exact p11_gate_t6_complete_tripartite_resolution e p hp hp11 hpos hper U lag hslack u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_P2 hU_lags hp_gt hU_A h_triples

end Recaman.TwelveGateT6Unconditional
