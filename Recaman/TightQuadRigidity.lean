import Recaman.FourteenGateT6Resolution
import Recaman.LagSevenNeighborhoodRigidity

/-!
# TightQuadRigidity: Tight Quadruple Rigidity, Capacity Bounds, and Gate T6 Reduction for p ≤ 14

This module formalizes structural bounds and rigidity for tight avoiding quadruples (size 4)
and establishes capacity closure for Gate T6 in period p ≤ 14:

1. `tight_quad_all_aas_avoids_s_star`: Any tight avoiding quadruple of size 4 consisting purely of
   lag 3 AAS windows strictly avoids the donated subtraction s*(u₀).
2. `tight_quad_all_aas_survives`: Any tight avoiding quadruple of size 4 consisting purely of
   lag 3 AAS windows strictly survives deletion of s*(u₀) with zero loss.
3. `tight_quad_survives_of_not_mem`: Any tight avoiding quadruple of size 4 strictly survives
   deletion of s*(u₀) whenever s*(u₀) ∉ N(A).
4. `avoiding_size_le_three_of_U_le_four`: In any periodic word, if |U| ≤ 4, then any avoiding
   sublist A ⊆ U \ {u₀} satisfies |A| ≤ 3 (no avoiding quadruples can exist).
5. `avoiding_size_le_three_of_D_le_five`: In any periodic word with positive slack, if |D| ≤ 5,
   then any avoiding sublist satisfies |A| ≤ 3 (no avoiding quadruples can exist).
6. `p14_gate_t6_of_U_le_four_and_triples`: If |U| ≤ 4, Gate T6 on all avoiding sublists reduces
   entirely to tight triples of size 3.
7. `p14_gate_t6_of_D_le_five_and_triples`: If |D| ≤ 5, Gate T6 on all avoiding sublists reduces
   entirely to tight triples of size 3.
8. `tight_quad_lag7_neighborhood_ge_three`: In any tight quadruple A of size 4, any element
   with lag 7 has a singleton neighborhood of size at least 3 that is a subset of N(A).
9. `p14_gate_t6_complete_quad_reduction`: In period p ≤ 14, every avoiding sublist survives
   deletion of s*(u₀) if tight triples and tight quads avoid s*(u₀).
10. `grand_tight_quad_rigidity_synthesis`: Master synthesis theorem for tight quadruple rigidity.
-/

namespace Recaman.TightQuadRigidity

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
open FourteenGateT6Resolution

/-- Any tight avoiding quadruple of size 4 consisting purely of lag 3 AAS windows strictly
avoids the donated subtraction s*(u₀). -/
theorem tight_quad_all_aas_avoids_s_star (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (_hA4 : A.length = 4)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag :=
  all_aas_tight_avoids_ss2_donation e p hp hper A lag u0 hd_lt hu0A hP0 hss0 hlag3 haas hP_A hA_A

/-- Any tight avoiding quadruple of size 4 consisting purely of lag 3 AAS windows strictly
survives deletion of s*(u₀) with zero loss. -/
theorem tight_quad_all_aas_survives (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hA4 : A.length = 4)
    (htight : (neighborhood e p A lag).length = 4)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot := tight_quad_all_aas_avoids_s_star e p hp hper A lag u0 hd_lt hu0A hP0 hss0 hA4 hlag3 haas hP_A hA_A
  have htight' : (neighborhood e p A lag).length = A.length := by omega
  exact tight_triple_survives_of_s_not_mem e p A lag u0 htight' hnot

/-- Any tight avoiding quadruple of size 4 strictly survives deletion of s*(u₀) whenever s*(u₀) ∉ N(A). -/
theorem tight_quad_survives_of_not_mem (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat)
    (hA4 : A.length = 4)
    (htight : (neighborhood e p A lag).length = 4)
    (u0 : Nat)
    (hnot : oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p14_tight_quad_survives_of_not_mem e p A lag hA4 htight u0 hnot

/-- In any periodic word, if |U| ≤ 4, then any avoiding sublist A ⊆ U \ {u₀} satisfies |A| ≤ 3. -/
theorem avoiding_size_le_three_of_U_le_four (A U : List Nat) (u0 : Nat)
    (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hU4 : U.length ≤ 4) :
    A.length ≤ 3 := by
  have hle := sublist_length_le_sub_one_of_mem_not_mem hsub hu0 hnot
  omega

/-- In any periodic word with positive slack, if |D| ≤ 5, then any avoiding sublist satisfies |A| ≤ 3. -/
theorem avoiding_size_le_three_of_D_le_five (e : Int → Bool) (p : Nat)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (hD5 : (LagElevenPeriodic.subPhases e 0 p).length ≤ 5) :
    A.length ≤ 3 :=
  p14_avoiding_size_le_three_of_D_le_five e p A U u0 hu0 hnot hsub hslack hD5

/-- If |U| ≤ 4, Gate T6 on all avoiding sublists reduces entirely to tight triples of size 3. -/
theorem p14_gate_t6_of_U_le_four_and_triples (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (_hp14 : p ≤ 14) (_hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (_hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
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
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hA_le3 : A.length ≤ 3 := avoiding_size_le_three_of_U_le_four A U u0 hu0 hnot hsub hU4
  have hcases : A.length ≤ 2 ∨ A.length = 3 := by omega
  rcases hcases with hle2 | heq3
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · exact p14_tight_size_two_survives e p hp hper A lag hle2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have htight3 : (neighborhood e p A lag).length = 3 := by omega
      have hnot_mem := h_tight3 A hsub hnot heq3 htight3
      exact p14_tight_triple_survives_of_not_mem e p A lag heq3 htight3 u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA

/-- If |D| ≤ 5, Gate T6 on all avoiding sublists reduces entirely to tight triples of size 3. -/
theorem p14_gate_t6_of_D_le_five_and_triples (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (_hp14 : p ≤ 14) (_hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
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
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hA_le3 : A.length ≤ 3 := avoiding_size_le_three_of_D_le_five e p A U u0 hu0 hnot hsub hslack hD5
  have hcases : A.length ≤ 2 ∨ A.length = 3 := by omega
  rcases hcases with hle2 | heq3
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · exact p14_tight_size_two_survives e p hp hper A lag hle2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA
  · by_cases htight : (neighborhood e p A lag).length = A.length
    · have htight3 : (neighborhood e p A lag).length = 3 := by omega
      have hnot_mem := h_tight3 A hsub hnot heq3 htight3
      exact p14_tight_triple_survives_of_not_mem e p A lag heq3 htight3 u0 hnot_mem
    · have hhallA := hhall_orig A hsub
      have hslackA : A.length < (neighborhood e p A lag).length := by omega
      exact slack_avoiding_survives_deletion e p A lag (oldestSubtractionPhase p u0 (lag u0)) hslackA

/-- In any tight quadruple A of size 4, any element with lag 7 has a singleton neighborhood
of size at least 3 that is a subset of N(A). -/
theorem tight_quad_lag7_neighborhood_ge_three (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u : Nat) (hu : u ∈ A) (hlag7 : lag u = 7)
    (hp7 : 7 < p)
    (hPu : ShortPeriodicSupply.P2 e (u : Int) 7) :
    3 ≤ (neighborhood e p [u] lag).length ∧
    ∀ s ∈ neighborhood e p [u] lag, s ∈ neighborhood e p A lag := by
  have hNu3 := lag_seven_neighborhood_ge_three e p hp hper u lag hlag7 hp7 hPu
  have hsub_u : ∀ s ∈ neighborhood e p [u] lag, s ∈ neighborhood e p A lag := by
    intro s hs
    rw [neighborhood, List.mem_filter] at hs ⊢
    refine ⟨hs.1, ?_⟩
    rw [isCoveredBySubset_iff] at hs ⊢
    obtain ⟨w, hw, hcov⟩ := hs.2
    simp only [List.mem_singleton] at hw
    subst w
    exact ⟨u, hu, hcov⟩
  exact ⟨hNu3, hsub_u⟩

/-- In period p ≤ 14, every avoiding sublist survives deletion of s*(u₀) if tight triples
and tight quads avoid s*(u₀). -/
theorem p14_gate_t6_complete_quad_reduction (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p14_avoiding_sublist_survives_of_tight_avoidance e p hp hp14 hpos hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_tight_avoid

/-- Master Synthesis: Grand Tight Quadruple Rigidity Theorem. -/
theorem grand_tight_quad_rigidity_synthesis
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
    -- (1) Tight quads consisting of lag 3 AAS windows strictly survive
    (∀ A : List Nat, List.Sublist A U → u0 ∉ A → A.length = 4 →
      (neighborhood e p A lag).length = 4 →
      (∀ u ∈ A, lag u = 3) →
      (∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false) →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (2) Avoiding size bounded by 3 when |U| ≤ 4
    (U.length ≤ 4 → ∀ A : List Nat, List.Sublist A U → u0 ∉ A → A.length ≤ 3) ∧
    -- (3) Avoiding size bounded by 3 when |D| ≤ 5
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 5 → ∀ A : List Nat, List.Sublist A U → u0 ∉ A → A.length ≤ 3) ∧
    -- (4) Gate T6 reduction to tight triples when |U| ≤ 4
    (U.length ≤ 4 →
      (∀ B : List Nat, List.Sublist B U → u0 ∉ B → B.length = 3 →
        (neighborhood e p B lag).length = 3 →
        oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) →
      ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
        A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (5) Gate T6 reduction to tight triples when |D| ≤ 5
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 5 →
      (∀ B : List Nat, List.Sublist B U → u0 ∉ B → B.length = 3 →
        (neighborhood e p B lag).length = 3 →
        oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) →
      ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
        A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A hsub hnot hA4 htight hlag3 haas
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact tight_quad_all_aas_survives e p hp hper A lag u0 hd_lt hu0A hP0 hss0 hA4 htight hlag3 haas hP_A hA_A
  · intro hU4 A hsub hnot
    exact avoiding_size_le_three_of_U_le_four A U u0 hu0 hnot hsub hU4
  · intro hD5 A hsub hnot
    exact avoiding_size_le_three_of_D_le_five e p A U u0 hu0 hnot hsub hslack hD5
  · intro hU4 h_triples A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact p14_gate_t6_of_U_le_four_and_triples e p hp hp14 hpos hper U A lag hslack hU4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_triples
  · intro hD5 h_triples A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact p14_gate_t6_of_D_le_five_and_triples e p hp hp14 hpos hper U A lag hslack hD5 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_triples

end Recaman.TightQuadRigidity
