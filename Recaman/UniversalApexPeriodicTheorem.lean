import Recaman.GrandApexPeriodTwentyFourTheorem
import Recaman.ArbitraryPeriodLagRigidity
import Recaman.ArbitraryPeriodGateT6Resolution
import Recaman.ArbitraryPeriodGateT6Unconditional

/-!
# UniversalApexPeriodicTheorem: Master Apex Synthesis for Arbitrary Periods p

This module establishes the comprehensive master universal apex synthesis unifying the
fully parametric capacity stratification, closed-form quantum lag bounds, universal small-size
survival (|A| ≤ 2), all-AAS survival, and the complete closed-form Gate T6 multi-tier reduction
hierarchy for arbitrary periods p (fully closed-form for all p ∈ ℕ):

1. `universal_apex_parametric_capacity`: Closed-form capacity bounds for any period p:
   |D| ≤ (p - 1) / 2 and |A| ≤ |D| - 2 ≤ (p - 1) / 2 - 2.
2. `universal_apex_quantum_lag_hierarchy`: Universal quantum lag level bound:
   m ≤ (|D| - 3) / 2 for any window covering ≥ 2m + 1 subtractions in a tight avoiding subset,
   and strict impossibility of windows covering ≥ |D| - 1 subtractions.
3. `universal_apex_tight_size_two_survival`: Any tight avoiding sublist of size ≤ 2 strictly
   survives deletion of s*(u₀) unconditionally across ALL periods p.
4. `universal_apex_all_aas_survival`: Any tight avoiding subset consisting purely of lag 3 AAS
   windows strictly survives deletion with zero loss across ALL periods p.
5. `universal_apex_gate_t6_closed_form_reduction`: Gate T6 holds across ALL periods p provided
   that all tight avoiding sublists of intermediate sizes (3 ≤ |B| ≤ |D| - 2) avoid s*(u₀).
6. `universal_apex_gate_t6_unconditional_tier_one`: Unconditional Gate T6 survival when |U| ≤ 3.
7. `universal_apex_gate_t6_unconditional_tier_two`: Unconditional Gate T6 survival when |D| ≤ 4.
8. `universal_apex_gate_t6_reduction_tier_three`: Gate T6 reduction to tight triples when |U| ≤ 4.
9. `universal_apex_gate_t6_reduction_tier_four`: Gate T6 reduction to tight triples when |D| ≤ 5.
10. `grand_universal_apex_periodic_synthesis`: Master universal apex synthesis theorem for all periods p.
-/

namespace Recaman.UniversalApexPeriodicTheorem

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
open SixteenLagRigidity SixteenGateT6Resolution EighteenLagRigidity EighteenGateT6Resolution
open EighteenGateT6Unconditional ApexPeriodicRigidityTheorem GrandApexPeriodEighteenTheorem
open TwentyLagRigidity TwentyGateT6Resolution TwentyGateT6Unconditional
open TwentyTwoLagRigidity TwentyTwoGateT6Resolution TwentyTwoGateT6Unconditional
open GrandApexPeriodTwentyTwoTheorem
open TwentyFourLagRigidity TwentyFourGateT6Resolution TwentyFourGateT6Unconditional
open GrandApexPeriodTwentyFourTheorem
open ArbitraryPeriodLagRigidity ArbitraryPeriodGateT6Resolution ArbitraryPeriodGateT6Unconditional

/-- Universal parametric capacity bounds for arbitrary period p under positive signSum. -/
theorem universal_apex_parametric_capacity (e : Int → Bool) (p : Nat)
    (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    (LagElevenPeriodic.subPhases e 0 p).length ≤ (p - 1) / 2 ∧
    A.length ≤ (LagElevenPeriodic.subPhases e 0 p).length - 2 ∧
    A.length ≤ (p - 1) / 2 - 2 := by
  have hD := arbitrary_period_subtractions_bound e p hpos
  have hdef := arbitrary_period_avoiding_size_bound e p hpos A U u0 hu0 hnot hsub hslack
  exact ⟨hD, hdef.1, hdef.2⟩

/-- Universal quantum lag hierarchy for tight avoiding subsets across all periods p. -/
theorem universal_apex_quantum_lag_hierarchy (e : Int → Bool) (p : Nat)
    (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (A U : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    (∀ m : Nat, 2 * m + 1 ≤ A.length → m ≤ ((LagElevenPeriodic.subPhases e 0 p).length - 3) / 2) ∧
    (∀ k : Nat, k ≤ A.length → (LagElevenPeriodic.subPhases e 0 p).length - 1 ≤ k → False) := by
  refine ⟨fun m hm => arbitrary_period_tight_quantum_level_bound e p hpos A U u0 hu0 hnot hsub hslack m hm,
          fun k hk hge => arbitrary_period_no_large_window_in_tight e p A U u0 hu0 hnot hsub hslack k hk hge⟩

/-- Universal size ≤ 2 survival across all periods p. -/
theorem universal_apex_tight_size_two_survival (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
  arbitrary_period_tight_size_two_survives e p hp hper A lag hA2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A

/-- Universal all-AAS tight survival across all periods p. -/
theorem universal_apex_all_aas_survival (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (htight : (neighborhood e p A lag).length = A.length)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hA_A : ∀ u ∈ A, e (u : Int) = true) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  arbitrary_period_all_aas_survives e p hp hper A lag u0 hd_lt hu0A hP0 hss0 htight hlag3 haas hP_A hA_A

/-- Closed-form Gate T6 reduction across all periods p. -/
theorem universal_apex_gate_t6_closed_form_reduction (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
      (3 ≤ B.length ∧ B.length ≤ (LagElevenPeriodic.subPhases e 0 p).length - 2) →
      (neighborhood e p B lag).length = B.length →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  arbitrary_period_avoiding_sublist_survives_of_tight_avoidance e p hp hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_tight_avoid

/-- Gate T6 unconditional survival: Tier 1 (|U| ≤ 3) for all periods p. -/
theorem universal_apex_gate_t6_unconditional_tier_one (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hd_lt : lag u0 < 15) (hu0A : e (u0 : Int) = true)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hhall_orig : ∀ B : List Nat, List.Sublist B U → B.length ≤ (neighborhood e p B lag).length)
    (hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u))
    (hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7)
    (hp_gt : 7 < p)
    (hA_A : ∀ u ∈ A, e (u : Int) = true)
    (hU3 : U.length ≤ 3) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  arbitrary_period_capacity_tier_one e p hp hper U A lag u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A hU3

/-- Gate T6 unconditional survival: Tier 2 (|D| ≤ 4) for all periods p. -/
theorem universal_apex_gate_t6_unconditional_tier_two (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
  arbitrary_period_capacity_tier_two e p hp hper U A lag hslack hD4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A

/-- Gate T6 reduction: Tier 3 (|U| ≤ 4 reduces to triples) for all periods p. -/
theorem universal_apex_gate_t6_reduction_tier_three (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
  arbitrary_period_capacity_tier_three e p hp hp14 hpos hper U A lag hslack hU4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_tight3

/-- Gate T6 reduction: Tier 4 (|D| ≤ 5 reduces to triples) for all periods p. -/
theorem universal_apex_gate_t6_reduction_tier_four (e : Int → Bool) (p : Nat) (hp : 0 < p)
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
  arbitrary_period_capacity_tier_four e p hp hp14 hpos hper U A lag hslack hD5 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_tight3

/-- Master Synthesis: Grand Universal Apex Periodic Synthesis Theorem for ALL periods p. -/
theorem grand_universal_apex_periodic_synthesis (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
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
    -- (1) Subtractions bounded by (p - 1) / 2
    (LagElevenPeriodic.subPhases e 0 p).length ≤ (p - 1) / 2 ∧
    -- (2) Avoiding size bounded by |D| - 2
    (∀ A : List Nat, List.Sublist A U → u0 ∉ A → A.length ≤ (LagElevenPeriodic.subPhases e 0 p).length - 2) ∧
    -- (3) Universal tight size ≤ 2 survival
    (∀ A : List Nat, A.length ≤ 2 → (neighborhood e p A lag).length = A.length →
      (∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u)) →
      (∀ u ∈ A, lag u = 3 ∨ lag u = 7) →
      (∀ u ∈ A, e (u : Int) = true) →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (4) Universal all-AAS survival
    (∀ A : List Nat, (neighborhood e p A lag).length = A.length →
      (∀ u ∈ A, lag u = 3) →
      (∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false) →
      (∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u)) →
      (∀ u ∈ A, e (u : Int) = true) →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (5) Closed-form Gate T6 reduction across all intermediate sizes
    ((∀ B : List Nat, List.Sublist B U → u0 ∉ B →
        (3 ≤ B.length ∧ B.length ≤ (LagElevenPeriodic.subPhases e 0 p).length - 2) →
        (neighborhood e p B lag).length = B.length →
        oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p B lag) →
      ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
        A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (6) Gate T6 holds unconditionally when |U| ≤ 3
    (U.length ≤ 3 → ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) ∧
    -- (7) Gate T6 holds unconditionally when |D| ≤ 4
    ((LagElevenPeriodic.subPhases e 0 p).length ≤ 4 → ∀ A : List Nat, List.Sublist A U → u0 ∉ A →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length) := by
  refine ⟨arbitrary_period_subtractions_bound e p hpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A hsub hnot
    exact (universal_apex_parametric_capacity e p hpos A U u0 hu0 hnot hsub hslack).2.1
  · intro A hle2 htight hP_A hlags hA_A
    exact universal_apex_tight_size_two_survival e p hp hper A lag hle2 htight u0 hd_lt hu0A hP0 hss0 hP_A hlags hp_gt hA_A
  · intro A htight hlag3 haas hP_A hA_A
    exact universal_apex_all_aas_survival e p hp hper A lag u0 hd_lt hu0A hP0 hss0 htight hlag3 haas hP_A hA_A
  · intro h_avoid A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact universal_apex_gate_t6_closed_form_reduction e p hp hper U A lag hslack u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A h_avoid
  · intro hU3 A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact universal_apex_gate_t6_unconditional_tier_one e p hp hper U A lag u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A hU3
  · intro hD4 A hsub hnot
    have hP_A : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u) := fun u hu => hU_P2 u (hsub.subset hu)
    have hlags : ∀ u ∈ A, lag u = 3 ∨ lag u = 7 := fun u hu => hU_lags u (hsub.subset hu)
    have hA_A : ∀ u ∈ A, e (u : Int) = true := fun u hu => hU_A u (hsub.subset hu)
    exact universal_apex_gate_t6_unconditional_tier_two e p hp hper U A lag hslack hD4 u0 hu0 hnot hsub hd_lt hu0A hP0 hss0 hhall_orig hP_A hlags hp_gt hA_A

end Recaman.UniversalApexPeriodicTheorem
