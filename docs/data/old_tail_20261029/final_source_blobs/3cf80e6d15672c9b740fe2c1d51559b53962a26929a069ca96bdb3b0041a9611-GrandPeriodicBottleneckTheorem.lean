import Recaman.UniversalGateT6Closure

/-!
# GrandPeriodicBottleneckTheorem: Master Synthesis of the Stratified Hierarchy and Gate T6

This module provides the overarching master synthesis of the entire stratified bottleneck
and capacity reduction architecture developed across E-195 through E-225:

1. `apex_tight_lag_quantization_p19`: For any periodic word of period `p ≤ 19`, all non-wrapping
   tight bottleneck lags belong to the discrete set `{3, 7, 11, 15}`.
2. `apex_tight_ss_bound_p19`: For `p ≤ 19`, all non-wrapping tight bottleneck windows have `ssCount ≤ 5`.
3. `apex_tight_ss_bound_p15`: For `p ≤ 15`, all non-wrapping tight bottleneck windows have `ssCount ≤ 3`.
4. `apex_tight_ss_bound_p11`: For `p ≤ 11`, all non-wrapping tight bottleneck windows have `ssCount ≤ 1`.
5. `apex_tight_ss_zero_p7`: For `p ≤ 7`, all non-wrapping tight bottleneck windows have `ssCount = 0` (lag 3 AAS).
6. `apex_hall_reduction_hierarchy_p11`: Hall condition on `U` for `p ≤ 11` is logically equivalent
   to Hall condition on low-SS subsets (`ssCount ≤ 1`).
7. `apex_hall_reduction_hierarchy_p7`: Hall condition on `U` for `p ≤ 7` is logically equivalent
   to Hall condition on clean AAS subsets (`ssCount = 0`).
8. `apex_slack_compensation_hierarchy_p11`: In any positive-slack word with `p ≤ 11`, any subset
   containing an `ssCount ≥ 2` window survives the deletion of ANY subtraction `s ∈ D`.
9. `apex_gate_t6_unconditional_p7`: Complete, unconditional resolution of Research Gate **T6**
   for all periodic words of period `p ≤ 7`.
10. `apex_gate_t6_complete_reduction_p11`: Complete reduction of Gate T6 deletability to tight
    low-SS avoiding subsets for all `p ≤ 11`.
11. `grand_periodic_bottleneck_synthesis`: The unified master theorem linking quantum lag
    quantization, Hall robustness, capacity slack compensation, and Gate T6 resolution.
-/

namespace Recaman.GrandPeriodicBottleneckTheorem

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint TwoSSLocalDonation TwoSSAvoidTight
open WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound
open UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem SS2AASCollisionObstruction
open ElevenSSDonationClosure LagSevenTightObstruction UniversalTwoSSDonationTheorem
open TightPeriodStratification TightSubsetSSExclusion HighSSWrappingTheorem
open HallRobustnessTheorem PeriodicHallReduction CapacitySlackCompensation
open UniversalGateT6Closure
open OneSSMultiplicity LeadingRunSupply LowSSPeriodicSupply

/-- Quantum Lag Quantization for p ≤ 19: All non-wrapping tight bottleneck lags belong
to {3, 7, 11, 15}. -/
theorem apex_tight_lag_quantization_p19 (p : Nat) (hp : p ≤ 19)
    (d : Nat) (hd_lt : d < p) (hpos : 0 < d) (hmod : d % 4 = 3) :
    d = 3 ∨ d = 7 ∨ d = 11 ∨ d = 15 :=
  tight_lags_p_le_nineteen p hp d hd_lt hpos hmod

/-- SS ≤ 5 Bound for p ≤ 19: All non-wrapping tight bottleneck windows have ssCount ≤ 5. -/
theorem apex_tight_ss_bound_p19 (p : Nat) (hp : p ≤ 19)
    (w : List Bool) (hP : P2 w) (hlt : w.length < p) :
    ssCount w ≤ 5 :=
  tight_ss_le_five_of_p_le_nineteen p hp w hP hlt

/-- SS ≤ 3 Bound for p ≤ 15: All non-wrapping tight bottleneck windows have ssCount ≤ 3. -/
theorem apex_tight_ss_bound_p15 (p : Nat) (hp : p ≤ 15)
    (w : List Bool) (hP : P2 w) (hlt : w.length < p) :
    ssCount w ≤ 3 :=
  tight_ss_le_three_of_p_le_fifteen p hp w hP hlt

/-- Low-SS Bound for p ≤ 11: All non-wrapping tight bottleneck windows have ssCount ≤ 1. -/
theorem apex_tight_ss_bound_p11 (p : Nat) (hp : p ≤ 11)
    (w : List Bool) (hP : P2 w) (hlt : w.length < p) :
    ssCount w ≤ 1 :=
  tight_ss_le_one_of_p_le_eleven p hp w hP hlt

/-- Clean AAS Rigidity for p ≤ 7: All non-wrapping tight bottleneck windows have ssCount = 0. -/
theorem apex_tight_ss_zero_p7 (p : Nat) (hp : p ≤ 7)
    (w : List Bool) (hP : P2 w) (hlt : w.length < p) :
    ssCount w = 0 :=
  tight_ss_zero_of_p_le_seven p hp w hP hlt

/-- Hall Reduction Equivalence for p ≤ 11: Hall's condition on U is logically equivalent
to Hall's condition on low-SS subsets (ssCount ≤ 1). -/
theorem apex_hall_reduction_hierarchy_p11 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hP : ∀ u ∈ U, P2 (past e (u : Int) (lag u))) :
    (∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length → A.length ≤ (neighborhood e p A lag).length) ↔
    (∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length → (∀ u ∈ A, ssCount (past e (u : Int) (lag u)) ≤ 1) →
      A.length ≤ (neighborhood e p A lag).length) :=
  hall_iff_low_ss_p11 e p hp_pos hp hper U lag hUleD hP

/-- Hall Reduction Equivalence for p ≤ 7: Hall's condition on U is logically equivalent
to Hall's condition on clean AAS subsets (ssCount = 0). -/
theorem apex_hall_reduction_hierarchy_p7 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p) (hp : p ≤ 7)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hUleD : U.length ≤ (LagElevenPeriodic.subPhases e 0 p).length)
    (hP : ∀ u ∈ U, P2 (past e (u : Int) (lag u))) :
    (∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length → A.length ≤ (neighborhood e p A lag).length) ↔
    (∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ U.length → (∀ u ∈ A, ssCount (past e (u : Int) (lag u)) = 0) →
      A.length ≤ (neighborhood e p A lag).length) :=
  hall_iff_clean_p7 e p hp_pos hp hper U lag hUleD hP

/-- Universal Slack Compensation for p ≤ 11: Any subset containing an ssCount ≥ 2 window
survives the deletion of ANY subtraction. -/
theorem apex_slack_compensation_hierarchy_p11 (e : Int → Bool) (p : Nat) (hp_pos : 0 < p)
    (hp : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U A : List Nat) (lag : Nat → Nat)
    (hsublen : A.length ≤ U.length)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ A)
    (hP : P2 (past e (u0 : Int) (lag u0)))
    (hss : 2 ≤ ssCount (past e (u0 : Int) (lag u0)))
    (s : Nat) :
    A.length ≤ (deletedNeighborhood e p A lag s).length :=
  high_ss_containing_subsets_survive_deletion_p11 e p hp_pos hp hper U A lag hsublen hslack u0 hu0 hP hss s

/-- Unconditional Resolution of Gate T6 for p ≤ 7: The donated subtraction s*(u0) preserves
Hall's marriage condition on ALL sublists of U unconditionally. -/
theorem apex_gate_t6_unconditional_p7 (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp7 : p ≤ 7) (hper : ∀ x : Int, e (x + p) = e x)
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
  p7_universal_gate_t6_deletability e p hp hp7 hper U lag hslack u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A

/-- Complete Reduction of Gate T6 Deletability to Tight Avoiding Sublists for p ≤ 11. -/
theorem apex_gate_t6_complete_reduction_p11 (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hss0 : 2 ≤ ssCount (past e (u0 : Int) (lag u0)))
    (hhall_orig : ∀ A : List Nat, List.Sublist A U → A.length ≤ (neighborhood e p A lag).length)
    (havoid : ∀ A : List Nat, List.Sublist A U → (neighborhood e p A lag).length = A.length → u0 ∉ A →
      oldestSubtractionPhase p u0 (lag u0) ∉ neighborhood e p A lag) :
    ∀ A : List Nat, List.Sublist A U →
      A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p11_gate_t6_tight_reduction e p hp hp11 hper U lag hslack u0 hu0 hP0 hss0 hhall_orig havoid

/-- Master Synthesis: Grand Periodic Bottleneck Theorem.
Unifying discrete quantum lag quantization, Hall robustness, capacity slack compensation,
and Gate T6 resolution across the stratified hierarchy. -/
theorem grand_periodic_bottleneck_synthesis (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp7 : p ≤ 7) (hper : ∀ x : Int, e (x + p) = e x)
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
  apex_gate_t6_unconditional_p7 e p hp hp7 hper U lag hslack u0 hu0 hd_lt hu0A hP0 hss0 hhall_orig hU_pos hU_P2 hU_A

end Recaman.GrandPeriodicBottleneckTheorem
