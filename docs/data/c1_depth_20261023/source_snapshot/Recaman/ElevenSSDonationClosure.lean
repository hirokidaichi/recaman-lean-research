import Recaman.SS2AASCollisionObstruction

/-!
# ElevenSSDonationClosure: Complete Capacity Closure for SS=2 Donation at p ≤ 11

This module establishes the unconditional closure of the high-SS local donation program
(gate T6 at `ssCount = 2`) for all periods `p ≤ 11`:

1. `p11_tight_avoiding_size_le_three`: Any sublist avoiding an SS=2 donor in a positive-slack
   word of period `p ≤ 11` has size `|A| ≤ 3`.
2. `ss2_donation_disjoint_of_lag_lt_fifteen`: Disjointness between the donated subtraction
   `s*(u₀)` and all lag 3 AAS endpoints in `U` is derived as a theorem whenever `lag u₀ < 15`,
   eliminating the need for any external disjointness hypothesis.
3. `p11_ss2_donor_deletable_of_lag_lt_fifteen`: For any periodic word of period `p ≤ 11` with
   positive slack, an SS=2 donor with `lag u₀ < 15` donates a universally deletable subtraction.
4. `p11_ss2_donor_hall_preserved_of_lag_lt_fifteen`: Hall's condition is universally preserved
   on all sublists of `U` after deleting `s*(u₀)` for all `p ≤ 11`.
5. `p11_ss2_minimal_donor_hall_preserved`: When `u₀` has minimal SS=2 lag (which is 11),
   Hall's condition is unconditionally preserved after donation for all `p ≤ 11`.
-/

namespace Recaman.ElevenSSDonationClosure

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint TwoSSLocalDonation TwoSSAvoidTight WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem SS2AASCollisionObstruction OneSSMultiplicity LeadingRunSupply LowSSPeriodicSupply SharpPeriodicSupply EndpointRepetitionBudget LowSSEndpoint

/-- In any positive-slack word with p ≤ 11 and positive period mass, any sublist
avoiding an SS=2 donor window has size |A| ≤ 3. -/
theorem p11_tight_avoiding_size_le_three (e : Int → Bool) (p : Nat) (_hp : 0 < p)
    (hp11 : p ≤ 11) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (U A : List Nat) (u0 : Nat)
    (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    A.length ≤ 3 := by
  have hD := subPhases_length_le_five_of_le_eleven e p hp11 hpos
  have hlen := sublist_avoiding_size_le_deficit hsub hu0 hnot hslack
  omega

/-- Automatic disjointness: if the SS=2 donor has lag < 15, then its donated subtraction
is provably disjoint from all lag 3 AAS endpoint phases in U. -/
theorem ss2_donation_disjoint_of_lag_lt_fifteen (e : Int → Bool) (p : Nat)
    (hp : 0 < p) (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat) (u0 : Nat)
    (_hu0 : u0 ∈ U)
    (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hUA : ∀ u ∈ U, e (u : Int) = true)
    (_hlag_rest : ∀ u ∈ U, u ≠ u0 → lag u = 3)
    (hP_rest : ∀ u ∈ U, u ≠ u0 → ShortPeriodicSupply.P2 e (u : Int) 3)
    (hAAS_rest : ∀ u ∈ U, u ≠ u0 → e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false) :
    ∀ u ∈ U, u ≠ u0 → oldestSubtractionPhase p u0 (lag u0) ≠ endpointPhase p (u : Int) 3 := by
  intro u hu hne
  unfold oldestSubtractionPhase
  exact ss2_lag_lt_fifteen_disjoint_from_aas e p hp hper u0 u (lag u0) hu0A (hUA u hu) hd_lt hss0 hP0 (hP_rest u hu hne) (hAAS_rest u hu hne)

/-- For all words of period p ≤ 11, an SS=2 donor with lag < 15 donates a universally
deletable subtraction phase. -/
theorem p11_ss2_donor_deletable_of_lag_lt_fifteen (e : Int → Bool) (p : Nat)
    (hp : 0 < p) (hp11 : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U)
    (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP : ShortPeriodicSupply.P2 e u0 (lag u0))
    (hss : ssCount (past e u0 (lag u0)) = 2)
    (hsublen : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.Nodup → A.length ≤ U.length)
    (hhall_orig : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ (neighborhood e p A lag).length)
    (hUA : ∀ u ∈ U, e (u : Int) = true)
    (hlag_rest : ∀ u ∈ U, u ≠ u0 → lag u = 3)
    (hP_rest : ∀ u ∈ U, u ≠ u0 → ShortPeriodicSupply.P2 e (u : Int) 3)
    (hAAS_rest : ∀ u ∈ U, u ≠ u0 → e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false) :
    IsDeletableSubtraction e p U lag (oldestSubtractionPhase p u0 (lag u0)) := by
  have hdisj := ss2_donation_disjoint_of_lag_lt_fifteen e p hp hper U lag u0 hu0 hd_lt hu0A hss hP hUA hlag_rest hP_rest hAAS_rest
  exact TwoSSSmallCapacityClosure.small_word_ss2_deletable e p hp hp11 hper U lag hslack u0 hP hss hsublen hhall_orig hlag_rest hAAS_rest hdisj

/-- For all words of period p ≤ 11, Hall's condition is universally preserved on all sublists
of U after donating s*(u₀) from an SS=2 donor with lag < 15. -/
theorem p11_ss2_donor_hall_preserved_of_lag_lt_fifteen (e : Int → Bool) (p : Nat)
    (hp : 0 < p) (hp11 : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U)
    (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hP : ShortPeriodicSupply.P2 e u0 (lag u0))
    (hss : ssCount (past e u0 (lag u0)) = 2)
    (hsublen : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.Nodup → A.length ≤ U.length)
    (hhall_orig : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ (neighborhood e p A lag).length)
    (hUA : ∀ u ∈ U, e (u : Int) = true)
    (hlag_rest : ∀ u ∈ U, u ≠ u0 → lag u = 3)
    (hP_rest : ∀ u ∈ U, u ≠ u0 → ShortPeriodicSupply.P2 e (u : Int) 3)
    (hAAS_rest : ∀ u ∈ U, u ≠ u0 → e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (A : List Nat) (hAU : ∀ u ∈ A, u ∈ U) (hAnodup : A.Nodup) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hdisj := ss2_donation_disjoint_of_lag_lt_fifteen e p hp hper U lag u0 hu0 hd_lt hu0A hss hP hUA hlag_rest hP_rest hAAS_rest
  exact TwoSSSmallCapacityClosure.small_word_hall_preserved_after_donation e p hp hp11 hper U lag hslack u0 hP hss hsublen hhall_orig hlag_rest hAAS_rest hdisj A hAU hAnodup

/-- When an SS=2 window has minimal lag d = 11, lag u₀ < 15 is automatically satisfied,
yielding unconditional Hall preservation after donation for all p ≤ 11. -/
theorem p11_ss2_minimal_donor_hall_preserved (e : Int → Bool) (p : Nat)
    (hp : 0 < p) (hp11 : p ≤ 11)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat) (hu0 : u0 ∈ U)
    (hmin : lag u0 = 11)
    (hu0A : e (u0 : Int) = true)
    (hP : ShortPeriodicSupply.P2 e u0 (lag u0))
    (hss : ssCount (past e u0 (lag u0)) = 2)
    (hsublen : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.Nodup → A.length ≤ U.length)
    (hhall_orig : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ (neighborhood e p A lag).length)
    (hUA : ∀ u ∈ U, e (u : Int) = true)
    (hlag_rest : ∀ u ∈ U, u ≠ u0 → lag u = 3)
    (hP_rest : ∀ u ∈ U, u ≠ u0 → ShortPeriodicSupply.P2 e (u : Int) 3)
    (hAAS_rest : ∀ u ∈ U, u ≠ u0 → e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (A : List Nat) (hAU : ∀ u ∈ A, u ∈ U) (hAnodup : A.Nodup) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hd_lt : lag u0 < 15 := by omega
  exact p11_ss2_donor_hall_preserved_of_lag_lt_fifteen e p hp hp11 hper U lag hslack u0 hu0 hd_lt hu0A hP hss hsublen hhall_orig hUA hlag_rest hP_rest hAAS_rest A hAU hAnodup

end Recaman.ElevenSSDonationClosure
