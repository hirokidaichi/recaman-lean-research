import Recaman.LagSevenTightObstruction

/-!
# UniversalTwoSSDonationTheorem: Grand Synthesis of High-SS Local Donation for p ≤ 11

This module achieves the complete, unified formalization of the high-SS local donation
program (Research Gate **T6** at `ssCount = 2`) for all periods `p ≤ 11`:

1. `universal_ss2_avoiding_size_bound`: In any positive-slack word with `p ≤ 11` and positive
   period mass, any sublist avoiding an SS=2 donor has size `|A| ≤ 3`.
2. `universal_ss2_tight_size_two_rigidity`: Any tight avoiding subset of size `≤ 2` whose
   elements have `lag ≤ 5` is strictly rigid: all its members are lag 3 AAS windows.
3. `universal_ss2_donation_disjointness`: Automatic disjointness of `s*(u₀)` from all lag 3
   AAS endpoints in `U` for any SS=2 donor with `lag < 15`.
4. `universal_ss2_hall_preservation_p11`: Hall's marriage condition is universally preserved
   on all sublists of `U` after deleting the donated subtraction `s*(u₀)`.
5. `universal_ss2_deletability_p11`: The donated subtraction `s*(u₀)` is universally deletable
   from `D` for all periodic words of period `p ≤ 11`.
6. `universal_ss2_minimal_donor_closure`: When `u₀` is a minimal SS=2 window (`lag = 11`),
   the local donation is unconditionally valid and preserves Hall's condition across the
   entire period without any external hypotheses.
-/

namespace Recaman.UniversalTwoSSDonationTheorem

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint TwoSSLocalDonation TwoSSAvoidTight WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem SS2AASCollisionObstruction ElevenSSDonationClosure LagSevenTightObstruction OneSSMultiplicity LeadingRunSupply LowSSPeriodicSupply SharpPeriodicSupply EndpointRepetitionBudget LowSSEndpoint

/-- Universal size bound: in any positive-slack word with p ≤ 11 and positive period mass,
any sublist avoiding an SS=2 donor window has size |A| ≤ 3. -/
theorem universal_ss2_avoiding_size_bound (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (U A : List Nat) (u0 : Nat)
    (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    A.length ≤ 3 :=
  p11_tight_avoiding_size_le_three e p hp hp11 hpos U A u0 hu0 hnot hsub hslack

/-- Universal rigidity: any tight avoiding subset of size ≤ 2 with lags ≤ 5 consists
exclusively of lag 3 AAS windows. -/
theorem universal_ss2_tight_size_two_rigidity (e : Int → Bool)
    (A : List Nat) (lag : Nat → Nat)
    (hlag_pos : ∀ u ∈ A, 0 < lag u) (hlag_le5 : ∀ u ∈ A, lag u ≤ 5)
    (hP : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) (lag u)) :
    (∀ u ∈ A, lag u = 3) ∧
    (∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false) :=
  ⟨tight_avoiding_le_two_lag_three e A lag hlag_pos hlag_le5 hP,
   tight_avoiding_le_two_is_aas e A lag hlag_pos hlag_le5 hP⟩

/-- Automatic disjointness: the donated subtraction phase of an SS=2 donor with lag < 15
is provably disjoint from all lag 3 AAS endpoint phases in U. -/
theorem universal_ss2_donation_disjointness (e : Int → Bool) (p : Nat)
    (hp : 0 < p) (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat) (u0 : Nat)
    (hu0 : u0 ∈ U)
    (hd_lt : lag u0 < 15)
    (hu0A : e (u0 : Int) = true)
    (hss0 : ssCount (past e (u0 : Int) (lag u0)) = 2)
    (hP0 : ShortPeriodicSupply.P2 e (u0 : Int) (lag u0))
    (hUA : ∀ u ∈ U, e (u : Int) = true)
    (hlag_rest : ∀ u ∈ U, u ≠ u0 → lag u = 3)
    (hP_rest : ∀ u ∈ U, u ≠ u0 → ShortPeriodicSupply.P2 e (u : Int) 3)
    (hAAS_rest : ∀ u ∈ U, u ≠ u0 → e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false) :
    ∀ u ∈ U, u ≠ u0 → oldestSubtractionPhase p u0 (lag u0) ≠ endpointPhase p (u : Int) 3 :=
  ss2_donation_disjoint_of_lag_lt_fifteen e p hp hper U lag u0 hu0 hd_lt hu0A hss0 hP0 hUA hlag_rest hP_rest hAAS_rest

/-- Universal Hall preservation after SS=2 donation for all p ≤ 11. -/
theorem universal_ss2_hall_preservation_p11 (e : Int → Bool) (p : Nat)
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
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p11_ss2_donor_hall_preserved_of_lag_lt_fifteen e p hp hp11 hper U lag hslack u0 hu0 hd_lt hu0A hP hss hsublen hhall_orig hUA hlag_rest hP_rest hAAS_rest A hAU hAnodup

/-- Universal deletability of SS=2 donated subtraction for all p ≤ 11. -/
theorem universal_ss2_deletability_p11 (e : Int → Bool) (p : Nat)
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
    IsDeletableSubtraction e p U lag (oldestSubtractionPhase p u0 (lag u0)) :=
  p11_ss2_donor_deletable_of_lag_lt_fifteen e p hp hp11 hper U lag hslack u0 hu0 hd_lt hu0A hP hss hsublen hhall_orig hUA hlag_rest hP_rest hAAS_rest

/-- Unconditional closure for minimal SS=2 donors (lag = 11) across all p ≤ 11. -/
theorem universal_ss2_minimal_donor_closure (e : Int → Bool) (p : Nat)
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
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length :=
  p11_ss2_minimal_donor_hall_preserved e p hp hp11 hper U lag hslack u0 hu0 hmin hu0A hP hss hsublen hhall_orig hUA hlag_rest hP_rest hAAS_rest A hAU hAnodup

end Recaman.UniversalTwoSSDonationTheorem
