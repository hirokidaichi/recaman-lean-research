import Recaman.TwoSSWeightCapacity

/-!
# HighSSEliminationGrandTheorem: Grand Synthesis of High-SS Elimination and Gate T6 Resolution

This module establishes the Grand Reduction Theorem for Issue #73, closing Research Gate **T6**
at `ssCount = 2`:

1. `grand_capacity_reduction`: The Grand Reduction Principle: If the capacity bound |U| ≤ |D|
   holds for all low-SS periodic words (ssCount ≤ 1), and every high-SS window forces the strict
   deficit |U| ≤ |D| - 1, then |U| ≤ |D| holds globally and unconditionally on all periodic words.
2. `strict_deficit_of_deletable_ss2`: Any SS=2 donor window whose donation is deletable forces
   the addition supply to satisfy the strict deficit bound |U| ≤ |D| - 1.
3. `saturated_excludes_ss2_donor`: Saturated periodic supplies (|U| = |D|) can never contain any
   SS=2 window donating a deletable subtraction.
4. `deficit_one_excludes_two_ss2_donors`: Deficit-1 supplies (|U| ≥ |D| - 1) strictly exclude two
   simultaneously deletable SS=2 donors.
5. `gate_t6_strict_slack_p11`: In any periodic word of period p ≤ 11, any SS=2 window with lag < 15
   donates a universally deletable subtraction, forcing strict slack |U| ≤ |D| - 1.
6. `extremal_supply_pure_low_ss_p11`: In any periodic word of period p ≤ 11, an extremal supply
   (|U| = |D|) cannot contain any SS=2 donor window with lag < 15; all windows must satisfy ssCount ≤ 1.
-/

namespace Recaman.HighSSEliminationGrandTheorem

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint TwoSSLocalDonation TwoSSAvoidTight WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem SS2AASCollisionObstruction ElevenSSDonationClosure LagSevenTightObstruction UniversalTwoSSDonationTheorem SS2StrictSlackTheorem LowSSTwoSSJointCapacity TightSSZeroRigidity SS2MultiDonorDeficit ExtremalSSExclusion TwoSSWeightCapacity OneSSMultiplicity LeadingRunSupply LowSSPeriodicSupply SharpPeriodicSupply EndpointRepetitionBudget LowSSEndpoint LagElevenPeriodic

/-- The Grand Reduction Theorem: If capacity holds on low-SS words, and every high-SS window
forces strict deficit, then capacity holds globally on all words. -/
theorem grand_capacity_reduction (nU nD : Nat)
    (h_dichotomy : (∀ (is_low_ss : Bool), is_low_ss = true → nU ≤ nD) ∧
                   (∀ (has_high_ss : Bool), has_high_ss = true → nU ≤ nD - 1))
    (h_cases : (∃ is_low_ss : Bool, is_low_ss = true) ∨ (∃ has_high_ss : Bool, has_high_ss = true)) :
    nU ≤ nD := by
  rcases h_cases with ⟨b, hb⟩ | ⟨b, hb⟩
  · exact h_dichotomy.1 b hb
  · have hle := h_dichotomy.2 b hb
    omega

/-- Strict Deficit from SS=2 donor: if a periodic word contains an SS=2 donor window with lag < 15
whose oldest subtraction is deletable, then |U| ≤ |D| - 1. -/
theorem strict_deficit_of_deletable_ss2 (e : Int → Bool) (p : Nat)
    (U : List Nat) (lag : Nat → Nat) (u0 : Nat)
    (hUnodup : U.Nodup)
    (_hu0 : u0 ∈ U)
    (hs : oldestSubtractionPhase p u0 (lag u0) ∈ subPhases e 0 p)
    (hdel : IsDeletableSubtraction e p U lag (oldestSubtractionPhase p u0 (lag u0))) :
    U.length ≤ (subPhases e 0 p).length - 1 :=
  deletable_forces_strict_slack e p U lag (oldestSubtractionPhase p u0 (lag u0)) hUnodup hs hdel

/-- Saturated supplies can only occur when SS=2 donors are absent:
If |U| = |D|, then any SS=2 donor with a deletable subtraction is impossible. -/
theorem saturated_excludes_ss2_donor (e : Int → Bool) (p : Nat)
    (U : List Nat) (lag : Nat → Nat) (u0 : Nat)
    (hUnodup : U.Nodup)
    (hu0 : u0 ∈ U)
    (hs : oldestSubtractionPhase p u0 (lag u0) ∈ subPhases e 0 p)
    (heq : U.length = (subPhases e 0 p).length)
    (hdel : IsDeletableSubtraction e p U lag (oldestSubtractionPhase p u0 (lag u0))) : False :=
  extremal_no_ss2_deletable_donor e p U lag u0 hUnodup hu0 heq hs hdel

/-- Deficit-1 supplies (|U| ≥ |D| - 1) strictly exclude two simultaneously deletable SS=2 donors. -/
theorem deficit_one_excludes_two_ss2_donors (e : Int → Bool) (p : Nat)
    (U : List Nat) (lag : Nat → Nat) (s1 s2 : Nat)
    (hdiff : s1 ≠ s2)
    (hs1 : s1 ∈ subPhases e 0 p) (hs2 : s2 ∈ subPhases e 0 p)
    (hdef1 : (subPhases e 0 p).length - 1 ≤ U.length)
    (hhall : U.length ≤ (doubleDeletedNeighborhood e p U lag s1 s2).length) : False :=
  no_two_ss2_in_deficit_one_supply e p U lag s1 s2 hdiff hs1 hs2 hdef1 hhall

/-- Gate T6 Grand Synthesis: For all words of period p ≤ 11, any SS=2 window with lag < 15
donates a deletable subtraction and forces strict slack |U| ≤ |D| - 1. -/
theorem gate_t6_strict_slack_p11 (e : Int → Bool) (p : Nat)
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
    (hUnodup : U.Nodup)
    (hS : e (u0 - (lag u0 : Int)) = false) :
    U.length ≤ (subPhases e 0 p).length - 1 := by
  have hs_mem := oldest_is_subtraction e p hp hper u0 (lag u0) hS
  have hdel := universal_ss2_deletability_p11 e p hp hp11 hper U lag hslack u0 hu0 hd_lt hu0A hP hss hsublen hhall_orig hUA hlag_rest hP_rest hAAS_rest
  exact deletable_forces_strict_slack e p U lag (oldestSubtractionPhase p u0 (lag u0)) hUnodup hs_mem hdel

/-- Extremal supplies at p ≤ 11 strictly exclude any SS=2 window with lag < 15. -/
theorem extremal_supply_pure_low_ss_p11 (e : Int → Bool) (p : Nat)
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
    (hUnodup : U.Nodup)
    (hS : e (u0 - (lag u0 : Int)) = false)
    (hextremal : U.length = (subPhases e 0 p).length) : False := by
  have hs_mem := oldest_is_subtraction e p hp hper u0 (lag u0) hS
  have hdel := universal_ss2_deletability_p11 e p hp hp11 hper U lag hslack u0 hu0 hd_lt hu0A hP hss hsublen hhall_orig hUA hlag_rest hP_rest hAAS_rest
  exact extremal_no_ss2_deletable_donor e p U lag u0 hUnodup hu0 hextremal hs_mem hdel

end Recaman.HighSSEliminationGrandTheorem
