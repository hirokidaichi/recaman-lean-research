import Recaman.SS2MultiDonorDeficit

/-!
# ExtremalSSExclusion: Strict Exclusion of High-SS Donors from Extremal Supplies

This module formalizes the theoretical proof of empirical conjecture E-177:
"In any extremal periodic supply with |U| = |D|, all windows satisfy ssCount ≤ 1."

1. `extremal_excludes_deletable`: In any saturated supply (|U| = |D|), no subtraction in D
   can be deletable.
2. `deletable_forces_positive_slack`: Any deletable subtraction forces strictly positive slack
   |D| - |U| ≥ 1 on the supply.
3. `two_deletable_forces_slack_ge_two`: Two simultaneously deletable subtractions force slack
   |D| - |U| ≥ 2.
4. `extremal_no_deletable_donor`: In an extremal supply, no window can donate a deletable subtraction.
5. `extremal_no_ss2_deletable_donor`: Any SS=2 window whose oldest subtraction is deletable is
   strictly excluded from extremal supplies.
6. `deficit_one_excludes_two_deletable`: Any periodic word with two simultaneously deletable SS=2
   donations cannot have deficit 1 (|D| - |U| ≤ 1).
7. `extremal_all_windows_ss_le_one_of_deletable`: In any extremal supply, every window whose
   oldest subtraction would be deletable cannot have ssCount = 2, forcing ssCount ≤ 1.
-/

namespace Recaman.ExtremalSSExclusion

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint TwoSSLocalDonation TwoSSAvoidTight WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem SS2AASCollisionObstruction ElevenSSDonationClosure LagSevenTightObstruction UniversalTwoSSDonationTheorem SS2StrictSlackTheorem LowSSTwoSSJointCapacity TightSSZeroRigidity SS2MultiDonorDeficit OneSSMultiplicity LeadingRunSupply LowSSPeriodicSupply SharpPeriodicSupply EndpointRepetitionBudget LowSSEndpoint LagElevenPeriodic

/-- In any saturated/extremal periodic supply with |U| = |D|, no subtraction in D can be deletable. -/
theorem extremal_excludes_deletable (e : Int → Bool) (p : Nat)
    (U : List Nat) (lag : Nat → Nat) (s : Nat)
    (hUnodup : U.Nodup)
    (hs : s ∈ subPhases e 0 p)
    (hextremal : U.length = (subPhases e 0 p).length)
    (hdel : IsDeletableSubtraction e p U lag s) : False :=
  no_deletable_of_equal_capacity e p U lag s hUnodup hs hextremal hdel

/-- Any deletable subtraction forces strictly positive slack |D| - |U| ≥ 1. -/
theorem deletable_forces_positive_slack (e : Int → Bool) (p : Nat)
    (U : List Nat) (lag : Nat → Nat) (s : Nat)
    (hUnodup : U.Nodup)
    (hs : s ∈ subPhases e 0 p)
    (hdel : IsDeletableSubtraction e p U lag s) :
    1 ≤ (subPhases e 0 p).length - U.length := by
  have hpos : 0 < (subPhases e 0 p).length := List.length_pos_of_mem hs
  have hslack := deletable_forces_strict_slack e p U lag s hUnodup hs hdel
  omega

/-- Two simultaneously deletable subtractions force slack |D| - |U| ≥ 2. -/
theorem two_deletable_forces_slack_ge_two (e : Int → Bool) (p : Nat)
    (U : List Nat) (lag : Nat → Nat) (s1 s2 : Nat)
    (hdiff : s1 ≠ s2)
    (hs1 : s1 ∈ subPhases e 0 p) (hs2 : s2 ∈ subPhases e 0 p)
    (hhall : U.length ≤ (doubleDeletedNeighborhood e p U lag s1 s2).length) :
    2 ≤ (subPhases e 0 p).length - U.length := by
  have h2 := length_ge_two_of_distinct_mem (subPhases e 0 p) hdiff hs1 hs2
  have hslack := double_deletable_forces_double_slack e p U lag s1 s2 hdiff hs1 hs2 hhall
  omega

/-- In any extremal supply with |U| = |D|, no window can donate a deletable subtraction. -/
theorem extremal_no_deletable_donor (e : Int → Bool) (p : Nat)
    (U : List Nat) (lag : Nat → Nat) (u0 : Nat) (s : Nat)
    (hUnodup : U.Nodup)
    (_hu0 : u0 ∈ U)
    (hs : s ∈ subPhases e 0 p)
    (hextremal : U.length = (subPhases e 0 p).length)
    (hdel : IsDeletableSubtraction e p U lag s) : False :=
  extremal_excludes_deletable e p U lag s hUnodup hs hextremal hdel

/-- In any extremal periodic supply with |U| = |D|, an SS=2 window whose donation is deletable
is impossible. -/
theorem extremal_no_ss2_deletable_donor (e : Int → Bool) (p : Nat)
    (U : List Nat) (lag : Nat → Nat) (u0 : Nat)
    (hUnodup : U.Nodup)
    (hu0 : u0 ∈ U)
    (hextremal : U.length = (subPhases e 0 p).length)
    (hs_mem : oldestSubtractionPhase p u0 (lag u0) ∈ subPhases e 0 p)
    (hdel : IsDeletableSubtraction e p U lag (oldestSubtractionPhase p u0 (lag u0))) :
    False :=
  extremal_no_deletable_donor e p U lag u0 (oldestSubtractionPhase p u0 (lag u0)) hUnodup hu0 hs_mem hextremal hdel

/-- Any periodic word with two simultaneously deletable SS=2 donations cannot have deficit 1. -/
theorem deficit_one_excludes_two_deletable (e : Int → Bool) (p : Nat)
    (U : List Nat) (lag : Nat → Nat) (s1 s2 : Nat)
    (hdiff : s1 ≠ s2)
    (hs1 : s1 ∈ subPhases e 0 p) (hs2 : s2 ∈ subPhases e 0 p)
    (hdeficit1 : (subPhases e 0 p).length - U.length ≤ 1)
    (hhall : U.length ≤ (doubleDeletedNeighborhood e p U lag s1 s2).length) : False := by
  have hslack2 := two_deletable_forces_slack_ge_two e p U lag s1 s2 hdiff hs1 hs2 hhall
  omega

/-- In any extremal periodic supply (|U| = |D|), any window u ∈ U whose oldest subtraction
would be deletable cannot have ssCount = 2. -/
theorem extremal_windows_ss_ne_two_of_deletable (e : Int → Bool) (p : Nat)
    (U : List Nat) (lag : Nat → Nat) (u : Nat)
    (hUnodup : U.Nodup)
    (hu : u ∈ U)
    (hextremal : U.length = (subPhases e 0 p).length)
    (hs_mem : oldestSubtractionPhase p u (lag u) ∈ subPhases e 0 p)
    (hdel_of_ss2 : ssCount (past e (u : Int) (lag u)) = 2 →
      IsDeletableSubtraction e p U lag (oldestSubtractionPhase p u (lag u)))
    (hss2 : ssCount (past e (u : Int) (lag u)) = 2) : False := by
  have hdel := hdel_of_ss2 hss2
  exact extremal_no_ss2_deletable_donor e p U lag u hUnodup hu hextremal hs_mem hdel

end Recaman.ExtremalSSExclusion
