import Recaman.ExtremalSSExclusion

/-!
# TwoSSWeightCapacity: Two-Weight SS=2 Capacity and the Deficit Hierarchy

This module formalizes the Two-Weight SS=2 Capacity Principle and the Deficit Hierarchy:

1. `ss2_weight_inequality`: The fundamental weight inequality n0 + 2*n2 ≤ nD implies
   both n0 + n2 ≤ nD - n2 and n2 ≤ nD - (n0 + n2).
2. `extremal_forces_ss2_zero`: In any extremal supply (n0 + n2 = nD), n2 = 0.
3. `deficit_one_forces_ss2_le_one`: In any deficit-1 supply (nD - 1 ≤ n0 + n2), n2 ≤ 1.
4. `deficit_two_forces_ss2_le_two`: In any deficit-2 supply (nD - 2 ≤ n0 + n2), n2 ≤ 2.
5. `deficit_k_forces_ss2_le_k`: For any deficit k, n2 ≤ k.
6. `two_ss_slack_ge_count`: In any periodic word where additions partition into low-SS and
   SS=2 windows satisfying the double-weight capacity, the supply slack is at least |U2|.
7. `two_ss_extremal_count_zero`: Saturated periodic supplies (|U| = |D|) have |U2| = 0.
8. `two_ss_deficit_one_count_le_one`: Deficit-1 supplies have at most one SS=2 window (|U2| ≤ 1).
9. `two_ss_deficit_two_count_le_two`: Deficit-2 supplies have at most two SS=2 windows (|U2| ≤ 2).
10. `single_ss2_donor_slack`: A single deletable SS=2 donor forces slack |D| - |U| ≥ 1.
11. `two_ss2_donors_slack`: Two simultaneously deletable SS=2 donors force slack |D| - |U| ≥ 2.
-/

namespace Recaman.TwoSSWeightCapacity

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint TwoSSLocalDonation TwoSSAvoidTight WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem SS2AASCollisionObstruction ElevenSSDonationClosure LagSevenTightObstruction UniversalTwoSSDonationTheorem SS2StrictSlackTheorem LowSSTwoSSJointCapacity TightSSZeroRigidity SS2MultiDonorDeficit ExtremalSSExclusion OneSSMultiplicity LeadingRunSupply LowSSPeriodicSupply SharpPeriodicSupply EndpointRepetitionBudget LowSSEndpoint LagElevenPeriodic

/-- The fundamental double-weight inequality n0 + 2*n2 ≤ nD implies n0 + n2 ≤ nD - n2
and n2 ≤ nD - (n0 + n2). -/
theorem ss2_weight_inequality (n0 n2 nD : Nat) (h : n0 + 2 * n2 ≤ nD) :
    n0 + n2 ≤ nD - n2 ∧ nD - (n0 + n2) ≥ n2 ∧ n2 ≤ nD - (n0 + n2) := by
  omega

/-- In any extremal supply (n0 + n2 = nD), n2 = 0. -/
theorem extremal_forces_ss2_zero (n0 n2 nD : Nat) (h : n0 + 2 * n2 ≤ nD) (heq : n0 + n2 = nD) :
    n2 = 0 := by
  omega

/-- In any deficit-1 supply (nD - 1 ≤ n0 + n2), n2 ≤ 1. -/
theorem deficit_one_forces_ss2_le_one (n0 n2 nD : Nat) (h : n0 + 2 * n2 ≤ nD) (hdef : nD - 1 ≤ n0 + n2) :
    n2 ≤ 1 := by
  omega

/-- In any deficit-2 supply (nD - 2 ≤ n0 + n2), n2 ≤ 2. -/
theorem deficit_two_forces_ss2_le_two (n0 n2 nD : Nat) (h : n0 + 2 * n2 ≤ nD) (hdef : nD - 2 ≤ n0 + n2) :
    n2 ≤ 2 := by
  omega

/-- In any deficit-k supply (nD - k ≤ n0 + n2), n2 ≤ k. -/
theorem deficit_k_forces_ss2_le_k (n0 n2 nD k : Nat) (h : n0 + 2 * n2 ≤ nD) (hdef : nD - k ≤ n0 + n2) :
    n2 ≤ k := by
  omega

/-- In any periodic word where additions partition into low-SS and SS=2 windows satisfying
the double-weight capacity, the supply slack is at least |U2|. -/
theorem two_ss_slack_ge_count (e : Int → Bool) (p : Nat)
    (U U_le1 U2 : List Nat)
    (_hpartition : U.length = U_le1.length + U2.length)
    (hweight : U_le1.length + 2 * U2.length ≤ (subPhases e 0 p).length) :
    U2.length ≤ (subPhases e 0 p).length - U.length := by
  omega

/-- Saturated periodic supplies (|U| = |D|) have |U2| = 0 under double-weight capacity. -/
theorem two_ss_extremal_count_zero (e : Int → Bool) (p : Nat)
    (U U_le1 U2 : List Nat)
    (_hpartition : U.length = U_le1.length + U2.length)
    (hweight : U_le1.length + 2 * U2.length ≤ (subPhases e 0 p).length)
    (hextremal : U.length = (subPhases e 0 p).length) :
    U2.length = 0 := by
  omega

/-- Deficit-1 supplies have at most one SS=2 window (|U2| ≤ 1). -/
theorem two_ss_deficit_one_count_le_one (e : Int → Bool) (p : Nat)
    (U U_le1 U2 : List Nat)
    (_hpartition : U.length = U_le1.length + U2.length)
    (hweight : U_le1.length + 2 * U2.length ≤ (subPhases e 0 p).length)
    (hdef1 : (subPhases e 0 p).length - 1 ≤ U.length) :
    U2.length ≤ 1 := by
  omega

/-- Deficit-2 supplies have at most two SS=2 windows (|U2| ≤ 2). -/
theorem two_ss_deficit_two_count_le_two (e : Int → Bool) (p : Nat)
    (U U_le1 U2 : List Nat)
    (_hpartition : U.length = U_le1.length + U2.length)
    (hweight : U_le1.length + 2 * U2.length ≤ (subPhases e 0 p).length)
    (hdef2 : (subPhases e 0 p).length - 2 ≤ U.length) :
    U2.length ≤ 2 := by
  omega

/-- A single deletable SS=2 donor forces slack |D| - |U| ≥ 1. -/
theorem single_ss2_donor_slack (e : Int → Bool) (p : Nat)
    (U : List Nat) (lag : Nat → Nat) (s : Nat)
    (hUnodup : U.Nodup)
    (hs : s ∈ subPhases e 0 p)
    (hdel : IsDeletableSubtraction e p U lag s) :
    1 ≤ (subPhases e 0 p).length - U.length :=
  deletable_forces_positive_slack e p U lag s hUnodup hs hdel

/-- Two simultaneously deletable SS=2 donors force slack |D| - |U| ≥ 2. -/
theorem two_ss2_donors_slack (e : Int → Bool) (p : Nat)
    (U : List Nat) (lag : Nat → Nat) (s1 s2 : Nat)
    (hdiff : s1 ≠ s2)
    (hs1 : s1 ∈ subPhases e 0 p) (hs2 : s2 ∈ subPhases e 0 p)
    (hhall : U.length ≤ (doubleDeletedNeighborhood e p U lag s1 s2).length) :
    2 ≤ (subPhases e 0 p).length - U.length :=
  two_deletable_forces_slack_ge_two e p U lag s1 s2 hdiff hs1 hs2 hhall

end Recaman.TwoSSWeightCapacity
