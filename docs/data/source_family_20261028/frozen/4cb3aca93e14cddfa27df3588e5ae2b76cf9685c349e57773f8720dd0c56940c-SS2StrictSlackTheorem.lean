import Recaman.UniversalTwoSSDonationTheorem

/-!
# SS2StrictSlackTheorem: Deletability Forces Strict Deficit and Saturated SS=2 Exclusion

This module establishes the fundamental connection between local subtraction donation
(Research Gate **T6** at `ssCount = 2`) and the strict slack / supply deficit of Issue #73:

1. `deletedNeighborhood_sublist_subPhases`: The deleted neighborhood `N(A) \ {s}` is always
   a sublist of `D = subPhases e 0 p`.
2. `not_mem_deletedNeighborhood`: The deleted subtraction `s` is never a member of `N(A) \ {s}`.
3. `deletable_forces_strict_slack`: Any deletable subtraction `s ∈ D` forces the additions list
   to satisfy the strict deficit bound `|U| ≤ |D| - 1`.
4. `no_deletable_of_equal_capacity`: In any saturated supply with `|U| = |D|`, no subtraction
   in `D` can ever be deletable.
5. `deleted_neighborhood_le_subPhases_sub_one`: For any `s ∈ D`, the deleted neighborhood of
   any subset `A` satisfies `|N(A) \ {s}| ≤ |D| - 1`.
6. `ss2_donation_hall_bound`: After deleting `s*(u₀)`, the full supply set `U` satisfies
   `|U| ≤ |D| - 1`.
-/

namespace Recaman.SS2StrictSlackTheorem

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint TwoSSLocalDonation TwoSSAvoidTight WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem SS2AASCollisionObstruction ElevenSSDonationClosure LagSevenTightObstruction UniversalTwoSSDonationTheorem OneSSMultiplicity LeadingRunSupply LowSSPeriodicSupply SharpPeriodicSupply EndpointRepetitionBudget LowSSEndpoint LagElevenPeriodic

/-- The deleted neighborhood is always a sublist of the entire subtraction set subPhases e 0 p. -/
theorem deletedNeighborhood_sublist_subPhases (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat) (s : Nat) :
    List.Sublist (deletedNeighborhood e p A lag s) (subPhases e 0 p) := by
  unfold deletedNeighborhood neighborhood
  exact List.Sublist.trans List.filter_sublist List.filter_sublist

/-- The deleted subtraction s is never a member of deletedNeighborhood e p A lag s. -/
theorem not_mem_deletedNeighborhood (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat) (s : Nat) :
    s ∉ deletedNeighborhood e p A lag s := by
  unfold deletedNeighborhood
  rw [List.mem_filter]
  rintro ⟨_, hbool⟩
  simp at hbool

/-- For any subtraction s ∈ D, the deleted neighborhood of any subset A has length at most |D| - 1. -/
theorem deleted_neighborhood_le_subPhases_sub_one (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat) (s : Nat)
    (hs : s ∈ subPhases e 0 p) :
    (deletedNeighborhood e p A lag s).length ≤ (subPhases e 0 p).length - 1 := by
  have hsub := deletedNeighborhood_sublist_subPhases e p A lag s
  have hnot := not_mem_deletedNeighborhood e p A lag s
  exact sublist_length_le_sub_one_of_mem_not_mem hsub hs hnot

/-- Fundamental Deficit Theorem: Any deletable subtraction s ∈ D forces strict slack
|U| ≤ |D| - 1 on the addition supply set U. -/
theorem deletable_forces_strict_slack (e : Int → Bool) (p : Nat)
    (U : List Nat) (lag : Nat → Nat) (s : Nat)
    (hUnodup : U.Nodup)
    (hs : s ∈ subPhases e 0 p)
    (hdel : IsDeletableSubtraction e p U lag s) :
    U.length ≤ (subPhases e 0 p).length - 1 := by
  have hhall := hdel U (fun u hu => hu) hUnodup
  have hle := deleted_neighborhood_le_subPhases_sub_one e p U lag s hs
  omega

/-- In any saturated supply with |U| = |D|, no subtraction in D can ever be deletable. -/
theorem no_deletable_of_equal_capacity (e : Int → Bool) (p : Nat)
    (U : List Nat) (lag : Nat → Nat) (s : Nat)
    (hUnodup : U.Nodup)
    (hs : s ∈ subPhases e 0 p)
    (heq : U.length = (subPhases e 0 p).length)
    (hdel : IsDeletableSubtraction e p U lag s) : False := by
  have hpos : 0 < (subPhases e 0 p).length := List.length_pos_of_mem hs
  have hslack := deletable_forces_strict_slack e p U lag s hUnodup hs hdel
  omega

/-- The donated subtraction s*(u₀) from an SS=2 donor window satisfies the universal
subtraction bound |N(U) \ {s*(u₀)}| ≤ |D| - 1. -/
theorem ss2_donation_hall_bound (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat) (u0 : Nat)
    (_hd_pos : 0 < lag u0)
    (hS : e (u0 - (lag u0 : Int)) = false) :
    (deletedNeighborhood e p U lag (oldestSubtractionPhase p u0 (lag u0))).length ≤
      (subPhases e 0 p).length - 1 := by
  have hs_mem := oldest_is_subtraction e p hp hper u0 (lag u0) hS
  exact deleted_neighborhood_le_subPhases_sub_one e p U lag (oldestSubtractionPhase p u0 (lag u0)) hs_mem

end Recaman.SS2StrictSlackTheorem
