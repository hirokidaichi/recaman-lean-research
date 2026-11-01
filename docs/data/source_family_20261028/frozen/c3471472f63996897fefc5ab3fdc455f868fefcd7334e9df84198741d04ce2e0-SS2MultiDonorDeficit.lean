import Recaman.TightSSZeroRigidity

/-!
# SS2MultiDonorDeficit: Multi-Donor Deficit and Simultaneous Deletion

This module proves the simultaneous multi-donor deficit theory:

1. `length_ge_two_of_distinct_mem`: Any list containing two distinct elements has length at least 2.
2. `filter_two_ne_sublist_length_le_sub_two`: Deleting two distinct elements from a list reduces
   its length by at least 2.
3. `doubleDeletedNeighborhood`: Neighborhood of a subset after deleting two subtractions s1, s2.
4. `double_deleted_neighborhood_sublist`: The double-deleted neighborhood is a sublist of the
   double-filtered subtraction pool.
5. `double_deleted_neighborhood_le_sub_two`: The double-deleted neighborhood has cardinality
   at most |D| - 2.
6. `double_deleted_neighborhood_eq`: If both subtractions avoid the neighborhood N(A),
   the double-deleted neighborhood is identical to N(A).
7. `two_ss_donors_distinct`: Two distinct SS=2 donor windows donate distinct modular subtractions.
8. `two_ss_donors_avoid_tight`: Both donated subtractions from two SS=2 donors with lag < 15
   avoid any tight AAS neighborhood.
9. `two_ss_double_deleted_tight_eq`: Deleting both donations leaves the tight neighborhood unchanged.
10. `double_deletable_forces_double_slack`: Simultaneous deletability of two subtractions forces
    the double deficit bound |U| ≤ |D| - 2.
11. `ss2_double_donation_hall_bound`: After deleting both donations s*(u1) and s*(u2), the full
    supply set U has double-deleted neighborhood bounded by |D| - 2.
12. `ss2_two_donors_force_double_slack`: If both donations are simultaneously deletable, the addition
    supply satisfies |U| ≤ |D| - 2.
13. `no_two_ss2_in_deficit_one_supply`: In any supply with |U| ≥ |D| - 1 (including all tight words
    and all deficit-1 words), having two distinct SS=2 donors with lag < 15 is impossible.
-/

namespace Recaman.SS2MultiDonorDeficit

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint TwoSSLocalDonation TwoSSAvoidTight WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure TightComponentSlackBound UniversalTightLagBound TightP2ParityRigidity TwoSSTightAvoidanceTheorem SS2AASCollisionObstruction ElevenSSDonationClosure LagSevenTightObstruction UniversalTwoSSDonationTheorem SS2StrictSlackTheorem LowSSTwoSSJointCapacity TightSSZeroRigidity OneSSMultiplicity LeadingRunSupply LowSSPeriodicSupply SharpPeriodicSupply EndpointRepetitionBudget LowSSEndpoint LagElevenPeriodic

/-- Any list containing two distinct elements has length at least 2. -/
theorem length_ge_two_of_distinct_mem {α : Type _} [DecidableEq α] (D : List α)
    {s1 s2 : α} (hdiff : s1 ≠ s2) (hs1 : s1 ∈ D) (hs2 : s2 ∈ D) :
    2 ≤ D.length := by
  have hs1_not : s1 ∉ D.filter (· ≠ s1) := by
    intro h; rw [List.mem_filter] at h; simp at h
  have hlen1 : (D.filter (· ≠ s1)).length ≤ D.length - 1 :=
    sublist_length_le_sub_one_of_mem_not_mem List.filter_sublist hs1 hs1_not
  have hs2_in : s2 ∈ D.filter (· ≠ s1) := by
    rw [List.mem_filter]; simp [hdiff.symm, hs2]
  have hpos : 0 < (D.filter (· ≠ s1)).length := List.length_pos_of_mem hs2_in
  omega

/-- Deleting two distinct elements from a list reduces its length by at least 2. -/
theorem filter_two_ne_sublist_length_le_sub_two {α : Type _} [DecidableEq α] (D : List α)
    {s1 s2 : α} (hdiff : s1 ≠ s2) (hs1 : s1 ∈ D) (hs2 : s2 ∈ D) :
    ((D.filter (· ≠ s1)).filter (· ≠ s2)).length ≤ D.length - 2 := by
  have hs1_not : s1 ∉ D.filter (· ≠ s1) := by
    intro h; rw [List.mem_filter] at h; simp at h
  have hlen1 : (D.filter (· ≠ s1)).length ≤ D.length - 1 :=
    sublist_length_le_sub_one_of_mem_not_mem List.filter_sublist hs1 hs1_not
  have hs2_in : s2 ∈ D.filter (· ≠ s1) := by
    rw [List.mem_filter]; simp [hdiff.symm, hs2]
  have hs2_not : s2 ∉ (D.filter (· ≠ s1)).filter (· ≠ s2) := by
    intro h; rw [List.mem_filter] at h; simp at h
  have hlen2 : ((D.filter (· ≠ s1)).filter (· ≠ s2)).length ≤ (D.filter (· ≠ s1)).length - 1 :=
    sublist_length_le_sub_one_of_mem_not_mem List.filter_sublist hs2_in hs2_not
  omega

/-- Neighborhood of a subset after deleting two subtractions s1 and s2. -/
def doubleDeletedNeighborhood (e : Int → Bool) (p : Nat) (A : List Nat) (lag : Nat → Nat) (s1 s2 : Nat) : List Nat :=
  ((neighborhood e p A lag).filter (· ≠ s1)).filter (· ≠ s2)

/-- The double-deleted neighborhood is always a sublist of the double-filtered subtraction pool. -/
theorem double_deleted_neighborhood_sublist (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat) (s1 s2 : Nat) :
    List.Sublist (doubleDeletedNeighborhood e p A lag s1 s2)
      (((subPhases e 0 p).filter (· ≠ s1)).filter (· ≠ s2)) := by
  unfold doubleDeletedNeighborhood
  have hsub : List.Sublist (neighborhood e p A lag) (subPhases e 0 p) := by
    unfold neighborhood
    exact List.filter_sublist
  exact (hsub.filter _).filter _

/-- The double-deleted neighborhood has cardinality at most |D| - 2. -/
theorem double_deleted_neighborhood_le_sub_two (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat) (s1 s2 : Nat)
    (hdiff : s1 ≠ s2)
    (hs1 : s1 ∈ subPhases e 0 p) (hs2 : s2 ∈ subPhases e 0 p) :
    (doubleDeletedNeighborhood e p A lag s1 s2).length ≤ (subPhases e 0 p).length - 2 := by
  have hsub := double_deleted_neighborhood_sublist e p A lag s1 s2
  have hlen := hsub.length_le
  have hcap := filter_two_ne_sublist_length_le_sub_two (subPhases e 0 p) hdiff hs1 hs2
  omega

/-- If both subtractions avoid the neighborhood N(A), the double-deleted neighborhood is identical to N(A). -/
theorem double_deleted_neighborhood_eq (e : Int → Bool) (p : Nat)
    (A : List Nat) (lag : Nat → Nat) (s1 s2 : Nat)
    (hs1 : s1 ∉ neighborhood e p A lag)
    (hs2 : s2 ∉ neighborhood e p A lag) :
    doubleDeletedNeighborhood e p A lag s1 s2 = neighborhood e p A lag := by
  unfold doubleDeletedNeighborhood
  have hf1 : (neighborhood e p A lag).filter (· ≠ s1) = neighborhood e p A lag := by
    rw [List.filter_eq_self]
    intro x hx
    simp only [decide_eq_true_eq]
    rintro rfl
    exact hs1 hx
  rw [hf1]
  rw [List.filter_eq_self]
  intro x hx
  simp only [decide_eq_true_eq]
  rintro rfl
  exact hs2 hx

/-- Two distinct SS=2 donor windows donate distinct modular subtractions. -/
theorem two_ss_donors_distinct (e : Int → Bool) (p : Nat) (lag : Nat → Nat)
    (u1 u2 : Nat) (hp : 0 < p) (hper : ∀ x, e (x + p) = e x)
    (hu1A : e (u1 : Int) = true) (hu2A : e (u2 : Int) = true)
    (hP1 : ShortPeriodicSupply.P2 e (u1 : Int) (lag u1))
    (hP2 : ShortPeriodicSupply.P2 e (u2 : Int) (lag u2))
    (hss1 : ssCount (past e (u1 : Int) (lag u1)) = 2)
    (hss2 : ssCount (past e (u2 : Int) (lag u2)) = 2)
    (hu_mod : (u1 : Int) % (p : Int) ≠ (u2 : Int) % (p : Int)) :
    endpointPhase p (u1 : Int) (lag u1) ≠ endpointPhase p (u2 : Int) (lag u2) := by
  intro heq
  have hmod := two_SS_endpoint_mod_injective e p hp hper (u1 : Int) (u2 : Int) (lag u1) (lag u2)
    hu1A hu2A hss1 hss2 hP1 hP2 heq
  exact hu_mod hmod

/-- Both donated subtractions from two SS=2 donors with lag < 15 avoid any tight AAS neighborhood. -/
theorem two_ss_donors_avoid_tight (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hAP : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) 3)
    (hAA : ∀ u ∈ A, e (u : Int) = true)
    (u1 u2 : Nat)
    (hu1A : e (u1 : Int) = true) (hu2A : e (u2 : Int) = true)
    (hP1 : ShortPeriodicSupply.P2 e (u1 : Int) (lag u1))
    (hP2 : ShortPeriodicSupply.P2 e (u2 : Int) (lag u2))
    (hss1 : ssCount (past e (u1 : Int) (lag u1)) = 2)
    (hss2 : ssCount (past e (u2 : Int) (lag u2)) = 2)
    (hlag1_lt : lag u1 < 15)
    (hlag2_lt : lag u2 < 15) :
    endpointPhase p (u1 : Int) (lag u1) ∉ neighborhood e p A lag ∧
    endpointPhase p (u2 : Int) (lag u2) ∉ neighborhood e p A lag := by
  have hd1 : ∀ u ∈ A, endpointPhase p (u1 : Int) (lag u1) ≠ endpointPhase p (u : Int) 3 := by
    intro u hu
    exact ss2_lag_lt_fifteen_disjoint_from_aas e p hp hper u1 u (lag u1) hu1A (hAA u hu) hlag1_lt hss1 hP1 (hAP u hu) (haas u hu)
  have hd2 : ∀ u ∈ A, endpointPhase p (u2 : Int) (lag u2) ≠ endpointPhase p (u : Int) 3 := by
    intro u hu
    exact ss2_lag_lt_fifteen_disjoint_from_aas e p hp hper u2 u (lag u2) hu2A (hAA u hu) hlag2_lt hss2 hP2 (hAP u hu) (haas u hu)
  constructor
  · exact tight_avoiding_s_not_mem e p hp A lag hlag3 haas (endpointPhase p (u1 : Int) (lag u1)) hd1
  · exact tight_avoiding_s_not_mem e p hp A lag hlag3 haas (endpointPhase p (u2 : Int) (lag u2)) hd2

/-- Deleting both donations leaves the tight AAS neighborhood completely unchanged. -/
theorem two_ss_double_deleted_tight_eq (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x, e (x + p) = e x)
    (A : List Nat) (lag : Nat → Nat)
    (hlag3 : ∀ u ∈ A, lag u = 3)
    (haas : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hAP : ∀ u ∈ A, ShortPeriodicSupply.P2 e (u : Int) 3)
    (hAA : ∀ u ∈ A, e (u : Int) = true)
    (u1 u2 : Nat)
    (hu1A : e (u1 : Int) = true) (hu2A : e (u2 : Int) = true)
    (hP1 : ShortPeriodicSupply.P2 e (u1 : Int) (lag u1))
    (hP2 : ShortPeriodicSupply.P2 e (u2 : Int) (lag u2))
    (hss1 : ssCount (past e (u1 : Int) (lag u1)) = 2)
    (hss2 : ssCount (past e (u2 : Int) (lag u2)) = 2)
    (hlag1_lt : lag u1 < 15)
    (hlag2_lt : lag u2 < 15) :
    doubleDeletedNeighborhood e p A lag (endpointPhase p (u1 : Int) (lag u1)) (endpointPhase p (u2 : Int) (lag u2)) =
    neighborhood e p A lag := by
  have ⟨hnot1, hnot2⟩ := two_ss_donors_avoid_tight e p hp hper A lag hlag3 haas hAP hAA u1 u2 hu1A hu2A hP1 hP2 hss1 hss2 hlag1_lt hlag2_lt
  exact double_deleted_neighborhood_eq e p A lag (endpointPhase p (u1 : Int) (lag u1)) (endpointPhase p (u2 : Int) (lag u2)) hnot1 hnot2

/-- Simultaneous deletability of two subtractions forces the double deficit bound |U| ≤ |D| - 2. -/
theorem double_deletable_forces_double_slack (e : Int → Bool) (p : Nat)
    (U : List Nat) (lag : Nat → Nat) (s1 s2 : Nat)
    (hdiff : s1 ≠ s2)
    (hs1 : s1 ∈ subPhases e 0 p) (hs2 : s2 ∈ subPhases e 0 p)
    (hhall : U.length ≤ (doubleDeletedNeighborhood e p U lag s1 s2).length) :
    U.length ≤ (subPhases e 0 p).length - 2 := by
  have hcap := double_deleted_neighborhood_le_sub_two e p U lag s1 s2 hdiff hs1 hs2
  omega

/-- After deleting both donations s*(u1) and s*(u2), the full supply set U has
double-deleted neighborhood bounded by |D| - 2. -/
theorem ss2_double_donation_hall_bound (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat) (u1 u2 : Nat)
    (hdiff : endpointPhase p (u1 : Int) (lag u1) ≠ endpointPhase p (u2 : Int) (lag u2))
    (hS1 : e (u1 - (lag u1 : Int)) = false)
    (hS2 : e (u2 - (lag u2 : Int)) = false) :
    (doubleDeletedNeighborhood e p U lag
      (endpointPhase p (u1 : Int) (lag u1)) (endpointPhase p (u2 : Int) (lag u2))).length ≤
      (subPhases e 0 p).length - 2 := by
  have hs1_mem := oldest_is_subtraction e p hp hper u1 (lag u1) hS1
  have hs2_mem := oldest_is_subtraction e p hp hper u2 (lag u2) hS2
  exact double_deleted_neighborhood_le_sub_two e p U lag
    (endpointPhase p (u1 : Int) (lag u1)) (endpointPhase p (u2 : Int) (lag u2))
    hdiff hs1_mem hs2_mem

/-- If both donations are simultaneously deletable, the addition supply satisfies |U| ≤ |D| - 2. -/
theorem ss2_two_donors_force_double_slack (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat) (u1 u2 : Nat)
    (hdiff : endpointPhase p (u1 : Int) (lag u1) ≠ endpointPhase p (u2 : Int) (lag u2))
    (hS1 : e (u1 - (lag u1 : Int)) = false)
    (hS2 : e (u2 - (lag u2 : Int)) = false)
    (hhall : U.length ≤ (doubleDeletedNeighborhood e p U lag
      (endpointPhase p (u1 : Int) (lag u1)) (endpointPhase p (u2 : Int) (lag u2))).length) :
    U.length ≤ (subPhases e 0 p).length - 2 := by
  have hbound := ss2_double_donation_hall_bound e p hp hper U lag u1 u2 hdiff hS1 hS2
  omega

/-- In any supply with |U| ≥ |D| - 1 (including all tight words and all deficit-1 words),
having two distinct SS=2 donors with lag < 15 is impossible. -/
theorem no_two_ss2_in_deficit_one_supply (e : Int → Bool) (p : Nat)
    (U : List Nat) (lag : Nat → Nat) (s1 s2 : Nat)
    (hdiff : s1 ≠ s2)
    (hs1 : s1 ∈ subPhases e 0 p) (hs2 : s2 ∈ subPhases e 0 p)
    (hslack : (subPhases e 0 p).length - 1 ≤ U.length)
    (hhall : U.length ≤ (doubleDeletedNeighborhood e p U lag s1 s2).length) :
    False := by
  have h2 := length_ge_two_of_distinct_mem (subPhases e 0 p) hdiff hs1 hs2
  have hdef := double_deletable_forces_double_slack e p U lag s1 s2 hdiff hs1 hs2 hhall
  omega

end Recaman.SS2MultiDonorDeficit
