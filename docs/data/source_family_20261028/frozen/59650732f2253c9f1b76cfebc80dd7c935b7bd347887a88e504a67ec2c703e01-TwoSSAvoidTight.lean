import Recaman.TwoSSLocalDonation

/-!
# TwoSSAvoidTight: Tight Subset Avoidance and Hall Preservation

This module establishes the general tight-subset avoidance mechanism for research gate **T6**:
1. **Neighborhood preservation without s**: If `s ∉ N(A)`, then deleting `s` does not change `N(A)`
   at all: `deletedNeighborhood_eq_of_not_mem`.
2. **Slack preservation**: If `|A| < |N(A)|`, deleting any element leaves `|A| ≤ |N(A) \ {s}|`:
   `deleted_hall_of_slack`.
3. **Tight avoidance criterion**: If every subset `A ⊆ U \ {u₀}` either has strict slack
   `|A| < |N(A)|` or avoids `s` (`s ∉ N(A)`), then Hall's condition is universally preserved
   on all subsets avoiding `u₀`: `hall_preserved_of_slack_or_avoid`.
4. **Deletability under tight avoidance**: Under `p ≤ 11` and positive slack, any subtraction `s`
   satisfying the tight avoidance criterion on `U \ {u₀}` is universally deletable:
   `deletable_of_tight_avoidance`.
-/

namespace Recaman.TwoSSAvoidTight

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint TwoSSLocalDonation OneSSMultiplicity LeadingRunSupply LowSSPeriodicSupply SharpPeriodicSupply

/-- The neighborhood is nodup because it is a sublist of `subPhases`. -/
theorem neighborhood_nodup (e : Int → Bool) (p : Nat) (A : List Nat) (lag : Nat → Nat) :
    (neighborhood e p A lag).Nodup :=
  List.Nodup.sublist List.filter_sublist (subPhases_nodup e p)

/-- Membership in the neighborhood is equivalent to being in `subPhases` and covered by `A`. -/
theorem mem_neighborhood_iff (e : Int → Bool) (p : Nat) (A : List Nat) (lag : Nat → Nat) (s : Nat) :
    s ∈ neighborhood e p A lag ↔ s ∈ LagElevenPeriodic.subPhases e 0 p ∧ isCoveredBySubset e p A lag s = true := by
  unfold neighborhood
  exact List.mem_filter

/-- If `s` is not covered by `A`, it is not in the neighborhood of `A`. -/
theorem not_mem_neighborhood_of_not_covered (e : Int → Bool) (p : Nat) (A : List Nat) (lag : Nat → Nat) (s : Nat)
    (hnot : isCoveredBySubset e p A lag s = false) :
    s ∉ neighborhood e p A lag := by
  rw [mem_neighborhood_iff]
  intro ⟨_, hcov⟩
  rw [hnot] at hcov
  contradiction

/-- If `s ∉ N(A)`, then deleting `s` leaves the neighborhood completely unchanged. -/
theorem deletedNeighborhood_eq_of_not_mem (e : Int → Bool) (p : Nat) (A : List Nat) (lag : Nat → Nat) (s : Nat)
    (hnot : s ∉ neighborhood e p A lag) :
    deletedNeighborhood e p A lag s = neighborhood e p A lag := by
  unfold deletedNeighborhood
  apply filter_all_true
  intro y hy
  have hne : y ≠ s := by
    rintro rfl
    exact hnot hy
  simp [hne]

/-- If `|A| < |N(A)|`, deleting any element leaves `|A| ≤ |N(A) \ {s}|`. -/
theorem deleted_hall_of_slack (e : Int → Bool) (p : Nat) (A : List Nat) (lag : Nat → Nat) (s : Nat)
    (hslack : A.length < (neighborhood e p A lag).length) :
    A.length ≤ (deletedNeighborhood e p A lag s).length := by
  unfold deletedNeighborhood
  have hfilt := filter_ne_nodup (neighborhood_nodup e p A lag) s
  omega

/-- If `s ∉ N(A)` and `|A| ≤ |N(A)|`, then `|A| ≤ |N(A) \ {s}|`. -/
theorem deleted_hall_of_not_mem (e : Int → Bool) (p : Nat) (A : List Nat) (lag : Nat → Nat) (s : Nat)
    (hnot : s ∉ neighborhood e p A lag)
    (hhall : A.length ≤ (neighborhood e p A lag).length) :
    A.length ≤ (deletedNeighborhood e p A lag s).length := by
  rw [deletedNeighborhood_eq_of_not_mem e p A lag s hnot]
  exact hhall

/-- If every subset `A` either has strict slack or avoids `s`, Hall's condition is preserved. -/
theorem hall_preserved_of_slack_or_avoid (e : Int → Bool) (p : Nat) (A : List Nat) (lag : Nat → Nat) (s : Nat)
    (hhall : A.length ≤ (neighborhood e p A lag).length)
    (hcase : A.length < (neighborhood e p A lag).length ∨ s ∉ neighborhood e p A lag) :
    A.length ≤ (deletedNeighborhood e p A lag s).length := by
  rcases hcase with hslack | hnot
  · exact deleted_hall_of_slack e p A lag s hslack
  · exact deleted_hall_of_not_mem e p A lag s hnot hhall

/-- Universal deletability under tight avoidance:
If `p ≤ 11`, `|U| < |D|`, and every sublist `A ⊆ U \ {u₀}` satisfies either strict slack
or avoids `s`, then `s` is deletable from `U`. -/
theorem deletable_of_tight_avoidance (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat)
    (hP : ShortPeriodicSupply.P2 e u0 (lag u0))
    (hss : ssCount (past e u0 (lag u0)) = 2)
    (s : Nat)
    (hsublen : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.Nodup → A.length ≤ U.length)
    (hhall_orig : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ (neighborhood e p A lag).length)
    (havoid : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → u0 ∉ A →
      A.length < (neighborhood e p A lag).length ∨ s ∉ neighborhood e p A lag) :
    IsDeletableSubtraction e p U lag s := by
  apply deletable_of_avoids_ss2 e p hp hp11 hper U lag hslack u0 hP hss s _ hsublen
  intro A hAU hu0A
  have hhallA := hhall_orig A hAU
  have hcaseA := havoid A hAU hu0A
  exact hall_preserved_of_slack_or_avoid e p A lag s hhallA hcaseA

/-- A window of lag 3 whose past is `AAS` (i.e. `e(t-1)=A, e(t-2)=A, e(t-3)=S`)
covers EXACTLY one subtraction phase: its endpoint phase `endpointPhase p t 3`. -/
theorem lag_three_covers_iff (e : Int → Bool) (p : Nat) (hp : 0 < p) (t : Int)
    (hA1 : e (t - 1) = true) (hA2 : e (t - 2) = true) (hS3 : e (t - 3) = false) (s : Nat) :
    WindowCoversSubtraction e p t 3 s ↔ s = endpointPhase p t 3 := by
  unfold WindowCoversSubtraction endpointPhase phase
  constructor
  · rintro ⟨i, hi, hfalse, hmod⟩
    have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi_cases with rfl | rfl | rfl
    · have : t - 1 - ((0 : Nat) : Int) = t - 1 := by omega
      rw [this] at hfalse
      rw [hA1] at hfalse
      contradiction
    · have : t - 1 - ((1 : Nat) : Int) = t - 2 := by omega
      rw [this] at hfalse
      rw [hA2] at hfalse
      contradiction
    · have h2 : t - 1 - ((2 : Nat) : Int) = (t - (3 : Int)) := by omega
      have h3 : (t - ((3 : Nat) : Int)) = (t - (3 : Int)) := by omega
      rw [h2] at hmod
      rw [h3]
      rw [hmod]
      simp
  · rintro rfl
    refine ⟨2, by omega, ?_, ?_⟩
    · have : t - 1 - ((2 : Nat) : Int) = t - 3 := by omega
      rw [this]; exact hS3
    · have : t - 1 - ((2 : Nat) : Int) = t - 3 := by omega
      rw [this]
      have hnn : 0 ≤ (t - 3) % (p : Int) := Int.emod_nonneg (t - 3) (by omega)
      exact (Int.toNat_of_nonneg hnn).symm

/-- For a subset A of additions all having lag 3 AAS windows,
a subtraction phase s is covered by A iff s is the endpoint phase of some u ∈ A. -/
theorem lag_three_subset_covers_iff (e : Int → Bool) (p : Nat) (hp : 0 < p) (A : List Nat) (lag : Nat → Nat)
    (hlag : ∀ u ∈ A, lag u = 3)
    (hAAS : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (s : Nat) :
    isCoveredBySubset e p A lag s = true ↔ ∃ u ∈ A, s = endpointPhase p (u : Int) 3 := by
  rw [isCoveredBySubset_iff]
  constructor
  · rintro ⟨u, hu, hcov⟩
    rw [hlag u hu] at hcov
    have hspec := (lag_three_covers_iff e p hp (u : Int) (hAAS u hu).1 (hAAS u hu).2.1 (hAAS u hu).2.2 s).mp hcov
    exact ⟨u, hu, hspec⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    rw [hlag u hu]
    exact (lag_three_covers_iff e p hp (u : Int) (hAAS u hu).1 (hAAS u hu).2.1 (hAAS u hu).2.2 _).mpr rfl

/-- If s is disjoint from the endpoint phases of all lag 3 AAS windows in A,
then s is not in the neighborhood of A. -/
theorem not_mem_neighborhood_of_lag_three (e : Int → Bool) (p : Nat) (hp : 0 < p) (A : List Nat) (lag : Nat → Nat)
    (hlag : ∀ u ∈ A, lag u = 3)
    (hAAS : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (s : Nat)
    (hdisj : ∀ u ∈ A, s ≠ endpointPhase p (u : Int) 3) :
    s ∉ neighborhood e p A lag := by
  intro hmem
  rw [mem_neighborhood_iff] at hmem
  have hcov := (lag_three_subset_covers_iff e p hp A lag hlag hAAS s).mp hmem.2
  obtain ⟨u, hu, rfl⟩ := hcov
  exact hdisj u hu rfl

/-- If all elements of a tight subset A have lag 3 AAS windows, and the SS=2 window u0's
donated subtraction s*(u0) is disjoint from all their endpoint phases,
then deleting s*(u0) preserves Hall's condition on A. -/
theorem oldest_donation_preserves_hall_on_lag_three_tight (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (A : List Nat) (lag : Nat → Nat)
    (hlag : ∀ u ∈ A, lag u = 3)
    (hAAS : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (u0 : Nat)
    (hdisj : ∀ u ∈ A, oldestSubtractionPhase p u0 (lag u0) ≠ endpointPhase p (u : Int) 3)
    (hhall : A.length ≤ (neighborhood e p A lag).length) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hnot := not_mem_neighborhood_of_lag_three e p hp A lag hlag hAAS (oldestSubtractionPhase p u0 (lag u0)) hdisj
  exact deleted_hall_of_not_mem e p A lag (oldestSubtractionPhase p u0 (lag u0)) hnot hhall

end Recaman.TwoSSAvoidTight

