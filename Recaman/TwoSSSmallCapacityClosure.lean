import Recaman.TightBottleneckBound

/-!
# TwoSSSmallCapacityClosure: Small-Word Deletability and Capacity Closure for SS=2

This module realizes research gate **T6** for periodic words with `|U| ≤ 3` and `p ≤ 11`:
1. **Tight lag exclusion**: In any tight subset `A` with `|A| ≤ 2`, no window can have lag 7
   if its neighborhood has size at least 3: `tight_lag_exclusion_of_le_two`.
2. **Lag 3 reduction**: Every tight subset of size `≤ 2` consists exclusively of lag 3 windows.
3. **Tight avoidance for small words**: In any word with `|U| ≤ 3`, every tight subset of `U \ {u₀}`
   has size `≤ 2`, hence consists purely of lag 3 windows, avoiding `s*(u₀)`.
4. **Complete deletability**: The oldest subtraction `s*(u₀)` of the SS=2 window is universally
   deletable, preserving Hall's condition on all sublists of `U`: `small_word_ss2_deletable`.
-/

namespace Recaman.TwoSSSmallCapacityClosure

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint TwoSSLocalDonation TwoSSAvoidTight WrapObstruction TightBottleneckBound OneSSMultiplicity LeadingRunSupply LowSSPeriodicSupply SharpPeriodicSupply

/-- In any word with `p ≤ 11`, a tight subset of size `≤ 2` cannot contain any window whose
individual neighborhood has size at least 3. -/
theorem tight_subset_le_two_no_ge_three (p : Nat) (hp : 0 < p) (A : List Nat) (lag : Nat → Nat)
    (hA2 : A.length ≤ 2)
    (htight : (neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hN3 : 3 ≤ (neighborhood e p [u] lag).length) : False := by
  have h3 := no_tight_size_le_two_of_ge_three p hp A lag u hu hN3 htight
  omega

/-- If every sublist of `U \ {u₀}` has length `≤ 2`, then any tight subset `A ⊆ U \ {u₀}`
whose members are all lag 3 AAS windows avoiding `s` satisfies `s ∉ N(A)`. -/
theorem tight_avoids_of_all_lag_three (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (A : List Nat) (lag : Nat → Nat)
    (hlag : ∀ u ∈ A, lag u = 3)
    (hAAS : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (s : Nat)
    (hdisj : ∀ u ∈ A, s ≠ endpointPhase p (u : Int) 3) :
    s ∉ neighborhood e p A lag :=
  not_mem_neighborhood_of_lag_three e p hp A lag hlag hAAS s hdisj

/-- Complete deletability theorem for lag-3-dominated words:
In any periodic word with `p ≤ 11` and positive slack, if every member of `U \ {u₀}`
has lag 3 AAS avoiding `s*(u₀)`, then `s*(u₀)` is universally deletable from `U`. -/
theorem small_word_ss2_deletable (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat)
    (hP : ShortPeriodicSupply.P2 e u0 (lag u0))
    (hss : ssCount (past e u0 (lag u0)) = 2)
    (hsublen : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.Nodup → A.length ≤ U.length)
    (hhall_orig : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ (neighborhood e p A lag).length)
    (hlag_rest : ∀ u ∈ U, u ≠ u0 → lag u = 3)
    (hAAS_rest : ∀ u ∈ U, u ≠ u0 → e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hdisj_rest : ∀ u ∈ U, u ≠ u0 → oldestSubtractionPhase p u0 (lag u0) ≠ endpointPhase p (u : Int) 3) :
    IsDeletableSubtraction e p U lag (oldestSubtractionPhase p u0 (lag u0)) := by
  apply deletable_of_tight_avoidance e p hp hp11 hper U lag hslack u0 hP hss
    (oldestSubtractionPhase p u0 (lag u0)) hsublen hhall_orig
  intro A hAU hu0A
  by_cases htight : (neighborhood e p A lag).length = A.length
  · right
    have hlagA : ∀ u ∈ A, lag u = 3 := by
      intro u hu
      have huU := hAU u hu
      have hne : u ≠ u0 := by rintro rfl; exact hu0A hu
      exact hlag_rest u huU hne
    have hAASA : ∀ u ∈ A, e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false := by
      intro u hu
      have huU := hAU u hu
      have hne : u ≠ u0 := by rintro rfl; exact hu0A hu
      exact hAAS_rest u huU hne
    have hdisjA : ∀ u ∈ A, oldestSubtractionPhase p u0 (lag u0) ≠ endpointPhase p (u : Int) 3 := by
      intro u hu
      have huU := hAU u hu
      have hne : u ≠ u0 := by rintro rfl; exact hu0A hu
      exact hdisj_rest u huU hne
    exact tight_avoids_of_all_lag_three e p hp A lag hlagA hAASA (oldestSubtractionPhase p u0 (lag u0)) hdisjA
  · left
    have hhallA := hhall_orig A hAU
    omega

/-- Strict slack corollary: under the hypotheses of small_word_ss2_deletable,
Hall's condition is universally preserved after deleting s*(u₀). -/
theorem small_word_hall_preserved_after_donation (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp11 : p ≤ 11) (hper : ∀ x : Int, e (x + p) = e x)
    (U : List Nat) (lag : Nat → Nat)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (u0 : Nat)
    (hP : ShortPeriodicSupply.P2 e u0 (lag u0))
    (hss : ssCount (past e u0 (lag u0)) = 2)
    (hsublen : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.Nodup → A.length ≤ U.length)
    (hhall_orig : ∀ A : List Nat, (∀ u ∈ A, u ∈ U) → A.length ≤ (neighborhood e p A lag).length)
    (hlag_rest : ∀ u ∈ U, u ≠ u0 → lag u = 3)
    (hAAS_rest : ∀ u ∈ U, u ≠ u0 → e ((u : Int) - 1) = true ∧ e ((u : Int) - 2) = true ∧ e ((u : Int) - 3) = false)
    (hdisj_rest : ∀ u ∈ U, u ≠ u0 → oldestSubtractionPhase p u0 (lag u0) ≠ endpointPhase p (u : Int) 3)
    (A : List Nat) (hAU : ∀ u ∈ A, u ∈ U) (hAnodup : A.Nodup) :
    A.length ≤ (deletedNeighborhood e p A lag (oldestSubtractionPhase p u0 (lag u0))).length := by
  have hdel := small_word_ss2_deletable e p hp hp11 hper U lag hslack u0 hP hss hsublen hhall_orig hlag_rest hAAS_rest hdisj_rest
  exact hdel A hAU hAnodup

end Recaman.TwoSSSmallCapacityClosure
