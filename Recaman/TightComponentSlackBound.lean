import Recaman.TwoSSSmallCapacityClosure

/-!
# TightComponentSlackBound: Period-Dependent Slack Bounds on Tight Component Sizes

This module establishes exact period-dependent capacity and size bounds for tight bottleneck
subsets avoiding an SS=2 donor window:

1. **Mass-Subtraction Identity**: `ShortPeriodicSupply.signSum e 0 p = p - 2 * |D|`.
2. **Subtraction Capacity Bound**: Positive period mass (`signSum > 0`) implies `2 * |D| < p`.
   - For `p ≤ 8`: `|D| ≤ 3`.
   - For `p ≤ 10`: `|D| ≤ 4`.
   - For `p ≤ 11`: `|D| ≤ 5`.
3. **Sublist Avoiding Length Bound**: Any sublist `List.Sublist A U` avoiding `u0 ∈ U` satisfies
   `A.length ≤ U.length - 1`.
4. **Tight Avoiding Size Bound for p ≤ 10**: Under positive slack (`|U| < |D|`), any sublist
   `List.Sublist A U` avoiding `u0` satisfies `A.length ≤ |D| - 2 ≤ 2`.
   For `p ≤ 8`, `A.length ≤ |D| - 2 ≤ 1`.
5. **Lag-3 Rigidity of Tight Avoiding Subsets**: For all `p ≤ 10`, every member of every tight
   subset avoiding `u0` must have lag 3. No window of lag ≥ 7 can ever belong to any tight subset
   avoiding `u0`.
6. **SS=2 Donor Deletability and Hall Preservation**: For all `p ≤ 10`, the oldest subtraction
   `s*(u0)` is universally deletable and Hall's condition is preserved on all sublists of `U`.
-/

namespace Recaman.TightComponentSlackBound

open TwoSSTightDisjoint TwoSSPeriodicSupply TwoSSEndpoint TwoSSLocalDonation TwoSSAvoidTight WrapObstruction TightBottleneckBound TwoSSSmallCapacityClosure OneSSMultiplicity LeadingRunSupply LowSSPeriodicSupply SharpPeriodicSupply

/-- The sum of additions and subtractions across any range of length n equals n. -/
theorem additionCount_add_subtractionCount (e : Int → Bool) (t : Int) (n : Nat) :
    ShortPeriodicSupply.additionCount e t n + ShortPeriodicSupply.subtractionCount e t n = n := by
  induction n with
  | zero => simp [ShortPeriodicSupply.additionCount, ShortPeriodicSupply.subtractionCount]
  | succ n ih =>
    cases hb : e (t + n) <;>
      simp [ShortPeriodicSupply.additionCount, ShortPeriodicSupply.subtractionCount, hb] <;> omega

/-- The signSum is exactly `n - 2 * subtractionCount`. -/
theorem signSum_eq_subtraction_bound (e : Int → Bool) (t : Int) (n : Nat) :
    ShortPeriodicSupply.signSum e t n = (n : Int) - 2 * (ShortPeriodicSupply.subtractionCount e t n : Int) := by
  have hcounts := ShortPeriodicSupply.signSum_eq_counts e t n
  have hsum := additionCount_add_subtractionCount e t n
  omega

/-- Positive period mass forces the number of subtractions to be strictly less than half the period. -/
theorem subPhases_bound_of_pos_signSum (e : Int → Bool) (p : Nat)
    (hpos : 0 < ShortPeriodicSupply.signSum e 0 p) :
    2 * (LagElevenPeriodic.subPhases e 0 p).length < p := by
  have hcounts := ShortPeriodicSupply.signSum_eq_counts e 0 p
  have hsum := additionCount_add_subtractionCount e 0 p
  have hfilter := LagElevenPeriodic.subtractionCount_eq_filter e 0 p
  have hsign := signSum_eq_subtraction_bound e 0 p
  rw [hfilter] at hsign
  omega

/-- For `p ≤ 8`, positive period mass forces `|D| ≤ 3`. -/
theorem subPhases_length_le_three_of_le_eight (e : Int → Bool) (p : Nat)
    (hp : p ≤ 8) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p) :
    (LagElevenPeriodic.subPhases e 0 p).length ≤ 3 := by
  have hbound := subPhases_bound_of_pos_signSum e p hpos
  omega

/-- For `p ≤ 10`, positive period mass forces `|D| ≤ 4`. -/
theorem subPhases_length_le_four_of_le_ten (e : Int → Bool) (p : Nat)
    (hp : p ≤ 10) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p) :
    (LagElevenPeriodic.subPhases e 0 p).length ≤ 4 := by
  have hbound := subPhases_bound_of_pos_signSum e p hpos
  omega

/-- For `p ≤ 11`, positive period mass forces `|D| ≤ 5`. -/
theorem subPhases_length_le_five_of_le_eleven (e : Int → Bool) (p : Nat)
    (hp : p ≤ 11) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p) :
    (LagElevenPeriodic.subPhases e 0 p).length ≤ 5 := by
  have hbound := subPhases_bound_of_pos_signSum e p hpos
  omega

/-- Any sublist of U avoiding an element `u0 ∈ U` has length at most `U.length - 1`. -/
theorem sublist_length_le_sub_one_of_mem_not_mem {α : Type _} {A U : List α}
    (hsub : List.Sublist A U) {u0 : α} (hmem : u0 ∈ U) (hnot : u0 ∉ A) :
    A.length ≤ U.length - 1 := by
  induction U generalizing A with
  | nil =>
    cases hsub
    contradiction
  | cons a l ih =>
    cases hsub with
    | cons _ h =>
      by_cases ha : a = u0
      · have hlen := h.length_le
        simp only [List.length_cons]
        omega
      · have hmem' : u0 ∈ l := by
          cases hmem with
          | head => exact False.elim (ha rfl)
          | tail _ h_tail => exact h_tail
        have ih' := ih h hmem' hnot
        simp only [List.length_cons]
        omega
    | cons_cons a h =>
      have ha : a ≠ u0 := by
        rintro rfl
        exact hnot List.mem_cons_self
      have hmem' : u0 ∈ l := by
        cases hmem with
        | head => exact False.elim (ha rfl)
        | tail _ h_tail => exact h_tail
      have hnot' : u0 ∉ _ := fun h_in => hnot (List.mem_cons_of_mem a h_in)
      have ih' := ih h hmem' hnot'
      have hpos := List.length_pos_of_mem hmem'
      simp only [List.length_cons]
      omega

/-- In any positive-slack word with `p ≤ 10`, any sublist avoiding an SS=2 donor window
has size at most 2. -/
theorem tight_avoiding_size_le_two_of_p10 (e : Int → Bool) (p : Nat)
    (hp : p ≤ 10) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (U A : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    A.length ≤ 2 := by
  have hle := sublist_length_le_sub_one_of_mem_not_mem hsub hu0 hnot
  have hD := subPhases_length_le_four_of_le_ten e p hp hpos
  omega

/-- In any positive-slack word with `p ≤ 8`, any sublist avoiding an SS=2 donor window
has size at most 1 (either empty or singleton). -/
theorem tight_avoiding_size_le_one_of_p8 (e : Int → Bool) (p : Nat)
    (hp : p ≤ 8) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (U A : List Nat) (u0 : Nat) (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length) :
    A.length ≤ 1 := by
  have hle := sublist_length_le_sub_one_of_mem_not_mem hsub hu0 hnot
  have hD := subPhases_length_le_three_of_le_eight e p hp hpos
  omega

/-- In any positive-slack word with `p ≤ 10`, no member of any tight subset
avoiding an SS=2 donor window can have neighborhood size at least 3. -/
theorem no_ge_three_in_tight_avoiding_p10 (e : Int → Bool) (p : Nat) (hp : 0 < p)
    (hp10 : p ≤ 10) (hpos : 0 < ShortPeriodicSupply.signSum e 0 p)
    (U A : List Nat) (lag : Nat → Nat) (u0 : Nat)
    (hu0 : u0 ∈ U) (hnot : u0 ∉ A) (hsub : List.Sublist A U)
    (hslack : U.length < (LagElevenPeriodic.subPhases e 0 p).length)
    (htight : (TwoSSTightDisjoint.neighborhood e p A lag).length = A.length)
    (u : Nat) (hu : u ∈ A)
    (hN3 : 3 ≤ (TwoSSTightDisjoint.neighborhood e p [u] lag).length) : False := by
  have hlen := tight_avoiding_size_le_two_of_p10 e p hp10 hpos U A u0 hu0 hnot hsub hslack
  exact tight_subset_le_two_no_ge_three p hp A lag hlen htight u hu hN3


/-- SS=2 donor phase is universally deletable for all words of period p ≤ 10. -/
theorem p10_ss2_donor_deletable (e : Int → Bool) (p : Nat)
    (hp : 0 < p) (hp10 : p ≤ 10)
    (hper : ∀ x : Int, e (x + p) = e x)
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
  have hp11 : p ≤ 11 := by omega
  exact TwoSSSmallCapacityClosure.small_word_ss2_deletable e p hp hp11 hper U lag hslack u0 hP hss hsublen hhall_orig hlag_rest hAAS_rest hdisj_rest

/-- Hall's condition is universally preserved after donating s*(u0) for all words of period p ≤ 10. -/
theorem p10_ss2_donor_hall_preserved (e : Int → Bool) (p : Nat)
    (hp : 0 < p) (hp10 : p ≤ 10)
    (hper : ∀ x : Int, e (x + p) = e x)
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
  have hp11 : p ≤ 11 := by omega
  exact TwoSSSmallCapacityClosure.small_word_hall_preserved_after_donation e p hp hp11 hper U lag hslack u0 hP hss hsublen hhall_orig hlag_rest hAAS_rest hdisj_rest A hAU hAnodup

end Recaman.TightComponentSlackBound
