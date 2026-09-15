import Recaman.PermanentHighToothcombBound
import Recaman.PermanentHighHistoryExhaustion
import Recaman.LagElevenPeriodic

namespace Recaman

/-! # Permanent High Blocker Capacity and Pigeonhole Exhaustion

This module formalizes the finite capacity obstruction on historical blockers
in the Recamán permanent high regime (`2n ≤ a n`):

1. **Strict Candidate Height Lower Bound**:
   For any `n ≥ 1` and `m < n`, every toothcomb candidate satisfies:
   `2n < a n + n - m`.
   In particular, `2n + 1 ≤ a n + n - m`.

2. **Small Index Exclusion**:
   Historical values at small indices (`a 0 = 0`, `a 1 = 1`) are strictly
   below `2n + 1`. Consequently:
   `j = 0` and `j = 1` can NEVER block ANY toothcomb candidate `m < n`!

3. **Pigeonhole Capacity Obstruction**:
   The list of `n` distinct toothcomb candidates `[c(0), ..., c(n-1)]` has
   length `n` and no duplicates (`Nodup`).
   If all `n` candidates were blocked by history `j < n`, their blockers
   would have to come from `{1, ..., n-1}`, a set of size `n - 1`.
   By the Pigeonhole Principle (`List.Nodup.length_le_of_subset`),
   `n ≤ n - 1`, which is an immediate contradiction!

4. **Existence of Unblocked Toothcomb Candidate**:
   For every `n ≥ 1` in the high regime `2n ≤ a n`, there exists at least one
   toothcomb step `m < n` whose candidate is completely unblocked by history:
   `∀ j < n, a j ≠ a n + n - m`.
   Furthermore, this candidate avoids `valuesThrough (n - 1)`, avoids `a n`,
   and avoids all toothcomb additions and prior subtractions.
-/

/-! ### Part 1: Candidate Height Lower Bounds and Small Index Exclusion -/

/-- For any n ≥ 1, m < n, and 2n ≤ a n, the toothcomb candidate strictly exceeds 2n. -/
theorem toothcomb_candidate_gt_two_n
    {n m : Nat} (hm : m < n) (hn_high : 2 * n ≤ a n) :
    2 * n < a n + n - m := by
  omega

/-- The toothcomb candidate cannot equal 0 when 1 ≤ n and 2n ≤ a n. -/
theorem toothcomb_candidate_pos
    {n m : Nat} (hm : m < n) (hn_high : 2 * n ≤ a n) :
    0 < a n + n - m := by
  omega

/-- Base value at step 0 is 0. -/
theorem a_zero_eq_zero : a 0 = 0 := rfl

/-- For n ≥ 1 and m < n, the candidate cannot be blocked by index 0. -/
theorem toothcomb_candidate_ne_a_zero
    {n m : Nat} (hm : m < n) (hn_high : 2 * n ≤ a n) :
    a 0 ≠ a n + n - m := by
  have : a 0 = 0 := rfl
  omega

/-- Historical blocker index can never be 0. -/
theorem toothcomb_blocker_ne_zero
    {n m j : Nat} (hm : m < n) (hn_high : 2 * n ≤ a n)
    (hblock : a j = a n + n - m) :
    j ≠ 0 := by
  intro hj
  rw [hj, a_zero_eq_zero] at hblock
  have hpos := toothcomb_candidate_pos hm hn_high
  omega

/-- Base value at step 1 is 1. -/
theorem a_one_eq_one : a 1 = 1 := rfl

/-- For n ≥ 1 and m < n, the candidate cannot be blocked by index 1. -/
theorem toothcomb_candidate_ne_a_one
    {n m : Nat} (hn : 1 ≤ n) (hm : m < n) (hn_high : 2 * n ≤ a n) :
    a 1 ≠ a n + n - m := by
  have : a 1 = 1 := rfl
  have : 1 ≤ n := hn
  omega

/-- Historical blocker index can never be 1 for n ≥ 1. -/
theorem toothcomb_blocker_ne_one
    {n m j : Nat} (hn : 1 ≤ n) (hm : m < n) (hn_high : 2 * n ≤ a n)
    (hblock : a j = a n + n - m) :
    j ≠ 1 := by
  intro hj
  rw [hj] at hblock
  exact toothcomb_candidate_ne_a_one hn hm hn_high hblock

/-! ### Part 2: List Formulations and Pigeonhole Impossibility -/

/-- The list of toothcomb candidates for m < n has length n. -/
theorem toothcomb_candidates_length (n : Nat) (an : Nat) :
    ((List.range n).map (fun m => an + n - m)).length = n := by
  simp

/-- The list of toothcomb candidates for m < n has no duplicates. -/
theorem toothcomb_candidates_nodup (n : Nat) (an : Nat) :
    ((List.range n).map (fun m => an + n - m)).Nodup := by
  refine LagElevenPeriodic.nodup_map_of_inj List.nodup_range ?_
  intro x y hx hy heq
  rw [List.mem_range] at hx hy
  omega

/-- Candidate list membership characterization. -/
theorem mem_toothcomb_candidates_iff {n an x : Nat} :
    x ∈ (List.range n).map (fun m => an + n - m) ↔
    ∃ m, m < n ∧ x = an + n - m := by
  simp only [List.mem_map, List.mem_range]
  constructor
  · intro ⟨m, hm, hx⟩
    exact ⟨m, hm, hx.symm⟩
  · intro ⟨m, hm, hx⟩
    exact ⟨m, hm, hx.symm⟩

/-- Historical non-zero values list has length n - 1. -/
theorem historical_nonzero_values_length (n : Nat) :
    ((List.range (n - 1)).map (fun i => a (i + 1))).length = n - 1 := by
  simp

/-- Blocker capacity impossibility:
It is mathematically impossible for all n toothcomb candidates to be
blocked by history j < n. -/
theorem toothcomb_not_all_blocked_by_history
    {n : Nat} (hn : 1 ≤ n) (hn_high : 2 * n ≤ a n)
    (h_all_blocked : ∀ m, m < n → ∃ j, j < n ∧ a j = a n + n - m) :
    False := by
  let cand_list := (List.range n).map (fun m => a n + n - m)
  let hist_list := (List.range (n - 1)).map (fun i => a (i + 1))
  have hsubset : cand_list ⊆ hist_list := by
    intro x hx
    rcases mem_toothcomb_candidates_iff.mp hx with ⟨m, hm, hx_eq⟩
    rcases h_all_blocked m hm with ⟨j, hj, hj_eq⟩
    have hj_ne : j ≠ 0 := toothcomb_blocker_ne_zero hm hn_high hj_eq
    have hj_lt : j - 1 < n - 1 := by omega
    rw [List.mem_map]
    refine ⟨j - 1, List.mem_range.mpr hj_lt, ?_⟩
    have : j - 1 + 1 = j := by omega
    rw [this, hj_eq, ← hx_eq]
  have hnodup := toothcomb_candidates_nodup n (a n)
  have hle := List.Nodup.length_le_of_subset hnodup hsubset
  have hlen1 : cand_list.length = n := toothcomb_candidates_length n (a n)
  have hlen2 : hist_list.length = n - 1 := historical_nonzero_values_length n
  rw [hlen1, hlen2] at hle
  omega

/-! ### Part 3: Existence and Isolation of Unblocked Candidate -/

/-- Existence of unblocked toothcomb candidate:
For any n ≥ 1 in the high regime 2n ≤ a n, there exists at least one
toothcomb step m < n whose candidate is completely unblocked by history j < n! -/
theorem toothcomb_exists_unblocked_candidate
    {n : Nat} (hn : 1 ≤ n) (hn_high : 2 * n ≤ a n) :
    ∃ m, m < n ∧ ∀ j, j < n → a j ≠ a n + n - m := by
  classical
  by_cases h : ∃ m, m < n ∧ ∀ j, j < n → a j ≠ a n + n - m
  · exact h
  · exfalso
    apply toothcomb_not_all_blocked_by_history hn hn_high
    intro m hm
    by_cases hex : ∃ j, j < n ∧ a j = a n + n - m
    · exact hex
    · exfalso
      apply h
      refine ⟨m, hm, ?_⟩
      intro j hj heq
      exact hex ⟨j, hj, heq⟩

/-- The unblocked toothcomb candidate strictly avoids all valuesThrough (n - 1). -/
theorem toothcomb_unblocked_candidate_avoids_valuesThrough
    {n m : Nat} (hn : 1 ≤ n) (hm : m < n)
    (hunblock : ∀ j, j < n → a j ≠ a n + n - m) :
    a n + n - m ∉ valuesThrough (n - 1) := by
  intro hmem
  rcases mem_valuesThrough_iff.mp hmem with ⟨j, hj, hval⟩
  have hj_lt : j < n := by omega
  exact hunblock j hj_lt hval

/-- The toothcomb candidate for m < n strictly exceeds the base value a n. -/
theorem toothcomb_candidate_gt_base
    {n m : Nat} (hm : m < n) :
    a n < a n + n - m := by
  omega

/-- The toothcomb candidate for m < n cannot equal the base value a n. -/
theorem toothcomb_candidate_ne_base
    {n m : Nat} (hm : m < n) :
    a n ≠ a n + n - m := by
  omega

/-- The unblocked toothcomb candidate strictly avoids all prior toothcomb subtractions. -/
theorem toothcomb_unblocked_candidate_avoids_prior_subtractions
    {n m i : Nat} (hi : i < m) (hm : m < n) :
    a n + n - m ≠ a n + n - i := by
  omega

/-- The unblocked toothcomb candidate strictly avoids all toothcomb additions. -/
theorem toothcomb_unblocked_candidate_avoids_additions
    {n m k : Nat} (hm : m < n) :
    a n + n - m ≠ a n + 2 * n + 4 + k := by
  omega

/-! ### Part 4: Grand Blocker Capacity Synthesis -/

/-- Grand Blocker Capacity Synthesis:
1. Every toothcomb candidate m < n satisfies 2n < a n + n - m.
2. Historical values at j = 0 and j = 1 can never block any candidate m < n.
3. The n candidates cannot all be blocked by the n - 1 available historical indices.
4. There strictly exists an unblocked step m < n avoiding all valuesThrough (n - 1).
5. The unblocked candidate strictly exceeds the base value a n, avoids all prior
   subtractions, and avoids all toothcomb additions. -/
theorem grand_permanent_high_blocker_capacity_synthesis
    {n : Nat} (hn : 1 ≤ n) (hn_high : 2 * n ≤ a n) :
    (∀ m, m < n → 2 * n < a n + n - m) ∧
    (∀ m j, m < n → a j = a n + n - m → j ≠ 0 ∧ j ≠ 1) ∧
    ((∀ m, m < n → ∃ j, j < n ∧ a j = a n + n - m) → False) ∧
    (∃ m, m < n ∧
       (∀ j, j < n → a j ≠ a n + n - m) ∧
       a n + n - m ∉ valuesThrough (n - 1) ∧
       a n < a n + n - m ∧
       (∀ i, i < m → a n + n - m ≠ a n + n - i) ∧
       (∀ k, a n + n - m ≠ a n + 2 * n + 4 + k)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m hm
    exact toothcomb_candidate_gt_two_n hm hn_high
  · intro m j hm hblock
    have hj0 := toothcomb_blocker_ne_zero hm hn_high hblock
    have hj1 := toothcomb_blocker_ne_one hn hm hn_high hblock
    exact ⟨hj0, hj1⟩
  · intro h_all
    exact toothcomb_not_all_blocked_by_history hn hn_high h_all
  · rcases toothcomb_exists_unblocked_candidate hn hn_high with ⟨m, hm, hunblock⟩
    have havoid := toothcomb_unblocked_candidate_avoids_valuesThrough hn hm hunblock
    have hgt := toothcomb_candidate_gt_base hm
    have hprior : ∀ i, i < m → a n + n - m ≠ a n + n - i := fun i hi =>
      toothcomb_unblocked_candidate_avoids_prior_subtractions hi hm
    have hadd : ∀ k, a n + n - m ≠ a n + 2 * n + 4 + k := fun k =>
      toothcomb_unblocked_candidate_avoids_additions hm
    exact ⟨m, hm, hunblock, havoid, hgt, hprior, hadd⟩

end Recaman
