import Recaman.CanonicalStepSpectrum
import Recaman.SubtractionLedger

namespace Recaman.CanonicalPathInvariants

open Recaman Recaman.CanonicalGapCapacity Recaman.CanonicalStepSpectrum
open Classical

/-! # Global clock-0 ledger, parity-partition, cut-connectivity, and multi-point cluster invariants

Beyond the 12 static local-metric, step-spectrum, consecutive-degree, and first-moment
invariants of `E-778`/`E-781`/`E-790` (which `E-791` proved cannot narrow `E-759` finite-word
languages statically), the actual clock-0 canonical Recamán trajectory `Recaman.Basic.a`
obeys four global structural laws established unconditionally below:

1. **Top-triangular subtraction complement & unconditional quadratic distinct-seen lower bound**:
   - `subSum_add_upperTri_complement_le`: `subSum b + upperTri (b - subCount b) ≤ upperTri b`
     (strictly sharpening `SubtractionLedger.subSum_le_mul_subCount`, sharp at `b = 4`).
   - `subCount_succ_le_cover_length`: every cover `V` of `valuesThrough b` satisfies
     `subCount b + 1 ≤ V.length` (every subtraction lands on a strictly unseen value, plus `a 0 = 0`).
   - `canonical_distinct_cover_quadratic_bound`:
     `2 * upperTri (b + 1 - V.length) ≤ upperTri b + a b`, forcing
     `|V| ≥ (1 - 1 / √2) * b` whenever `a b = o(b^2)` with no corridor hypotheses.
2. **Exact mod-4 parity-partition capacity**:
   - `canonical_even_visit_count_le` and `canonical_odd_visit_count_le`: every `Nodup` list of
     even (resp. odd) visited values in `valuesThrough b` has length at most `evenClockCount b`
     (resp. `oddClockCount b`), sharp at `b = 10` (`5/5` evens, `6/6` odds).
3. **Global cut-crossing connectivity**:
   - `canonical_cut_crossing_step`: every cut `S : Nat → Prop` separating `0` from some
     `v ∈ valuesThrough b` is crossed by a step `1 ≤ t ≤ b` with `stepDist (a (t - 1)) (a t) = t`.
4. **Interior cluster entry-exit span and disjoint multi-point cluster clock budget**:
   - `canonical_interior_cluster_entry_exit_span`: every interior cluster `S` (`¬ S 0`, `¬ S (a b)`)
     containing a nonempty `Nodup` list `L ⊆ valuesThrough b` with boundary distance `≥ θ`
     admits entry/exit clocks `1 ≤ t₁ < t₂ ≤ b` with `θ ≤ t₁`, `θ ≤ t₂`, and `θ + L.length ≤ b`.
   - `canonical_disjoint_clusters_clock_budget`: every list `Cs : List (List Nat)` of nonempty
     `Nodup` interior clusters in `valuesThrough b` with boundary distance `≥ θ` and mutual
     distance `> b` satisfies `Cs.length + (Cs.map List.length).sum ≤ b + 1 - θ`, strictly
     unifying and generalizing both `E-781` single-tail capacity and `E-790` isolated-vertex
     `2 * m ≤ b + 1 - θ` to arbitrary multi-point clusters.
-/

/-! ## Definitions and basic distance/list helpers -/

/-- Symmetric absolute distance between two natural numbers. -/
def stepDist (u v : Nat) : Nat :=
  if u ≤ v then v - u else u - v

/-- Number of clocks `t ∈ {0, ..., b}` congruent to `0` or `3` mod `4` (even-value clocks). -/
def evenClockCount (b : Nat) : Nat :=
  ((List.range (b + 1)).filter (fun t => t % 4 == 0 || t % 4 == 3)).length

/-- Number of clocks `t ∈ {0, ..., b}` congruent to `1` or `2` mod `4` (odd-value clocks). -/
def oddClockCount (b : Nat) : Nat :=
  ((List.range (b + 1)).filter (fun t => t % 4 == 1 || t % 4 == 2)).length

private theorem stepDist_self (u : Nat) : stepDist u u = 0 := by
  unfold stepDist
  simp

private theorem stepDist_symm (u v : Nat) : stepDist u v = stepDist v u := by
  unfold stepDist
  split <;> split <;> omega

private theorem stepDist_at (t : Nat) : stepDist (a t) (a (t + 1)) = t + 1 := by
  have hrec := recurrence t
  unfold stepDist
  by_cases hcan : CanSubtract (t + 1) (stateAt t)
  · rw [if_pos hcan] at hrec
    have hlt : t + 1 < a t := hcan.1
    rw [hrec]
    rw [if_neg (by omega)]
    omega
  · rw [if_neg hcan] at hrec
    rw [hrec, if_pos (by omega)]
    omega

private theorem a_zero_eq : a 0 = 0 := by
  simp [a, stateAt, initial]

private theorem nodup_length_le_of_subset :
    ∀ {α : Type} [DecidableEq α] {L M : List α}, L.Nodup → (∀ x ∈ L, x ∈ M) → L.length ≤ M.length
  | _, _, [], _, _, _ => Nat.zero_le _
  | α, _, x :: xs, M, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have hxM : x ∈ M := hsub x (List.mem_cons_self ..)
    have hsub' : ∀ y ∈ xs, y ∈ M.erase x := by
      intro y hy
      have hyx : y ≠ x := fun h => hnd.1 (h ▸ hy)
      exact (List.mem_erase_of_ne hyx).mpr (hsub y (List.mem_cons_of_mem x hy))
    have ih := nodup_length_le_of_subset hnd.2 hsub'
    have herase : (M.erase x).length + 1 = M.length := by
      have hlen := List.length_erase_of_mem hxM
      have hpos : 0 < M.length := List.length_pos_of_mem hxM
      omega
    simp only [List.length_cons]
    omega

private theorem nodup_map_of_inj {α β : Type} (L : List α) (f : α → β)
    (hnd : L.Nodup) (hinj : ∀ x ∈ L, ∀ y ∈ L, f x = f y → x = y) :
    (L.map f).Nodup := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hnd.2 (fun a ha b hb h =>
      hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb) h)⟩
    intro hmem
    obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hmem
    have heq := hinj y (List.mem_cons_of_mem x hy) x (List.mem_cons_self ..) hfy
    exact hnd.1 (heq ▸ hy)

private theorem nodup_sum_append {α β : Type} (L₁ : List α) (L₂ : List β)
    (h₁ : L₁.Nodup) (h₂ : L₂.Nodup) :
    (L₁.map Sum.inl ++ L₂.map Sum.inr).Nodup := by
  rw [List.nodup_append]
  refine ⟨nodup_map_of_inj L₁ Sum.inl h₁ (fun _ _ _ _ h => by cases h; rfl),
    nodup_map_of_inj L₂ Sum.inr h₂ (fun _ _ _ _ h => by cases h; rfl), ?_⟩
  intro x hx y hy hxy
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hy
  cases hxy

private theorem first_witness (P : Nat → Prop) :
    ∀ k, (∃ t, t ≤ k ∧ P t) → ∃ t, t ≤ k ∧ P t ∧ ∀ j, j < t → ¬ P j
  | 0, ⟨t, ht, hPt⟩ => by
    have : t = 0 := by omega
    subst this
    exact ⟨0, Nat.le_refl 0, hPt, fun j hj => by omega⟩
  | k + 1, h => by
    by_cases hprev : ∃ t, t ≤ k ∧ P t
    · obtain ⟨t, htk, hPt, hmin⟩ := first_witness P k hprev
      exact ⟨t, by omega, hPt, hmin⟩
    · obtain ⟨t, htk, hPt⟩ := h
      have ht : t = k + 1 := by
        by_cases hne : t = k + 1
        · exact hne
        · exact (hprev ⟨t, by omega, hPt⟩).elim
      subst ht
      refine ⟨k + 1, Nat.le_refl _, hPt, fun j hj hPj => hprev ⟨j, by omega, hPj⟩⟩

private theorem last_witness (P : Nat → Prop) :
    ∀ k, (∃ t, t ≤ k ∧ P t) → ∃ t, t ≤ k ∧ P t ∧ ∀ j, t < j → j ≤ k → ¬ P j
  | 0, ⟨t, ht, hPt⟩ => by
    have : t = 0 := by omega
    subst this
    exact ⟨0, Nat.le_refl 0, hPt, fun j h1 h2 => by omega⟩
  | k + 1, h => by
    by_cases htop : P (k + 1)
    · exact ⟨k + 1, Nat.le_refl _, htop, fun j h1 h2 => by omega⟩
    · obtain ⟨t, htk, hPt⟩ := h
      have htk' : t ≤ k := by
        by_cases heq : t = k + 1
        · subst heq; exact (htop hPt).elim
        · omega
      obtain ⟨s, hsk, hPs, hmax⟩ := last_witness P k ⟨t, htk', hPt⟩
      refine ⟨s, by omega, hPs, fun j hj1 hj2 hPj => ?_⟩
      by_cases heq : j = k + 1
      · subst heq; exact htop hPj
      · exact hmax j hj1 (by omega) hPj

/-! ## 1. Top-triangular subtraction complement and unconditional quadratic distinct-seen bound -/

/-- Exact top-triangular complement bound on the subtraction clock sum:
`subSum b + upperTri (b - subCount b) ≤ upperTri b`, strictly sharpening
`SubtractionLedger.subSum_le_mul_subCount` (and sharp with equality at `b = 4`). -/
theorem subSum_add_upperTri_complement_le (b : Nat) :
    subSum b + upperTri (b - subCount b) ≤ upperTri b := by
  induction b with
  | zero => simp [subSum, subCount, upperTri]
  | succ k ih =>
    have hle := subCount_le k
    by_cases hcan : CanSubtract (k + 1) (stateAt k)
    · have hsum : subSum (k + 1) = subSum k + (k + 1) := by
        rw [subSum_succ, if_pos hcan]
      have hcnt : subCount (k + 1) = subCount k + 1 := by
        rw [subCount_succ, if_pos hcan]
      have hdiff : k + 1 - subCount (k + 1) = k - subCount k := by omega
      have htri := upperTri_succ k
      rw [hsum, hdiff, htri]
      omega
    · have hsum : subSum (k + 1) = subSum k := by
        rw [subSum_succ, if_neg hcan]; omega
      have hcnt : subCount (k + 1) = subCount k := by
        rw [subCount_succ, if_neg hcan]; omega
      have hdiff : k + 1 - subCount (k + 1) = (k - subCount k) + 1 := by omega
      have htri1 := upperTri_succ (k - subCount k)
      have htri2 := upperTri_succ k
      rw [hsum, hdiff, htri1, htri2]
      omega

private def subClocks : Nat → List Nat
  | 0 => [0]
  | k + 1 => if CanSubtract (k + 1) (stateAt k) then (k + 1) :: subClocks k else subClocks k

private theorem subClocks_length (b : Nat) : (subClocks b).length = subCount b + 1 := by
  induction b with
  | zero => rfl
  | succ k ih =>
    unfold subClocks
    rw [subCount_succ]
    by_cases hcan : CanSubtract (k + 1) (stateAt k)
    · rw [if_pos hcan, if_pos hcan, List.length_cons, ih]
    · rw [if_neg hcan, if_neg hcan, Nat.add_zero, ih]

private theorem subClocks_le (b : Nat) : ∀ t ∈ subClocks b, t ≤ b := by
  induction b with
  | zero =>
    intro t ht
    simp only [subClocks, List.mem_cons, List.not_mem_nil, or_false] at ht
    omega
  | succ k ih =>
    intro t ht
    unfold subClocks at ht
    by_cases hcan : CanSubtract (k + 1) (stateAt k)
    · rw [if_pos hcan] at ht
      rcases List.mem_cons.mp ht with rfl | htail
      · exact Nat.le_refl _
      · exact Nat.le_trans (ih t htail) (Nat.le_succ k)
    · rw [if_neg hcan] at ht
      exact Nat.le_trans (ih t ht) (Nat.le_succ k)

private theorem subClocks_map_a_nodup (b : Nat) : ((subClocks b).map a).Nodup := by
  induction b with
  | zero => simp [subClocks]
  | succ k ih =>
    unfold subClocks
    by_cases hcan : CanSubtract (k + 1) (stateAt k)
    · rw [if_pos hcan, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro hmem
      obtain ⟨t, ht, hval⟩ := List.mem_map.mp hmem
      have htk : t ≤ k := subClocks_le k t ht
      have hseen : a t ∈ valuesThrough k := mem_valuesThrough_iff.mpr ⟨t, htk, rfl⟩
      have haSucc := a_succ_of_canSubtract hcan
      have hnot : a k - (k + 1) ∉ valuesThrough k := hcan.2
      rw [← haSucc, ← hval] at hnot
      exact hnot hseen
    · rw [if_neg hcan]
      exact ih

/-- Every subtraction step produces a strictly fresh unseen value, and `a 0 = 0` starts
the orbit, so every list covering `valuesThrough b` has length at least `subCount b + 1`. -/
theorem subCount_succ_le_cover_length (b : Nat) (V : List Nat)
    (hcov : ∀ v ∈ valuesThrough b, v ∈ V) :
    subCount b + 1 ≤ V.length := by
  have hnd := subClocks_map_a_nodup b
  have hsub : ∀ v ∈ (subClocks b).map a, v ∈ V := by
    intro v hv
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
    exact hcov (a t) (mem_valuesThrough_iff.mpr ⟨t, subClocks_le b t ht, rfl⟩)
  have hlen := nodup_length_le_of_subset hnd hsub
  rw [List.length_map, subClocks_length] at hlen
  exact hlen

/-- Unconditional quadratic lower bound on the number of distinct visited values of the
canonical Recamán sequence: for every `b : Nat` and every cover `V` of `valuesThrough b`,
`2 * upperTri (b + 1 - V.length) ≤ upperTri b + a b`
(forcing `|V| ≥ (1 - 1 / √2) * b` whenever `a b = o(b^2)`). -/
theorem canonical_distinct_cover_quadratic_bound (b : Nat) (V : List Nat)
    (hcov : ∀ v ∈ valuesThrough b, v ∈ V) :
    2 * upperTri (b + 1 - V.length) ≤ upperTri b + a b := by
  have hcover := subCount_succ_le_cover_length b V hcov
  have hcomp := subSum_add_upperTri_complement_le b
  have hled := ledger_identity b
  have hmono : upperTri (b + 1 - V.length) ≤ upperTri (b - subCount b) :=
    upperTri_mono (by omega)
  omega

/-! ## 2. Exact mod-4 parity-partition capacity -/

/-- Every `Nodup` list of even visited values in `valuesThrough b` has length at most
`evenClockCount b` (the number of clocks `≤ b` congruent to `0` or `3` mod `4`). -/
theorem canonical_even_visit_count_le (b : Nat) (L : List Nat)
    (hnd : L.Nodup) (hmem : ∀ v ∈ L, v ∈ valuesThrough b)
    (heven : ∀ v ∈ L, v % 2 = 0) :
    L.length ≤ evenClockCount b := by
  have hwit : ∀ v, v ∈ L → ∃ t, t ≤ b ∧ a t = v := fun v hv =>
    mem_valuesThrough_iff.mp (hmem v hv)
  let tOf : Nat → Nat := fun v => if h : v ∈ L then Classical.choose (hwit v h) else 0
  have htSpec : ∀ v, (h : v ∈ L) → tOf v ≤ b ∧ a (tOf v) = v := by
    intro v hv
    simp only [tOf, dif_pos hv]
    exact Classical.choose_spec (hwit v hv)
  have hinj : ∀ x ∈ L, ∀ y ∈ L, tOf x = tOf y → x = y := by
    intro x hx y hy hxy
    have hxE := (htSpec x hx).2
    have hyE := (htSpec y hy).2
    rw [hxy] at hxE
    omega
  have hnd_img := nodup_map_of_inj L tOf hnd hinj
  let tgt := (List.range (b + 1)).filter (fun t => t % 4 == 0 || t % 4 == 3)
  have hsub : ∀ t ∈ L.map tOf, t ∈ tgt := by
    intro t ht
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
    obtain ⟨htb, hval⟩ := htSpec v hv
    have hmod := even_value_time_mod_four (heven v hv) hval
    simp only [tgt, List.mem_filter, List.mem_range, Bool.or_eq_true, beq_iff_eq]
    exact ⟨by omega, hmod⟩
  have hlen := nodup_length_le_of_subset hnd_img hsub
  rw [List.length_map] at hlen
  exact hlen

/-- Every `Nodup` list of odd visited values in `valuesThrough b` has length at most
`oddClockCount b` (the number of clocks `≤ b` congruent to `1` or `2` mod `4`). -/
theorem canonical_odd_visit_count_le (b : Nat) (L : List Nat)
    (hnd : L.Nodup) (hmem : ∀ v ∈ L, v ∈ valuesThrough b)
    (hodd : ∀ v ∈ L, v % 2 = 1) :
    L.length ≤ oddClockCount b := by
  have hwit : ∀ v, v ∈ L → ∃ t, t ≤ b ∧ a t = v := fun v hv =>
    mem_valuesThrough_iff.mp (hmem v hv)
  let tOf : Nat → Nat := fun v => if h : v ∈ L then Classical.choose (hwit v h) else 0
  have htSpec : ∀ v, (h : v ∈ L) → tOf v ≤ b ∧ a (tOf v) = v := by
    intro v hv
    simp only [tOf, dif_pos hv]
    exact Classical.choose_spec (hwit v hv)
  have hinj : ∀ x ∈ L, ∀ y ∈ L, tOf x = tOf y → x = y := by
    intro x hx y hy hxy
    have hxE := (htSpec x hx).2
    have hyE := (htSpec y hy).2
    rw [hxy] at hxE
    omega
  have hnd_img := nodup_map_of_inj L tOf hnd hinj
  let tgt := (List.range (b + 1)).filter (fun t => t % 4 == 1 || t % 4 == 2)
  have hsub : ∀ t ∈ L.map tOf, t ∈ tgt := by
    intro t ht
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
    obtain ⟨htb, hval⟩ := htSpec v hv
    have hmod := odd_value_time_mod_four (hodd v hv) hval
    simp only [tgt, List.mem_filter, List.mem_range, Bool.or_eq_true, beq_iff_eq]
    exact ⟨by omega, hmod⟩
  have hlen := nodup_length_le_of_subset hnd_img hsub
  rw [List.length_map] at hlen
  exact hlen

/-! ## 3. Global cut-crossing connectivity -/

/-- Global cut-crossing theorem on `valuesThrough b`: every subset `S` containing `0`
and omitting at least one visited value is crossed by a canonical step `1 ≤ t ≤ b`
with `stepDist (a (t - 1)) (a t) = t`. -/
theorem canonical_cut_crossing_step (b : Nat) (S : Nat → Prop)
    (h0 : S 0) (hout : ∃ v ∈ valuesThrough b, ¬ S v) :
    ∃ t, 1 ≤ t ∧ t ≤ b ∧ S (a (t - 1)) ∧ ¬ S (a t) ∧ stepDist (a (t - 1)) (a t) = t := by
  obtain ⟨v, hv, hnotS⟩ := hout
  obtain ⟨s, hsb, rfl⟩ := mem_valuesThrough_iff.mp hv
  obtain ⟨t, htb, hnt, hmin⟩ := first_witness (fun i => ¬ S (a i)) b ⟨s, hsb, hnotS⟩
  have ht1 : 1 ≤ t := by
    by_cases hz : t = 0
    · subst hz; rw [a_zero_eq] at hnt; exact (hnt h0).elim
    · omega
  have hprev : S (a (t - 1)) := by
    by_cases hS : S (a (t - 1))
    · exact hS
    · exact (hmin (t - 1) (by omega) hS).elim
  have hdist := stepDist_at (t - 1)
  rw [show t - 1 + 1 = t by omega] at hdist
  exact ⟨t, ht1, htb, hprev, hnt, hdist⟩

/-! ## 4. Interior cluster entry-exit span and disjoint multi-point cluster clock budget -/

/-- Every interior cluster `S` (`¬ S 0`, `¬ S (a b)`) containing a nonempty `Nodup` list `L`
of visited values with boundary distance `≥ θ` admits entry and exit clocks `1 ≤ t₁ < t₂ ≤ b`
satisfying `θ ≤ t₁`, `θ ≤ t₂`, and `θ + L.length ≤ b`. -/
theorem canonical_interior_cluster_entry_exit_span (b θ : Nat) (S : Nat → Prop) (L : List Nat)
    (hnd : L.Nodup) (hne : L ≠ []) (hmem : ∀ v ∈ L, v ∈ valuesThrough b ∧ S v)
    (h0 : ¬ S 0) (hb : ¬ S (a b))
    (hsep : ∀ u v, u ∈ valuesThrough b → v ∈ valuesThrough b → S u → ¬ S v → θ ≤ stepDist u v) :
    ∃ t₁ t₂, 1 ≤ t₁ ∧ t₁ < t₂ ∧ t₂ ≤ b ∧ θ ≤ t₁ ∧ θ ≤ t₂ ∧
      ¬ S (a (t₁ - 1)) ∧ S (a t₁) ∧ S (a (t₂ - 1)) ∧ ¬ S (a t₂) ∧
      θ + L.length ≤ b := by
  have hex : ∃ s, s ≤ b ∧ S (a s) := by
    cases L with
    | nil => exact (hne rfl).elim
    | cons x xs =>
      obtain ⟨hxm, hxS⟩ := hmem x (List.mem_cons_self ..)
      obtain ⟨s, hsb, rfl⟩ := mem_valuesThrough_iff.mp hxm
      exact ⟨s, hsb, hxS⟩
  obtain ⟨t₁, ht₁b, hSt₁, hfirst⟩ := first_witness (fun i => S (a i)) b hex
  obtain ⟨u, hub, hSu, hlast⟩ := last_witness (fun i => S (a i)) b hex
  have ht₁1 : 1 ≤ t₁ := by
    by_cases hz : t₁ = 0
    · subst hz; rw [a_zero_eq] at hSt₁; exact (h0 hSt₁).elim
    · omega
  have hprev1 : ¬ S (a (t₁ - 1)) := hfirst (t₁ - 1) (by omega)
  have hub_lt : u < b := by
    by_cases heq : u = b
    · subst heq; exact (hb hSu).elim
    · omega
  let t₂ := u + 1
  have ht₂b : t₂ ≤ b := by omega
  have hnot2 : ¬ S (a t₂) := hlast t₂ (by omega) ht₂b
  have ht₁_le_u : t₁ ≤ u := by
    by_cases hle : t₁ ≤ u
    · exact hle
    · exact (hfirst u (by omega) hSu).elim
  have ht₁_lt_t₂ : t₁ < t₂ := by omega
  have hθ₁ : θ ≤ t₁ := by
    have hdist := stepDist_at (t₁ - 1)
    rw [show t₁ - 1 + 1 = t₁ by omega] at hdist
    have hsep1 := hsep (a t₁) (a (t₁ - 1))
      (mem_valuesThrough_iff.mpr ⟨t₁, ht₁b, rfl⟩)
      (mem_valuesThrough_iff.mpr ⟨t₁ - 1, by omega, rfl⟩)
      hSt₁ hprev1
    have hsym := stepDist_symm (a t₁) (a (t₁ - 1))
    omega
  have hθ₂ : θ ≤ t₂ := by
    have hdist := stepDist_at u
    have hsep2 := hsep (a u) (a t₂)
      (mem_valuesThrough_iff.mpr ⟨u, hub, rfl⟩)
      (mem_valuesThrough_iff.mpr ⟨t₂, ht₂b, rfl⟩)
      hSu hnot2
    omega
  -- Inject L into clocks {t₁, ..., u} (length u + 1 - t₁ = t₂ - t₁ <= b - θ)
  have hwit : ∀ v, v ∈ L → ∃ s, s ≤ b ∧ a s = v := fun v hv =>
    mem_valuesThrough_iff.mp (hmem v hv).1
  let sOf : Nat → Nat := fun v => if h : v ∈ L then Classical.choose (hwit v h) else 0
  have hsSpec : ∀ v, (h : v ∈ L) → t₁ ≤ sOf v ∧ sOf v ≤ u ∧ a (sOf v) = v := by
    intro v hv
    have hsp : Classical.choose (hwit v hv) ≤ b ∧ a (Classical.choose (hwit v hv)) = v :=
      Classical.choose_spec (hwit v hv)
    have hSv : S (a (Classical.choose (hwit v hv))) := by rw [hsp.2]; exact (hmem v hv).2
    have hge : t₁ ≤ Classical.choose (hwit v hv) := by
      by_cases h : t₁ ≤ Classical.choose (hwit v hv)
      · exact h
      · exact (hfirst (Classical.choose (hwit v hv)) (by omega) hSv).elim
    have hle : Classical.choose (hwit v hv) ≤ u := by
      by_cases h : Classical.choose (hwit v hv) ≤ u
      · exact h
      · exact (hlast (Classical.choose (hwit v hv)) (by omega) hsp.1 hSv).elim
    simp only [sOf, dif_pos hv]
    exact ⟨hge, hle, hsp.2⟩
  have hinj : ∀ x ∈ L, ∀ y ∈ L, sOf x - t₁ = sOf y - t₁ → x = y := by
    intro x hx y hy hxy
    obtain ⟨hx1, _, hxE⟩ := hsSpec x hx
    obtain ⟨hy1, _, hyE⟩ := hsSpec y hy
    have hseq : sOf x = sOf y := by omega
    rw [hseq] at hxE
    omega
  have hnd_img := nodup_map_of_inj L (fun v => sOf v - t₁) hnd hinj
  have hsub : ∀ k ∈ L.map (fun v => sOf v - t₁), k ∈ List.range (t₂ - t₁) := by
    intro k hk
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hk
    obtain ⟨hv1, hv2, _⟩ := hsSpec v hv
    rw [List.mem_range]
    omega
  have hlen := nodup_length_le_of_subset hnd_img hsub
  rw [List.length_map, List.length_range] at hlen
  refine ⟨t₁, t₂, ht₁1, ht₁_lt_t₂, ht₂b, hθ₁, hθ₂, hprev1, hSt₁, ?_, hnot2, by omega⟩
  rw [show t₂ - 1 = u by omega]
  exact hSu

private def clusterPairsAux : Nat → List (List Nat) → List (Nat × Nat)
  | _, [] => []
  | idx, C :: Cs => C.map (fun v => (idx, v)) ++ clusterPairsAux (idx + 1) Cs

private theorem clusterPairsAux_length (idx : Nat) (Cs : List (List Nat)) :
    (clusterPairsAux idx Cs).length = (Cs.map List.length).sum := by
  induction Cs generalizing idx with
  | nil => rfl
  | cons C rest ih =>
    simp [clusterPairsAux, List.length_append, List.length_map, ih]

private theorem clusterPairsAux_mem (idx : Nat) (Cs : List (List Nat)) (p : Nat × Nat) :
    p ∈ clusterPairsAux idx Cs ↔
      ∃ h : p.1 - idx < Cs.length, idx ≤ p.1 ∧ p.2 ∈ Cs[p.1 - idx] := by
  induction Cs generalizing idx with
  | nil => simp [clusterPairsAux]
  | cons C rest ih =>
    simp only [clusterPairsAux, List.mem_append, List.mem_map]
    constructor
    · rintro (⟨v, hv, rfl⟩ | htail)
      · refine ⟨by simp, Nat.le_refl idx, ?_⟩
        simpa [Nat.sub_self] using hv
      · obtain ⟨hlt, hge, hv⟩ := (ih (idx + 1)).mp htail
        have hsub : p.1 - idx = (p.1 - (idx + 1)) + 1 := by omega
        refine ⟨by simp; omega, by omega, ?_⟩
        simpa [hsub] using hv
    · rintro ⟨hlt, hge, hv⟩
      by_cases heq : p.1 = idx
      · left
        refine ⟨p.2, ?_, Prod.ext heq.symm rfl⟩
        simpa [heq, Nat.sub_self] using hv
      · right
        apply (ih (idx + 1)).mpr
        have hsub : p.1 - idx = (p.1 - (idx + 1)) + 1 := by omega
        simp only [List.length_cons] at hlt
        refine ⟨by omega, by omega, ?_⟩
        simpa [hsub] using hv

private theorem clusterPairsAux_nodup (idx : Nat) (Cs : List (List Nat))
    (hnd : ∀ C ∈ Cs, C.Nodup) :
    (clusterPairsAux idx Cs).Nodup := by
  induction Cs generalizing idx with
  | nil => simp [clusterPairsAux]
  | cons C rest ih =>
    simp only [clusterPairsAux]
    rw [List.nodup_append]
    refine ⟨nodup_map_of_inj C (fun v => (idx, v)) (hnd C (List.mem_cons_self ..))
        (fun _ _ _ _ h => by injection h),
      ih (idx + 1) (fun D hD => hnd D (List.mem_cons_of_mem C hD)), ?_⟩
    intro x hx y hy hxy
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨_, hge, _⟩ := (clusterPairsAux_mem (idx + 1) rest y).mp hy
    rw [← hxy] at hge
    omega

/-- Disjoint multi-point interior cluster clock budget on `Recaman.Basic.a`:
every list `Cs : List (List Nat)` of nonempty `Nodup` interior clusters inside `valuesThrough b`
with boundary separation `≥ θ` and mutual separation `> b` satisfies
`Cs.length + (Cs.map List.length).sum ≤ b + 1 - θ`.
Strictly generalizes both `E-781` single-tail capacity and `E-790` isolated-vertex
`2 * m ≤ b + 1 - θ` to arbitrary multi-point clusters. -/
theorem canonical_disjoint_clusters_clock_budget (b θ : Nat) (Cs : List (List Nat))
    (hC : ∀ C ∈ Cs, C.Nodup ∧ C ≠ [] ∧ (∀ v ∈ C, v ∈ valuesThrough b) ∧ 0 ∉ C ∧ a b ∉ C)
    (hsep : ∀ C ∈ Cs, ∀ u ∈ C, ∀ v ∈ valuesThrough b, v ∉ C → θ ≤ stepDist u v)
    (hmut : ∀ (i j : Nat) (hi : i < Cs.length) (hj : j < Cs.length), i ≠ j →
      ∀ u ∈ Cs[i], ∀ v ∈ Cs[j], b < stepDist u v) :
    Cs.length + (Cs.map List.length).sum ≤ b + 1 - θ := by
  -- For each cluster C_i, extract its entry clock t₁ ≥ θ and last-exit clock t_out ∈ [θ, b]
  have hExitData : ∀ i, (hi : i < Cs.length) →
      ∃ t₁ t_out, 1 ≤ t₁ ∧ t₁ < t_out ∧ t_out ≤ b ∧ θ ≤ t₁ ∧ θ ≤ t_out ∧
        a (t_out - 1) ∈ Cs[i] ∧ a t_out ∉ Cs[i] ∧
        ∀ s, s ≤ b → a s ∈ Cs[i] → t₁ ≤ s := by
    intro i hi
    have hCi := hC Cs[i] (List.getElem_mem hi)
    have hex : ∃ s, s ≤ b ∧ a s ∈ Cs[i] := by
      cases hEq : Cs[i] with
      | nil => exact (hCi.2.1 hEq).elim
      | cons x xs =>
        have hxm : x ∈ valuesThrough b := hCi.2.2.1 x (by rw [hEq]; exact List.mem_cons_self ..)
        obtain ⟨s, hsb, rfl⟩ := mem_valuesThrough_iff.mp hxm
        exact ⟨s, hsb, List.mem_cons_self ..⟩
    obtain ⟨t₁, ht₁b, hSt₁, hfirst⟩ := first_witness (fun s => a s ∈ Cs[i]) b hex
    obtain ⟨u, hub, hSu, hlast⟩ := last_witness (fun s => a s ∈ Cs[i]) b hex
    have ht₁1 : 1 ≤ t₁ := by
      by_cases hz : t₁ = 0
      · subst hz; rw [a_zero_eq] at hSt₁; exact (hCi.2.2.2.1 hSt₁).elim
      · omega
    have hprev1 : a (t₁ - 1) ∉ Cs[i] := hfirst (t₁ - 1) (by omega)
    have hub_lt : u < b := by
      by_cases heq : u = b
      · subst heq; exact (hCi.2.2.2.2 hSu).elim
      · omega
    have ht₁_le_u : t₁ ≤ u := by
      by_cases hle : t₁ ≤ u
      · exact hle
      · exact (hfirst u (by omega) hSu).elim
    have hnot_out : a (u + 1) ∉ Cs[i] := hlast (u + 1) (by omega) (by omega)
    have hθ₁ : θ ≤ t₁ := by
      have hdist := stepDist_at (t₁ - 1)
      rw [show t₁ - 1 + 1 = t₁ by omega] at hdist
      have hsep1 := hsep Cs[i] (List.getElem_mem hi) (a t₁) hSt₁ (a (t₁ - 1))
        (mem_valuesThrough_iff.mpr ⟨t₁ - 1, by omega, rfl⟩) hprev1
      have hsym := stepDist_symm (a t₁) (a (t₁ - 1))
      omega
    have hθ_out : θ ≤ u + 1 := by
      have hdist := stepDist_at u
      have hsep2 := hsep Cs[i] (List.getElem_mem hi) (a u) hSu (a (u + 1))
        (mem_valuesThrough_iff.mpr ⟨u + 1, by omega, rfl⟩) hnot_out
      omega
    refine ⟨t₁, u + 1, ht₁1, by omega, by omega, hθ₁, hθ_out, by simpa using hSu, hnot_out, ?_⟩
    intro s hsb hSs
    by_cases hge : t₁ ≤ s
    · exact hge
    · exact (hfirst s (by omega) hSs).elim
  let tOutOf : Nat → Nat := fun i =>
    if h : i < Cs.length then Classical.choose (Classical.choose_spec (hExitData i h)) else 0
  have htOutSpec : ∀ i, (hi : i < Cs.length) →
      1 ≤ tOutOf i ∧ tOutOf i ≤ b ∧ θ ≤ tOutOf i ∧
        a (tOutOf i - 1) ∈ Cs[i] ∧ a (tOutOf i) ∉ Cs[i] := by
    intro i hi
    have hsp := Classical.choose_spec (Classical.choose_spec (hExitData i hi))
    simp only [tOutOf, dif_pos hi]
    exact ⟨by omega, hsp.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2.1, hsp.2.2.2.2.2.2.1⟩
  have hVisitData : ∀ (p : Nat × Nat), p ∈ clusterPairsAux 0 Cs →
      ∃ s, θ ≤ s ∧ s ≤ b ∧ a s = p.2 := by
    intro p hp
    obtain ⟨hlt, _, hv⟩ := (clusterPairsAux_mem 0 Cs p).mp hp
    simp only [Nat.sub_zero] at hlt hv
    have hCi := hC Cs[p.1] (List.getElem_mem hlt)
    obtain ⟨s, hsb, has⟩ := mem_valuesThrough_iff.mp (hCi.2.2.1 p.2 hv)
    obtain ⟨t₁, _, _, _, _, hθ₁, _, _, _, hmin⟩ := hExitData p.1 hlt
    exact ⟨s, Nat.le_trans hθ₁ (hmin s hsb (by rw [has]; exact hv)), hsb, has⟩
  let sOf : Nat × Nat → Nat := fun p =>
    if h : p ∈ clusterPairsAux 0 Cs then Classical.choose (hVisitData p h) else 0
  have hsSpec : ∀ p, (hp : p ∈ clusterPairsAux 0 Cs) →
      θ ≤ sOf p ∧ sOf p ≤ b ∧ a (sOf p) = p.2 := by
    intro p hp
    simp only [sOf, dif_pos hp]
    exact Classical.choose_spec (hVisitData p hp)
  let dom1 := clusterPairsAux 0 Cs
  let dom2 := List.range Cs.length
  let dom : List (Sum (Nat × Nat) Nat) := dom1.map Sum.inl ++ dom2.map Sum.inr
  let phi : Sum (Nat × Nat) Nat → Nat := fun x =>
    match x with
    | Sum.inl p => sOf p - θ
    | Sum.inr i => tOutOf i - θ
  have hnd_dom : dom.Nodup :=
    nodup_sum_append dom1 dom2
      (clusterPairsAux_nodup 0 Cs (fun C hCm => (hC C hCm).1))
      List.nodup_range
  have hsub : ∀ k ∈ dom.map phi, k ∈ List.range (b + 1 - θ) := by
    intro k hk
    obtain ⟨x, hxm, rfl⟩ := List.mem_map.mp hk
    rw [List.mem_range]
    rcases List.mem_append.mp hxm with h1 | h2
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h1
      obtain ⟨hθs, hsb, _⟩ := hsSpec p hp
      dsimp only [phi]; omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h2
      rw [List.mem_range] at hi
      obtain ⟨_, htb, hθt, _, _⟩ := htOutSpec i hi
      dsimp only [phi]; omega
  have hinj : ∀ x ∈ dom, ∀ y ∈ dom, phi x = phi y → x = y := by
    intro x hx y hy hxy
    rcases List.mem_append.mp hx with hx1 | hx2 <;> rcases List.mem_append.mp hy with hy1 | hy2
    · -- Both first-visit clocks
      obtain ⟨px, hpx, rfl⟩ := List.mem_map.mp hx1
      obtain ⟨py, hpy, rfl⟩ := List.mem_map.mp hy1
      obtain ⟨hθx, _, hax⟩ := hsSpec px hpx
      obtain ⟨hθy, _, hay⟩ := hsSpec py hpy
      have hseq : sOf px = sOf py := by dsimp only [phi] at hxy; omega
      have hveq : px.2 = py.2 := by rw [← hax, hseq, hay]
      obtain ⟨hltx, _, hvx⟩ := (clusterPairsAux_mem 0 Cs px).mp hpx
      obtain ⟨hlty, _, hvy⟩ := (clusterPairsAux_mem 0 Cs py).mp hpy
      simp only [Nat.sub_zero] at hltx hvx hlty hvy
      have hieq : px.1 = py.1 := by
        by_cases he : px.1 = py.1
        · exact he
        · have hgt := hmut px.1 py.1 hltx hlty he px.2 hvx py.2 hvy
          rw [hveq, stepDist_self] at hgt
          omega
      exact congrArg Sum.inl (Prod.ext hieq hveq)
    · -- First-visit clock vs exit clock: impossible
      obtain ⟨px, hpx, rfl⟩ := List.mem_map.mp hx1
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy2
      rw [List.mem_range] at hj
      obtain ⟨hθx, _, hax⟩ := hsSpec px hpx
      obtain ⟨ht1, htb, hθt, hprevj, hnotj⟩ := htOutSpec j hj
      have hseq : sOf px = tOutOf j := by dsimp only [phi] at hxy; omega
      obtain ⟨hltx, _, hvx⟩ := (clusterPairsAux_mem 0 Cs px).mp hpx
      simp only [Nat.sub_zero] at hltx hvx
      have hat_mem : a (tOutOf j) ∈ Cs[px.1] := by rw [← hseq, hax]; exact hvx
      by_cases hij : px.1 = j
      · subst hij; exact (hnotj hat_mem).elim
      · have hgt := hmut j px.1 hj hltx (fun h => hij h.symm) (a (tOutOf j - 1)) hprevj (a (tOutOf j)) hat_mem
        have hdist := stepDist_at (tOutOf j - 1)
        rw [show tOutOf j - 1 + 1 = tOutOf j by omega] at hdist
        omega
    · -- Exit clock vs first-visit clock: symmetric impossible
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx2
      obtain ⟨py, hpy, rfl⟩ := List.mem_map.mp hy1
      rw [List.mem_range] at hi
      obtain ⟨ht1, htb, hθt, hprevi, hnoti⟩ := htOutSpec i hi
      obtain ⟨hθy, _, hay⟩ := hsSpec py hpy
      have hseq : tOutOf i = sOf py := by dsimp only [phi] at hxy; omega
      obtain ⟨hlty, _, hvy⟩ := (clusterPairsAux_mem 0 Cs py).mp hpy
      simp only [Nat.sub_zero] at hlty hvy
      have hat_mem : a (tOutOf i) ∈ Cs[py.1] := by rw [hseq, hay]; exact hvy
      by_cases hij : i = py.1
      · subst hij; exact (hnoti hat_mem).elim
      · have hgt := hmut i py.1 hi hlty hij (a (tOutOf i - 1)) hprevi (a (tOutOf i)) hat_mem
        have hdist := stepDist_at (tOutOf i - 1)
        rw [show tOutOf i - 1 + 1 = tOutOf i by omega] at hdist
        omega
    · -- Both exit clocks
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx2
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy2
      rw [List.mem_range] at hi hj
      obtain ⟨_, _, hθi, hprevi, _⟩ := htOutSpec i hi
      obtain ⟨_, _, hθj, hprevj, _⟩ := htOutSpec j hj
      have hteq : tOutOf i = tOutOf j := by dsimp only [phi] at hxy; omega
      have heq : i = j := by
        by_cases he : i = j
        · exact he
        · have hgt := hmut i j hi hj he (a (tOutOf i - 1)) hprevi (a (tOutOf j - 1)) hprevj
          rw [hteq, stepDist_self] at hgt
          omega
      exact congrArg Sum.inr heq
  have hnd_img := nodup_map_of_inj dom phi hnd_dom hinj
  have hlen := nodup_length_le_of_subset hnd_img hsub
  rw [List.length_map, List.length_range] at hlen
  have hdom_len : dom.length = (Cs.map List.length).sum + Cs.length := by
    simp only [dom, List.length_append, List.length_map, dom1, dom2, clusterPairsAux_length,
      List.length_range]
  omega

end Recaman.CanonicalPathInvariants
