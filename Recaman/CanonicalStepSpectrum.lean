import Recaman.CanonicalGapCapacity

namespace Recaman.CanonicalStepSpectrum

open Recaman Recaman.CanonicalGapCapacity
open Classical

/-! # Step-spectrum realization, consecutive-step degree, and moment bounds on `Recaman.Basic.a`

Every canonical clock `b : Nat` traces `valuesThrough b` via steps `1, 2, ..., b`
starting from `a 0 = 0`.  Beyond the gap-width bounds of `Recaman.CanonicalGapCapacity`
(`E-781`), the step-size structure of `Recaman.Basic.a` imposes four sharper structural
invariants on `valuesThrough b`:

1. `canonical_step_difference_realized`:
   Every step size `k ∈ {1, ..., b}` is realized as `|u - v| = k` for some
   `u, v ∈ valuesThrough b` (disqualifying `E-782`'s constant-step bridge `G_d`,
   which omits all steps `k ∈ (b/2, d)`).
2. `canonical_consecutive_incident_steps` & `canonical_odd_even_neighbor`:
   Every interior visited value `v ∈ valuesThrough b \ {0, a b}` admits a clock
   `1 ≤ t < b` with BOTH `t` and `t + 1` realized as distances to elements of
   `valuesThrough b`, and in particular has BOTH an even-distance and an odd-distance
   neighbor within distance `b` (disqualifying `E-782`'s `G_d` at interior bridge points).
3. `canonical_separated_set_clock_budget`:
   Any `Nodup` list `L` of interior visited values in `valuesThrough b \ {0, a b}`
   with pairwise distances `> b` and nearest neighbor in `valuesThrough b` at distance
   `≥ θ` (`1 ≤ θ ≤ b`) consumes two disjoint consecutive clocks per element in `{θ, ..., b}`,
   forcing `2 * L.length ≤ b + 1 - θ` (strictly `2x` stronger than `E-781` on isolated peaks).
4. `canonical_distinct_sum_le_upperTri_top`:
   Any `Nodup` list `L` of elements in `valuesThrough b` obeys the exact first-moment
   capacity `L.sum ≤ topUpperTriSum b L.length = ∑_{j=0}^{L.length-1} upperTri (b - j)`
   (sharp at `b = 1, 3`).
-/

/-! ## Step-difference realization and consecutive incident steps -/

private theorem step_dist_at (t : Nat) :
    a t + (t + 1) = a (t + 1) ∨ a (t + 1) + (t + 1) = a t := by
  have hrec := recurrence t
  by_cases hcan : CanSubtract (t + 1) (stateAt t)
  · rw [if_pos hcan] at hrec
    have hgt : t + 1 ≤ a t := by
      have := hcan.1
      change t + 1 < a t at this
      omega
    right; omega
  · rw [if_neg hcan] at hrec
    left; omega

/-- Every step size `k ∈ {1, ..., b}` appears as an exact difference `|u - v| = k`
between two elements `u, v ∈ valuesThrough b`. -/
theorem canonical_step_difference_realized (b k : Nat) (hk1 : 1 ≤ k) (hkb : k ≤ b) :
    ∃ u ∈ valuesThrough b, ∃ v ∈ valuesThrough b, u + k = v ∨ v + k = u := by
  have hu : a (k - 1) ∈ valuesThrough b :=
    mem_valuesThrough_iff.mpr ⟨k - 1, by omega, rfl⟩
  have hv : a k ∈ valuesThrough b :=
    mem_valuesThrough_iff.mpr ⟨k, hkb, rfl⟩
  have hd := step_dist_at (k - 1)
  rw [show k - 1 + 1 = k by omega] at hd
  exact ⟨a (k - 1), hu, a k, hv, hd⟩

/-- Every interior visited value `v ∈ valuesThrough b` (`v ≠ 0`, `v ≠ a b`) has
two consecutive incident step sizes `t` and `t + 1` (`1 ≤ t < b`) to elements of
`valuesThrough b`. -/
theorem canonical_consecutive_incident_steps (b v : Nat)
    (hv : v ∈ valuesThrough b) (hv0 : v ≠ 0) (hvb : v ≠ a b) :
    ∃ t u₁ u₂, 1 ≤ t ∧ t < b ∧
      u₁ ∈ valuesThrough b ∧ u₂ ∈ valuesThrough b ∧
      (v + t = u₁ ∨ u₁ + t = v) ∧
      (v + (t + 1) = u₂ ∨ u₂ + (t + 1) = v) := by
  rcases mem_valuesThrough_iff.mp hv with ⟨t, htb, rfl⟩
  have ht1 : 1 ≤ t := by
    by_cases h0 : t = 0
    · subst h0
      have ha0 : a 0 = 0 := by simp [a, stateAt, initial]
      exact (hv0 ha0).elim
    · omega
  have hlt : t < b := by
    by_cases heq : t = b
    · subst heq; exact (hvb rfl).elim
    · omega
  have hu1 : a (t - 1) ∈ valuesThrough b :=
    mem_valuesThrough_iff.mpr ⟨t - 1, by omega, rfl⟩
  have hu2 : a (t + 1) ∈ valuesThrough b :=
    mem_valuesThrough_iff.mpr ⟨t + 1, by omega, rfl⟩
  have hd1 := step_dist_at (t - 1)
  rw [show t - 1 + 1 = t by omega] at hd1
  have hd2 := step_dist_at t
  refine ⟨t, a (t - 1), a (t + 1), ht1, hlt, hu1, hu2, ?_, ?_⟩
  · rcases hd1 with h | h
    · right; exact h
    · left; exact h
  · rcases hd2 with h | h
    · left; exact h
    · right; exact h

/-- Every interior visited value `v ∈ valuesThrough b` (`v ≠ 0`, `v ≠ a b`) has BOTH
an even-distance neighbor and an odd-distance neighbor in `valuesThrough b` within
distance `b`. -/
theorem canonical_odd_even_neighbor (b v : Nat)
    (hv : v ∈ valuesThrough b) (hv0 : v ≠ 0) (hvb : v ≠ a b) :
    (∃ d₁ u₁, 1 ≤ d₁ ∧ d₁ ≤ b ∧ d₁ % 2 = 0 ∧ u₁ ∈ valuesThrough b ∧ (v + d₁ = u₁ ∨ u₁ + d₁ = v)) ∧
    (∃ d₂ u₂, 1 ≤ d₂ ∧ d₂ ≤ b ∧ d₂ % 2 = 1 ∧ u₂ ∈ valuesThrough b ∧ (v + d₂ = u₂ ∨ u₂ + d₂ = v)) := by
  obtain ⟨t, u₁, u₂, ht1, hlt, hu1, hu2, hd1, hd2⟩ :=
    canonical_consecutive_incident_steps b v hv hv0 hvb
  by_cases hpar : t % 2 = 0
  · exact ⟨⟨t, u₁, ht1, by omega, hpar, hu1, hd1⟩,
      ⟨t + 1, u₂, by omega, by omega, by omega, hu2, hd2⟩⟩
  · exact ⟨⟨t + 1, u₂, by omega, by omega, by omega, hu2, hd2⟩,
      ⟨t, u₁, ht1, by omega, by omega, hu1, hd1⟩⟩

/-! ## Separated-set 2x clock budget -/

private theorem nodup_length_le_of_subset :
    ∀ {L M : List Nat}, L.Nodup → (∀ x ∈ L, x ∈ M) → L.length ≤ M.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, M, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have hxM : x ∈ M := hsub x (List.mem_cons_self ..)
    have hsub' : ∀ y ∈ xs, y ∈ M.erase x := by
      intro y hy
      have hne : y ≠ x := fun heq => hnd.1 (heq ▸ hy)
      exact (List.mem_erase_of_ne hne).mpr (hsub y (List.mem_cons_of_mem x hy))
    have hih := nodup_length_le_of_subset hnd.2 hsub'
    have herase : (M.erase x).length + 1 = M.length := by
      have hlen := List.length_erase_of_mem hxM
      have hpos : 0 < M.length := List.length_pos_of_mem hxM
      omega
    simp only [List.length_cons]
    omega

private theorem pair_flatMap_length (tOf : Nat → Nat) :
    ∀ L : List Nat, (L.flatMap (fun v => [tOf v, tOf v + 1])).length = 2 * L.length
  | [] => rfl
  | x :: xs => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil,
      pair_flatMap_length tOf xs]
    omega

private theorem pair_flatMap_nodup (tOf : Nat → Nat) :
    ∀ L : List Nat, L.Nodup →
      (∀ v ∈ L, ∀ w ∈ L, v ≠ w → tOf v ≠ tOf w ∧ tOf v + 1 ≠ tOf w ∧ tOf v ≠ tOf w + 1) →
      (L.flatMap (fun v => [tOf v, tOf v + 1])).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, hnd, hdisj => by
    rw [List.nodup_cons] at hnd
    have hrest := pair_flatMap_nodup tOf xs hnd.2 (fun v hv w hw hne =>
      hdisj v (List.mem_cons_of_mem x hv) w (List.mem_cons_of_mem x hw) hne)
    have hnot0 : tOf x ∉ xs.flatMap (fun v => [tOf v, tOf v + 1]) := by
      intro hm
      rw [List.mem_flatMap] at hm
      obtain ⟨y, hy, hxy⟩ := hm
      have hne : x ≠ y := fun heq => hnd.1 (heq ▸ hy)
      have hd := hdisj x (List.mem_cons_self ..) y (List.mem_cons_of_mem x hy) hne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hxy
      omega
    have hnot1 : tOf x + 1 ∉ xs.flatMap (fun v => [tOf v, tOf v + 1]) := by
      intro hm
      rw [List.mem_flatMap] at hm
      obtain ⟨y, hy, hxy⟩ := hm
      have hne : x ≠ y := fun heq => hnd.1 (heq ▸ hy)
      have hd := hdisj x (List.mem_cons_self ..) y (List.mem_cons_of_mem x hy) hne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hxy
      omega
    rw [List.flatMap_cons, List.cons_append, List.cons_append, List.nil_append]
    rw [List.nodup_cons, List.nodup_cons]
    refine ⟨?_, hnot1, hrest⟩
    intro hm
    simp only [List.mem_cons] at hm
    rcases hm with heq | hmem
    · omega
    · exact hnot0 hmem

/-- Separated-set `2x` clock budget on `valuesThrough b`:
any `Nodup` list `L` of interior visited values (`v ≠ 0`, `v ≠ a b`) with pairwise
distances `> b` and nearest neighbor in `valuesThrough b` at distance `≥ θ` (`1 ≤ θ ≤ b`)
satisfies `2 * L.length ≤ b + 1 - θ`. -/
theorem canonical_separated_set_clock_budget (b θ : Nat) (hθ1 : 1 ≤ θ) (hθb : θ ≤ b)
    (L : List Nat) (hnd : L.Nodup)
    (hmem : ∀ v ∈ L, v ∈ valuesThrough b ∧ v ≠ 0 ∧ v ≠ a b)
    (hsep : ∀ v ∈ L, ∀ w ∈ L, v ≠ w → b < v - w ∨ b < w - v)
    (hnb : ∀ v ∈ L, ∀ u ∈ valuesThrough b, u ≠ v → θ ≤ v - u ∨ θ ≤ u - v) :
    2 * L.length ≤ b + 1 - θ := by
  let tOf : Nat → Nat := fun v =>
    if h : v ∈ valuesThrough b then Classical.choose (mem_valuesThrough_iff.mp h) else 0
  have htSpec : ∀ v ∈ L, tOf v ≤ b ∧ a (tOf v) = v ∧ θ ≤ tOf v ∧ tOf v < b := by
    intro v hv
    have hm := hmem v hv
    have hsp := Classical.choose_spec (mem_valuesThrough_iff.mp hm.1)
    have ht_eq : tOf v = Classical.choose (mem_valuesThrough_iff.mp hm.1) := dif_pos hm.1
    rw [← ht_eq] at hsp
    have ht1 : 1 ≤ tOf v := by
      by_cases h0 : tOf v = 0
      · have ha0 : a 0 = 0 := by simp [a, stateAt, initial]
        have : v = 0 := by rw [← hsp.2, h0, ha0]
        exact (hm.2.1 this).elim
      · omega
    have hlt : tOf v < b := by
      by_cases heq : tOf v = b
      · have : v = a b := by rw [← hsp.2, heq]
        exact (hm.2.2 this).elim
      · omega
    have hu1 : a (tOf v - 1) ∈ valuesThrough b :=
      mem_valuesThrough_iff.mpr ⟨tOf v - 1, by omega, rfl⟩
    have hd1 := step_dist_at (tOf v - 1)
    rw [show tOf v - 1 + 1 = tOf v by omega, hsp.2] at hd1
    have hune : a (tOf v - 1) ≠ v := by omega
    have hdist := hnb v hv (a (tOf v - 1)) hu1 hune
    exact ⟨hsp.1, hsp.2, by omega, hlt⟩
  have hdisj : ∀ v ∈ L, ∀ w ∈ L, v ≠ w →
      tOf v ≠ tOf w ∧ tOf v + 1 ≠ tOf w ∧ tOf v ≠ tOf w + 1 := by
    intro v hv w hw hne
    have hsv := htSpec v hv
    have hsw := htSpec w hw
    have hsp := hsep v hv w hw hne
    refine ⟨?_, ?_, ?_⟩
    · intro heq
      apply hne
      rw [← hsv.2.1, ← hsw.2.1, heq]
    · intro heq
      have hd := step_dist_at (tOf v)
      rw [heq, hsv.2.1, hsw.2.1] at hd
      omega
    · intro heq
      have hd := step_dist_at (tOf w)
      rw [← heq, hsv.2.1, hsw.2.1] at hd
      omega
  let clocks := L.flatMap (fun v => [tOf v, tOf v + 1])
  let pool := (List.range (b + 1 - θ)).map (fun j => θ + j)
  have hcl_nd : clocks.Nodup := pair_flatMap_nodup tOf L hnd hdisj
  have hsub : ∀ c ∈ clocks, c ∈ pool := by
    intro c hc
    rw [List.mem_flatMap] at hc
    obtain ⟨v, hv, hcv⟩ := hc
    have hsv := htSpec v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcv
    rw [List.mem_map]
    rcases hcv with rfl | rfl
    · refine ⟨tOf v - θ, List.mem_range.mpr (by omega), by omega⟩
    · refine ⟨tOf v + 1 - θ, List.mem_range.mpr (by omega), by omega⟩
  have hlen := nodup_length_le_of_subset hcl_nd hsub
  have hcl_len : clocks.length = 2 * L.length := pair_flatMap_length tOf L
  have hpool_len : pool.length = b + 1 - θ := by simp [pool]
  omega

/-! ## Canonical first-moment / top-`upperTri` sum capacity -/

/-- Sum of the `k` largest triangular bounds `upperTri b + upperTri (b - 1) + ... + upperTri (b - (k - 1))`. -/
def topUpperTriSum (b : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => topUpperTriSum b k + upperTri (b - k)

private theorem upperTri_mono {x y : Nat} (hxy : x ≤ y) : upperTri x ≤ upperTri y := by
  induction y with
  | zero =>
    have hx : x = 0 := by omega
    subst hx; exact Nat.le_refl _
  | succ y ih =>
    rcases Nat.eq_or_lt_of_le hxy with rfl | hlt
    · exact Nat.le_refl _
    · have ih' := ih (Nat.le_of_lt_succ hlt)
      rw [upperTri]
      omega

private theorem topUpperTriSum_mono_b (b : Nat) :
    ∀ k, topUpperTriSum b k ≤ topUpperTriSum (b + 1) k
  | 0 => Nat.le_refl 0
  | k + 1 => by
    have ih := topUpperTriSum_mono_b b k
    simp only [topUpperTriSum]
    have htri := upperTri_mono (show b - k ≤ b + 1 - k by omega)
    omega

private theorem topUpperTriSum_succ_succ (b : Nat) :
    ∀ k, topUpperTriSum (b + 1) (k + 1) = upperTri (b + 1) + topUpperTriSum b k
  | 0 => by simp [topUpperTriSum]
  | k + 1 => by
    have ih := topUpperTriSum_succ_succ b k
    simp only [topUpperTriSum] at ih ⊢
    rw [show b + 1 - (k + 1) = b - k by omega]
    omega

private theorem sum_map_upperTri_erase (x : Nat) :
    ∀ {T : List Nat}, x ∈ T →
      (T.map upperTri).sum = upperTri x + ((T.erase x).map upperTri).sum
  | [], hm => nomatch hm
  | y :: ys, hm => by
    by_cases hxy : y = x
    · subst hxy
      simp [List.erase_cons_head]
    · have hbeq : (y == x) = false := beq_false_of_ne hxy
      have hmem : x ∈ ys := by
        simp only [List.mem_cons] at hm
        rcases hm with rfl | h
        · exact (hxy rfl).elim
        · exact h
      have ih := sum_map_upperTri_erase x hmem
      simp only [List.erase_cons, hbeq, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
      omega

private theorem nodup_sum_upperTri_le_top :
    ∀ (b : Nat) (T : List Nat), T.Nodup → (∀ t ∈ T, t ≤ b) →
      (T.map upperTri).sum ≤ topUpperTriSum b T.length
  | 0, T, _, hle => by
    have hz : ∀ (U : List Nat), (∀ t ∈ U, t ≤ 0) → (U.map upperTri).sum = 0 := by
      intro U
      induction U with
      | nil => intro _; rfl
      | cons x xs ih =>
        intro hU
        have hx : x = 0 := by have := hU x (List.mem_cons_self ..); omega
        have ih' := ih (fun t ht => hU t (List.mem_cons_of_mem x ht))
        subst hx
        simp [upperTri, ih']
    rw [hz T hle]
    exact Nat.zero_le _
  | b + 1, T, hnd, hle => by
    by_cases hmem : b + 1 ∈ T
    · have hnd' : (T.erase (b + 1)).Nodup := hnd.erase (b + 1)
      have hnot : b + 1 ∉ T.erase (b + 1) := List.Nodup.not_mem_erase hnd
      have hle' : ∀ t ∈ T.erase (b + 1), t ≤ b := by
        intro t ht
        have htT : t ∈ T := List.mem_of_mem_erase ht
        have htb := hle t htT
        have hne : t ≠ b + 1 := fun heq => hnot (heq ▸ ht)
        omega
      have ih := nodup_sum_upperTri_le_top b (T.erase (b + 1)) hnd' hle'
      have hsum := sum_map_upperTri_erase (b + 1) hmem
      have hlen : (T.erase (b + 1)).length + 1 = T.length := by
        have h1 := List.length_erase_of_mem hmem
        have hpos : 0 < T.length := List.length_pos_of_mem hmem
        omega
      rw [← hlen, topUpperTriSum_succ_succ b (T.erase (b + 1)).length, hsum]
      omega
    · have hle' : ∀ t ∈ T, t ≤ b := by
        intro t ht
        have htb := hle t ht
        have hne : t ≠ b + 1 := fun heq => hmem (heq ▸ ht)
        omega
      have ih := nodup_sum_upperTri_le_top b T hnd hle'
      exact Nat.le_trans ih (topUpperTriSum_mono_b b T.length)

private theorem list_sum_le_map_upperTri (tOf : Nat → Nat) :
    ∀ L : List Nat, (∀ v ∈ L, v ≤ upperTri (tOf v)) →
      L.sum ≤ ((L.map tOf).map upperTri).sum
  | [], _ => Nat.le_refl 0
  | x :: xs, h => by
    have hx := h x (List.mem_cons_self ..)
    have ih := list_sum_le_map_upperTri tOf xs (fun v hv => h v (List.mem_cons_of_mem x hv))
    simp only [List.sum_cons, List.map_cons]
    omega

private theorem map_nodup_of_inj (tOf : Nat → Nat) :
    ∀ L : List Nat, L.Nodup →
      (∀ v ∈ L, ∀ w ∈ L, tOf v = tOf w → v = w) →
      (L.map tOf).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, hnd, hinj => by
    rw [List.nodup_cons] at hnd
    have ih := map_nodup_of_inj tOf xs hnd.2 (fun v hv w hw heq =>
      hinj v (List.mem_cons_of_mem x hv) w (List.mem_cons_of_mem x hw) heq)
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih⟩
    intro hm
    rw [List.mem_map] at hm
    obtain ⟨y, hy, hyx⟩ := hm
    have hxy : y = x := hinj y (List.mem_cons_of_mem x hy) x (List.mem_cons_self ..) hyx
    exact hnd.1 (hxy ▸ hy)

/-- Canonical first-moment capacity on `valuesThrough b`:
any `Nodup` list `L` of elements in `valuesThrough b` obeys
`L.sum ≤ topUpperTriSum b L.length` (sharp at `b = 1, 3`). -/
theorem canonical_distinct_sum_le_upperTri_top (b : Nat) (L : List Nat)
    (hnd : L.Nodup) (hmem : ∀ v ∈ L, v ∈ valuesThrough b) :
    L.sum ≤ topUpperTriSum b L.length := by
  let tOf : Nat → Nat := fun v =>
    if h : v ∈ valuesThrough b then Classical.choose (mem_valuesThrough_iff.mp h) else 0
  have htSpec : ∀ v ∈ L, tOf v ≤ b ∧ a (tOf v) = v := by
    intro v hv
    have hm := hmem v hv
    have hsp := Classical.choose_spec (mem_valuesThrough_iff.mp hm)
    have ht_eq : tOf v = Classical.choose (mem_valuesThrough_iff.mp hm) := dif_pos hm
    rwa [← ht_eq] at hsp
  have hle_ut : ∀ v ∈ L, v ≤ upperTri (tOf v) := by
    intro v hv
    have h := a_le_upperTri (tOf v)
    rwa [(htSpec v hv).2] at h
  have hndT : (L.map tOf).Nodup := map_nodup_of_inj tOf L hnd (fun v hv w hw heq => by
    rw [← (htSpec v hv).2, ← (htSpec w hw).2, heq])
  have hleT : ∀ t ∈ L.map tOf, t ≤ b := by
    intro t ht
    rw [List.mem_map] at ht
    obtain ⟨v, hv, rfl⟩ := ht
    exact (htSpec v hv).1
  have h1 := list_sum_le_map_upperTri tOf L hle_ut
  have h2 := nodup_sum_upperTri_le_top b (L.map tOf) hndT hleT
  rw [List.length_map] at h2
  exact Nat.le_trans h1 h2

end Recaman.CanonicalStepSpectrum
