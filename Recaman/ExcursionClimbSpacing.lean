import Recaman.SupplyExcursionSpacing

namespace Recaman.ExcursionClimbSpacing

open Recaman.SupplyExcursionSpacing
open Recaman.SupplyHeightWeightBudget Recaman.SupplyDescentWeight Recaman.SupplyDescentSlots
open Recaman.SupplyAreaCrossings Recaman.FloorSupplyPotential Recaman.FloorSupplyFreeBudget
open Recaman.LowTargetWeightedGap Recaman.LevelTriangleArea Recaman.AdditionRankSlack
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction
open Recaman.SuffixHallOwnerMap
open Classical

/-! # Double-ascent excursion 3-spacing budget

In `Recaman/SupplyExcursionSpacing.lean` (`E-785`), each supplied addition `t` at height
`r + 1` was charged against the exit of the downward excursion below `r` containing its
latest downward crossing `q(t)` of `p = floorPotential f n (r - 1)`.  Because
`floor_potential_step` gives `p (i + 1) = p i + Fw f (i + 1) - r`, the potential `p`
remains monotone non-increasing whenever `Fw f (i + 1) ≤ r` (not only `< r`).

Extending the excursion from below `r` to below `r + 1` (exiting at `d'` with
`Fw f d' = r`, `f d' = true`, `Fw f (d' + 1) = r + 1`), the preceding step `d₁ = d' - 1`
must lie in `[q(t), d']`, hence satisfies `Fw f d₁ ≤ r`, forcing
`Fw f d₁ = r - 1 ∧ f d₁ = true ∧ f (d₁ + 1) = true ∧ d₁ + 1 < n + K`.
Thus only genuine double-ascent (`AA`) exits `r - 1 → r → r + 1` can carry the two
overflow slots, strictly sharpening `E-785` (`2 * A_{r-1}` → `2 * doubleAscent(r - 1)`),
`E-653` (`E_{m+2} ≤ F_m` → `3 * E_{m+2} ≤ F_m + 2 * AA_m`), and `E-785`'s floor-plus-four
bound (`3 * E_{m+4} ≤ 8 * free` → `3 * E_{m+4} ≤ 6 * free + 2 * AA_{m+2}`).
-/

/-! ## Double-ascent counter and basic monotonicity/level bounds -/

/-- Count of in-window double-ascent transitions `h → h + 1 → h + 2` starting at `t ∈ [n, n + K)`
with `t + 1 < n + K`. -/
noncomputable def doubleAscent (f : Nat → Bool) (n K : Nat) (h : Int) : Nat :=
  cN (fun t => Fw f t = h ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < n + K) n K

private theorem doubleAscent_le_of_le (f : Nat → Bool) (n d K : Nat) (h : Int) (hd : d ≤ K) :
    doubleAscent f n d h ≤ doubleAscent f n K h := by
  unfold doubleAscent
  have h1 :
      cN (fun t => Fw f t = h ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < n + d) n d ≤
        cN (fun t => Fw f t = h ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < n + K) n d :=
    cN_mono _ _ n d (fun t _ _ ht => ⟨ht.1, ht.2.1, ht.2.2.1, by omega⟩)
  have h2 := cN_add (fun t => Fw f t = h ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < n + K) n d (K - d)
  rw [show d + (K - d) = K by omega] at h2
  omega

private theorem doubleAscent_le_levelAdditions_left (f : Nat → Bool) (n K : Nat) (h : Int) :
    doubleAscent f n K h ≤ levelAdditions f n K h := by
  unfold doubleAscent levelAdditions
  exact cN_mono _ _ n K (fun t _ _ ht => ⟨ht.1, ht.2.1⟩)

private theorem cN_shift_one (P : Nat → Prop) (n : Nat) :
    ∀ k, cN (fun t => P (t + 1)) n k = cN P (n + 1) k
  | 0 => rfl
  | k + 1 => by
    have ih := cN_shift_one P n k
    have heq : n + k + 1 = (n + 1) + k := by omega
    by_cases h : P ((n + 1) + k)
    · have h' : P (n + k + 1) := by rwa [heq]
      rw [cN_succ_pos _ n k h', cN_succ_pos _ (n + 1) k h, ih]
    · have h' : ¬ P (n + k + 1) := by rwa [heq]
      rw [cN_succ_neg _ n k h', cN_succ_neg _ (n + 1) k h, ih]

private theorem doubleAscent_le_levelAdditions_right (f : Nat → Bool) (n K : Nat) (h : Int) :
    doubleAscent f n K h ≤ levelAdditions f n K (h + 1) := by
  cases K with
  | zero =>
    unfold doubleAscent levelAdditions
    simp [cN]
  | succ k =>
    unfold doubleAscent levelAdditions
    have hlast :
        ¬ (Fw f (n + k) = h ∧ f (n + k) = true ∧ f (n + k + 1) = true ∧
          n + k + 1 < n + (k + 1)) := by
      intro ht
      omega
    rw [cN_succ_neg _ n k hlast]
    have hstep :
        cN (fun t => Fw f t = h ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < n + (k + 1)) n k ≤
          cN (fun t => Fw f (t + 1) = h + 1 ∧ f (t + 1) = true) n k := by
      apply cN_mono
      intro t _ _ ht
      have hFw : Fw f (t + 1) = h + 1 := by
        rcases fw_cases f t with ⟨hA, _⟩ | ⟨_, hS⟩
        · omega
        · rw [ht.2.1] at hS
          cases hS
      exact ⟨hFw, ht.2.2.1⟩
    rw [cN_shift_one (fun t => Fw f t = h + 1 ∧ f t = true) n k] at hstep
    have hsplit := cN_add (fun t => Fw f t = h + 1 ∧ f t = true) n 1 k
    rw [show 1 + k = k + 1 by omega] at hsplit
    omega

/-! ## Extended excursion helpers (staying `≤ r`, exiting to `r + 1`) -/

private theorem lastAbove_bounds (f : Nat → Bool) (n : Nat) (r : Int) :
    ∀ k, n ≤ lastAbove f n r k ∧ lastAbove f n r k ≤ n + k
  | 0 => ⟨Nat.le_refl n, Nat.le_refl n⟩
  | k + 1 => by
    unfold lastAbove
    split
    · omega
    · have ih := lastAbove_bounds f n r k
      omega

private theorem lastAbove_below_after (f : Nat → Bool) (n : Nat) (r : Int) :
    ∀ k i, lastAbove f n r k < i → i ≤ n + k → Fw f i < r
  | 0, i, h1, h2 => by unfold lastAbove at h1; omega
  | k + 1, i, h1, h2 => by
    unfold lastAbove at h1
    split at h1
    · omega
    · next hnot =>
      by_cases hi : i = n + k + 1
      · rw [hi]; omega
      · exact lastAbove_below_after f n r k i h1 (by omega)

private theorem lastAbove_gt_ge (f : Nat → Bool) (n : Nat) (r : Int) :
    ∀ k, n < lastAbove f n r k → r ≤ Fw f (lastAbove f n r k)
  | 0, h => by unfold lastAbove at h; omega
  | k + 1, h => by
    unfold lastAbove at h ⊢
    by_cases hge : r ≤ Fw f (n + k + 1)
    · rw [if_pos hge]
      exact hge
    · rw [if_neg hge] at h ⊢
      exact lastAbove_gt_ge f n r k h

private theorem lastAbove_lt_of_below (f : Nat → Bool) (n k q : Nat) (r : Int)
    (hnq : n < q) (hbel : ∀ i, q ≤ i → i ≤ n + k → Fw f i < r) :
    lastAbove f n r k < q := by
  by_cases h : lastAbove f n r k < q
  · exact h
  · have hgt : n < lastAbove f n r k := by omega
    have hge := lastAbove_gt_ge f n r k hgt
    have hle := (lastAbove_bounds f n r k).2
    have hlt := hbel (lastAbove f n r k) (by omega) hle
    omega

/-- `floorPotential f n (r - 1)` is non-increasing on every segment where `Fw f i ≤ r`. -/
private theorem potential_mono_le (f : Nat → Bool) (n : Nat) (r : Int) (a : Nat)
    (hna : n ≤ a) :
    ∀ len, (∀ i, a < i → i ≤ a + len → Fw f i ≤ r) →
      floorPotential f n (r - 1) (a + len) ≤ floorPotential f n (r - 1) a
  | 0, _ => Int.le_refl _
  | len + 1, hbel => by
    have ih := potential_mono_le f n r a hna len (fun i h1 h2 => hbel i h1 (by omega))
    have hstep := floor_potential_step f n (a + len) (r - 1) (by omega)
    have hle := hbel (a + len + 1) (by omega) (by omega)
    rw [show a + (len + 1) = a + len + 1 by omega]
    omega

/-- First exit from `Fw ≤ r` back to `r + 1` after a point `q < t` with `Fw f q < r` and
`Fw f t = r + 1`.  The penultimate index `d' - 1` is forced to be an `AA` climb
`r - 1 → r → r + 1`. -/
private theorem exists_extended_exit (f : Nat → Bool) (q t : Nat) (r : Int)
    (hqt : q < t) (hqF : Fw f q < r) (htF : Fw f t = r + 1) :
    ∃ d', q < d' ∧ d' < t ∧ Fw f (d' - 1) = r - 1 ∧ f (d' - 1) = true ∧
      Fw f d' = r ∧ f d' = true ∧ Fw f (d' + 1) = r + 1 ∧
      ∀ i, q ≤ i → i ≤ d' → Fw f i ≤ r := by
  let Q := fun i => q < i ∧ r + 1 ≤ Fw f i
  obtain ⟨e, het, hQe, hfirst⟩ := first_mark Q t ⟨t, Nat.le_refl t, hqt, by omega⟩
  have hprev : Fw f (e - 1) ≤ r := by
    by_cases h : q = e - 1
    · rw [← h]; omega
    · by_cases hge : r + 1 ≤ Fw f (e - 1)
      · exact (hfirst (e - 1) (by have := hQe.1; omega) ⟨by have := hQe.1; omega, hge⟩).elim
      · omega
  have hstep : Fw f (e - 1) = r ∧ f (e - 1) = true ∧ Fw f e = r + 1 := by
    rcases fw_cases f (e - 1) with ⟨hA, hfA⟩ | ⟨hS, _⟩
    · rw [show e - 1 + 1 = e by have := hQe.1; omega] at hA
      exact ⟨by have := hQe.2; omega, hfA, by have := hQe.2; omega⟩
    · rw [show e - 1 + 1 = e by have := hQe.1; omega] at hS
      have := hQe.2
      omega
  have hqd' : q < e - 1 := by
    by_cases h : q = e - 1
    · rw [← h] at hstep
      omega
    · have := hQe.1
      omega
  have hbel : ∀ i, q ≤ i → i ≤ e - 1 → Fw f i ≤ r := by
    intro i hqi hid
    by_cases h : i = q
    · rw [h]; omega
    · by_cases hge : r + 1 ≤ Fw f i
      · exact (hfirst i (by have := hQe.1; omega) ⟨by omega, hge⟩).elim
      · omega
  have hprev2 : Fw f (e - 1 - 1) ≤ r := hbel (e - 1 - 1) (by omega) (by omega)
  have hstep2 : Fw f (e - 1 - 1) = r - 1 ∧ f (e - 1 - 1) = true := by
    rcases fw_cases f (e - 1 - 1) with ⟨hA, hfA⟩ | ⟨hS, _⟩
    · rw [show e - 1 - 1 + 1 = e - 1 by omega] at hA
      exact ⟨by omega, hfA⟩
    · rw [show e - 1 - 1 + 1 = e - 1 by omega] at hS
      omega
  refine ⟨e - 1, hqd', by omega, hstep2.1, hstep2.2, hstep.1, hstep.2.1, ?_, hbel⟩
  rw [show e - 1 + 1 = e by have := hQe.1; omega]
  exact hstep.2.2

private theorem extended_exit_unique (f : Nat → Bool) (q d₁ d₂ : Nat) (r : Int)
    (hq₁ : q ≤ d₁) (he₁ : Fw f (d₁ + 1) = r + 1) (hb₁ : ∀ i, q ≤ i → i ≤ d₁ → Fw f i ≤ r)
    (hq₂ : q ≤ d₂) (he₂ : Fw f (d₂ + 1) = r + 1) (hb₂ : ∀ i, q ≤ i → i ≤ d₂ → Fw f i ≤ r) :
    d₁ = d₂ := by
  rcases Nat.lt_trichotomy d₁ d₂ with hlt | heq | hgt
  · have := hb₂ (d₁ + 1) (by omega) (by omega)
    omega
  · exact heq
  · have := hb₁ (d₂ + 1) (by omega) (by omega)
    omega

/-! ## List helper lemmas for the 3-for-1 injection -/

private noncomputable def idxMarks (P : Nat → Prop) (n K : Nat) : List Nat :=
  (List.range K).filter (fun i => @decide (P (n + i)) (Classical.propDecidable _))

private theorem mem_idxMarks (P : Nat → Prop) (n K i : Nat) :
    i ∈ idxMarks P n K ↔ i < K ∧ P (n + i) := by
  simp [idxMarks]

private theorem count_eq_idxMarks_length (P : Nat → Prop) (n : Nat) :
    ∀ K, cN P n K = (idxMarks P n K).length
  | 0 => rfl
  | k + 1 => by
    have ih := count_eq_idxMarks_length P n k
    by_cases h : P (n + k)
    · rw [cN_succ_pos P n k h, ih]
      simp [idxMarks, List.range_succ, List.filter_append, h]
    · rw [cN_succ_neg P n k h, ih]
      simp [idxMarks, List.range_succ, List.filter_append, h]

private theorem triple_flatMap_length (L : List Nat) :
    (L.flatMap (fun i => [(i, 0), (i, 1), (i, 2)])).length = 3 * L.length := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp [List.flatMap_cons, ih]
    omega

private theorem pair_flatMap_length (L : List Nat) (n : Nat) :
    (L.flatMap (fun i => [(n + i, 0), (n + i, 1)])).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp [List.flatMap_cons, ih]
    omega

private theorem triple_flatMap_nodup (L : List Nat) (hnd : L.Nodup) :
    (L.flatMap (fun i => [(i, 0), (i, 1), (i, 2)])).Nodup := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    have hrest := ih hnd.2
    have hnot : ∀ k : Nat, (x, k) ∉ xs.flatMap (fun i => [(i, 0), (i, 1), (i, 2)]) := by
      intro k hmem
      rw [List.mem_flatMap] at hmem
      obtain ⟨y, hy, hpair⟩ := hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hpair
      rcases hpair with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact hnd.1 hy
    rw [List.flatMap_cons, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
    rw [List.nodup_cons, List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, hnot 2, hrest⟩
    · intro h
      simp only [List.mem_cons] at h
      rcases h with h0 | h1 | h2
      · cases h0
      · cases h1
      · exact hnot 0 h2
    · intro h
      simp only [List.mem_cons] at h
      rcases h with h1 | h2
      · cases h1
      · exact hnot 1 h2

/-! ## 3-for-1 slot injection charging overflows solely to `AA` climbs -/

/-- Every supplied addition at height `r + 1` occupies three distinct slots across
`descentSlots f n r K` and two overflow slots per in-window double-ascent (`AA`)
transition `r - 1 → r → r + 1`. -/
theorem actual_same_height_supply_aa_slots (f : Nat → Bool) (n a K : Nat) (r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true) :
    3 * cN (fun t => Fw f t = r + 1 ∧ EndN f 0 t) n K ≤
      (descentSlots f n r K).length + 2 * doubleAscent f n K (r - 1) := by
  let p := floorPotential f n (r - 1)
  let P := fun t => Fw f t = r + 1 ∧ EndN f 0 t
  let Q := fun t => Fw f t = r - 1 ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < n + K
  let Good := fun t => n ≤ t ∧ t < n + K ∧ P t
  have hdata (t : Nat) (ht : Good t) :
      ∃ q d', n < q ∧ q < d' ∧ d' < t ∧ Fw f (d' - 1) = r - 1 ∧ f (d' - 1) = true ∧
        Fw f d' = r ∧ f d' = true ∧ Fw f (d' + 1) = r + 1 ∧
        (∀ i, q ≤ i → i ≤ d' → Fw f i ≤ r) ∧
        areaCrossesDown p (p t) q ∧
        (∀ j, q < j → j < t → ¬ areaCrossesDown p (p t) j) := by
    obtain ⟨hnt, _, hF, he⟩ := ht
    obtain ⟨q, hnq, hqt, hqF, hcross, hafter⟩ :=
      latest_actual_supply_area_crossing f n a t r hw hpre hnt hF he
    obtain ⟨d', hqd', hd't, hd1F, hd1A, hd'F, hd'A, hd'Exit, hbel⟩ :=
      exists_extended_exit f q t r hqt hqF hF
    exact ⟨q, d', hnq, hqd', hd't, hd1F, hd1A, hd'F, hd'A, hd'Exit, hbel, hcross, hafter⟩
  let qOf := fun t => if h : Good t then Classical.choose (hdata t h) else n
  let dOf := fun t => if h : Good t then Classical.choose (Classical.choose_spec (hdata t h)) else n
  have hSpec (t : Nat) (ht : Good t) :
      n < qOf t ∧ qOf t < dOf t ∧ dOf t < t ∧ Fw f (dOf t - 1) = r - 1 ∧ f (dOf t - 1) = true ∧
        Fw f (dOf t) = r ∧ f (dOf t) = true ∧ Fw f (dOf t + 1) = r + 1 ∧
        (∀ i, qOf t ≤ i → i ≤ dOf t → Fw f i ≤ r) ∧
        areaCrossesDown p (p t) (qOf t) ∧
        (∀ j, qOf t < j → j < t → ¬ areaCrossesDown p (p t) j) := by
    simp only [qOf, dOf, dif_pos ht]
    exact Classical.choose_spec (Classical.choose_spec (hdata t ht))
  have hEntry (t : Nat) (ht : Good t) :
      let d' := dOf t
      let a0 := lastAbove f n (r + 1) (d' - n)
      n ≤ a0 ∧ a0 < qOf t ∧ a0 ≤ d' ∧
        (∀ i, a0 < i → i ≤ d' → Fw f i ≤ r) ∧
        p d' < p t ∧ p t ≤ p a0 := by
    obtain ⟨hnq, hqd', _, _, _, _, _, _, hbel, hcross, _⟩ := hSpec t ht
    have hab := lastAbove_bounds f n (r + 1) (dOf t - n)
    have hlt := lastAbove_lt_of_below f n (dOf t - n) (qOf t) (r + 1) hnq (by
      intro i hi1 hi2
      have := hbel i hi1 (by omega)
      omega)
    have hbelA : ∀ i, lastAbove f n (r + 1) (dOf t - n) < i → i ≤ dOf t → Fw f i ≤ r := by
      intro i hi1 hi2
      have := lastAbove_below_after f n (r + 1) (dOf t - n) i hi1 (by omega)
      omega
    have hpd : p (dOf t) ≤ p (qOf t) := by
      have h := potential_mono_le f n r (qOf t) (by omega) (dOf t - qOf t) (by
        intro i hi1 hi2; exact hbel i (by omega) (by omega))
      rwa [Nat.add_sub_cancel' (by omega)] at h
    have hpa : p (qOf t - 1) ≤ p (lastAbove f n (r + 1) (dOf t - n)) := by
      have h := potential_mono_le f n r (lastAbove f n (r + 1) (dOf t - n)) hab.1
        (qOf t - 1 - lastAbove f n (r + 1) (dOf t - n)) (by
          intro i hi1 hi2; exact hbelA i hi1 (by omega))
      rwa [Nat.add_sub_cancel' (by omega)] at h
    have hc1 : p (qOf t) < p t := hcross.1
    have hc2 : p t ≤ p (qOf t - 1) := hcross.2
    exact ⟨hab.1, hlt, by omega, hbelA, by omega, by omega⟩
  have hCross (t k : Nat) (ht : Good t)
      (hle : p t + (k : Int) ≤ p (lastAbove f n (r + 1) (dOf t - n))) :
      ∃ q', lastAbove f n (r + 1) (dOf t - n) < q' ∧ q' ≤ dOf t ∧
        areaCrossesDown p (p t + (k : Int)) q' := by
    obtain ⟨_, _, had, _, hpdt, _⟩ := hEntry t ht
    exact downcross_from_end_values p (lastAbove f n (r + 1) (dOf t - n)) (dOf t)
      (p t + (k : Int)) had hle (by omega)
  let phi : Nat × Nat → Sum (Nat × Int) (Nat × Nat) := fun pair =>
    let t := n + pair.1
    let k := pair.2
    if ht : Good t then
      let d' := dOf t
      let a0 := lastAbove f n (r + 1) (d' - n)
      if hle : p t + (k : Int) ≤ p a0 then
        Sum.inl (Classical.choose (hCross t k ht hle), p t + (k : Int))
      else
        Sum.inr (d' - 1, (p t + (k : Int) - p a0 - 1).toNat)
    else
      Sum.inr (n, 0)
  let dom := (idxMarks P n K).flatMap (fun i => [(i, 0), (i, 1), (i, 2)])
  let exits := idxMarks Q n K
  let target : List (Sum (Nat × Int) (Nat × Nat)) :=
    (descentSlots f n r K).map Sum.inl ++
      (exits.flatMap (fun i => [(n + i, 0), (n + i, 1)])).map Sum.inr
  have hdom_mem : ∀ pair, pair ∈ dom → pair.1 < K ∧ P (n + pair.1) ∧ pair.2 ≤ 2 := by
    intro pair hmem
    simp only [dom, List.mem_flatMap, mem_idxMarks, List.mem_cons, List.not_mem_nil, or_false] at hmem
    obtain ⟨i, ⟨hiK, hiP⟩, hpair⟩ := hmem
    rcases hpair with rfl | rfl | rfl <;> exact ⟨hiK, hiP, by omega⟩
  have hsub : dom.map phi ⊆ target := by
    intro y hy
    obtain ⟨pair, hpm, rfl⟩ := List.mem_map.mp hy
    obtain ⟨hiK, hiP, hk2⟩ := hdom_mem pair hpm
    have ht : Good (n + pair.1) := ⟨by omega, by omega, hiP⟩
    dsimp only [phi]
    rw [dif_pos ht]
    split
    · next hle =>
      apply List.mem_append_left
      apply List.mem_map.mpr
      obtain ⟨haq, hqd', hcr⟩ := Classical.choose_spec (hCross (n + pair.1) pair.2 ht hle)
      obtain ⟨_, _, hd't, _, _, _, _, _, _, _, _⟩ := hSpec (n + pair.1) ht
      obtain ⟨hna, _, _, _, _, _⟩ := hEntry (n + pair.1) ht
      refine ⟨(Classical.choose (hCross (n + pair.1) pair.2 ht hle), p (n + pair.1) + (pair.2 : Int)), ?_, rfl⟩
      exact crossing_mem_descent_slots f n K _ r _ (by omega) (by omega) hcr
    · next hnot =>
      apply List.mem_append_right
      apply List.mem_map.mpr
      obtain ⟨hnq, hqd', hd't, hd1F, hd1A, _, hd'A, _, _, _, _⟩ := hSpec (n + pair.1) ht
      obtain ⟨_, _, _, _, _, hpta⟩ := hEntry (n + pair.1) ht
      let d' := dOf (n + pair.1)
      let d1 := d' - 1
      let j := (p (n + pair.1) + (pair.2 : Int) - p (lastAbove f n (r + 1) (d' - n)) - 1).toNat
      refine ⟨(d1, j), ?_, rfl⟩
      simp only [List.mem_flatMap, exits, mem_idxMarks]
      refine ⟨d1 - n, ⟨by omega, ?_⟩, ?_⟩
      · rw [Nat.add_sub_cancel' (show n ≤ d1 by omega)]
        refine ⟨hd1F, hd1A, ?_, by omega⟩
        rw [show d1 + 1 = d' by omega]
        exact hd'A
      · rw [Nat.add_sub_cancel' (show n ≤ d1 by omega)]
        have hj : j = 0 ∨ j = 1 := by
          dsimp only [j, d']
          omega
        rcases hj with h0 | h1
        · simp [h0]
        · simp [h1]
  have hnd_dom : dom.Nodup :=
    triple_flatMap_nodup (idxMarks P n K) (List.nodup_range.filter _)
  have hinj : ∀ x ∈ dom, ∀ y ∈ dom, phi x = phi y → x = y := by
    intro x hx y hy hxy
    obtain ⟨hxK, hxP, hxk⟩ := hdom_mem x hx
    obtain ⟨hyK, hyP, hyk⟩ := hdom_mem y hy
    have htx : Good (n + x.1) := ⟨by omega, by omega, hxP⟩
    have hty : Good (n + y.1) := ⟨by omega, by omega, hyP⟩
    have hkey : dOf (n + x.1) = dOf (n + y.1) ∧
        p (n + x.1) + (x.2 : Int) = p (n + y.1) + (y.2 : Int) := by
      dsimp only [phi] at hxy
      rw [dif_pos htx, dif_pos hty] at hxy
      split at hxy <;> split at hxy
      · next hlex hley =>
        injection hxy with hpair
        have hqeq : Classical.choose (hCross (n + x.1) x.2 htx hlex) =
            Classical.choose (hCross (n + y.1) y.2 hty hley) := congrArg Prod.fst hpair
        have hveq : p (n + x.1) + (x.2 : Int) = p (n + y.1) + (y.2 : Int) := congrArg Prod.snd hpair
        obtain ⟨hax, hqx, _⟩ := Classical.choose_spec (hCross (n + x.1) x.2 htx hlex)
        obtain ⟨hay, hqy, _⟩ := Classical.choose_spec (hCross (n + y.1) y.2 hty hley)
        obtain ⟨_, _, _, _, _, _, _, hEx, _, _, _⟩ := hSpec (n + x.1) htx
        obtain ⟨_, _, _, _, _, _, _, hEy, _, _, _⟩ := hSpec (n + y.1) hty
        obtain ⟨_, _, _, hBx, _, _⟩ := hEntry (n + x.1) htx
        obtain ⟨_, _, _, hBy, _, _⟩ := hEntry (n + y.1) hty
        have hdeq := extended_exit_unique f (Classical.choose (hCross (n + x.1) x.2 htx hlex))
          (dOf (n + x.1)) (dOf (n + y.1)) r hqx hEx
          (fun i hi1 hi2 => hBx i (by omega) hi2)
          (by rw [hqeq]; exact hqy) hEy
          (fun i hi1 hi2 => hBy i (by omega) hi2)
        exact ⟨hdeq, hveq⟩
      · cases hxy
      · cases hxy
      · next hnx hny =>
        injection hxy with hpair
        have hd1eq : dOf (n + x.1) - 1 = dOf (n + y.1) - 1 := congrArg Prod.fst hpair
        obtain ⟨hnqx, hqdx, _, _, _, _, _, _, _, _, _⟩ := hSpec (n + x.1) htx
        obtain ⟨hnqy, hqdy, _, _, _, _, _, _, _, _, _⟩ := hSpec (n + y.1) hty
        have hdeq : dOf (n + x.1) = dOf (n + y.1) := by omega
        have hjeq : (p (n + x.1) + (x.2 : Int) - p (lastAbove f n (r + 1) (dOf (n + x.1) - n)) - 1).toNat =
            (p (n + y.1) + (y.2 : Int) - p (lastAbove f n (r + 1) (dOf (n + y.1) - n)) - 1).toNat :=
          congrArg Prod.snd hpair
        rw [hdeq] at hjeq hnx
        refine ⟨hdeq, ?_⟩
        omega
    obtain ⟨hdeq, hveq⟩ := hkey
    have hfst : x.1 = y.1 := by
      rcases Nat.lt_trichotomy x.1 y.1 with hlt | heq | hgt
      · obtain ⟨_, _, hdxt, _, _, _, _, _, _, _, _⟩ := hSpec (n + x.1) htx
        obtain ⟨_, hqyd, _, _, _, _, _, _, _, _, haftery⟩ := hSpec (n + y.1) hty
        have hspace := supply_potential_spacing_after_last_crossing f n (n + x.1) (n + y.1)
          (qOf (n + y.1)) r (by omega) (by omega) (by omega) hxP.1 hyP.1 hxP.2.1 haftery
        change p (n + x.1) + 3 ≤ p (n + y.1) at hspace
        omega
      · exact heq
      · obtain ⟨_, _, hdyt, _, _, _, _, _, _, _, _⟩ := hSpec (n + y.1) hty
        obtain ⟨_, hqxd, _, _, _, _, _, _, _, _, hafterx⟩ := hSpec (n + x.1) htx
        have hspace := supply_potential_spacing_after_last_crossing f n (n + y.1) (n + x.1)
          (qOf (n + x.1)) r (by omega) (by omega) (by omega) hyP.1 hxP.1 hyP.2.1 hafterx
        change p (n + y.1) + 3 ≤ p (n + x.1) at hspace
        omega
    have hsnd : x.2 = y.2 := by
      rw [hfst] at hveq
      omega
    exact Prod.ext hfst hsnd
  have hnd_img := nodup_map_of_inj dom phi hnd_dom hinj
  have hlen := hnd_img.length_le_of_subset hsub
  rw [List.length_map] at hlen
  have hdom_len : dom.length = 3 * cN P n K := by
    rw [triple_flatMap_length, count_eq_idxMarks_length]
  have htgt_len : target.length = (descentSlots f n r K).length + 2 * doubleAscent f n K (r - 1) := by
    simp only [target, List.length_append, List.length_map, pair_flatMap_length, exits,
      doubleAscent, Q, count_eq_idxMarks_length]
  change 3 * cN P n K ≤ (descentSlots f n r K).length + 2 * doubleAscent f n K (r - 1)
  omega

/-! ## Weight budget and strict sharpenings of E-785 and E-653 -/

/-- Arbitrary-height, arbitrary-interval 3-spacing weight budget charging overflows
only to in-window double-ascent (`AA`) exits at `r - 1`, strictly strengthening `E-785`. -/
theorem same_height_supply_aa_spacing_budget (f : Nat → Bool) (n a K : Nat) (r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true) :
    3 * (cN (fun t => Fw f t = r + 1 ∧ EndN f 0 t) n K : Int) ≤
      lowAdditionWeights f n r K + 2 * (doubleAscent f n K (r - 1) : Int) := by
  let P := fun t => Fw f t = r + 1 ∧ EndN f 0 t
  obtain ⟨d, hd, hlast, hafter⟩ := last_markN P n K
  have htail : cN P (n + d) (K - d) = 0 := by
    apply cN_zero_of
    intro i hi hiK
    have h := hafter (i - n) (by omega) (by omega)
    rwa [show n + (i - n) = i by omega] at h
  have hc := cN_add P n d (K - d)
  rw [show d + (K - d) = K by omega, htail, Nat.add_zero] at hc
  by_cases hz : d = 0
  · rw [hz] at hc
    change cN P n K = 0 at hc
    have hnonneg := low_weights_nonnegative f n r K
    change 3 * (cN P n K : Int) ≤ _
    rw [hc]
    omega
  · have hp := hlast.resolve_left hz
    have htA := hp.2.1
    have hend : r ≤ Fw f (n + d) := by
      rcases fw_cases f (n + d - 1) with ⟨h, _⟩ | ⟨_, h⟩
      · rw [show n + d - 1 + 1 = n + d by omega] at h
        have := hp.1
        omega
      · rw [htA] at h
        cases h
    have hslots := actual_same_height_supply_aa_slots f n a d r hw hpre
    have hsum := descent_slots_exact_weight f n r d
    have h0 : 0 ≤ belowTriangle r (Fw f n) := by
      unfold belowTriangle
      exact Int.mul_nonneg (Int.le_max_left _ _)
        (by have := Int.le_max_left 0 (r - Fw f n); omega)
    have h1 : belowTriangle r (Fw f (n + d)) = 0 := by
      simp [belowTriangle, Int.max_eq_left (show r - Fw f (n + d) ≤ 0 by omega)]
    rw [h1] at hsum
    have hsplitW := low_weights_append f n r d (K - d)
    rw [show d + (K - d) = K by omega] at hsplitW
    have hnonnegW := low_weights_nonnegative f (n + d) r (K - d)
    have hmonoAA := doubleAscent_le_of_le f n d K (r - 1) hd
    change cN P n K = cN P n d at hc
    change 3 * cN P n d ≤ (descentSlots f n r d).length + 2 * doubleAscent f n d (r - 1) at hslots
    change 3 * (cN P n K : Int) ≤ lowAdditionWeights f n r K + 2 * (doubleAscent f n K (r - 1) : Int)
    omega

/-- Level-count corollary bounding the overflow by `min(A_{r-1}, A_r)`. -/
theorem same_height_supply_min_level_budget (f : Nat → Bool) (n a K : Nat) (r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true) :
    3 * (levelSupplied f n K (r + 1) : Int) ≤
      lowAdditionWeights f n r K +
        2 * (Nat.min (levelAdditions f n K (r - 1)) (levelAdditions f n K r) : Int) := by
  have hb := same_height_supply_aa_spacing_budget f n a K r hw hpre
  have hL := doubleAscent_le_levelAdditions_left f n K (r - 1)
  have hR := doubleAscent_le_levelAdditions_right f n K (r - 1)
  rw [show r - 1 + 1 = r by omega] at hR
  have hmin : doubleAscent f n K (r - 1) ≤
      Nat.min (levelAdditions f n K (r - 1)) (levelAdditions f n K r) :=
    Nat.le_min.mpr ⟨hL, hR⟩
  unfold levelSupplied
  omega

/-- Zero-overflow spacing budget whenever no in-window `AA` climb leaves `r - 1`. -/
theorem as_plateau_no_overflow_budget (f : Nat → Bool) (n a K : Nat) (r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hnoAA : doubleAscent f n K (r - 1) = 0) :
    3 * (levelSupplied f n K (r + 1) : Int) ≤ lowAdditionWeights f n r K := by
  have hb := same_height_supply_aa_spacing_budget f n a K r hw hpre
  rw [hnoAA] at hb
  unfold levelSupplied
  omega

private theorem lowAdditionWeights_floor_succ (f : Nat → Bool) (n K : Nat) (m : Int)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    lowAdditionWeights f n (m + 1) K = (levelAdditions f n K m : Int) := by
  induction K with
  | zero =>
    simp [lowAdditionWeights, levelAdditions, cN]
  | succ k ih =>
    have hfk : ∀ i, n ≤ i → i ≤ n + k → m ≤ Fw f i := fun i h1 h2 => hfloor i h1 (by omega)
    have hbase := ih hfk
    have hmin := hfloor (n + k) (by omega) (by omega)
    rw [lowAdditionWeights, hbase]
    unfold levelAdditions
    by_cases h : Fw f (n + k) = m ∧ f (n + k) = true
    · rw [cN_succ_pos _ n k h]
      have hlw : lowAdditionWeight f (m + 1) (n + k) = 1 := by
        unfold lowAdditionWeight
        rw [if_pos ⟨h.2, by omega⟩]
        omega
      rw [hlw]
      push_cast
      omega
    · rw [cN_succ_neg _ n k h]
      have hlw : lowAdditionWeight f (m + 1) (n + k) = 0 := by
        unfold lowAdditionWeight
        rw [if_neg (fun ht => h ⟨by omega, ht.1⟩)]
      rw [hlw]
      omega

/-- Strictly sharpens `E-653` (`actual_floor_supply_count`: `E_{m+2} ≤ F_m`) to
`3 * E_{m+2} ≤ F_m + 2 * AA_m`, saving `2/3` of a supply slot per floor `(AS)` bounce. -/
theorem floor_plus_two_aa_budget (f : Nat → Bool) (n a K : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    3 * levelSupplied f n K (m + 2) ≤ levelFree f n K m + 2 * doubleAscent f n K m := by
  have hb := same_height_supply_aa_spacing_budget f n a K (m + 1) hw hpre
  have hW := lowAdditionWeights_floor_succ f n K m hfloor
  rw [hW, show m + 1 - 1 = m by omega, show m + 1 + 1 = m + 2 by omega] at hb
  have hAeqF : levelAdditions f n K m = levelFree f n K m := by
    unfold levelAdditions levelFree
    apply cN_congr
    intro t hnt htK
    constructor
    · intro ht
      refine ⟨ht.1, ht.2, ?_⟩
      exact block_prefix_low_clock_not_endable f n a t hw hpre hnt m
        (fun i hi hj => hfloor i hi (by omega)) (by omega)
    · intro ht
      exact ⟨ht.1, ht.2.1⟩
  rw [hAeqF] at hb
  change 3 * (levelSupplied f n K (m + 2) : Int) ≤
    (levelFree f n K m : Int) + 2 * (doubleAscent f n K m : Int) at hb
  omega

/-- Strictly sharpens `E-785`'s `actual_floor_plus_four_three_spacing`
(`3 * E_{m+4} ≤ 8 * free`) to `3 * E_{m+4} ≤ 6 * free + 2 * AA_{m+2}`. -/
theorem actual_floor_plus_four_aa_budget (f : Nat → Bool) (n a K : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    3 * levelSupplied f n K (m + 4) ≤ 6 * free f n K + 2 * doubleAscent f n K (m + 2) := by
  have hb := same_height_supply_aa_spacing_budget f n a K (m + 3) hw hpre
  have hW := low_weights_le_six_free f n a K m (m + 3) hw hpre hfloor (by omega)
  rw [show m + 3 + 1 = m + 4 by omega, show m + 3 - 1 = m + 2 by omega] at hb
  change 3 * (levelSupplied f n K (m + 4) : Int) ≤ _ at hb
  omega

end Recaman.ExcursionClimbSpacing
