import Recaman.SupplyHeightWeightBudget

namespace Recaman.SupplyExcursionSpacing

open Recaman.SupplyHeightWeightBudget Recaman.SupplyDescentWeight Recaman.SupplyDescentSlots
open Recaman.SupplyAreaCrossings Recaman.FloorSupplyPotential Recaman.FloorSupplyFreeBudget
open Recaman.LowTargetWeightedGap Recaman.LevelTriangleArea Recaman.AdditionRankSlack
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction
open Recaman.SuffixHallOwnerMap
open Classical

/-! # Excursion 3-spacing budget and dyadic height-weighted capacity

Every supplied addition `t` at height `r + 1` after a `BlockWord` prefix has a
latest downward crossing `q(t)` of the source-level potential below height `r`.
Assigning `t` to the unique exit `d(t)` of the downward excursion below `r`
containing `q(t)` (where `Fw f (d t) = r - 1` and `f (d t) = true`), any two
supplied additions `t < u` sharing an excursion exit satisfy `q(u) ≤ d(t) < t`,
so `supply_potential_spacing_after_last_crossing` forces `p t + 3 ≤ p u`.

Injecting `(t, 0), (t, 1), (t, 2)` into `descentSlots f n r K` plus two overflow
slots per exit `d` proves the arbitrary-height, arbitrary-interval 3-spacing
budget
  `3 * E_{r+1} ≤ lowAdditionWeights f n r K + 2 * A_{r-1}`,
strictly strengthening `E-674` (`same_height_supply_weight_budget`).

Consequences proved below:
- `actual_floor_plus_four_three_spacing`: `3 * E_{m+4} ≤ 8 * free f n K`
  (improving `E-674`'s `E_{m+4} ≤ 6 * free f n K`).
- `dyadic_height_weighted_capacity`: `dyadicAdditions f n K m H ≤ 3 * dyadicFree f n K m H`,
  proving a uniform geometric capacity at `q = 1/2` on actual `EndN` (strictly
  separating actual `EndN` from the relaxed `E-674` cone barrier `q < 0.4534` of `E-775`).
- `actual_height_exp_two_bound`: `A_{m+h} ≤ 3 * 2^h * free f n K` for every `h : Nat`.
-/

/-! ## Level counts and dyadic sums -/

noncomputable def levelAdditions (f : Nat → Bool) (n K : Nat) (h : Int) : Nat :=
  cN (fun t => Fw f t = h ∧ f t = true) n K

noncomputable def levelSupplied (f : Nat → Bool) (n K : Nat) (h : Int) : Nat :=
  cN (fun t => Fw f t = h ∧ EndN f 0 t) n K

noncomputable def levelFree (f : Nat → Bool) (n K : Nat) (h : Int) : Nat :=
  cN (fun t => Fw f t = h ∧ f t = true ∧ ¬ EndN f 0 t) n K

noncomputable def dyadicSum (g : Nat → Nat) : Nat → Nat
  | 0 => g 0
  | H + 1 => 2 * dyadicSum g H + g (H + 1)

noncomputable def dyadicAdditions (f : Nat → Bool) (n K : Nat) (m : Int) (H : Nat) : Nat :=
  dyadicSum (fun h => levelAdditions f n K (m + (h : Int))) H

noncomputable def dyadicSupplied (f : Nat → Bool) (n K : Nat) (m : Int) (H : Nat) : Nat :=
  dyadicSum (fun h => levelSupplied f n K (m + (h : Int))) H

noncomputable def dyadicFree (f : Nat → Bool) (n K : Nat) (m : Int) (H : Nat) : Nat :=
  dyadicSum (fun h => levelFree f n K (m + (h : Int))) H

/-! ## Excursion entry and exit helpers -/

/-- Last index in `[n, n + k]` with `r ≤ Fw f i`, or `n` if none exceeds `n`. -/
def lastAbove (f : Nat → Bool) (n : Nat) (r : Int) : Nat → Nat
  | 0 => n
  | k + 1 => if r ≤ Fw f (n + k + 1) then n + k + 1 else lastAbove f n r k

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

private theorem potential_mono_below (f : Nat → Bool) (n : Nat) (r : Int) (a : Nat)
    (hna : n ≤ a) :
    ∀ len, (∀ i, a < i → i ≤ a + len → Fw f i < r) →
      floorPotential f n (r - 1) (a + len) ≤ floorPotential f n (r - 1) a
  | 0, _ => Int.le_refl _
  | len + 1, hbel => by
    have ih := potential_mono_below f n r a hna len (fun i h1 h2 => hbel i h1 (by omega))
    have hstep := floor_potential_step f n (a + len) (r - 1) (by omega)
    have hlt := hbel (a + len + 1) (by omega) (by omega)
    rw [show a + (len + 1) = a + len + 1 by omega]
    omega

private theorem exists_excursion_exit (f : Nat → Bool) (q t : Nat) (r : Int)
    (hqt : q < t) (hqF : Fw f q < r) (htF : Fw f t = r + 1) :
    ∃ d, q ≤ d ∧ d < t ∧ Fw f d = r - 1 ∧ f d = true ∧ Fw f (d + 1) = r ∧
      ∀ i, q ≤ i → i ≤ d → Fw f i < r := by
  let Q := fun i => q < i ∧ r ≤ Fw f i
  obtain ⟨e, het, hQe, hfirst⟩ := first_mark Q t ⟨t, Nat.le_refl t, hqt, by omega⟩
  have hprev : Fw f (e - 1) < r := by
    by_cases h : q = e - 1
    · rwa [← h]
    · by_cases hge : r ≤ Fw f (e - 1)
      · exact (hfirst (e - 1) (by have := hQe.1; omega) ⟨by have := hQe.1; omega, hge⟩).elim
      · omega
  have hstep : Fw f (e - 1) = r - 1 ∧ f (e - 1) = true ∧ Fw f e = r := by
    rcases fw_cases f (e - 1) with ⟨hA, hfA⟩ | ⟨hS, _⟩
    · rw [show e - 1 + 1 = e by have := hQe.1; omega] at hA
      exact ⟨by have := hQe.2; omega, hfA, by have := hQe.2; omega⟩
    · rw [show e - 1 + 1 = e by have := hQe.1; omega] at hS
      have := hQe.2
      omega
  refine ⟨e - 1, by have := hQe.1; omega, by omega, hstep.1, hstep.2.1, ?_, ?_⟩
  · rw [show e - 1 + 1 = e by have := hQe.1; omega]
    exact hstep.2.2
  · intro i hqi hid
    by_cases h : i = q
    · rwa [h]
    · by_cases hge : r ≤ Fw f i
      · exact (hfirst i (by have := hQe.1; omega) ⟨by omega, hge⟩).elim
      · omega

private theorem excursion_exit_unique (f : Nat → Bool) (q d₁ d₂ : Nat) (r : Int)
    (hq₁ : q ≤ d₁) (he₁ : Fw f (d₁ + 1) = r) (hb₁ : ∀ i, q ≤ i → i ≤ d₁ → Fw f i < r)
    (hq₂ : q ≤ d₂) (he₂ : Fw f (d₂ + 1) = r) (hb₂ : ∀ i, q ≤ i → i ≤ d₂ → Fw f i < r) :
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

/-! ## 3-for-1 slot injection on arbitrary heights -/

/-- Every supplied addition at height `r + 1` occupies three distinct slots
across `descentSlots f n r K` and two overflow slots per exit addition at `r - 1`. -/
theorem actual_same_height_supply_three_slots (f : Nat → Bool) (n a K : Nat) (r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true) :
    3 * cN (fun t => Fw f t = r + 1 ∧ EndN f 0 t) n K ≤
      (descentSlots f n r K).length +
        2 * cN (fun t => Fw f t = r - 1 ∧ f t = true) n K := by
  let p := floorPotential f n (r - 1)
  let P := fun t => Fw f t = r + 1 ∧ EndN f 0 t
  let Q := fun t => Fw f t = r - 1 ∧ f t = true
  let Good := fun t => n ≤ t ∧ t < n + K ∧ P t
  have hdata (t : Nat) (ht : Good t) :
      ∃ q d, n < q ∧ q ≤ d ∧ d < t ∧ Fw f d = r - 1 ∧ f d = true ∧ Fw f (d + 1) = r ∧
        (∀ i, q ≤ i → i ≤ d → Fw f i < r) ∧
        areaCrossesDown p (p t) q ∧
        (∀ j, q < j → j < t → ¬ areaCrossesDown p (p t) j) := by
    obtain ⟨hnt, _, hF, he⟩ := ht
    obtain ⟨q, hnq, hqt, hqF, hcross, hafter⟩ :=
      latest_actual_supply_area_crossing f n a t r hw hpre hnt hF he
    obtain ⟨d, hqd, hdt, hdF, hdA, hdExit, hbel⟩ :=
      exists_excursion_exit f q t r hqt hqF hF
    exact ⟨q, d, hnq, hqd, hdt, hdF, hdA, hdExit, hbel, hcross, hafter⟩
  let qOf := fun t => if h : Good t then Classical.choose (hdata t h) else n
  let dOf := fun t => if h : Good t then Classical.choose (Classical.choose_spec (hdata t h)) else n
  have hSpec (t : Nat) (ht : Good t) :
      n < qOf t ∧ qOf t ≤ dOf t ∧ dOf t < t ∧ Fw f (dOf t) = r - 1 ∧ f (dOf t) = true ∧
        Fw f (dOf t + 1) = r ∧ (∀ i, qOf t ≤ i → i ≤ dOf t → Fw f i < r) ∧
        areaCrossesDown p (p t) (qOf t) ∧
        (∀ j, qOf t < j → j < t → ¬ areaCrossesDown p (p t) j) := by
    simp only [qOf, dOf, dif_pos ht]
    exact Classical.choose_spec (Classical.choose_spec (hdata t ht))
  have hEntry (t : Nat) (ht : Good t) :
      let d := dOf t
      let a0 := lastAbove f n r (d - n)
      n ≤ a0 ∧ a0 < qOf t ∧ a0 ≤ d ∧
        (∀ i, a0 < i → i ≤ d → Fw f i < r) ∧
        p d < p t ∧ p t ≤ p a0 := by
    obtain ⟨hnq, hqd, _, _, _, _, hbel, hcross, _⟩ := hSpec t ht
    have hdn : n + (dOf t - n) = dOf t := by omega
    have hab := lastAbove_bounds f n r (dOf t - n)
    have hlt := lastAbove_lt_of_below f n (dOf t - n) (qOf t) r hnq (by
      intro i hi1 hi2; exact hbel i hi1 (by omega))
    have hbelA : ∀ i, lastAbove f n r (dOf t - n) < i → i ≤ dOf t → Fw f i < r := by
      intro i hi1 hi2
      exact lastAbove_below_after f n r (dOf t - n) i hi1 (by omega)
    have hpd : p (dOf t) ≤ p (qOf t) := by
      have h := potential_mono_below f n r (qOf t) (by omega) (dOf t - qOf t) (by
        intro i hi1 hi2; exact hbel i (by omega) (by omega))
      rwa [Nat.add_sub_cancel' hqd] at h
    have hpa : p (qOf t - 1) ≤ p (lastAbove f n r (dOf t - n)) := by
      have h := potential_mono_below f n r (lastAbove f n r (dOf t - n)) hab.1
        (qOf t - 1 - lastAbove f n r (dOf t - n)) (by
          intro i hi1 hi2; exact hbelA i hi1 (by omega))
      rwa [Nat.add_sub_cancel' (by omega)] at h
    have hc1 : p (qOf t) < p t := hcross.1
    have hc2 : p t ≤ p (qOf t - 1) := hcross.2
    exact ⟨hab.1, hlt, by omega, hbelA, by omega, by omega⟩
  have hCross (t k : Nat) (ht : Good t) (hle : p t + (k : Int) ≤ p (lastAbove f n r (dOf t - n))) :
      ∃ q', lastAbove f n r (dOf t - n) < q' ∧ q' ≤ dOf t ∧
        areaCrossesDown p (p t + (k : Int)) q' := by
    obtain ⟨_, _, had, _, hpdt, _⟩ := hEntry t ht
    exact downcross_from_end_values p (lastAbove f n r (dOf t - n)) (dOf t)
      (p t + (k : Int)) had hle (by omega)
  let phi : Nat × Nat → Sum (Nat × Int) (Nat × Nat) := fun pair =>
    let t := n + pair.1
    let k := pair.2
    if ht : Good t then
      let d := dOf t
      let a0 := lastAbove f n r (d - n)
      if hle : p t + (k : Int) ≤ p a0 then
        Sum.inl (Classical.choose (hCross t k ht hle), p t + (k : Int))
      else
        Sum.inr (d, (p t + (k : Int) - p a0 - 1).toNat)
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
      obtain ⟨haq, hqd, hcr⟩ := Classical.choose_spec (hCross (n + pair.1) pair.2 ht hle)
      obtain ⟨_, _, hdt, _, _, _, _, _, _⟩ := hSpec (n + pair.1) ht
      obtain ⟨hna, _, _, _, _, _⟩ := hEntry (n + pair.1) ht
      refine ⟨(Classical.choose (hCross (n + pair.1) pair.2 ht hle), p (n + pair.1) + (pair.2 : Int)), ?_, rfl⟩
      exact crossing_mem_descent_slots f n K _ r _ (by omega) (by omega) hcr
    · next hnot =>
      apply List.mem_append_right
      apply List.mem_map.mpr
      obtain ⟨hnq, hqd, hdt, hdF, hdA, _, _, _, _⟩ := hSpec (n + pair.1) ht
      obtain ⟨_, _, _, _, _, hpta⟩ := hEntry (n + pair.1) ht
      let d := dOf (n + pair.1)
      let j := (p (n + pair.1) + (pair.2 : Int) - p (lastAbove f n r (d - n)) - 1).toNat
      refine ⟨(d, j), ?_, rfl⟩
      simp only [List.mem_flatMap, exits, mem_idxMarks]
      refine ⟨d - n, ⟨by omega, ?_⟩, ?_⟩
      · rw [Nat.add_sub_cancel' (show n ≤ d by omega)]
        exact ⟨hdF, hdA⟩
      · rw [Nat.add_sub_cancel' (show n ≤ d by omega)]
        have hj : j = 0 ∨ j = 1 := by
          dsimp only [j, d]
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
        obtain ⟨_, _, _, _, _, hEx, _, _, _⟩ := hSpec (n + x.1) htx
        obtain ⟨_, _, _, _, _, hEy, _, _, _⟩ := hSpec (n + y.1) hty
        obtain ⟨_, _, _, hBx, _, _⟩ := hEntry (n + x.1) htx
        obtain ⟨_, _, _, hBy, _, _⟩ := hEntry (n + y.1) hty
        have hdeq := excursion_exit_unique f (Classical.choose (hCross (n + x.1) x.2 htx hlex))
          (dOf (n + x.1)) (dOf (n + y.1)) r hqx hEx
          (fun i hi1 hi2 => hBx i (by omega) hi2)
          (by rw [hqeq]; exact hqy) hEy
          (fun i hi1 hi2 => hBy i (by omega) hi2)
        exact ⟨hdeq, hveq⟩
      · cases hxy
      · cases hxy
      · next hnx hny =>
        injection hxy with hpair
        have hdeq : dOf (n + x.1) = dOf (n + y.1) := congrArg Prod.fst hpair
        have hjeq : (p (n + x.1) + (x.2 : Int) - p (lastAbove f n r (dOf (n + x.1) - n)) - 1).toNat =
            (p (n + y.1) + (y.2 : Int) - p (lastAbove f n r (dOf (n + y.1) - n)) - 1).toNat :=
          congrArg Prod.snd hpair
        rw [hdeq] at hjeq hnx
        refine ⟨hdeq, ?_⟩
        omega
    obtain ⟨hdeq, hveq⟩ := hkey
    have hfst : x.1 = y.1 := by
      rcases Nat.lt_trichotomy x.1 y.1 with hlt | heq | hgt
      · obtain ⟨_, _, hdxt, _, _, _, _, _, _⟩ := hSpec (n + x.1) htx
        obtain ⟨_, hqyd, _, _, _, _, _, _, haftery⟩ := hSpec (n + y.1) hty
        have hspace := supply_potential_spacing_after_last_crossing f n (n + x.1) (n + y.1)
          (qOf (n + y.1)) r (by omega) (by omega) (by omega) hxP.1 hyP.1 hxP.2.1 haftery
        change p (n + x.1) + 3 ≤ p (n + y.1) at hspace
        omega
      · exact heq
      · obtain ⟨_, _, hdyt, _, _, _, _, _, _⟩ := hSpec (n + y.1) hty
        obtain ⟨_, hqxd, _, _, _, _, _, _, hafterx⟩ := hSpec (n + x.1) htx
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
  have htgt_len : target.length = (descentSlots f n r K).length + 2 * cN Q n K := by
    simp only [target, List.length_append, List.length_map, pair_flatMap_length, exits,
      count_eq_idxMarks_length]
  change 3 * cN P n K ≤ (descentSlots f n r K).length + 2 * cN Q n K
  omega

/-! ## Arbitrary-height 3-spacing weight budget (strictly strengthening E-674) -/

/-- Every original interval and arbitrary supplied height `r + 1` obeys the
3-spacing excursion budget `3 * E_{r+1} ≤ lowAdditionWeights f n r K + 2 * A_{r-1}`,
with no endpoint height, floor, or run-count restriction. -/
theorem same_height_supply_three_spacing_budget (f : Nat → Bool) (n a K : Nat) (r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true) :
    3 * (cN (fun t => Fw f t = r + 1 ∧ EndN f 0 t) n K : Int) ≤
      lowAdditionWeights f n r K +
        2 * (cN (fun t => Fw f t = r - 1 ∧ f t = true) n K : Int) := by
  let P := fun t => Fw f t = r + 1 ∧ EndN f 0 t
  let Q := fun t => Fw f t = r - 1 ∧ f t = true
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
    have hslots := actual_same_height_supply_three_slots f n a d r hw hpre
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
    have hsplitQ := cN_add Q n d (K - d)
    rw [show d + (K - d) = K by omega] at hsplitQ
    change cN P n K = cN P n d at hc
    change 3 * cN P n d ≤ (descentSlots f n r d).length + 2 * cN Q n d at hslots
    change 3 * (cN P n K : Int) ≤ lowAdditionWeights f n r K + 2 * (cN Q n K : Int)
    omega

/-! ## Floor-plus-four improvement and arbitrary-height dyadic capacity -/

private theorem level_additions_split (f : Nat → Bool) (n K : Nat) (h : Int) :
    levelAdditions f n K h = levelFree f n K h + levelSupplied f n K h := by
  unfold levelAdditions levelFree levelSupplied
  have hs := cN_split (fun t => Fw f t = h ∧ f t = true) (EndN f 0) n K
  have h1 : cN (fun t => (Fw f t = h ∧ f t = true) ∧ EndN f 0 t) n K =
      cN (fun t => Fw f t = h ∧ EndN f 0 t) n K :=
    cN_congr _ _ n K (fun t _ _ => ⟨fun ht => ⟨ht.1.1, ht.2⟩, fun ht => ⟨⟨ht.1, ht.2.1⟩, ht.2⟩⟩)
  have h2 : cN (fun t => (Fw f t = h ∧ f t = true) ∧ ¬ EndN f 0 t) n K =
      cN (fun t => Fw f t = h ∧ f t = true ∧ ¬ EndN f 0 t) n K :=
    cN_congr _ _ n K (fun t _ _ => ⟨fun ht => ⟨ht.1.1, ht.1.2, ht.2⟩, fun ht => ⟨⟨ht.1, ht.2.1⟩, ht.2.2⟩⟩)
  omega

/-- Strictly sharpens `E-674`'s `actual_floor_plus_four_count` (`E_{m+4} ≤ 6 * free`)
to `3 * E_{m+4} ≤ 8 * free f n K`, with arbitrary excursions above `m + 4`. -/
theorem actual_floor_plus_four_three_spacing (f : Nat → Bool) (n a K : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    3 * cN (fun t => Fw f t = m + 4 ∧ EndN f 0 t) n K ≤ 8 * free f n K := by
  have hb := same_height_supply_three_spacing_budget f n a K (m + 3) hw hpre
  have hW := low_weights_le_six_free f n a K m (m + 3) hw hpre hfloor (by omega)
  have hA2 := level_additions_split f n K (m + 2)
  have hE2 := actual_floor_supply_count f n a K m hw hpre hfloor
  have hF0F2 :
      cN (fun t => Fw f t = m ∧ f t = true ∧ ¬ EndN f 0 t) n K +
        cN (fun t => Fw f t = m + 2 ∧ f t = true ∧ ¬ EndN f 0 t) n K ≤ free f n K := by
    have hsplit := cN_split (fun t => f t = true ∧ ¬ EndN f 0 t) (fun t => Fw f t = m) n K
    have h0 : cN (fun t => Fw f t = m ∧ f t = true ∧ ¬ EndN f 0 t) n K ≤
        cN (fun t => (f t = true ∧ ¬ EndN f 0 t) ∧ Fw f t = m) n K :=
      cN_mono _ _ n K (fun t _ _ ht => ⟨ht.2, ht.1⟩)
    have h2 : cN (fun t => Fw f t = m + 2 ∧ f t = true ∧ ¬ EndN f 0 t) n K ≤
        cN (fun t => (f t = true ∧ ¬ EndN f 0 t) ∧ ¬ Fw f t = m) n K :=
      cN_mono _ _ n K (fun t _ _ ht => ⟨ht.2, by omega⟩)
    unfold free
    omega
  have heq4 : cN (fun t => Fw f t = m + 4 ∧ EndN f 0 t) n K =
      cN (fun t => Fw f t = m + 3 + 1 ∧ EndN f 0 t) n K := by
    rw [show m + 3 + 1 = m + 4 by omega]
  have heq2 : levelAdditions f n K (m + 2) =
      cN (fun t => Fw f t = m + 3 - 1 ∧ f t = true) n K := by
    unfold levelAdditions
    rw [show m + 3 - 1 = m + 2 by omega]
  unfold levelFree levelSupplied at hA2
  rw [heq4]
  rw [← heq2] at hb
  omega

/-! ## Level-sum decomposition and dyadic height-weighted capacity -/

private noncomputable def levelSum (g : Nat → Nat) : Nat → Nat
  | 0 => g 0
  | H + 1 => levelSum g H + g (H + 1)

private noncomputable def levelWeightSum (g : Nat → Nat) : Nat → Nat
  | 0 => g 0
  | H + 1 => levelWeightSum g H + 2 * levelSum g H + g (H + 1)

private theorem lowAdditionWeights_eq_levelWeightSum (f : Nat → Bool) (n K : Nat) (m : Int)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    ∀ (d : Nat), lowAdditionWeights f n (m + (d : Int) + 1) K =
      (levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) d : Int) := by
  induction K with
  | zero =>
    intro d
    induction d with
    | zero => simp [lowAdditionWeights, levelWeightSum, levelAdditions, cN]
    | succ d ih =>
      have hu : ∀ h, levelSum (fun j => levelAdditions f n 0 (m + (j : Int))) h = 0 := by
        intro h
        induction h with
        | zero => rfl
        | succ h ihh =>
          change levelSum (fun j => levelAdditions f n 0 (m + (j : Int))) h + 0 = 0
          omega
      have hz : levelAdditions f n 0 (m + ((d + 1 : Nat) : Int)) = 0 := rfl
      rw [lowAdditionWeights] at ih ⊢
      change (0 : Int) = ((levelWeightSum (fun j => levelAdditions f n 0 (m + (j : Int))) d +
        2 * levelSum (fun j => levelAdditions f n 0 (m + (j : Int))) d +
        levelAdditions f n 0 (m + ((d + 1 : Nat) : Int))) : Nat)
      rw [hu d, hz]
      omega
  | succ k ih =>
    have hfk : ∀ i, n ≤ i → i ≤ n + k → m ≤ Fw f i := fun i hi1 hi2 => hfloor i hi1 (by omega)
    have hbase := ih hfk
    have hmin := hfloor (n + k) (by omega) (by omega)
    by_cases hf : f (n + k) = true
    · have hstepU : ∀ (d : Nat),
          levelSum (fun j => levelAdditions f n (k + 1) (m + (j : Int))) d =
            levelSum (fun j => levelAdditions f n k (m + (j : Int))) d +
              (if Fw f (n + k) ≤ m + (d : Int) then 1 else 0) := by
        intro d
        induction d with
        | zero =>
          simp only [levelSum, levelAdditions]
          by_cases h0 : Fw f (n + k) = m + ((0 : Nat) : Int)
          · rw [cN_succ_pos _ n k ⟨h0, hf⟩, if_pos (by omega)]
          · rw [cN_succ_neg _ n k (fun h => h0 h.1), if_neg (by omega)]
            omega
        | succ d ihd =>
          simp only [levelSum]
          rw [ihd]
          by_cases h1 : Fw f (n + k) = m + ((d + 1 : Nat) : Int)
          · have hc : levelAdditions f n (k + 1) (m + ((d + 1 : Nat) : Int)) =
                levelAdditions f n k (m + ((d + 1 : Nat) : Int)) + 1 :=
              cN_succ_pos _ n k ⟨h1, hf⟩
            rw [hc, if_neg (by omega), if_pos (by omega)]
            omega
          · have hc : levelAdditions f n (k + 1) (m + ((d + 1 : Nat) : Int)) =
                levelAdditions f n k (m + ((d + 1 : Nat) : Int)) :=
              cN_succ_neg _ n k (fun h => h1 h.1)
            rw [hc]
            by_cases h2 : Fw f (n + k) ≤ m + (d : Int)
            · rw [if_pos h2, if_pos (by omega)]
              omega
            · rw [if_neg h2, if_neg (by omega)]
              omega
      intro d
      rw [lowAdditionWeights, hbase d]
      induction d with
      | zero =>
        simp only [levelWeightSum, levelAdditions]
        by_cases h0 : Fw f (n + k) = m + ((0 : Nat) : Int)
        · rw [cN_succ_pos _ n k ⟨h0, hf⟩]
          have hlw : lowAdditionWeight f (m + ((0 : Nat) : Int) + 1) (n + k) = 1 := by
            unfold lowAdditionWeight
            rw [if_pos ⟨hf, by omega⟩]
            omega
          rw [hlw]
          push_cast
          omega
        · rw [cN_succ_neg _ n k (fun h => h0 h.1)]
          have hlw : lowAdditionWeight f (m + ((0 : Nat) : Int) + 1) (n + k) = 0 := by
            unfold lowAdditionWeight
            rw [if_neg (fun h => h0 (by omega))]
          rw [hlw]
          omega
      | succ d ihd =>
        simp only [levelWeightSum]
        have hU := hstepU d
        by_cases htop : Fw f (n + k) = m + ((d + 1 : Nat) : Int)
        · have hc : levelAdditions f n (k + 1) (m + ((d + 1 : Nat) : Int)) =
              levelAdditions f n k (m + ((d + 1 : Nat) : Int)) + 1 :=
            cN_succ_pos _ n k ⟨htop, hf⟩
          rw [hc]
          have hlw1 : lowAdditionWeight f (m + ((d + 1 : Nat) : Int) + 1) (n + k) = 1 := by
            unfold lowAdditionWeight
            rw [if_pos ⟨hf, by omega⟩]
            omega
          have hlw0 : lowAdditionWeight f (m + (d : Int) + 1) (n + k) = 0 := by
            unfold lowAdditionWeight
            rw [if_neg (fun h => by omega)]
          rw [hlw1]
          rw [hlw0] at ihd
          rw [if_neg (by omega)] at hU
          push_cast
          omega
        · have hc : levelAdditions f n (k + 1) (m + ((d + 1 : Nat) : Int)) =
              levelAdditions f n k (m + ((d + 1 : Nat) : Int)) :=
            cN_succ_neg _ n k (fun h => htop h.1)
          rw [hc]
          by_cases hlow : Fw f (n + k) ≤ m + (d : Int)
          · have hlw1 : lowAdditionWeight f (m + ((d + 1 : Nat) : Int) + 1) (n + k) =
                lowAdditionWeight f (m + (d : Int) + 1) (n + k) + 2 := by
              unfold lowAdditionWeight
              rw [if_pos ⟨hf, by omega⟩, if_pos ⟨hf, by omega⟩]
              omega
            rw [hlw1]
            rw [if_pos hlow] at hU
            push_cast
            omega
          · have hlw1 : lowAdditionWeight f (m + ((d + 1 : Nat) : Int) + 1) (n + k) = 0 := by
              unfold lowAdditionWeight
              rw [if_neg (fun h => by omega)]
            have hlw0 : lowAdditionWeight f (m + (d : Int) + 1) (n + k) = 0 := by
              unfold lowAdditionWeight
              rw [if_neg (fun h => by omega)]
            rw [hlw1]
            rw [hlw0] at ihd
            rw [if_neg hlow] at hU
            push_cast
            omega
    · have hAeq : ∀ j : Nat, levelAdditions f n (k + 1) (m + (j : Int)) =
          levelAdditions f n k (m + (j : Int)) := by
        intro j
        exact cN_succ_neg _ n k (fun h => hf h.2)
      have hfn : (fun j : Nat => levelAdditions f n (k + 1) (m + (j : Int))) =
          (fun j : Nat => levelAdditions f n k (m + (j : Int))) := funext hAeq
      intro d
      rw [lowAdditionWeights, hbase d, hfn]
      have hlw : lowAdditionWeight f (m + (d : Int) + 1) (n + k) = 0 := by
        unfold lowAdditionWeight
        rw [if_neg (fun h => hf h.1)]
      rw [hlw]
      omega

private theorem dyadicSum_add (g₁ g₂ : Nat → Nat) :
    ∀ H, dyadicSum (fun h => g₁ h + g₂ h) H = dyadicSum g₁ H + dyadicSum g₂ H
  | 0 => rfl
  | H + 1 => by
    simp only [dyadicSum, dyadicSum_add g₁ g₂ H]
    omega

private theorem dyadicSum_le_pow_mul_sum (g : Nat → Nat) :
    ∀ H, dyadicSum g H ≤ 2 ^ H * levelSum g H
  | 0 => by simp [dyadicSum, levelSum]
  | H + 1 => by
    have ih := dyadicSum_le_pow_mul_sum g H
    have hpow : 1 ≤ 2 ^ (H + 1) := Nat.one_le_two_pow
    simp only [dyadicSum, levelSum, Nat.pow_succ, Nat.mul_add]
    have h1 : 2 * (2 ^ H * levelSum g H) = 2 ^ H * 2 * levelSum g H := by
      rw [Nat.mul_comm (2 ^ H) 2, Nat.mul_assoc]
    have h2 : g (H + 1) ≤ 2 ^ H * 2 * g (H + 1) := by
      have hge : 1 ≤ 2 ^ H * 2 := by have := @Nat.one_le_two_pow H; omega
      exact Nat.le_mul_of_pos_left _ (by omega)
    omega

private theorem dyadicSum_last_le (g : Nat → Nat) : ∀ H, g H ≤ dyadicSum g H
  | 0 => Nat.le_refl _
  | H + 1 => by simp only [dyadicSum]; omega

private theorem levelSum_free_le (f : Nat → Bool) (n K : Nat) (m : Int) :
    ∀ H, levelSum (fun h => levelFree f n K (m + (h : Int))) H ≤
      cN (fun t => f t = true ∧ ¬ EndN f 0 t ∧ Fw f t ≤ m + (H : Int)) n K
  | 0 => by
    simp only [levelSum, levelFree]
    apply cN_mono
    intro t _ _ ht
    exact ⟨ht.2.1, ht.2.2, by omega⟩
  | H + 1 => by
    have ih := levelSum_free_le f n K m H
    simp only [levelSum]
    have hsplit := cN_split
      (fun t => f t = true ∧ ¬ EndN f 0 t ∧ Fw f t ≤ m + ((H + 1 : Nat) : Int))
      (fun t => Fw f t ≤ m + (H : Int)) n K
    have h1 : cN (fun t => f t = true ∧ ¬ EndN f 0 t ∧ Fw f t ≤ m + (H : Int)) n K ≤
        cN (fun t => (f t = true ∧ ¬ EndN f 0 t ∧ Fw f t ≤ m + ((H + 1 : Nat) : Int)) ∧
          Fw f t ≤ m + (H : Int)) n K :=
      cN_mono _ _ n K (fun t _ _ ht => ⟨⟨ht.1, ht.2.1, by omega⟩, ht.2.2⟩)
    have h2 : levelFree f n K (m + ((H + 1 : Nat) : Int)) ≤
        cN (fun t => (f t = true ∧ ¬ EndN f 0 t ∧ Fw f t ≤ m + ((H + 1 : Nat) : Int)) ∧
          ¬ Fw f t ≤ m + (H : Int)) n K := by
      unfold levelFree
      exact cN_mono _ _ n K (fun t _ _ ht => ⟨⟨ht.2.1, ht.2.2, by omega⟩, by omega⟩)
    omega

private theorem dyadic_supplied_invariant (f : Nat → Bool) (n a K : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    ∀ H, 3 * dyadicSupplied f n K m (H + 1) +
        levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1) +
        levelAdditions f n K (m + ((H + 1 : Nat) : Int)) +
        levelAdditions f n K (m + (H : Int)) ≤
      2 * dyadicAdditions f n K m (H + 1) := by
  have hE0 : levelSupplied f n K (m + (0 : Nat)) = 0 := by
    apply cN_zero_of
    intro t hnt htK ht
    exact block_prefix_low_clock_not_endable f n a t hw hpre hnt m
      (fun i hi hj => hfloor i hi (by omega)) (by omega) ht.2
  have hE1 : levelSupplied f n K (m + (1 : Nat)) = 0 := by
    apply cN_zero_of
    intro t hnt htK ht
    exact block_prefix_low_clock_not_endable f n a t hw hpre hnt m
      (fun i hi hj => hfloor i hi (by omega)) (by omega) ht.2
  intro H
  induction H with
  | zero =>
    simp only [dyadicSupplied, dyadicAdditions, dyadicSum, levelWeightSum, levelSum]
    rw [hE0, hE1]
    omega
  | succ H ih =>
    have hb := same_height_supply_three_spacing_budget f n a K (m + (H : Int) + 1) hw hpre
    have hW := lowAdditionWeights_eq_levelWeightSum f n K m hfloor H
    rw [hW] at hb
    have hEqE : cN (fun t => Fw f t = m + (H : Int) + 1 + 1 ∧ EndN f 0 t) n K =
        levelSupplied f n K (m + ((H + 1 + 1 : Nat) : Int)) := by
      unfold levelSupplied
      rw [show m + (H : Int) + 1 + 1 = m + ((H + 1 + 1 : Nat) : Int) by omega]
    have hEqA : cN (fun t => Fw f t = m + (H : Int) + 1 - 1 ∧ f t = true) n K =
        levelAdditions f n K (m + (H : Int)) := by
      unfold levelAdditions
      rw [show m + (H : Int) + 1 - 1 = m + (H : Int) by omega]
    rw [hEqE, hEqA] at hb
    have hbNat : 3 * levelSupplied f n K (m + ((H + 1 + 1 : Nat) : Int)) ≤
        levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) H +
          2 * levelAdditions f n K (m + (H : Int)) := by
      omega
    simp only [dyadicSupplied, dyadicAdditions, dyadicSum, levelWeightSum, levelSum] at ih ⊢
    omega

/-- Uniform dyadic (`q = 1/2`) height-weighted capacity on actual `EndN`
for every height horizon `H`, arbitrary `BlockWord` prehistory, and arbitrary
excursions above floor `m`.  Breaks the `E-775` barrier `q < 0.4534` of the
relaxed `E-674` height-kernel cone directly on actual `EndN`. -/
theorem dyadic_height_weighted_capacity (f : Nat → Bool) (n a K H : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    dyadicAdditions f n K m H ≤ 3 * dyadicFree f n K m H := by
  have hsplit : dyadicAdditions f n K m H =
      dyadicFree f n K m H + dyadicSupplied f n K m H := by
    unfold dyadicAdditions dyadicFree dyadicSupplied
    rw [← dyadicSum_add]
    congr 1
    funext h
    exact level_additions_split f n K (m + (h : Int))
  cases H with
  | zero =>
    have hE0 : levelSupplied f n K (m + ((0 : Nat) : Int)) = 0 := by
      apply cN_zero_of
      intro t hnt htK ht
      exact block_prefix_low_clock_not_endable f n a t hw hpre hnt m
        (fun i hi hj => hfloor i hi (by omega)) (by omega) ht.2
    have hz : dyadicSupplied f n K m 0 = 0 := by
      unfold dyadicSupplied dyadicSum
      exact hE0
    omega
  | succ H =>
    have hinv := dyadic_supplied_invariant f n a K m hw hpre hfloor H
    omega

/-- Unweighted arbitrary-height bound `A_{m+h} ≤ 3 * 2^h * free f n K` on actual `EndN`
for every height `h : Nat` above any floor `m`, strictly below the relaxed `E-674`/`E-775`
growth rate `2.2056^h`. -/
theorem actual_height_exp_two_bound (f : Nat → Bool) (n a K h : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    levelAdditions f n K (m + (h : Int)) ≤ 3 * 2 ^ h * free f n K := by
  have hcap := dyadic_height_weighted_capacity f n a K h m hw hpre hfloor
  have hlast : levelAdditions f n K (m + (h : Int)) ≤ dyadicAdditions f n K m h :=
    dyadicSum_last_le (fun j => levelAdditions f n K (m + (j : Int))) h
  have hdy : dyadicFree f n K m h ≤
      2 ^ h * levelSum (fun j => levelFree f n K (m + (j : Int))) h :=
    dyadicSum_le_pow_mul_sum (fun j => levelFree f n K (m + (j : Int))) h
  have hls := levelSum_free_le f n K m h
  have hfr : cN (fun t => f t = true ∧ ¬ EndN f 0 t ∧ Fw f t ≤ m + (h : Int)) n K ≤
      free f n K := by
    unfold free
    exact cN_mono _ _ n K (fun t _ _ ht => ⟨ht.1, ht.2.1⟩)
  have hmul : 2 ^ h * levelSum (fun j => levelFree f n K (m + (j : Int))) h ≤
      2 ^ h * free f n K :=
    Nat.mul_le_mul_left (2 ^ h) (Nat.le_trans hls hfr)
  have h3 : 3 * dyadicFree f n K m h ≤ 3 * (2 ^ h * free f n K) :=
    Nat.mul_le_mul_left 3 (Nat.le_trans hdy hmul)
  rw [← Nat.mul_assoc] at h3
  omega

end Recaman.SupplyExcursionSpacing
