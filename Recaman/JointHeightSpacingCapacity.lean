import Recaman.ExcursionClimbSpacing
import Recaman.SharpThreeSpacingCapacity

namespace Recaman.JointHeightSpacingCapacity

open Recaman.ExcursionClimbSpacing Recaman.SharpThreeSpacingCapacity
open Recaman.SupplyExcursionSpacing Recaman.SupplyHeightWeightBudget
open Recaman.SupplyDescentWeight Recaman.SupplyDescentSlots Recaman.SupplyAreaCrossings
open Recaman.FloorSupplyPotential Recaman.FloorSupplyFreeBudget Recaman.LowTargetWeightedGap
open Recaman.LevelTriangleArea Recaman.AdditionRankSlack Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction Recaman.SuffixHallOwnerMap
open Classical

/-! # Coupled two-height excursion spacing and breaking the `1.8067` cone barrier

The single-height excursion 3-spacing budget (`E-785`, `E-788`, `E-792`) uses
`p = floorPotential f n (r - 1)` to inject three slots per supplied addition at height `r + 1`,
producing an exact rational cone barrier at `κ₃ ≈ 0.55350` (`1 / κ₃ ≈ 1.80669`).

Here we show that the SAME potential `p = floorPotential f n (r - 1)` simultaneously controls
supplied additions at height `r`: every `u` with `Fw f u = r ∧ EndN f 0 u` has an anchor
`s < u` with `p u + 1 ≤ p s`, hence a latest downward crossing `q(u) < u` of `p` at level
`p u + 1` with `Fw f (q u) < r`, and its extended excursion exit `d' ≤ u` forces `d' - 1`
to be an in-window double ascent `AA` (`r - 1 → r → r + 1`).

Injecting `{p t, p t + 1, p t + 2}` for each `t` at height `r + 1` together with `{p u}` for
each `u` at height `r` into `descentSlots f n r K ⊕ (AA_{r-1} × {0, 1, 2})` proves:
  `3 * E_{r+1} + E_r ≤ lowAdditionWeights f n r K + 3 * doubleAscent f n K (r - 1)`.

A zero-slack rational polynomial telescoping invariant across the new joint cone
`1/2 ≤ P / Q < κ_joint ≈ 0.563708` (`1 / κ_joint ≈ 1.77397`) strictly breaks the `E-785`/`E-788`
`1.8067` cone barrier directly on actual `EndN`, yielding concrete unconditional Lean bounds at:
- `P / Q = 5 / 9` (base `9 / 5 = 1.8000`, previously the negative control outside `E-788`),
- `P / Q = 9 / 16` (base `16 / 9 ≈ 1.7778`),
- `P / Q = 107 / 190` (base `190 / 107 ≈ 1.7757`, within `0.10%` of `1.77397`),
narrowing the `PROVED-LEAN` actual-`EndN` exponential growth bracket from `[5/3, 199/110]`
to `[5/3, 190/107]`.
-/

/-! ## Joint cone polynomials -/

def jointK (P Q : Nat) : Nat :=
  Q * (Q - P) * (Q - P)

def jointL (P Q : Nat) : Nat :=
  (3 * Q + P) * jointK P Q

def jointM (P Q : Nat) : Nat :=
  P * P * (4 * Q * Q + 3 * P * P - 5 * P * Q)

/-! ## Height-`r` latest crossing and extended excursion helpers -/

private theorem latest_same_height_supply_crossing (f : Nat → Bool) (n a u : Nat) (r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hnu : n ≤ u) (hF : Fw f u = r) (he : EndN f 0 u) :
    let p := floorPotential f n (r - 1)
    ∃ q, n < q ∧ q < u ∧ Fw f q < r ∧ areaCrossesDown p (p u + 1) q ∧
      ∀ j, q < j → j ≤ u → ¬ areaCrossesDown p (p u + 1) j := by
  let p := floorPotential f n (r - 1)
  change ∃ q, n < q ∧ q < u ∧ Fw f q < r ∧ areaCrossesDown p (p u + 1) q ∧ _
  obtain ⟨_, s, k, _, hsk, hk, hLevel, hArea⟩ := he
  rw [hsk] at hLevel
  have hsF : Fw f s = r - 1 := by omega
  have hArs : Ar f s (u - s) = 0 := by
    rw [show u - s = k by omega]
    exact hArea
  have hAnchor : ∃ s', n ≤ s' ∧ s' < u ∧ p u + 1 ≤ p s' := by
    by_cases hns : n ≤ s
    · refine ⟨s, hns, by omega, ?_⟩
      have hsp := area_split_at f n s u hns (by omega)
      rw [hArs, hsF] at hsp
      have hl : ((u - n : Nat) : Int) = ((s - n : Nat) : Int) + ((u - s : Nat) : Int) := by omega
      change Ar f n (u - n) + ((u - n : Nat) : Int) * (Fw f n - (r - 1 + 1)) + 1 ≤
        Ar f n (s - n) + ((s - n : Nat) : Int) * (Fw f n - (r - 1 + 1))
      rw [hsp, hl, Int.add_mul]
      have hmul :
          ((u - s : Nat) : Int) * (r - 1 - Fw f n) +
            ((u - s : Nat) : Int) * (Fw f n - (r - 1 + 1)) = -((u - s : Nat) : Int) := by
        rw [← Int.mul_add, show r - 1 - Fw f n + (Fw f n - (r - 1 + 1)) = -1 by omega]
        omega
      omega
    · have hsn : s < n := by omega
      have hpos := (block_suffix_positive_walk f 0 n a hw hpre s (Nat.zero_le _) (by omega)).2
      simp only [Nat.zero_add] at hpos
      have hsp := area_split_at f s n u (by omega) hnu
      rw [hArs, hsF] at hsp
      have hpu : p u ≤ -1 := by
        change Ar f n (u - n) + ((u - n : Nat) : Int) * (Fw f n - (r - 1 + 1)) ≤ -1
        have hmul :
            ((u - n : Nat) : Int) * (Fw f n - (r - 1)) =
              ((u - n : Nat) : Int) * (Fw f n - (r - 1 + 1)) + ((u - n : Nat) : Int) := by
          have : Fw f n - (r - 1) = (Fw f n - (r - 1 + 1)) + 1 := by omega
          rw [this, Int.mul_add, Int.mul_one]
        omega
      have hpn : p n = 0 := by simp [p, floorPotential, Ar]
      have hlt : n < u := by
        by_cases heq : n = u
        · rw [← heq, hpn] at hpu
          omega
        · omega
      exact ⟨n, Nat.le_refl n, hlt, by omega⟩
  obtain ⟨s', hns', hs'u, hp'⟩ := hAnchor
  obtain ⟨q0, hsq0, hq0u, hQ0⟩ := downcross_from_end_values p s' u (p u + 1) (by omega) hp' (by omega)
  let Q := fun j => n < j ∧ areaCrossesDown p (p u + 1) j
  obtain ⟨d, hd, hdm, hafter⟩ := last_markN Q n (u + 1 - n)
  have hdz : d ≠ 0 := by
    intro hz
    have hno := hafter (q0 - n) (by omega) (by omega)
    rw [Nat.add_sub_cancel' (show n ≤ q0 by omega)] at hno
    exact hno ⟨by omega, hQ0⟩
  have hmark : Q (n + d - 1) := hdm.resolve_left hdz
  let q := n + d - 1
  have hqn : n < q := hmark.1
  have hcross : areaCrossesDown p (p u + 1) q := hmark.2
  have hqStep := floor_potential_step f n (q - 1) (r - 1) (by omega)
  rw [show q - 1 + 1 = q by omega] at hqStep
  change p q = p (q - 1) + Fw f q - (r - 1 + 1) at hqStep
  have hqF : Fw f q < r := by
    have := hcross.1
    have := hcross.2
    omega
  have hqu : q < u := by
    by_cases heq : q = u
    · rw [heq] at hqF
      omega
    · dsimp only [q]
      omega
  refine ⟨q, hqn, hqu, hqF, hcross, ?_⟩
  intro j hjq hju hj
  have hno := hafter (j - n) (by dsimp only [q] at hjq; omega) (by omega)
  rw [Nat.add_sub_cancel' (show n ≤ j by omega)] at hno
  exact hno ⟨by omega, hj⟩

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

private theorem exists_extended_exit (f : Nat → Bool) (q target : Nat) (r : Int)
    (hqt : q < target) (hqF : Fw f q < r) (htF : Fw f target = r + 1) :
    ∃ d', q < d' ∧ d' < target ∧ Fw f (d' - 1) = r - 1 ∧ f (d' - 1) = true ∧
      Fw f d' = r ∧ f d' = true ∧ Fw f (d' + 1) = r + 1 ∧
      ∀ i, q ≤ i → i ≤ d' → Fw f i ≤ r := by
  let Q := fun i => q < i ∧ r + 1 ≤ Fw f i
  obtain ⟨e, het, hQe, hfirst⟩ := first_mark Q target ⟨target, Nat.le_refl target, hqt, by omega⟩
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

/-! ## Pairwise separation lemmas inside a shared excursion -/

private theorem spacing_r_r (f : Nat → Bool) (n u₁ u₂ q₂ : Nat) (r : Int)
    (hnu₁ : n ≤ u₁) (hu₁₂ : u₁ < u₂) (hq : q₂ < u₁)
    (hF₁ : Fw f u₁ = r) (hF₂ : Fw f u₂ = r) (hA₁ : f u₁ = true)
    (hAfter : ∀ j, q₂ < j → j ≤ u₂ →
      ¬ areaCrossesDown (floorPotential f n (r - 1)) (floorPotential f n (r - 1) u₂ + 1) j) :
    floorPotential f n (r - 1) u₁ + 1 ≤ floorPotential f n (r - 1) u₂ := by
  let p := floorPotential f n (r - 1)
  change p u₁ + 1 ≤ p u₂
  have h1 : Fw f (u₁ + 1) = r + 1 := by
    rcases fw_cases f u₁ with ⟨h, _⟩ | ⟨_, h⟩
    · omega
    · simp [hA₁] at h
  have hgap : u₁ + 1 < u₂ := by
    by_cases he : u₁ + 1 = u₂
    · rw [he] at h1; omega
    · omega
  have hs := floor_potential_step f n u₁ (r - 1) hnu₁
  change p (u₁ + 1) = p u₁ + Fw f (u₁ + 1) - (r - 1 + 1) at hs
  by_cases h : p u₁ + 1 ≤ p u₂
  · exact h
  · obtain ⟨j, hj1, hj2, hcr⟩ := downcross_from_end_values p (u₁ + 1) u₂ (p u₂ + 1)
      (by omega) (by omega) (by omega)
    exact (hAfter j (by omega) hj2 hcr).elim

private theorem spacing_r_rp1 (f : Nat → Bool) (n u t qt : Nat) (r : Int)
    (hnu : n ≤ u) (hut : u < t) (hq : qt < u)
    (hFu : Fw f u = r) (hFt : Fw f t = r + 1) (hAu : f u = true)
    (hAfter : ∀ j, qt < j → j < t →
      ¬ areaCrossesDown (floorPotential f n (r - 1)) (floorPotential f n (r - 1) t) j) :
    floorPotential f n (r - 1) u + 1 ≤ floorPotential f n (r - 1) t := by
  let p := floorPotential f n (r - 1)
  change p u + 1 ≤ p t
  have h1 : Fw f (u + 1) = r + 1 := by
    rcases fw_cases f u with ⟨h, _⟩ | ⟨_, h⟩
    · omega
    · simp [hAu] at h
  have hs := floor_potential_step f n u (r - 1) hnu
  change p (u + 1) = p u + Fw f (u + 1) - (r - 1 + 1) at hs
  by_cases heq : u + 1 = t
  · rw [heq] at hs
    omega
  · have hlt : u + 1 < t := by omega
    have htStep := floor_potential_step f n (t - 1) (r - 1) (by omega)
    rw [show t - 1 + 1 = t by omega, hFt] at htStep
    change p t = p (t - 1) + (r + 1) - (r - 1 + 1) at htStep
    by_cases h : p u + 1 ≤ p t
    · exact h
    · obtain ⟨j, hj1, hj2, hcr⟩ := downcross_from_end_values p (u + 1) (t - 1) (p t)
        (by omega) (by omega) (by omega)
      exact (hAfter j (by omega) (by omega) hcr).elim

private theorem spacing_rp1_r (f : Nat → Bool) (n t u qu : Nat) (r : Int)
    (hnt : n ≤ t) (htu : t < u) (hq : qu < t)
    (hFt : Fw f t = r + 1) (hFu : Fw f u = r) (hAt : f t = true)
    (hAfter : ∀ j, qu < j → j ≤ u →
      ¬ areaCrossesDown (floorPotential f n (r - 1)) (floorPotential f n (r - 1) u + 1) j) :
    floorPotential f n (r - 1) t + 3 ≤ floorPotential f n (r - 1) u := by
  let p := floorPotential f n (r - 1)
  change p t + 3 ≤ p u
  have h1 : Fw f (t + 1) = r + 2 := by
    rcases fw_cases f t with ⟨h, _⟩ | ⟨_, h⟩
    · omega
    · simp [hAt] at h
  have h2 : r + 1 ≤ Fw f (t + 2) := by
    rcases fw_cases f (t + 1) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [show t + 1 + 1 = t + 2 by omega] at h; omega
    · rw [show t + 1 + 1 = t + 2 by omega] at h; omega
  have hgap1 : t + 1 < u := by
    by_cases he : t + 1 = u
    · rw [he] at h1; omega
    · omega
  have hgap2 : t + 2 < u := by
    by_cases he : t + 2 = u
    · rw [he] at h2; omega
    · omega
  have hs1 := floor_potential_step f n t (r - 1) hnt
  change p (t + 1) = p t + Fw f (t + 1) - (r - 1 + 1) at hs1
  have hs2 := floor_potential_step f n (t + 1) (r - 1) (by omega)
  change p (t + 2) = p (t + 1) + Fw f (t + 2) - (r - 1 + 1) at hs2
  by_cases h : p t + 3 ≤ p u
  · exact h
  · obtain ⟨j, hj1, hj2, hcr⟩ := downcross_from_end_values p (t + 2) u (p u + 1)
      (by omega) (by omega) (by omega)
    exact (hAfter j (by omega) hj2 hcr).elim

/-! ## List helper lemmas for the joint 3+1 injection -/

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

private theorem triple_offset_length (L : List Nat) (n : Nat) :
    (L.flatMap (fun i => [(n + i, 0), (n + i, 1), (n + i, 2)])).length = 3 * L.length := by
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

private theorem nodup_sum_append {α β : Type} (L₁ : List α) (L₂ : List β)
    (h₁ : L₁.Nodup) (h₂ : L₂.Nodup) :
    (L₁.map Sum.inl ++ L₂.map Sum.inr).Nodup := by
  rw [List.nodup_append]
  refine ⟨nodup_map_of_inj L₁ Sum.inl h₁ (fun _ _ _ _ h => by cases h; rfl),
    nodup_map_of_inj L₂ Sum.inr h₂ (fun _ _ _ _ h => by cases h; rfl), ?_⟩
  intro x hx y hy hxy
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hy
  cases hxy

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

private theorem doubleAscent_le_levelAdditions (f : Nat → Bool) (n K : Nat) (h : Int) :
    doubleAscent f n K h ≤ levelAdditions f n K h := by
  unfold doubleAscent levelAdditions
  exact cN_mono _ _ n K (fun t _ _ ht => ⟨ht.1, ht.2.1⟩)

/-! ## Core joint 3+1 slot injection and arbitrary-height weight budget -/

/-- Joint 3+1 slot injection on `floorPotential f n (r - 1)`: every supplied addition at
height `r + 1` claims three slots and every supplied addition at height `r` claims one slot
across `descentSlots f n r K` and three overflow slots per in-window `AA` transition at `r - 1`. -/
theorem actual_joint_height_supply_aa_slots (f : Nat → Bool) (n a K : Nat) (r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true) :
    3 * levelSupplied f n K (r + 1) + levelSupplied f n K r ≤
      (descentSlots f n r K).length + 3 * doubleAscent f n K (r - 1) := by
  let p := floorPotential f n (r - 1)
  let P1 := fun t => Fw f t = r + 1 ∧ EndN f 0 t
  let P2 := fun u => Fw f u = r ∧ EndN f 0 u
  let QAA := fun t => Fw f t = r - 1 ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < n + K
  let Good1 := fun t => n ≤ t ∧ t < n + K ∧ P1 t
  let Good2 := fun u => n ≤ u ∧ u < n + K ∧ P2 u
  -- Type 1 data (height r + 1)
  have hdata1 (t : Nat) (ht : Good1 t) :
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
  let q1Of := fun t => if h : Good1 t then Classical.choose (hdata1 t h) else n
  let d1Of := fun t => if h : Good1 t then Classical.choose (Classical.choose_spec (hdata1 t h)) else n
  have hSpec1 (t : Nat) (ht : Good1 t) :
      n < q1Of t ∧ q1Of t < d1Of t ∧ d1Of t < t ∧ Fw f (d1Of t - 1) = r - 1 ∧ f (d1Of t - 1) = true ∧
        Fw f (d1Of t) = r ∧ f (d1Of t) = true ∧ Fw f (d1Of t + 1) = r + 1 ∧
        (∀ i, q1Of t ≤ i → i ≤ d1Of t → Fw f i ≤ r) ∧
        areaCrossesDown p (p t) (q1Of t) ∧
        (∀ j, q1Of t < j → j < t → ¬ areaCrossesDown p (p t) j) := by
    simp only [q1Of, d1Of, dif_pos ht]
    exact Classical.choose_spec (Classical.choose_spec (hdata1 t ht))
  have hEntry1 (t : Nat) (ht : Good1 t) :
      let d' := d1Of t
      let a0 := lastAbove f n (r + 1) (d' - n)
      n ≤ a0 ∧ a0 < q1Of t ∧ a0 ≤ d' ∧
        (∀ i, a0 < i → i ≤ d' → Fw f i ≤ r) ∧
        p d' < p t ∧ p t ≤ p a0 := by
    obtain ⟨hnq, hqd', _, _, _, _, _, _, hbel, hcross, _⟩ := hSpec1 t ht
    have hab := lastAbove_bounds f n (r + 1) (d1Of t - n)
    have hlt := lastAbove_lt_of_below f n (d1Of t - n) (q1Of t) (r + 1) hnq (by
      intro i hi1 hi2; have := hbel i hi1 (by omega); omega)
    have hbelA : ∀ i, lastAbove f n (r + 1) (d1Of t - n) < i → i ≤ d1Of t → Fw f i ≤ r := by
      intro i hi1 hi2; have := lastAbove_below_after f n (r + 1) (d1Of t - n) i hi1 (by omega); omega
    have hpd : p (d1Of t) ≤ p (q1Of t) := by
      have h := potential_mono_le f n r (q1Of t) (by omega) (d1Of t - q1Of t) (by
        intro i hi1 hi2; exact hbel i (by omega) (by omega))
      rwa [Nat.add_sub_cancel' (by omega)] at h
    have hpa : p (q1Of t - 1) ≤ p (lastAbove f n (r + 1) (d1Of t - n)) := by
      have h := potential_mono_le f n r (lastAbove f n (r + 1) (d1Of t - n)) hab.1
        (q1Of t - 1 - lastAbove f n (r + 1) (d1Of t - n)) (by
          intro i hi1 hi2; exact hbelA i hi1 (by omega))
      rwa [Nat.add_sub_cancel' (by omega)] at h
    have hc1 : p (q1Of t) < p t := hcross.1
    have hc2 : p t ≤ p (q1Of t - 1) := hcross.2
    exact ⟨hab.1, hlt, by omega, hbelA, by omega, by omega⟩
  have hCross1 (t k : Nat) (ht : Good1 t)
      (hle : p t + (k : Int) ≤ p (lastAbove f n (r + 1) (d1Of t - n))) :
      ∃ q', lastAbove f n (r + 1) (d1Of t - n) < q' ∧ q' ≤ d1Of t ∧
        areaCrossesDown p (p t + (k : Int)) q' := by
    obtain ⟨_, _, had, _, hpdt, _⟩ := hEntry1 t ht
    exact downcross_from_end_values p (lastAbove f n (r + 1) (d1Of t - n)) (d1Of t)
      (p t + (k : Int)) had hle (by omega)
  -- Type 2 data (height r)
  have hdata2 (u : Nat) (hu : Good2 u) :
      ∃ q d', n < q ∧ q < d' ∧ d' ≤ u ∧ Fw f (d' - 1) = r - 1 ∧ f (d' - 1) = true ∧
        Fw f d' = r ∧ f d' = true ∧ Fw f (d' + 1) = r + 1 ∧
        (∀ i, q ≤ i → i ≤ d' → Fw f i ≤ r) ∧
        areaCrossesDown p (p u + 1) q ∧
        (∀ j, q < j → j ≤ u → ¬ areaCrossesDown p (p u + 1) j) := by
    obtain ⟨hnu, _, hF, he⟩ := hu
    obtain ⟨q, hnq, hqu, hqF, hcross, hafter⟩ :=
      latest_same_height_supply_crossing f n a u r hw hpre hnu hF he
    have hu1 : Fw f (u + 1) = r + 1 := by
      rcases fw_cases f u with ⟨h, _⟩ | ⟨_, h⟩
      · omega
      · have hA := he.1; simp [hA] at h
    obtain ⟨d', hqd', hd'u1, hd1F, hd1A, hd'F, hd'A, hd'Exit, hbel⟩ :=
      exists_extended_exit f q (u + 1) r (by omega) hqF hu1
    exact ⟨q, d', hnq, hqd', by omega, hd1F, hd1A, hd'F, hd'A, hd'Exit, hbel, hcross, hafter⟩
  let q2Of := fun u => if h : Good2 u then Classical.choose (hdata2 u h) else n
  let d2Of := fun u => if h : Good2 u then Classical.choose (Classical.choose_spec (hdata2 u h)) else n
  have hSpec2 (u : Nat) (hu : Good2 u) :
      n < q2Of u ∧ q2Of u < d2Of u ∧ d2Of u ≤ u ∧ Fw f (d2Of u - 1) = r - 1 ∧ f (d2Of u - 1) = true ∧
        Fw f (d2Of u) = r ∧ f (d2Of u) = true ∧ Fw f (d2Of u + 1) = r + 1 ∧
        (∀ i, q2Of u ≤ i → i ≤ d2Of u → Fw f i ≤ r) ∧
        areaCrossesDown p (p u + 1) (q2Of u) ∧
        (∀ j, q2Of u < j → j ≤ u → ¬ areaCrossesDown p (p u + 1) j) := by
    simp only [q2Of, d2Of, dif_pos hu]
    exact Classical.choose_spec (Classical.choose_spec (hdata2 u hu))
  have hEntry2 (u : Nat) (hu : Good2 u) :
      let d' := d2Of u
      let a0 := lastAbove f n (r + 1) (d' - n)
      n ≤ a0 ∧ a0 < q2Of u ∧ a0 ≤ d' ∧
        (∀ i, a0 < i → i ≤ d' → Fw f i ≤ r) ∧
        p d' ≤ p u ∧ p u < p a0 := by
    obtain ⟨hnq, hqd', _, _, _, _, _, _, hbel, hcross, _⟩ := hSpec2 u hu
    have hab := lastAbove_bounds f n (r + 1) (d2Of u - n)
    have hlt := lastAbove_lt_of_below f n (d2Of u - n) (q2Of u) (r + 1) hnq (by
      intro i hi1 hi2; have := hbel i hi1 (by omega); omega)
    have hbelA : ∀ i, lastAbove f n (r + 1) (d2Of u - n) < i → i ≤ d2Of u → Fw f i ≤ r := by
      intro i hi1 hi2; have := lastAbove_below_after f n (r + 1) (d2Of u - n) i hi1 (by omega); omega
    have hpd : p (d2Of u) ≤ p (q2Of u) := by
      have h := potential_mono_le f n r (q2Of u) (by omega) (d2Of u - q2Of u) (by
        intro i hi1 hi2; exact hbel i (by omega) (by omega))
      rwa [Nat.add_sub_cancel' (by omega)] at h
    have hpa : p (q2Of u - 1) ≤ p (lastAbove f n (r + 1) (d2Of u - n)) := by
      have h := potential_mono_le f n r (lastAbove f n (r + 1) (d2Of u - n)) hab.1
        (q2Of u - 1 - lastAbove f n (r + 1) (d2Of u - n)) (by
          intro i hi1 hi2; exact hbelA i hi1 (by omega))
      rwa [Nat.add_sub_cancel' (by omega)] at h
    have hc1 : p (q2Of u) < p u + 1 := hcross.1
    have hc2 : p u + 1 ≤ p (q2Of u - 1) := hcross.2
    exact ⟨hab.1, hlt, by omega, hbelA, by omega, by omega⟩
  have hCross2 (u : Nat) (hu : Good2 u) (hlt : p (d2Of u) < p u) :
      ∃ q', lastAbove f n (r + 1) (d2Of u - n) < q' ∧ q' ≤ d2Of u ∧
        areaCrossesDown p (p u) q' := by
    obtain ⟨_, _, had, _, _, hpa⟩ := hEntry2 u hu
    exact downcross_from_end_values p (lastAbove f n (r + 1) (d2Of u - n)) (d2Of u)
      (p u) had (by omega) hlt
  -- Joint map phi : Sum (Nat × Nat) Nat → Sum (Nat × Int) (Nat × Nat)
  let phi : Sum (Nat × Nat) Nat → Sum (Nat × Int) (Nat × Nat) := fun x =>
    match x with
    | Sum.inl pair =>
      let t := n + pair.1
      let k := pair.2
      if ht : Good1 t then
        let d' := d1Of t
        let a0 := lastAbove f n (r + 1) (d' - n)
        if hle : p t + (k : Int) ≤ p a0 then
          Sum.inl (Classical.choose (hCross1 t k ht hle), p t + (k : Int))
        else
          Sum.inr (d' - 1, (p t + (k : Int) - p a0 - 1).toNat)
      else
        Sum.inr (n, 0)
    | Sum.inr idx =>
      let u := n + idx
      if hu : Good2 u then
        let d' := d2Of u
        if hlt : p d' < p u then
          Sum.inl (Classical.choose (hCross2 u hu hlt), p u)
        else
          Sum.inr (d' - 1, 2)
      else
        Sum.inr (n, 0)
  let dom1 := (idxMarks P1 n K).flatMap (fun i => [(i, 0), (i, 1), (i, 2)])
  let dom2 := idxMarks P2 n K
  let dom : List (Sum (Nat × Nat) Nat) := dom1.map Sum.inl ++ dom2.map Sum.inr
  let exits := idxMarks QAA n K
  let target : List (Sum (Nat × Int) (Nat × Nat)) :=
    (descentSlots f n r K).map Sum.inl ++
      (exits.flatMap (fun i => [(n + i, 0), (n + i, 1), (n + i, 2)])).map Sum.inr
  have hdom1_mem : ∀ pair, pair ∈ dom1 → pair.1 < K ∧ P1 (n + pair.1) ∧ pair.2 ≤ 2 := by
    intro pair hmem
    simp only [dom1, List.mem_flatMap, mem_idxMarks, List.mem_cons, List.not_mem_nil, or_false] at hmem
    obtain ⟨i, ⟨hiK, hiP⟩, hpair⟩ := hmem
    rcases hpair with rfl | rfl | rfl <;> exact ⟨hiK, hiP, by omega⟩
  have hsub : dom.map phi ⊆ target := by
    intro y hy
    obtain ⟨x, hxm, rfl⟩ := List.mem_map.mp hy
    rcases List.mem_append.mp hxm with h1 | h2
    · obtain ⟨pair, hpm, rfl⟩ := List.mem_map.mp h1
      obtain ⟨hiK, hiP, hk2⟩ := hdom1_mem pair hpm
      have ht : Good1 (n + pair.1) := ⟨by omega, by omega, hiP⟩
      dsimp only [phi]
      rw [dif_pos ht]
      split
      · next hle =>
        apply List.mem_append_left
        apply List.mem_map.mpr
        obtain ⟨haq, hqd', hcr⟩ := Classical.choose_spec (hCross1 (n + pair.1) pair.2 ht hle)
        obtain ⟨_, _, hd't, _, _, _, _, _, _, _, _⟩ := hSpec1 (n + pair.1) ht
        obtain ⟨hna, _, _, _, _, _⟩ := hEntry1 (n + pair.1) ht
        refine ⟨(Classical.choose (hCross1 (n + pair.1) pair.2 ht hle), p (n + pair.1) + (pair.2 : Int)), ?_, rfl⟩
        exact crossing_mem_descent_slots f n K _ r _ (by omega) (by omega) hcr
      · next hnot =>
        apply List.mem_append_right
        apply List.mem_map.mpr
        obtain ⟨hnq, hqd', hd't, hd1F, hd1A, _, hd'A, _, _, _, _⟩ := hSpec1 (n + pair.1) ht
        obtain ⟨_, _, _, _, _, hpta⟩ := hEntry1 (n + pair.1) ht
        let d' := d1Of (n + pair.1)
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
          have hj : j = 0 ∨ j = 1 := by dsimp only [j, d']; omega
          rcases hj with h0 | h1
          · simp [h0]
          · simp [h1]
    · obtain ⟨idx, him, rfl⟩ := List.mem_map.mp h2
      obtain ⟨hiK, hiP⟩ := (mem_idxMarks P2 n K idx).mp him
      have hu : Good2 (n + idx) := ⟨by omega, by omega, hiP⟩
      dsimp only [phi]
      rw [dif_pos hu]
      split
      · next hlt =>
        apply List.mem_append_left
        apply List.mem_map.mpr
        obtain ⟨haq, hqd', hcr⟩ := Classical.choose_spec (hCross2 (n + idx) hu hlt)
        obtain ⟨_, _, hd'u, _, _, _, _, _, _, _, _⟩ := hSpec2 (n + idx) hu
        obtain ⟨hna, _, _, _, _, _⟩ := hEntry2 (n + idx) hu
        refine ⟨(Classical.choose (hCross2 (n + idx) hu hlt), p (n + idx)), ?_, rfl⟩
        exact crossing_mem_descent_slots f n K _ r _ (by omega) (by omega) hcr
      · next hnot =>
        apply List.mem_append_right
        apply List.mem_map.mpr
        obtain ⟨hnq, hqd', hd'u, hd1F, hd1A, _, hd'A, _, _, _, _⟩ := hSpec2 (n + idx) hu
        let d' := d2Of (n + idx)
        let d1 := d' - 1
        refine ⟨(d1, 2), ?_, rfl⟩
        simp only [List.mem_flatMap, exits, mem_idxMarks]
        refine ⟨d1 - n, ⟨by omega, ?_⟩, ?_⟩
        · rw [Nat.add_sub_cancel' (show n ≤ d1 by omega)]
          refine ⟨hd1F, hd1A, ?_, by omega⟩
          rw [show d1 + 1 = d' by omega]
          exact hd'A
        · rw [Nat.add_sub_cancel' (show n ≤ d1 by omega)]
          simp
  have hnd_dom : dom.Nodup :=
    nodup_sum_append dom1 dom2
      (triple_flatMap_nodup (idxMarks P1 n K) (List.nodup_range.filter _))
      (List.nodup_range.filter _)
  have hkey_cross :
      ∀ (t : Nat) (k : Nat) (ht : Good1 t) (u : Nat) (hu : Good2 u),
        d1Of t = d2Of u → p t + (k : Int) = p u → k ≤ 2 → False := by
    intro t k ht u hu hdeq hveq hk2
    rcases Nat.lt_trichotomy t u with hlt | heq | hgt
    · obtain ⟨_, _, hd1t, _, _, _, _, _, _, _, _⟩ := hSpec1 t ht
      obtain ⟨_, hq2d, _, _, _, _, _, _, _, _, hafter2⟩ := hSpec2 u hu
      have hspace := spacing_rp1_r f n t u (q2Of u) r ht.1 hlt (by omega)
        ht.2.2.1 hu.2.2.1 ht.2.2.2.1 hafter2
      change p t + 3 ≤ p u at hspace
      omega
    · have h1 := ht.2.2.1
      have h2 := hu.2.2.1
      rw [heq] at h1
      omega
    · obtain ⟨_, _, hd2u, _, _, _, _, _, _, _, _⟩ := hSpec2 u hu
      obtain ⟨_, hq1d, _, _, _, _, _, _, _, _, hafter1⟩ := hSpec1 t ht
      have hspace := spacing_r_rp1 f n u t (q1Of t) r hu.1 hgt (by omega)
        hu.2.2.1 ht.2.2.1 hu.2.2.2.1 hafter1
      change p u + 1 ≤ p t at hspace
      omega
  have hinj : ∀ x ∈ dom, ∀ y ∈ dom, phi x = phi y → x = y := by
    intro x hx y hy hxy
    rcases List.mem_append.mp hx with hx1 | hx2 <;> rcases List.mem_append.mp hy with hy1 | hy2
    · -- Both Type 1
      obtain ⟨px, hpx, rfl⟩ := List.mem_map.mp hx1
      obtain ⟨py, hpy, rfl⟩ := List.mem_map.mp hy1
      obtain ⟨hxK, hxP, hxk⟩ := hdom1_mem px hpx
      obtain ⟨hyK, hyP, hyk⟩ := hdom1_mem py hpy
      have htx : Good1 (n + px.1) := ⟨by omega, by omega, hxP⟩
      have hty : Good1 (n + py.1) := ⟨by omega, by omega, hyP⟩
      have hkey : d1Of (n + px.1) = d1Of (n + py.1) ∧
          p (n + px.1) + (px.2 : Int) = p (n + py.1) + (py.2 : Int) := by
        dsimp only [phi] at hxy
        rw [dif_pos htx, dif_pos hty] at hxy
        split at hxy <;> split at hxy
        · next hlex hley =>
          injection hxy with hpair
          have hqeq : Classical.choose (hCross1 (n + px.1) px.2 htx hlex) =
              Classical.choose (hCross1 (n + py.1) py.2 hty hley) := congrArg Prod.fst hpair
          have hveq : p (n + px.1) + (px.2 : Int) = p (n + py.1) + (py.2 : Int) := congrArg Prod.snd hpair
          obtain ⟨hax, hqx, _⟩ := Classical.choose_spec (hCross1 (n + px.1) px.2 htx hlex)
          obtain ⟨hay, hqy, _⟩ := Classical.choose_spec (hCross1 (n + py.1) py.2 hty hley)
          obtain ⟨_, _, _, _, _, _, _, hEx, _, _, _⟩ := hSpec1 (n + px.1) htx
          obtain ⟨_, _, _, _, _, _, _, hEy, _, _, _⟩ := hSpec1 (n + py.1) hty
          obtain ⟨_, _, _, hBx, _, _⟩ := hEntry1 (n + px.1) htx
          obtain ⟨_, _, _, hBy, _, _⟩ := hEntry1 (n + py.1) hty
          have hdeq := extended_exit_unique f (Classical.choose (hCross1 (n + px.1) px.2 htx hlex))
            (d1Of (n + px.1)) (d1Of (n + py.1)) r hqx hEx
            (fun i hi1 hi2 => hBx i (by omega) hi2)
            (by rw [hqeq]; exact hqy) hEy
            (fun i hi1 hi2 => hBy i (by omega) hi2)
          exact ⟨hdeq, hveq⟩
        · cases hxy
        · cases hxy
        · next hnx hny =>
          injection hxy with hpair
          have hd1eq : d1Of (n + px.1) - 1 = d1Of (n + py.1) - 1 := congrArg Prod.fst hpair
          obtain ⟨hnqx, hqdx, _, _, _, _, _, _, _, _, _⟩ := hSpec1 (n + px.1) htx
          obtain ⟨hnqy, hqdy, _, _, _, _, _, _, _, _, _⟩ := hSpec1 (n + py.1) hty
          have hdeq : d1Of (n + px.1) = d1Of (n + py.1) := by omega
          have hjeq : (p (n + px.1) + (px.2 : Int) - p (lastAbove f n (r + 1) (d1Of (n + px.1) - n)) - 1).toNat =
              (p (n + py.1) + (py.2 : Int) - p (lastAbove f n (r + 1) (d1Of (n + py.1) - n)) - 1).toNat :=
            congrArg Prod.snd hpair
          rw [hdeq] at hjeq hnx
          exact ⟨hdeq, by omega⟩
      obtain ⟨hdeq, hveq⟩ := hkey
      have hfst : px.1 = py.1 := by
        rcases Nat.lt_trichotomy px.1 py.1 with hlt | heq | hgt
        · obtain ⟨_, _, hdxt, _, _, _, _, _, _, _, _⟩ := hSpec1 (n + px.1) htx
          obtain ⟨_, hqyd, _, _, _, _, _, _, _, _, haftery⟩ := hSpec1 (n + py.1) hty
          have hspace := supply_potential_spacing_after_last_crossing f n (n + px.1) (n + py.1)
            (q1Of (n + py.1)) r (by omega) (by omega) (by omega) hxP.1 hyP.1 hxP.2.1 haftery
          change p (n + px.1) + 3 ≤ p (n + py.1) at hspace
          omega
        · exact heq
        · obtain ⟨_, _, hdyt, _, _, _, _, _, _, _, _⟩ := hSpec1 (n + py.1) hty
          obtain ⟨_, hqxd, _, _, _, _, _, _, _, _, hafterx⟩ := hSpec1 (n + px.1) htx
          have hspace := supply_potential_spacing_after_last_crossing f n (n + py.1) (n + px.1)
            (q1Of (n + px.1)) r (by omega) (by omega) (by omega) hyP.1 hxP.1 hyP.2.1 hafterx
          change p (n + py.1) + 3 ≤ p (n + px.1) at hspace
          omega
      have hsnd : px.2 = py.2 := by rw [hfst] at hveq; omega
      exact congrArg Sum.inl (Prod.ext hfst hsnd)
    · -- Type 1 vs Type 2: impossible
      obtain ⟨px, hpx, rfl⟩ := List.mem_map.mp hx1
      obtain ⟨iy, hiy, rfl⟩ := List.mem_map.mp hy2
      obtain ⟨hxK, hxP, hxk⟩ := hdom1_mem px hpx
      obtain ⟨hyK, hyP⟩ := (mem_idxMarks P2 n K iy).mp hiy
      have htx : Good1 (n + px.1) := ⟨by omega, by omega, hxP⟩
      have huy : Good2 (n + iy) := ⟨by omega, by omega, hyP⟩
      dsimp only [phi] at hxy
      rw [dif_pos htx, dif_pos huy] at hxy
      split at hxy <;> split at hxy
      · next hlex hlty =>
        injection hxy with hpair
        have hqeq : Classical.choose (hCross1 (n + px.1) px.2 htx hlex) =
            Classical.choose (hCross2 (n + iy) huy hlty) := congrArg Prod.fst hpair
        have hveq : p (n + px.1) + (px.2 : Int) = p (n + iy) := congrArg Prod.snd hpair
        obtain ⟨hax, hqx, _⟩ := Classical.choose_spec (hCross1 (n + px.1) px.2 htx hlex)
        obtain ⟨hay, hqy, _⟩ := Classical.choose_spec (hCross2 (n + iy) huy hlty)
        obtain ⟨_, _, _, _, _, _, _, hEx, _, _, _⟩ := hSpec1 (n + px.1) htx
        obtain ⟨_, _, _, _, _, _, _, hEy, _, _, _⟩ := hSpec2 (n + iy) huy
        obtain ⟨_, _, _, hBx, _, _⟩ := hEntry1 (n + px.1) htx
        obtain ⟨_, _, _, hBy, _, _⟩ := hEntry2 (n + iy) huy
        have hdeq := extended_exit_unique f (Classical.choose (hCross1 (n + px.1) px.2 htx hlex))
          (d1Of (n + px.1)) (d2Of (n + iy)) r hqx hEx
          (fun i hi1 hi2 => hBx i (by omega) hi2)
          (by rw [hqeq]; exact hqy) hEy
          (fun i hi1 hi2 => hBy i (by omega) hi2)
        exact (hkey_cross (n + px.1) px.2 htx (n + iy) huy hdeq hveq hxk).elim
      · cases hxy
      · cases hxy
      · next hnx hny =>
        injection hxy with hpair
        have hjeq : (p (n + px.1) + (px.2 : Int) - p (lastAbove f n (r + 1) (d1Of (n + px.1) - n)) - 1).toNat = 2 :=
          congrArg Prod.snd hpair
        obtain ⟨_, _, _, _, _, hpta⟩ := hEntry1 (n + px.1) htx
        omega
    · -- Type 2 vs Type 1: symmetric impossible
      obtain ⟨ix, hix, rfl⟩ := List.mem_map.mp hx2
      obtain ⟨py, hpy, rfl⟩ := List.mem_map.mp hy1
      obtain ⟨hxK, hxP⟩ := (mem_idxMarks P2 n K ix).mp hix
      obtain ⟨hyK, hyP, hyk⟩ := hdom1_mem py hpy
      have hux : Good2 (n + ix) := ⟨by omega, by omega, hxP⟩
      have hty : Good1 (n + py.1) := ⟨by omega, by omega, hyP⟩
      dsimp only [phi] at hxy
      rw [dif_pos hux, dif_pos hty] at hxy
      split at hxy <;> split at hxy
      · next hltx hley =>
        injection hxy with hpair
        have hqeq : Classical.choose (hCross2 (n + ix) hux hltx) =
            Classical.choose (hCross1 (n + py.1) py.2 hty hley) := congrArg Prod.fst hpair
        have hveq : p (n + ix) = p (n + py.1) + (py.2 : Int) := congrArg Prod.snd hpair
        obtain ⟨hax, hqx, _⟩ := Classical.choose_spec (hCross2 (n + ix) hux hltx)
        obtain ⟨hay, hqy, _⟩ := Classical.choose_spec (hCross1 (n + py.1) py.2 hty hley)
        obtain ⟨_, _, _, _, _, _, _, hEx, _, _, _⟩ := hSpec2 (n + ix) hux
        obtain ⟨_, _, _, _, _, _, _, hEy, _, _, _⟩ := hSpec1 (n + py.1) hty
        obtain ⟨_, _, _, hBx, _, _⟩ := hEntry2 (n + ix) hux
        obtain ⟨_, _, _, hBy, _, _⟩ := hEntry1 (n + py.1) hty
        have hdeq := extended_exit_unique f (Classical.choose (hCross2 (n + ix) hux hltx))
          (d2Of (n + ix)) (d1Of (n + py.1)) r hqx hEx
          (fun i hi1 hi2 => hBx i (by omega) hi2)
          (by rw [hqeq]; exact hqy) hEy
          (fun i hi1 hi2 => hBy i (by omega) hi2)
        exact (hkey_cross (n + py.1) py.2 hty (n + ix) hux hdeq.symm hveq.symm hyk).elim
      · cases hxy
      · cases hxy
      · next hnx hny =>
        injection hxy with hpair
        have hjeq : 2 = (p (n + py.1) + (py.2 : Int) - p (lastAbove f n (r + 1) (d1Of (n + py.1) - n)) - 1).toNat :=
          congrArg Prod.snd hpair
        obtain ⟨_, _, _, _, _, hpta⟩ := hEntry1 (n + py.1) hty
        omega
    · -- Both Type 2
      obtain ⟨ix, hix, rfl⟩ := List.mem_map.mp hx2
      obtain ⟨iy, hiy, rfl⟩ := List.mem_map.mp hy2
      obtain ⟨hxK, hxP⟩ := (mem_idxMarks P2 n K ix).mp hix
      obtain ⟨hyK, hyP⟩ := (mem_idxMarks P2 n K iy).mp hiy
      have hux : Good2 (n + ix) := ⟨by omega, by omega, hxP⟩
      have huy : Good2 (n + iy) := ⟨by omega, by omega, hyP⟩
      have hkey : d2Of (n + ix) = d2Of (n + iy) ∧ p (n + ix) = p (n + iy) := by
        dsimp only [phi] at hxy
        rw [dif_pos hux, dif_pos huy] at hxy
        split at hxy <;> split at hxy
        · next hltx hlty =>
          injection hxy with hpair
          have hqeq : Classical.choose (hCross2 (n + ix) hux hltx) =
              Classical.choose (hCross2 (n + iy) huy hlty) := congrArg Prod.fst hpair
          have hveq : p (n + ix) = p (n + iy) := congrArg Prod.snd hpair
          obtain ⟨hax, hqx, _⟩ := Classical.choose_spec (hCross2 (n + ix) hux hltx)
          obtain ⟨hay, hqy, _⟩ := Classical.choose_spec (hCross2 (n + iy) huy hlty)
          obtain ⟨_, _, _, _, _, _, _, hEx, _, _, _⟩ := hSpec2 (n + ix) hux
          obtain ⟨_, _, _, _, _, _, _, hEy, _, _, _⟩ := hSpec2 (n + iy) huy
          obtain ⟨_, _, _, hBx, _, _⟩ := hEntry2 (n + ix) hux
          obtain ⟨_, _, _, hBy, _, _⟩ := hEntry2 (n + iy) huy
          have hdeq := extended_exit_unique f (Classical.choose (hCross2 (n + ix) hux hltx))
            (d2Of (n + ix)) (d2Of (n + iy)) r hqx hEx
            (fun i hi1 hi2 => hBx i (by omega) hi2)
            (by rw [hqeq]; exact hqy) hEy
            (fun i hi1 hi2 => hBy i (by omega) hi2)
          exact ⟨hdeq, hveq⟩
        · cases hxy
        · cases hxy
        · next hnx hny =>
          injection hxy with hpair
          have hd1eq : d2Of (n + ix) - 1 = d2Of (n + iy) - 1 := congrArg Prod.fst hpair
          obtain ⟨hnqx, hqdx, _, _, _, _, _, _, _, _, _⟩ := hSpec2 (n + ix) hux
          obtain ⟨hnqy, hqdy, _, _, _, _, _, _, _, _, _⟩ := hSpec2 (n + iy) huy
          have hdeq : d2Of (n + ix) = d2Of (n + iy) := by omega
          obtain ⟨_, _, _, _, hpdx, _⟩ := hEntry2 (n + ix) hux
          obtain ⟨_, _, _, _, hpdy, _⟩ := hEntry2 (n + iy) huy
          rw [hdeq] at hnx hpdx
          exact ⟨hdeq, by omega⟩
      obtain ⟨hdeq, hveq⟩ := hkey
      have heq : ix = iy := by
        rcases Nat.lt_trichotomy ix iy with hlt | heq | hgt
        · obtain ⟨_, _, hdxu, _, _, _, _, _, _, _, _⟩ := hSpec2 (n + ix) hux
          obtain ⟨_, hqyd, _, _, _, _, _, _, _, _, haftery⟩ := hSpec2 (n + iy) huy
          have hspace := spacing_r_r f n (n + ix) (n + iy) (q2Of (n + iy)) r
            (by omega) (by omega) (by omega) hxP.1 hyP.1 hxP.2.1 haftery
          change p (n + ix) + 1 ≤ p (n + iy) at hspace
          omega
        · exact heq
        · obtain ⟨_, _, hdyu, _, _, _, _, _, _, _, _⟩ := hSpec2 (n + iy) huy
          obtain ⟨_, hqxd, _, _, _, _, _, _, _, _, hafterx⟩ := hSpec2 (n + ix) hux
          have hspace := spacing_r_r f n (n + iy) (n + ix) (q2Of (n + ix)) r
            (by omega) (by omega) (by omega) hyP.1 hxP.1 hyP.2.1 hafterx
          change p (n + iy) + 1 ≤ p (n + ix) at hspace
          omega
      exact congrArg Sum.inr heq
  have hnd_img := nodup_map_of_inj dom phi hnd_dom hinj
  have hlen := hnd_img.length_le_of_subset hsub
  rw [List.length_map] at hlen
  have hdom_len : dom.length = 3 * levelSupplied f n K (r + 1) + levelSupplied f n K r := by
    simp only [dom, List.length_append, List.length_map, dom1, dom2, triple_flatMap_length,
      levelSupplied, P1, P2, count_eq_idxMarks_length]
  have htgt_len : target.length = (descentSlots f n r K).length + 3 * doubleAscent f n K (r - 1) := by
    simp only [target, List.length_append, List.length_map, triple_offset_length, exits,
      doubleAscent, QAA, count_eq_idxMarks_length]
  omega

/-- Arbitrary-height, arbitrary-interval coupled two-height spacing weight budget:
`3 * E_{r+1} + E_r ≤ lowAdditionWeights f n r K + 3 * doubleAscent f n K (r - 1)`. -/
theorem joint_height_supply_aa_spacing_budget (f : Nat → Bool) (n a K : Nat) (r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true) :
    3 * (levelSupplied f n K (r + 1) : Int) + (levelSupplied f n K r : Int) ≤
      lowAdditionWeights f n r K + 3 * (doubleAscent f n K (r - 1) : Int) := by
  let P1 := fun t => Fw f t = r + 1 ∧ EndN f 0 t
  let P2 := fun t => Fw f t = r ∧ EndN f 0 t
  let Pboth := fun t => (Fw f t = r + 1 ∨ Fw f t = r) ∧ EndN f 0 t
  obtain ⟨d, hd, hlast, hafter⟩ := last_markN Pboth n K
  have htail1 : cN P1 (n + d) (K - d) = 0 := by
    apply cN_zero_of
    intro i hi hiK h1
    have h := hafter (i - n) (by omega) (by omega)
    rw [show n + (i - n) = i by omega] at h
    exact h ⟨Or.inl h1.1, h1.2⟩
  have htail2 : cN P2 (n + d) (K - d) = 0 := by
    apply cN_zero_of
    intro i hi hiK h2
    have h := hafter (i - n) (by omega) (by omega)
    rw [show n + (i - n) = i by omega] at h
    exact h ⟨Or.inr h2.1, h2.2⟩
  have hc1 := cN_add P1 n d (K - d)
  rw [show d + (K - d) = K by omega, htail1, Nat.add_zero] at hc1
  have hc2 := cN_add P2 n d (K - d)
  rw [show d + (K - d) = K by omega, htail2, Nat.add_zero] at hc2
  by_cases hz : d = 0
  · rw [hz] at hc1 hc2
    have hz1 : levelSupplied f n K (r + 1) = 0 := by unfold levelSupplied; exact hc1
    have hz2 : levelSupplied f n K r = 0 := by unfold levelSupplied; exact hc2
    have hnonneg := low_weights_nonnegative f n r K
    rw [hz1, hz2]
    omega
  · have hp := hlast.resolve_left hz
    have htA := hp.2.1
    have hend : r ≤ Fw f (n + d) := by
      rcases fw_cases f (n + d - 1) with ⟨h, _⟩ | ⟨_, h⟩
      · rw [show n + d - 1 + 1 = n + d by omega] at h
        rcases hp.1 with h1 | h2 <;> omega
      · rw [htA] at h
        cases h
    have hslots := actual_joint_height_supply_aa_slots f n a d r hw hpre
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
    have heq1 : levelSupplied f n K (r + 1) = levelSupplied f n d (r + 1) := hc1
    have heq2 : levelSupplied f n K r = levelSupplied f n d r := hc2
    rw [heq1, heq2]
    omega

/-! ## Level-sum representation and zero-slack joint rational telescoping -/

private noncomputable def levelSum (g : Nat → Nat) : Nat → Nat
  | 0 => g 0
  | d + 1 => levelSum g d + g (d + 1)

private noncomputable def levelWeightSum (g : Nat → Nat) : Nat → Nat
  | 0 => g 0
  | d + 1 => levelWeightSum g d + 2 * levelSum g d + g (d + 1)

private theorem level_additions_split (f : Nat → Bool) (n K : Nat) (h : Int) :
    levelAdditions f n K h = levelFree f n K h + levelSupplied f n K h := by
  have hs := cN_split (fun t => Fw f t = h ∧ f t = true) (fun t => EndN f 0 t) n K
  have h1 : cN (fun t => (Fw f t = h ∧ f t = true) ∧ EndN f 0 t) n K =
      levelSupplied f n K h := by
    unfold levelSupplied
    apply Nat.le_antisymm
    · exact cN_mono _ _ n K (fun t _ _ ht => ⟨ht.1.1, ht.2⟩)
    · exact cN_mono _ _ n K (fun t _ _ ht => ⟨⟨ht.1, ht.2.1⟩, ht.2⟩)
  have h2 : cN (fun t => (Fw f t = h ∧ f t = true) ∧ ¬ EndN f 0 t) n K =
      levelFree f n K h := by
    unfold levelFree
    apply Nat.le_antisymm
    · exact cN_mono _ _ n K (fun t _ _ ht => ⟨ht.1.1, ht.1.2, ht.2⟩)
    · exact cN_mono _ _ n K (fun t _ _ ht => ⟨⟨ht.1, ht.2.1⟩, ht.2.2⟩)
  unfold levelAdditions
  omega

private theorem ratSum_add (P Q : Nat) (g₁ g₂ : Nat → Nat) :
    ∀ H, ratSum P Q (fun h => g₁ h + g₂ h) H = ratSum P Q g₁ H + ratSum P Q g₂ H
  | 0 => rfl
  | H + 1 => by
    simp only [ratSum, ratSum_add P Q g₁ g₂ H, Nat.mul_add]
    omega

private theorem rat_additions_split (P Q : Nat) (f : Nat → Bool) (n K : Nat) (m : Int) (H : Nat) :
    ratAdditions P Q f n K m H = ratFree P Q f n K m H + ratSupplied P Q f n K m H := by
  unfold ratAdditions ratFree ratSupplied
  rw [← ratSum_add]
  congr 1
  funext h
  exact level_additions_split f n K (m + (h : Int))

private theorem ratSum_last_le (P Q : Nat) (g : Nat → Nat) :
    ∀ H, P ^ H * g H ≤ ratSum P Q g H
  | 0 => by simp [ratSum]
  | H + 1 => by simp only [ratSum]; omega

private theorem ratSum_le_pow_mul_sum (P Q : Nat) (hPQ : P ≤ Q) (g : Nat → Nat) :
    ∀ H, ratSum P Q g H ≤ Q ^ H * levelSum g H
  | 0 => by simp [ratSum, levelSum]
  | H + 1 => by
    have ih := ratSum_le_pow_mul_sum P Q hPQ g H
    have hpow : P ^ (H + 1) ≤ Q ^ (H + 1) := Nat.pow_le_pow_left hPQ (H + 1)
    have h1 : Q * ratSum P Q g H ≤ Q * (Q ^ H * levelSum g H) := Nat.mul_le_mul_left Q ih
    have h2 : P ^ (H + 1) * g (H + 1) ≤ Q ^ (H + 1) * g (H + 1) := Nat.mul_le_mul_right _ hpow
    have h3 : Q * (Q ^ H * levelSum g H) = Q ^ (H + 1) * levelSum g H := by
      rw [Nat.pow_succ, Nat.mul_comm (Q ^ H) Q, Nat.mul_assoc]
    simp only [ratSum, levelSum, Nat.mul_add]
    omega

private theorem levelSum_free_le (f : Nat → Bool) (n K : Nat) (m : Int) :
    ∀ H, levelSum (fun h => levelFree f n K (m + (h : Int))) H ≤
      cN (fun t => f t = true ∧ ¬ EndN f 0 t ∧ Fw f t ≤ m + (H : Int)) n K
  | 0 => by
    simp only [levelSum, levelFree]
    exact cN_mono _ _ n K (fun t _ _ ht => ⟨ht.2.1, ht.2.2, by omega⟩)
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

private theorem ratFree_le_pow_free (P Q : Nat) (hPQ : P ≤ Q)
    (f : Nat → Bool) (n K H : Nat) (m : Int) :
    ratFree P Q f n K m H ≤ Q ^ H * free f n K := by
  have h1 := ratSum_le_pow_mul_sum P Q hPQ (fun h => levelFree f n K (m + (h : Int))) H
  have h2 := levelSum_free_le f n K m H
  have h3 : cN (fun t => f t = true ∧ ¬ EndN f 0 t ∧ Fw f t ≤ m + (H : Int)) n K ≤ free f n K := by
    unfold free
    exact cN_mono _ _ n K (fun t _ _ ht => ⟨ht.1, ht.2.1⟩)
  have h4 : Q ^ H * levelSum (fun h => levelFree f n K (m + (h : Int))) H ≤ Q ^ H * free f n K :=
    Nat.mul_le_mul_left (Q ^ H) (Nat.le_trans h2 h3)
  exact Nat.le_trans h1 h4

private theorem lowAdditionWeights_mono_r (f : Nat → Bool) (n : Nat) (r₁ r₂ : Int) (hr : r₁ ≤ r₂) :
    ∀ K, lowAdditionWeights f n r₁ K ≤ lowAdditionWeights f n r₂ K
  | 0 => Int.le_refl 0
  | k + 1 => by
    have ih := lowAdditionWeights_mono_r f n r₁ r₂ hr k
    simp only [lowAdditionWeights]
    have hstep : lowAdditionWeight f r₁ (n + k) ≤ lowAdditionWeight f r₂ (n + k) := by
      unfold lowAdditionWeight
      by_cases h1 : f (n + k) = true ∧ Fw f (n + k) < r₁
      · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]
        omega
      · rw [if_neg h1]
        by_cases h2 : f (n + k) = true ∧ Fw f (n + k) < r₂
        · rw [if_pos h2]; omega
        · rw [if_neg h2]; exact Int.le_refl 0
    omega

private theorem lowAdditionWeights_zero_le_floor (f : Nat → Bool) (n : Nat) (m r : Int)
    (hr : r ≤ m) :
    ∀ K, (∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) → lowAdditionWeights f n r K = 0
  | 0, _ => rfl
  | k + 1, hfloor => by
    have ih := lowAdditionWeights_zero_le_floor f n m r hr k (fun i hi hj => hfloor i hi (by omega))
    have hmin := hfloor (n + k) (by omega) (by omega)
    rw [lowAdditionWeights, ih]
    unfold lowAdditionWeight
    rw [if_neg (fun h => by omega)]
    omega

private theorem lowAdditionWeights_eq_levelWeightSum (f : Nat → Bool) (n : Nat) :
    ∀ K (m : Int), (∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) →
      ∀ d : Nat, lowAdditionWeights f n (m + (d : Int) + 1) K =
        (levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) d : Int)
  | 0, m, _, d => by
    have hzero : ∀ (g : Nat → Nat), (∀ j, g j = 0) → ∀ k, levelSum g k = 0 ∧ levelWeightSum g k = 0 := by
      intro g hg k
      induction k with
      | zero => simp [levelSum, levelWeightSum, hg 0]
      | succ k ih => simp [levelSum, levelWeightSum, ih.1, ih.2, hg (k + 1)]
    have hz := (hzero (fun j => levelAdditions f n 0 (m + (j : Int))) (fun _ => rfl) d).2
    simp [lowAdditionWeights, hz]
  | k + 1, m, hfloor, d => by
    have hbase := lowAdditionWeights_eq_levelWeightSum f n k m
      (fun i hi hj => hfloor i hi (by omega))
    have hmin := hfloor (n + k) (by omega) (by omega)
    by_cases hf : f (n + k) = true
    · have hstepU : ∀ d : Nat,
          levelSum (fun j => levelAdditions f n (k + 1) (m + (j : Int))) d =
            levelSum (fun j => levelAdditions f n k (m + (j : Int))) d +
              (if Fw f (n + k) ≤ m + (d : Int) then 1 else 0) := by
        intro d0
        induction d0 with
        | zero =>
          simp only [levelSum, levelAdditions]
          by_cases h0 : Fw f (n + k) = m + ((0 : Nat) : Int)
          · rw [cN_succ_pos _ n k ⟨h0, hf⟩, if_pos (by omega)]
          · rw [cN_succ_neg _ n k (fun h => h0 h.1), if_neg (by omega)]
            omega
        | succ d0 ih0 =>
          simp only [levelSum, ih0]
          by_cases htop : Fw f (n + k) = m + ((d0 + 1 : Nat) : Int)
          · have hc : levelAdditions f n (k + 1) (m + ((d0 + 1 : Nat) : Int)) =
                levelAdditions f n k (m + ((d0 + 1 : Nat) : Int)) + 1 :=
              cN_succ_pos _ n k ⟨htop, hf⟩
            rw [hc, if_neg (by omega), if_pos (by omega)]
            omega
          · have hc : levelAdditions f n (k + 1) (m + ((d0 + 1 : Nat) : Int)) =
                levelAdditions f n k (m + ((d0 + 1 : Nat) : Int)) :=
              cN_succ_neg _ n k (fun h => htop h.1)
            rw [hc]
            by_cases hle : Fw f (n + k) ≤ m + (d0 : Int)
            · rw [if_pos hle, if_pos (by omega)]; omega
            · rw [if_neg hle, if_neg (by omega)]; omega
      induction d with
      | zero =>
        simp only [lowAdditionWeights, levelWeightSum, hbase 0]
        unfold levelAdditions
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
        simp only [lowAdditionWeights] at ihd ⊢
        rw [hbase (d + 1)]
        simp only [levelWeightSum]
        have hbase_d := hbase d
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
      rw [lowAdditionWeights, hbase d, hfn]
      have hlw : lowAdditionWeight f (m + (d : Int) + 1) (n + k) = 0 := by
        unfold lowAdditionWeight
        rw [if_neg (fun h => hf h.1)]
      rw [hlw]
      omega

/-! ## Exact polynomial telescoping identities for the joint cone -/

private def cW (P Q : Nat) : Nat := P * Q * Q * (Q - P)
private def cU (P Q : Nat) : Nat := 2 * P * P * Q * Q
private def cPrev (P Q : Nat) : Nat := 3 * P * Q * (Q - P) * (Q - P)

private theorem jointM_sub_le (P Q : Nat) (hPQ : P < Q) :
    5 * P * Q ≤ 4 * Q * Q + 3 * P * P := by
  have h1 : 0 ≤ (4 * (Q : Int) - (P : Int)) * ((Q : Int) - (P : Int)) + 2 * (P : Int) * (P : Int) := by
    have ha : 0 ≤ (4 * (Q : Int) - (P : Int)) * ((Q : Int) - (P : Int)) :=
      Int.mul_nonneg (by omega) (by omega)
    have hb : 0 ≤ 2 * (P : Int) * (P : Int) :=
      Int.mul_nonneg (Int.mul_nonneg (by omega) (Int.natCast_nonneg _)) (Int.natCast_nonneg _)
    omega
  have h2 : (4 * (Q : Int) * (Q : Int) + 3 * (P : Int) * (P : Int)) - 5 * (P : Int) * (Q : Int) =
      (4 * (Q : Int) - (P : Int)) * ((Q : Int) - (P : Int)) + 2 * (P : Int) * (P : Int) := by
    grind
  exact Int.ofNat_le.mp (by push_cast; omega)

private theorem p_mul_jointK_le_jointM (P Q : Nat) (hPQ : P < Q) (h2P : Q ≤ 2 * P) :
    P * jointK P Q ≤ jointM P Q := by
  have hsub := jointM_sub_le P Q hPQ
  unfold jointK jointM
  have hdiff :
      ((P * P * (4 * Q * Q + 3 * P * P - 5 * P * Q) : Nat) : Int) -
      ((P * (Q * (Q - P) * (Q - P)) : Nat) : Int) =
      (P : Int) * (2 * (P : Int) * (P : Int) * (P : Int) +
        3 * (P : Int) * (P : Int) * ((Q : Int) - (P : Int)) +
        3 * (P : Int) * ((Q : Int) - (P : Int)) * ((Q : Int) - (P : Int)) -
        ((Q : Int) - (P : Int)) * ((Q : Int) - (P : Int)) * ((Q : Int) - (P : Int))) := by
    push_cast
    rw [Int.ofNat_sub (Nat.le_of_lt hPQ), Int.ofNat_sub hsub]
    push_cast
    grind
  have hdle : (Q : Int) - (P : Int) ≤ (P : Int) := by omega
  have hdnn : 0 ≤ (Q : Int) - (P : Int) := by omega
  have hp3 : ((Q : Int) - (P : Int)) * ((Q : Int) - (P : Int)) * ((Q : Int) - (P : Int)) ≤
      (P : Int) * (P : Int) * (P : Int) := by
    have hsq : ((Q : Int) - (P : Int)) * ((Q : Int) - (P : Int)) ≤ (P : Int) * (P : Int) :=
      Int.mul_le_mul hdle hdle hdnn (Int.natCast_nonneg P)
    exact Int.mul_le_mul hsq hdle hdnn (Int.mul_nonneg (Int.natCast_nonneg P) (Int.natCast_nonneg P))
  have ht1 : 0 ≤ 3 * (P : Int) * (P : Int) * ((Q : Int) - (P : Int)) :=
    Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg (by omega) (Int.natCast_nonneg P)) (Int.natCast_nonneg P)) hdnn
  have ht2 : 0 ≤ 3 * (P : Int) * ((Q : Int) - (P : Int)) * ((Q : Int) - (P : Int)) :=
    Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg (by omega) (Int.natCast_nonneg P)) hdnn) hdnn
  have hp3nn : 0 ≤ (P : Int) * (P : Int) * (P : Int) :=
    Int.mul_nonneg (Int.mul_nonneg (Int.natCast_nonneg P) (Int.natCast_nonneg P)) (Int.natCast_nonneg P)
  have h2p3 : 2 * (P : Int) * (P : Int) * (P : Int) = 2 * ((P : Int) * (P : Int) * (P : Int)) := by grind
  have hnn : 0 ≤ (P : Int) * (2 * (P : Int) * (P : Int) * (P : Int) +
      3 * (P : Int) * (P : Int) * ((Q : Int) - (P : Int)) +
      3 * (P : Int) * ((Q : Int) - (P : Int)) * ((Q : Int) - (P : Int)) -
      ((Q : Int) - (P : Int)) * ((Q : Int) - (P : Int)) * ((Q : Int) - (P : Int))) :=
    Int.mul_nonneg (Int.natCast_nonneg P) (by omega)
  exact Int.ofNat_le.mp (by omega)

private theorem joint_poly_base_ident (P Q a0 a1 : Nat) (hPQ : P < Q) :
    P * (cW P Q * a0 + cU P Q * a0 + cPrev P Q * a0 + jointM P Q * a1) =
      jointM P Q * (Q * a0 + P * a1) := by
  have hsub := jointM_sub_le P Q hPQ
  unfold cW cU cPrev jointM
  have hInt :
      ((P * (P * Q * Q * (Q - P) * a0 + 2 * P * P * Q * Q * a0 +
          3 * P * Q * (Q - P) * (Q - P) * a0 +
          P * P * (4 * Q * Q + 3 * P * P - 5 * P * Q) * a1) : Nat) : Int) =
      ((P * P * (4 * Q * Q + 3 * P * P - 5 * P * Q) * (Q * a0 + P * a1) : Nat) : Int) := by
    push_cast
    rw [Int.ofNat_sub (Nat.le_of_lt hPQ), Int.ofNat_sub hsub]
    push_cast
    grind
  omega

private theorem joint_poly_step_ident (P Q pPow e1 e2 wh uh ah a1 a2 : Nat)
    (hPQ : P < Q) (hb : 3 * e2 + e1 ≤ wh + 3 * ah) :
    jointL P Q * (pPow * P * e2) +
      pPow * P * (cW P Q * (wh + 2 * uh + a1) + cU P Q * (uh + a1) +
        cPrev P Q * a1 + jointM P Q * a2) +
      Q * (P * jointK P Q * (pPow * e1)) ≤
      Q * (pPow * (cW P Q * wh + cU P Q * uh + cPrev P Q * ah + jointM P Q * a1)) +
      jointM P Q * (pPow * P * a2) +
      P * jointK P Q * (pPow * P * e2) := by
  have hsub := jointM_sub_le P Q hPQ
  unfold cW cU cPrev jointL jointK jointM
  have hdiff :
      ((Q * (pPow * (P * Q * Q * (Q - P) * wh + 2 * P * P * Q * Q * uh +
          3 * P * Q * (Q - P) * (Q - P) * ah +
          P * P * (4 * Q * Q + 3 * P * P - 5 * P * Q) * a1)) +
        P * P * (4 * Q * Q + 3 * P * P - 5 * P * Q) * (pPow * P * a2) +
        P * (Q * (Q - P) * (Q - P)) * (pPow * P * e2) : Nat) : Int) -
      (((3 * Q + P) * (Q * (Q - P) * (Q - P)) * (pPow * P * e2) +
        pPow * P * (P * Q * Q * (Q - P) * (wh + 2 * uh + a1) +
          2 * P * P * Q * Q * (uh + a1) +
          3 * P * Q * (Q - P) * (Q - P) * a1 +
          P * P * (4 * Q * Q + 3 * P * P - 5 * P * Q) * a2) +
        Q * (P * (Q * (Q - P) * (Q - P)) * (pPow * e1)) : Nat) : Int) =
      (pPow : Int) * (P : Int) * (Q : Int) * ((Q * (Q - P) * (Q - P) : Nat) : Int) *
        (((wh + 3 * ah : Nat) : Int) - ((3 * e2 + e1 : Nat) : Int)) := by
    push_cast
    rw [Int.ofNat_sub (Nat.le_of_lt hPQ), Int.ofNat_sub hsub]
    push_cast
    grind
  have hnn : 0 ≤ (pPow : Int) * (P : Int) * (Q : Int) * ((Q * (Q - P) * (Q - P) : Nat) : Int) *
      (((wh + 3 * ah : Nat) : Int) - ((3 * e2 + e1 : Nat) : Int)) := by
    have hA : 0 ≤ (pPow : Int) * (P : Int) * (Q : Int) * ((Q * (Q - P) * (Q - P) : Nat) : Int) :=
      Int.mul_nonneg
        (Int.mul_nonneg (Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
          (Int.natCast_nonneg _))
        (Int.natCast_nonneg _)
    exact Int.mul_nonneg hA (by omega)
  exact Int.ofNat_le.mp (by omega)

private theorem joint_rational_supplied_invariant (P Q : Nat) (hPQ : P < Q)
    (f : Nat → Bool) (n a K : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    ∀ H, jointL P Q * ratSupplied P Q f n K m (H + 1) +
        P ^ (H + 1) * (
          cW P Q * levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) H +
          cU P Q * levelSum (fun j => levelAdditions f n K (m + (j : Int))) H +
          cPrev P Q * levelAdditions f n K (m + (H : Int)) +
          jointM P Q * levelAdditions f n K (m + ((H + 1 : Nat) : Int))) ≤
      jointM P Q * ratAdditions P Q f n K m (H + 1) +
        P * jointK P Q * (P ^ (H + 1) * levelSupplied f n K (m + ((H + 1 : Nat) : Int))) := by
  have hE0 : levelSupplied f n K (m + ((0 : Nat) : Int)) = 0 := by
    apply cN_zero_of
    intro t hnt htK ht
    exact block_prefix_low_clock_not_endable f n a t hw hpre hnt m
      (fun i hi hj => hfloor i hi (by omega)) (by omega) ht.2
  have hE1 : levelSupplied f n K (m + ((1 : Nat) : Int)) = 0 := by
    apply cN_zero_of
    intro t hnt htK ht
    exact block_prefix_low_clock_not_endable f n a t hw hpre hnt m
      (fun i hi hj => hfloor i hi (by omega)) (by omega) ht.2
  intro H
  induction H with
  | zero =>
    simp only [ratSupplied, ratAdditions, ratSum, levelWeightSum, levelSum, Nat.zero_add, Nat.pow_one]
    rw [hE0, hE1]
    have hbase := joint_poly_base_ident P Q
      (levelAdditions f n K (m + ((0 : Nat) : Int)))
      (levelAdditions f n K (m + ((1 : Nat) : Int))) hPQ
    omega
  | succ H ih =>
    have hb := joint_height_supply_aa_spacing_budget f n a K (m + (H : Int) + 1) hw hpre
    have hW := lowAdditionWeights_eq_levelWeightSum f n K m hfloor H
    rw [hW] at hb
    have hAA := doubleAscent_le_levelAdditions f n K (m + (H : Int) + 1 - 1)
    have hEqE2 : levelSupplied f n K (m + (H : Int) + 1 + 1) =
        levelSupplied f n K (m + ((H + 1 + 1 : Nat) : Int)) := by
      rw [show m + (H : Int) + 1 + 1 = m + ((H + 1 + 1 : Nat) : Int) by omega]
    have hEqE1 : levelSupplied f n K (m + (H : Int) + 1) =
        levelSupplied f n K (m + ((H + 1 : Nat) : Int)) := by
      rw [show m + (H : Int) + 1 = m + ((H + 1 : Nat) : Int) by omega]
    have hEqA : levelAdditions f n K (m + (H : Int) + 1 - 1) =
        levelAdditions f n K (m + (H : Int)) := by
      rw [show m + (H : Int) + 1 - 1 = m + (H : Int) by omega]
    rw [hEqE2, hEqE1] at hb
    rw [hEqA] at hAA
    have hbNat :
        3 * levelSupplied f n K (m + ((H + 1 + 1 : Nat) : Int)) +
          levelSupplied f n K (m + ((H + 1 : Nat) : Int)) ≤
        levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) H +
          3 * levelAdditions f n K (m + (H : Int)) := by
      omega
    have hQih := Nat.mul_le_mul_left Q ih
    have hstep := joint_poly_step_ident P Q (P ^ (H + 1))
      (levelSupplied f n K (m + ((H + 1 : Nat) : Int)))
      (levelSupplied f n K (m + ((H + 1 + 1 : Nat) : Int)))
      (levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) H)
      (levelSum (fun j => levelAdditions f n K (m + (j : Int))) H)
      (levelAdditions f n K (m + (H : Int)))
      (levelAdditions f n K (m + ((H + 1 : Nat) : Int)))
      (levelAdditions f n K (m + ((H + 1 + 1 : Nat) : Int)))
      hPQ hbNat
    have hpow : P ^ (H + 1 + 1) = P ^ (H + 1) * P := Nat.pow_succ P (H + 1)
    have hreE : ratSupplied P Q f n K m (H + 1 + 1) =
        Q * ratSupplied P Q f n K m (H + 1) +
          P ^ (H + 1 + 1) * levelSupplied f n K (m + ((H + 1 + 1 : Nat) : Int)) := rfl
    have hreA : ratAdditions P Q f n K m (H + 1 + 1) =
        Q * ratAdditions P Q f n K m (H + 1) +
          P ^ (H + 1 + 1) * levelAdditions f n K (m + ((H + 1 + 1 : Nat) : Int)) := rfl
    have hreW : levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1) =
        levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) H +
          2 * levelSum (fun j => levelAdditions f n K (m + (j : Int))) H +
          levelAdditions f n K (m + ((H + 1 : Nat) : Int)) := rfl
    have hreU : levelSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1) =
        levelSum (fun j => levelAdditions f n K (m + (j : Int))) H +
          levelAdditions f n K (m + ((H + 1 : Nat) : Int)) := rfl
    rw [hreE, hreA, hreW, hreU, hpow]
    have hL1 : jointL P Q * (Q * ratSupplied P Q f n K m (H + 1)) =
        Q * (jointL P Q * ratSupplied P Q f n K m (H + 1)) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (jointL P Q) Q, Nat.mul_assoc]
    have hM1 : jointM P Q * (Q * ratAdditions P Q f n K m (H + 1)) =
        Q * (jointM P Q * ratAdditions P Q f n K m (H + 1)) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (jointM P Q) Q, Nat.mul_assoc]
    rw [Nat.mul_add (jointL P Q), Nat.mul_add (jointM P Q), hL1, hM1]
    rw [Nat.mul_add Q, Nat.mul_add Q] at hQih
    omega

private theorem joint_rational_cancelled_invariant (P Q : Nat) (hPQ : P < Q) (h2P : Q ≤ 2 * P)
    (f : Nat → Bool) (n a K H : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    jointL P Q * ratSupplied P Q f n K m (H + 1) +
      P ^ (H + 1) * (
        cW P Q * levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) H +
        cU P Q * levelSum (fun j => levelAdditions f n K (m + (j : Int))) H +
        cPrev P Q * levelAdditions f n K (m + (H : Int))) ≤
      jointM P Q * ratAdditions P Q f n K m (H + 1) := by
  have hinv := joint_rational_supplied_invariant P Q hPQ f n a K m hw hpre hfloor H
  have hPKM := p_mul_jointK_le_jointM P Q hPQ h2P
  have hEA : levelSupplied f n K (m + ((H + 1 : Nat) : Int)) ≤
      levelAdditions f n K (m + ((H + 1 : Nat) : Int)) := by
    have hsp := level_additions_split f n K (m + ((H + 1 : Nat) : Int))
    omega
  have hcancel :
      P * jointK P Q * (P ^ (H + 1) * levelSupplied f n K (m + ((H + 1 : Nat) : Int))) ≤
        P ^ (H + 1) * (jointM P Q * levelAdditions f n K (m + ((H + 1 : Nat) : Int))) := by
    have h1 : P * jointK P Q * levelSupplied f n K (m + ((H + 1 : Nat) : Int)) ≤
        jointM P Q * levelAdditions f n K (m + ((H + 1 : Nat) : Int)) :=
      Nat.mul_le_mul hPKM hEA
    have h2 := Nat.mul_le_mul_left (P ^ (H + 1)) h1
    have hcomm :
        P * jointK P Q * (P ^ (H + 1) * levelSupplied f n K (m + ((H + 1 : Nat) : Int))) =
        P ^ (H + 1) * (P * jointK P Q * levelSupplied f n K (m + ((H + 1 : Nat) : Int))) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (P * jointK P Q) (P ^ (H + 1)), Nat.mul_assoc]
    rw [hcomm]
    exact h2
  rw [Nat.mul_add] at hinv
  omega

/-! ## Main joint rational capacity, exponential, and low-weight theorems -/

/-- Uniform rational height-weighted capacity across the entire coupled two-height cone
`1/2 ≤ P / Q < κ_joint ≈ 0.563708` (`1 / κ_joint ≈ 1.77397`). -/
theorem joint_rational_height_weighted_capacity (P Q : Nat)
    (hPQ : P < Q) (h2P : Q ≤ 2 * P) (hcone : jointM P Q ≤ jointL P Q)
    (f : Nat → Bool) (n a K H : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    (jointL P Q - jointM P Q) * ratAdditions P Q f n K m H ≤
      jointL P Q * ratFree P Q f n K m H := by
  have hsplit := rat_additions_split P Q f n K m H
  cases H with
  | zero =>
    have hE0 : levelSupplied f n K (m + ((0 : Nat) : Int)) = 0 := by
      apply cN_zero_of
      intro t hnt htK ht
      exact block_prefix_low_clock_not_endable f n a t hw hpre hnt m
        (fun i hi hj => hfloor i hi (by omega)) (by omega) ht.2
    have hz : ratSupplied P Q f n K m 0 = 0 := by
      unfold ratSupplied ratSum
      exact hE0
    rw [hz, Nat.add_zero] at hsplit
    rw [hsplit]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  | succ H =>
    have hinv := joint_rational_cancelled_invariant P Q hPQ h2P f n a K H m hw hpre hfloor
    have hLE : jointL P Q * ratSupplied P Q f n K m (H + 1) ≤
        jointM P Q * ratAdditions P Q f n K m (H + 1) := by omega
    have hsub : (jointL P Q - jointM P Q) * ratAdditions P Q f n K m (H + 1) +
        jointM P Q * ratAdditions P Q f n K m (H + 1) =
        jointL P Q * ratAdditions P Q f n K m (H + 1) := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hcone]
    have hadd : jointL P Q * ratAdditions P Q f n K m (H + 1) =
        jointL P Q * ratFree P Q f n K m (H + 1) +
        jointL P Q * ratSupplied P Q f n K m (H + 1) := by
      rw [hsplit, Nat.mul_add]
    omega

/-- Unweighted arbitrary-height exponential bound for every rational `P / Q` in the
coupled two-height cone `1/2 ≤ P / Q < κ_joint ≈ 0.563708`. -/
theorem joint_rational_height_exp_bound (P Q : Nat)
    (hPQ : P < Q) (h2P : Q ≤ 2 * P) (hcone : jointM P Q ≤ jointL P Q)
    (f : Nat → Bool) (n a K h : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    (jointL P Q - jointM P Q) * P ^ h * levelAdditions f n K (m + (h : Int)) ≤
      jointL P Q * Q ^ h * free f n K := by
  have hcap := joint_rational_height_weighted_capacity P Q hPQ h2P hcone f n a K h m hw hpre hfloor
  have hlast := ratSum_last_le P Q (fun j => levelAdditions f n K (m + (j : Int))) h
  have hfree := ratFree_le_pow_free P Q (Nat.le_of_lt hPQ) f n K h m
  have h1 : (jointL P Q - jointM P Q) * (P ^ h * levelAdditions f n K (m + (h : Int))) ≤
      (jointL P Q - jointM P Q) * ratAdditions P Q f n K m h :=
    Nat.mul_le_mul_left _ hlast
  have h2 : jointL P Q * ratFree P Q f n K m h ≤ jointL P Q * (Q ^ h * free f n K) :=
    Nat.mul_le_mul_left _ hfree
  rw [Nat.mul_assoc, Nat.mul_assoc]
  exact Nat.le_trans h1 (Nat.le_trans hcap h2)

/-- Arbitrary-depth low-weight bound across the entire coupled two-height cone without any
`1 / (jointL - jointM)` prefactor blowup. -/
theorem joint_rational_low_weights_bound (P Q : Nat)
    (hPQ : P < Q) (h2P : Q ≤ 2 * P) (hcone : jointM P Q ≤ jointL P Q)
    (f : Nat → Bool) (n a K d : Nat) (m r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i)
    (hr : r ≤ m + (d : Int)) :
    ((P ^ (d + 1) * Q ^ 2 * (Q - P) : Nat) : Int) * lowAdditionWeights f n r K ≤
      ((jointM P Q * Q ^ d * free f n K : Nat) : Int) := by
  cases d with
  | zero =>
    have hz := lowAdditionWeights_zero_le_floor f n m r (by omega) K hfloor
    rw [hz, Int.mul_zero]
    exact Int.natCast_nonneg _
  | succ H =>
    have hmono := lowAdditionWeights_mono_r f n r (m + (H : Int) + 1) (by omega) K
    have hW := lowAdditionWeights_eq_levelWeightSum f n K m hfloor H
    have hinv := joint_rational_cancelled_invariant P Q hPQ h2P f n a K H m hw hpre hfloor
    have hsplit := rat_additions_split P Q f n K m (H + 1)
    have hMsup : jointM P Q * ratSupplied P Q f n K m (H + 1) ≤
        jointL P Q * ratSupplied P Q f n K m (H + 1) :=
      Nat.mul_le_mul_right _ hcone
    have hterm :
        P ^ (H + 1) * (cW P Q * levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) H) ≤
          jointM P Q * ratFree P Q f n K m (H + 1) := by
      rw [hsplit, Nat.mul_add (jointM P Q), Nat.mul_add (P ^ (H + 1)), Nat.mul_add (P ^ (H + 1))] at hinv
      omega
    have hfree := ratFree_le_pow_free P Q (Nat.le_of_lt hPQ) f n K (H + 1) m
    have hNat :
        P ^ (H + 1 + 1) * Q ^ 2 * (Q - P) *
          levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) H ≤
        jointM P Q * Q ^ (H + 1) * free f n K := by
      have hrhs : jointM P Q * ratFree P Q f n K m (H + 1) ≤
          jointM P Q * (Q ^ (H + 1) * free f n K) :=
        Nat.mul_le_mul_left _ hfree
      have hlhs :
          P ^ (H + 1) * (cW P Q * levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) H) =
          P ^ (H + 1 + 1) * Q ^ 2 * (Q - P) *
            levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) H := by
        unfold cW
        have hq2 : Q ^ 2 = Q * Q := by rw [Nat.pow_succ, Nat.pow_one]
        have hp1 : P ^ (H + 1 + 1) = P ^ (H + 1) * P := Nat.pow_succ P (H + 1)
        rw [hq2, hp1]
        simp only [Nat.mul_assoc]
      rw [hlhs] at hterm
      rw [Nat.mul_assoc (jointM P Q)]
      exact Nat.le_trans hterm hrhs
    have hInt :
        ((P ^ (H + 1 + 1) * Q ^ 2 * (Q - P) : Nat) : Int) * lowAdditionWeights f n r K ≤
          ((P ^ (H + 1 + 1) * Q ^ 2 * (Q - P) : Nat) : Int) *
            (levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) H : Int) := by
      rw [← hW]
      exact Int.mul_le_mul_of_nonneg_left hmono (Int.natCast_nonneg _)
    have hCast :
        ((P ^ (H + 1 + 1) * Q ^ 2 * (Q - P) : Nat) : Int) *
            (levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) H : Int) ≤
          ((jointM P Q * Q ^ (H + 1) * free f n K : Nat) : Int) := by
      exact_mod_cast hNat
    exact Int.le_trans hInt hCast

/-! ## Concrete unconditional bounds breaking the `1.8067` cone barrier -/

/-- Unconditional actual-`EndN` exponential bound at `P / Q = 5 / 9` (base `9 / 5 = 1.8000`),
strictly breaking the `E-785`/`E-788` 3-spacing cone barrier `1.8067`. -/
theorem actual_height_exp_nine_fifths (f : Nat → Bool) (n a K h : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    43 * 5 ^ h * levelAdditions f n K (m + (h : Int)) ≤ 768 * 9 ^ h * free f n K := by
  have hb := joint_rational_height_exp_bound 5 9 (by decide) (by decide) (by decide)
    f n a K h m hw hpre hfloor
  have hL : jointL 5 9 = 4608 := by decide
  have hM : jointM 5 9 = 4350 := by decide
  rw [hL, hM] at hb
  have hsub : 4608 - 4350 = 258 := by decide
  rw [hsub] at hb
  have h1 : 258 * 5 ^ h * levelAdditions f n K (m + (h : Int)) =
      6 * (43 * 5 ^ h * levelAdditions f n K (m + (h : Int))) := by grind
  have h2 : 4608 * 9 ^ h * free f n K = 6 * (768 * 9 ^ h * free f n K) := by grind
  omega

/-- Unconditional actual-`EndN` exponential bound at `P / Q = 9 / 16` (base `16 / 9 ≈ 1.7778`). -/
theorem actual_height_exp_sixteen_ninths (f : Nat → Bool) (n a K h : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    127 * 9 ^ h * levelAdditions f n K (m + (h : Int)) ≤ 14896 * 16 ^ h * free f n K := by
  have hb := joint_rational_height_exp_bound 9 16 (by decide) (by decide) (by decide)
    f n a K h m hw hpre hfloor
  have hL : jointL 9 16 = 44688 := by decide
  have hM : jointM 9 16 = 44307 := by decide
  rw [hL, hM] at hb
  have hsub : 44688 - 44307 = 381 := by decide
  rw [hsub] at hb
  have h1 : 381 * 9 ^ h * levelAdditions f n K (m + (h : Int)) =
      3 * (127 * 9 ^ h * levelAdditions f n K (m + (h : Int))) := by grind
  have h2 : 44688 * 16 ^ h * free f n K = 3 * (14896 * 16 ^ h * free f n K) := by grind
  omega

/-- Unconditional actual-`EndN` exponential bound at `P / Q = 107 / 190` (base `190 / 107 ≈ 1.7757`,
within `0.10%` of the exact joint cone root `1.77397`), narrowing the `PROVED-LEAN` actual-`EndN`
exponential growth bracket from `[5/3, 199/110]` (`E-786`/`E-788`) to `[5/3, 190/107]`. -/
theorem actual_height_exp_190_107 (f : Nat → Bool) (n a K h : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    3448517 * 107 ^ h * levelAdditions f n K (m + (h : Int)) ≤
      886132070 * 190 ^ h * free f n K := by
  have hb := joint_rational_height_exp_bound 107 190 (by decide) (by decide) (by decide)
    f n a K h m hw hpre hfloor
  have hL : jointL 107 190 = 886132070 := by decide
  have hM : jointM 107 190 = 882683553 := by decide
  rw [hL, hM] at hb
  have hsub : 886132070 - 882683553 = 3448517 := by decide
  rw [hsub] at hb
  exact hb

end Recaman.JointHeightSpacingCapacity
