import Recaman.ExcursionClimbSpacing
import Recaman.SharpThreeSpacingCapacity

namespace Recaman.ExactFiveThirdsCapacity

open Recaman.ExcursionClimbSpacing Recaman.SharpThreeSpacingCapacity
open Recaman.SupplyExcursionSpacing Recaman.SupplyHeightWeightBudget
open Recaman.SupplyDescentWeight Recaman.SupplyDescentSlots Recaman.SupplyAreaCrossings
open Recaman.FloorSupplyPotential Recaman.FloorSupplyFreeBudget Recaman.LowTargetWeightedGap
open Recaman.GapSquareLowAdditions
open Recaman.LevelTriangleArea Recaman.AdditionRankSlack Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction Recaman.SuffixHallOwnerMap
open Classical

/-! # Exact `5/3` actual-`EndN` capacity via 8-slot double-ascent excursion spacing (`E-797`)

In `E-794`, the coupled two-height 3+1 slot injection on `p = floorPotential f n (r - 1)`
established `3 * E_{r+1} + E_r ≤ lowAdditionWeights f n r K + 3 * doubleAscent f n K (r - 1)`,
reaching `190/107 ≈ 1.7757` (cone root `1.77397`), while `E-796` proved that the `3 * AA_{r-1}`
overflow term is pointwise sharp to constant slack `1` and cannot be dropped at a single height.

Here we break the `1.77397` barrier all the way down to the **exact** `E-786` lower-bound base
`5/3` by observing that any supplied addition `t` at height `r + 1` which is ALSO an in-window
double ascent (`f t = true ∧ f (t + 1) = true`, so `Fw` climbs `r + 1 → r + 2 → r + 3`) raises
`p = floorPotential f n (r - 1)` by at least `+8` before the next visit to `{r, r + 1}`:
`p(t + 1) = p t + 2`, `p(t + 2) = p t + 5`, `p(t + 3) ≥ p t + 7`, `p(t + 4) ≥ p t + 8`.

Assigning `3 + δ` slots (for any `δ ≤ 5`, sharp at `δ = 5` / 8 slots, where `δ = 6` fails) to
every supplied double ascent at height `r + 1`, `3` slots to every remaining supplied addition
at height `r + 1`, and `1` slot to every supplied addition at height `r` injects into
`descentSlots f n r K ⊕ (AA_{r-1} × {0, ..., 2 + δ})`, proving unconditionally for every `δ ≤ 5`:
  `3 * E_{r+1} + δ * EAA_{r+1} + E_r ≤ W(r) + (3 + δ) * AA_{r-1}`.

At `δ = 2` (5 slots) and the critical ratio `q = 3/5`, the double-ascent overflow cancels
identically across heights (`2 * (3/5)^h ≥ 5 * (3/5)^{h+2}` since `2 ≥ 9/5`), and the exact
algebraic identity
  `5 * T(H) + 3 * A_{H+1} + A_H = 3 * T(H + 1) + W(H)`
for the triangular height sum `T(H) = ∑_{h=0}^H (H - h + 1) * A_{m+h}` telescopes in one
two-term induction to:
- `3 ^ (H + 1) * triAdditions f n K m (H + 1) ≤ 9 * 5 ^ H * free f n K` (`∀ H : Nat`),
- `5 * 3 ^ h * levelAdditions f n K (m + h) ≤ 9 * 5 ^ h * free f n K` (`∀ h : Nat`),
- `5 * 3 ^ H * additions f n K ≤ 9 * 5 ^ H * free f n K` on every height strip `[m, m + H]`
  (matching `E-786`'s `2 * 5 ^ H * (free + O_c) ≤ 5 * 3 ^ H * additions` to a uniform factor
  of `9/2` for every `H`, closing the actual-`EndN` exponential growth base to **exact `5/3`**),
- `(25 * 3 ^ d : Int) * lowAdditionWeights f n r K ≤ (54 * 5 ^ d : Int) * free f n K`,
- `(25 * 3 ^ d : Int) * (j + 1)^2 ≤ (54 * 5 ^ d : Int) * free f n (b - n)` (without `hpos` or
  height ceiling).
-/

/-! ## Supplied double ascents and triangular level sums -/

/-- Supplied in-window double ascents at height `h`: indices `t ∈ [n, n + K)` with
`Fw f t = h`, `EndN f 0 t`, `f (t + 1) = true`, and `t + 1 < n + K`. -/
noncomputable def suppliedDoubleAscent (f : Nat → Bool) (n K : Nat) (h : Int) : Nat :=
  cN (fun t => Fw f t = h ∧ EndN f 0 t ∧ f (t + 1) = true ∧ t + 1 < n + K) n K

private noncomputable def levelSum (g : Nat → Nat) : Nat → Nat
  | 0 => g 0
  | H + 1 => levelSum g H + g (H + 1)

private noncomputable def levelWeightSum (g : Nat → Nat) : Nat → Nat
  | 0 => g 0
  | H + 1 => levelWeightSum g H + 2 * levelSum g H + g (H + 1)

/-- Triangular level sum `∑_{h=0}^H (H - h + 1) * g h`. -/
noncomputable def triSum (g : Nat → Nat) : Nat → Nat
  | 0 => g 0
  | H + 1 => triSum g H + levelSum g (H + 1)

/-- Triangular height-weighted sum of additions above floor `m` up to `m + H`. -/
noncomputable def triAdditions (f : Nat → Bool) (n K : Nat) (m : Int) (H : Nat) : Nat :=
  triSum (fun h => levelAdditions f n K (m + (h : Int))) H

/-! ## Same-height crossing, excursion exit, and monotonicity helpers -/

private theorem latest_same_height_supply_crossing (f : Nat → Bool) (n a u : Nat) (r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hnu : n ≤ u) (hFu : Fw f u = r) (he : EndN f 0 u) :
    ∃ q, n < q ∧ q < u ∧ Fw f q < r ∧
      areaCrossesDown (floorPotential f n (r - 1)) (floorPotential f n (r - 1) u + 1) q ∧
      ∀ j, q < j → j ≤ u →
        ¬ areaCrossesDown (floorPotential f n (r - 1)) (floorPotential f n (r - 1) u + 1) j := by
  let p := floorPotential f n (r - 1)
  have hAnchor : ∃ s, n ≤ s ∧ s < u ∧ p u + 1 ≤ p s := by
    obtain ⟨_, s, k, _, hsk, hk, hLevel, hArea⟩ := he
    rw [hsk] at hLevel
    have hsF : Fw f s = r - 1 := by omega
    have hAs : Ar f s (u - s) = 0 := by rw [show u - s = k by omega]; exact hArea
    by_cases hns : n ≤ s
    · refine ⟨s, hns, by omega, ?_⟩
      have hsp := area_split_at f n s u hns (by omega)
      rw [hAs, hsF] at hsp
      have hl : ((u - n : Nat) : Int) = ((s - n : Nat) : Int) + ((u - s : Nat) : Int) := by omega
      change p u + 1 ≤ p s
      unfold p floorPotential
      rw [hsp, hl, Int.add_mul]
      have hmul :
          ((u - s : Nat) : Int) * (r - 1 - Fw f n) +
            ((u - s : Nat) : Int) * (Fw f n - (r - 1 + 1)) =
          -((u - s : Nat) : Int) := by
        rw [← Int.mul_add, show r - 1 - Fw f n + (Fw f n - (r - 1 + 1)) = -1 by omega]
        omega
      have hpos : (1 : Int) ≤ ((u - s : Nat) : Int) := by omega
      omega
    · have hp := (block_suffix_positive_walk f 0 n a hw hpre s (Nat.zero_le _) (by omega)).2
      simp only [Nat.zero_add] at hp
      have hsp := area_split_at f s n u (by omega) hnu
      rw [hAs, hsF] at hsp
      have hmul :
          ((u - n : Nat) : Int) * (Fw f n - (r - 1)) -
            ((u - n : Nat) : Int) * (Fw f n - (r - 1 + 1)) =
          ((u - n : Nat) : Int) := by
        rw [← Int.mul_sub, show Fw f n - (r - 1) - (Fw f n - (r - 1 + 1)) = 1 by omega]
        omega
      have hneg : p u + 1 ≤ 0 := by
        change floorPotential f n (r - 1) u + 1 ≤ 0
        unfold floorPotential
        omega
      have hz : p n = 0 := by simp [p, floorPotential, Ar]
      have hlt : n < u := by
        by_cases hne : n = u
        · rw [← hne, hz] at hneg; omega
        · omega
      exact ⟨n, Nat.le_refl _, hlt, by omega⟩
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
    · rw [heq] at hqF; omega
    · omega
  refine ⟨q, hqn, hqu, hqF, hcross, ?_⟩
  intro j hqj hju hjcr
  have hno := hafter (j - n) (by omega) (by omega)
  rw [Nat.add_sub_cancel' (show n ≤ j by omega)] at hno
  exact hno ⟨by omega, hjcr⟩

private theorem lastAbove_bounds (f : Nat → Bool) (n : Nat) (r : Int) :
    ∀ k, n ≤ lastAbove f n r k ∧ lastAbove f n r k ≤ n + k
  | 0 => ⟨Nat.le_refl n, Nat.le_refl n⟩
  | k + 1 => by
    unfold lastAbove
    split
    · omega
    · have ih := lastAbove_bounds f n r k; omega

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
    · rw [if_pos hge]; exact hge
    · rw [if_neg hge] at h ⊢; exact lastAbove_gt_ge f n r k h

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
    have hlt := hbel (a + len + 1) (by omega) (by omega)
    rw [show a + (len + 1) = a + len + 1 by omega, hstep]
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
    · rw [← h] at hstep; omega
    · have := hQe.1; omega
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
  · have := hb₂ (d₁ + 1) (by omega) (by omega); omega
  · exact heq
  · have := hb₁ (d₂ + 1) (by omega) (by omega); omega

/-! ## Pairwise separation lemmas (including the 8-slot double-ascent jump) -/

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
  · rw [heq] at hs; omega
  · have htStep := floor_potential_step f n (t - 1) (r - 1) (by omega)
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
  have hgap2 : t + 2 < u := by
    by_cases he1 : t + 1 = u
    · rw [he1] at h1; omega
    · by_cases he2 : t + 2 = u
      · rw [he2] at h2; omega
      · omega
  have hs1 := floor_potential_step f n t (r - 1) hnt
  have hs2 := floor_potential_step f n (t + 1) (r - 1) (by omega)
  change p (t + 1) = p t + Fw f (t + 1) - (r - 1 + 1) at hs1
  change p (t + 2) = p (t + 1) + Fw f (t + 2) - (r - 1 + 1) at hs2
  by_cases h : p t + 3 ≤ p u
  · exact h
  · obtain ⟨j, hj1, hj2, hcr⟩ := downcross_from_end_values p (t + 2) u (p u + 1)
      (by omega) (by omega) (by omega)
    exact (hAfter j (by omega) hj2 hcr).elim

private theorem double_ascent_four_step_jump (f : Nat → Bool) (n t : Nat) (r : Int)
    (hnt : n ≤ t) (hFt : Fw f t = r + 1) (hA0 : f t = true) (hA1 : f (t + 1) = true) :
    Fw f (t + 1) = r + 2 ∧ Fw f (t + 2) = r + 3 ∧
      r + 2 ≤ Fw f (t + 3) ∧ r + 1 ≤ Fw f (t + 4) ∧
      floorPotential f n (r - 1) t + 8 ≤ floorPotential f n (r - 1) (t + 4) := by
  have h1 : Fw f (t + 1) = r + 2 := by
    rcases fw_cases f t with ⟨h, _⟩ | ⟨_, h⟩
    · omega
    · simp [hA0] at h
  have h2 : Fw f (t + 2) = r + 3 := by
    rcases fw_cases f (t + 1) with ⟨h, _⟩ | ⟨_, h⟩
    · rw [show t + 1 + 1 = t + 2 by omega] at h; omega
    · simp [hA1] at h
  have h3 : r + 2 ≤ Fw f (t + 3) := by
    rcases fw_cases f (t + 2) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [show t + 2 + 1 = t + 3 by omega] at h; omega
    · rw [show t + 2 + 1 = t + 3 by omega] at h; omega
  have h4 : r + 1 ≤ Fw f (t + 4) := by
    rcases fw_cases f (t + 3) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [show t + 3 + 1 = t + 4 by omega] at h; omega
    · rw [show t + 3 + 1 = t + 4 by omega] at h; omega
  have hs1 := floor_potential_step f n t (r - 1) hnt
  have hs2 := floor_potential_step f n (t + 1) (r - 1) (by omega)
  have hs3 := floor_potential_step f n (t + 2) (r - 1) (by omega)
  have hs4 := floor_potential_step f n (t + 3) (r - 1) (by omega)
  rw [show t + 1 + 1 = t + 2 by omega] at hs2
  rw [show t + 2 + 1 = t + 3 by omega] at hs3
  rw [show t + 3 + 1 = t + 4 by omega] at hs4
  exact ⟨h1, h2, h3, h4, by omega⟩

private theorem spacing_aa_rp1_rp1 (f : Nat → Bool) (n t₁ t₂ q₂ : Nat) (r : Int)
    (hnt₁ : n ≤ t₁) (ht₁₂ : t₁ < t₂) (hq : q₂ < t₁)
    (hF₁ : Fw f t₁ = r + 1) (hF₂ : Fw f t₂ = r + 1)
    (hA₀ : f t₁ = true) (hA₁ : f (t₁ + 1) = true)
    (hAfter : ∀ j, q₂ < j → j < t₂ →
      ¬ areaCrossesDown (floorPotential f n (r - 1)) (floorPotential f n (r - 1) t₂) j) :
    floorPotential f n (r - 1) t₁ + 8 ≤ floorPotential f n (r - 1) t₂ := by
  let p := floorPotential f n (r - 1)
  change p t₁ + 8 ≤ p t₂
  obtain ⟨h1, h2, h3, _, hp4⟩ := double_ascent_four_step_jump f n t₁ r hnt₁ hF₁ hA₀ hA₁
  change p t₁ + 8 ≤ p (t₁ + 4) at hp4
  have hge4 : t₁ + 4 ≤ t₂ := by
    by_cases e1 : t₁ + 1 = t₂
    · rw [e1] at h1; omega
    · by_cases e2 : t₁ + 2 = t₂
      · rw [e2] at h2; omega
      · by_cases e3 : t₁ + 3 = t₂
        · rw [e3] at h3; omega
        · omega
  by_cases heq : t₁ + 4 = t₂
  · rw [← heq]; exact hp4
  · have htStep := floor_potential_step f n (t₂ - 1) (r - 1) (by omega)
    rw [show t₂ - 1 + 1 = t₂ by omega, hF₂] at htStep
    change p t₂ = p (t₂ - 1) + (r + 1) - (r - 1 + 1) at htStep
    by_cases h : p t₁ + 8 ≤ p t₂
    · exact h
    · obtain ⟨j, hj1, hj2, hcr⟩ := downcross_from_end_values p (t₁ + 4) (t₂ - 1) (p t₂)
        (by omega) (by omega) (by omega)
      exact (hAfter j (by omega) (by omega) hcr).elim

private theorem spacing_aa_rp1_r (f : Nat → Bool) (n t u qu : Nat) (r : Int)
    (hnt : n ≤ t) (htu : t < u) (hq : qu < t)
    (hFt : Fw f t = r + 1) (hFu : Fw f u = r)
    (hA₀ : f t = true) (hA₁ : f (t + 1) = true)
    (hAfter : ∀ j, qu < j → j ≤ u →
      ¬ areaCrossesDown (floorPotential f n (r - 1)) (floorPotential f n (r - 1) u + 1) j) :
    floorPotential f n (r - 1) t + 8 ≤ floorPotential f n (r - 1) u := by
  let p := floorPotential f n (r - 1)
  change p t + 8 ≤ p u
  obtain ⟨h1, h2, h3, h4, hp4⟩ := double_ascent_four_step_jump f n t r hnt hFt hA₀ hA₁
  change p t + 8 ≤ p (t + 4) at hp4
  have hgt4 : t + 4 < u := by
    by_cases e1 : t + 1 = u
    · rw [e1] at h1; omega
    · by_cases e2 : t + 2 = u
      · rw [e2] at h2; omega
      · by_cases e3 : t + 3 = u
        · rw [e3] at h3; omega
        · by_cases e4 : t + 4 = u
          · rw [e4] at h4; omega
          · omega
  by_cases h : p t + 8 ≤ p u
  · exact h
  · obtain ⟨j, hj1, hj2, hcr⟩ := downcross_from_end_values p (t + 4) u (p u + 1)
      (by omega) (by omega) (by omega)
    exact (hAfter j (by omega) hj2 hcr).elim

/-! ## List helper lemmas for the parameterized `(3 + δ)`-slot injection -/

private noncomputable def idxMarks (P : Nat → Prop) (n K : Nat) : List Nat :=
  (List.range K).filter (fun i => @decide (P (n + i)) (Classical.propDecidable _))

private theorem mem_idxMarks (P : Nat → Prop) (n K i : Nat) :
    i ∈ idxMarks P n K ↔ i < K ∧ P (n + i) := by
  unfold idxMarks
  simp [List.mem_filter, List.mem_range]

private theorem count_eq_idxMarks_length (P : Nat → Prop) (n : Nat) :
    ∀ K, cN P n K = (idxMarks P n K).length
  | 0 => rfl
  | K + 1 => by
    unfold idxMarks
    rw [List.range_succ, List.filter_append, List.length_append]
    have ih := count_eq_idxMarks_length P n K
    unfold idxMarks at ih
    by_cases hP : P (n + K)
    · rw [cN_succ_pos P n K hP, ih]
      simp [hP]
    · rw [cN_succ_neg P n K hP, ih]
      simp [hP]

private theorem range_flatMap_length (m c : Nat) (L : List Nat) :
    (L.flatMap (fun i => (List.range m).map (fun j => (i, c + j)))).length = m * L.length := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_range, ih,
      List.length_cons]
    rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]

private theorem range_offset_length (m n : Nat) (L : List Nat) :
    (L.flatMap (fun i => (List.range m).map (fun j => (n + i, j)))).length = m * L.length := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_range, ih,
      List.length_cons]
    rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]

private theorem nodup_map_of_inj {α β : Type} (L : List α) (g : α → β)
    (hnd : L.Nodup) (hinj : ∀ x, x ∈ L → ∀ y, y ∈ L → g x = g y → x = y) :
    (L.map g).Nodup := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hnd.2 (fun x hx y hy h => hinj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) h)⟩
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨b, hb, hgb⟩ := hmem
    have heq := hinj b (List.mem_cons_of_mem a hb) a (List.mem_cons_self ..) hgb
    exact hnd.1 (heq ▸ hb)

private theorem range_flatMap_nodup (m c : Nat) (L : List Nat) (hnd : L.Nodup) :
    (L.flatMap (fun i => (List.range m).map (fun j => (i, c + j)))).Nodup := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨?_, ih hnd.2, ?_⟩
    · exact nodup_map_of_inj (List.range m) (fun j => (a, c + j)) (List.nodup_range (n := m))
        (fun j₁ _ j₂ _ h => by have h2 := congrArg Prod.snd h; dsimp at h2; omega)
    · intro x hx y hy hxy
      rw [List.mem_map] at hx
      rw [List.mem_flatMap] at hy
      obtain ⟨j₁, _, rfl⟩ := hx
      obtain ⟨b, hb, hy'⟩ := hy
      rw [List.mem_map] at hy'
      obtain ⟨j₂, _, rfl⟩ := hy'
      have h1 := congrArg Prod.fst hxy
      dsimp at h1
      exact hnd.1 (h1 ▸ hb)

private theorem nodup_sum_append {α β : Type} (L₁ : List α) (L₂ : List β)
    (h₁ : L₁.Nodup) (h₂ : L₂.Nodup) :
    (L₁.map Sum.inl ++ L₂.map Sum.inr).Nodup := by
  rw [List.nodup_append]
  refine ⟨nodup_map_of_inj L₁ Sum.inl h₁ (fun _ _ _ _ h => Sum.inl.inj h),
    nodup_map_of_inj L₂ Sum.inr h₂ (fun _ _ _ _ h => Sum.inr.inj h), ?_⟩
  intro x hx y hy hxy
  rw [List.mem_map] at hx hy
  obtain ⟨a, _, rfl⟩ := hx
  obtain ⟨b, _, rfl⟩ := hy
  cases hxy

private theorem doubleAscent_le_of_le (f : Nat → Bool) (n d K : Nat) (h : Int) (hd : d ≤ K) :
    doubleAscent f n d h ≤ doubleAscent f n K h := by
  unfold doubleAscent
  have h1 := cN_mono
    (fun t => Fw f t = h ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < n + d)
    (fun t => Fw f t = h ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < n + K)
    n d (fun _ _ _ ht => ⟨ht.1, ht.2.1, ht.2.2.1, by omega⟩)
  have h2 := cN_add (fun t => Fw f t = h ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < n + K) n d (K - d)
  rw [Nat.add_sub_cancel' hd] at h2
  omega

private theorem doubleAscent_le_levelAdditions (f : Nat → Bool) (n K : Nat) (h : Int) :
    doubleAscent f n K h ≤ levelAdditions f n K h := by
  unfold doubleAscent levelAdditions
  exact cN_mono _ _ n K (fun _ _ _ ht => ⟨ht.1, ht.2.1⟩)

/-! ## Core parameterized `(3 + δ)`-slot injection (`δ ≤ 5`, sharp at `δ = 5`) -/

/-- Parameterized double-ascent excursion spacing slot bound: for every `δ ≤ 5`, every
padded `BlockWord` prefix, every interval `[n, n + K)`, and every height `r : Int`,
  `3 * E_{r+1} + δ * EAA_{r+1} + E_r ≤ (descentSlots f n r K).length + (3 + δ) * AA_{r-1}`.
At `δ = 5` this achieves the sharp 8-slot ceiling (`δ = 6` fails); at `δ = 2` (5 slots)
it drives the exact `5/3` telescoping theorem below. -/
theorem actual_double_ascent_spacing_slots (f : Nat → Bool) (n a K δ : Nat) (r : Int)
    (hδ : δ ≤ 5)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true) :
    3 * levelSupplied f n K (r + 1) + δ * suppliedDoubleAscent f n K (r + 1) +
      levelSupplied f n K r ≤
      (descentSlots f n r K).length + (3 + δ) * doubleAscent f n K (r - 1) := by
  let p := floorPotential f n (r - 1)
  let P1 := fun t => Fw f t = r + 1 ∧ EndN f 0 t
  let P1AA := fun t => Fw f t = r + 1 ∧ EndN f 0 t ∧ f (t + 1) = true ∧ t + 1 < n + K
  let P2 := fun u => Fw f u = r ∧ EndN f 0 u
  let QAA := fun t => Fw f t = r - 1 ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < n + K
  let Good1 := fun t => n ≤ t ∧ t < n + K ∧ P1 t
  let Good2 := fun u => n ≤ u ∧ u < n + K ∧ P2 u
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
          Sum.inr (d' - 1, 2 + δ)
      else
        Sum.inr (n, 0)
  let dom1a := (idxMarks P1 n K).flatMap (fun i => (List.range 3).map (fun j => (i, 0 + j)))
  let dom1b := (idxMarks P1AA n K).flatMap (fun i => (List.range δ).map (fun j => (i, 3 + j)))
  let dom1 := dom1a ++ dom1b
  let dom2 := idxMarks P2 n K
  let dom : List (Sum (Nat × Nat) Nat) := dom1.map Sum.inl ++ dom2.map Sum.inr
  let exits := idxMarks QAA n K
  let target : List (Sum (Nat × Int) (Nat × Nat)) :=
    (descentSlots f n r K).map Sum.inl ++
      (exits.flatMap (fun i => (List.range (3 + δ)).map (fun j => (n + i, j)))).map Sum.inr
  have hdom1_mem : ∀ pair, pair ∈ dom1 →
      pair.1 < K ∧ P1 (n + pair.1) ∧ pair.2 ≤ 2 + δ ∧
        (3 ≤ pair.2 → f (n + pair.1 + 1) = true) := by
    intro pair hmem
    rw [List.mem_append] at hmem
    rcases hmem with ha | hb
    · rw [List.mem_flatMap] at ha
      obtain ⟨i, hi, hpair⟩ := ha
      rw [mem_idxMarks] at hi
      rw [List.mem_map] at hpair
      obtain ⟨j, hj, rfl⟩ := hpair
      rw [List.mem_range] at hj
      exact ⟨hi.1, hi.2, by omega, fun _ => by omega⟩
    · rw [List.mem_flatMap] at hb
      obtain ⟨i, hi, hpair⟩ := hb
      rw [mem_idxMarks] at hi
      rw [List.mem_map] at hpair
      obtain ⟨j, hj, rfl⟩ := hpair
      rw [List.mem_range] at hj
      exact ⟨hi.1, ⟨hi.2.1, hi.2.2.1⟩, by omega, fun _ => hi.2.2.2.1⟩
  have hdom1_nodup : dom1.Nodup := by
    rw [List.nodup_append]
    refine ⟨range_flatMap_nodup 3 0 _ ((List.nodup_range (n := K)).filter _),
      range_flatMap_nodup δ 3 _ ((List.nodup_range (n := K)).filter _), ?_⟩
    intro x hx y hy hxy
    rw [List.mem_flatMap] at hx hy
    obtain ⟨i₁, _, hx'⟩ := hx
    obtain ⟨i₂, _, hy'⟩ := hy
    rw [List.mem_map] at hx' hy'
    obtain ⟨j₁, hj₁, rfl⟩ := hx'
    obtain ⟨j₂, hj₂, rfl⟩ := hy'
    rw [List.mem_range] at hj₁ hj₂
    have h2 := congrArg Prod.snd hxy
    dsimp at h2
    omega
  have hdom_nodup : dom.Nodup :=
    nodup_sum_append dom1 dom2 hdom1_nodup ((List.nodup_range (n := K)).filter _)
  have hdom_len : dom.length =
      3 * levelSupplied f n K (r + 1) + δ * suppliedDoubleAscent f n K (r + 1) +
        levelSupplied f n K r := by
    simp only [dom, dom1, dom1a, dom1b, dom2, List.length_append, List.length_map,
      range_flatMap_length, levelSupplied, suppliedDoubleAscent, P1, P1AA, P2,
      count_eq_idxMarks_length]
  have htgt_len : target.length =
      (descentSlots f n r K).length + (3 + δ) * doubleAscent f n K (r - 1) := by
    simp only [target, exits, List.length_append, List.length_map, range_offset_length,
      doubleAscent, QAA, count_eq_idxMarks_length]
  have hmem : ∀ x, x ∈ dom → phi x ∈ target := by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx1 | hx2
    · rw [List.mem_map] at hx1
      obtain ⟨⟨i, k⟩, hmem1, rfl⟩ := hx1
      obtain ⟨hiK, hiP, hk2, _⟩ := hdom1_mem (i, k) hmem1
      have ht : Good1 (n + i) := ⟨Nat.le_add_right n i, by omega, hiP⟩
      dsimp only [phi]
      rw [dif_pos ht]
      obtain ⟨hnq, hqd', hd't, hd1F, hd1A, _, hd'A, _, _, _, _⟩ := hSpec1 (n + i) ht
      obtain ⟨hna0, _, _, _, _, hpa0⟩ := hEntry1 (n + i) ht
      split
      · next hle =>
        apply List.mem_append_left
        apply List.mem_map.mpr
        have hcs := Classical.choose_spec (hCross1 (n + i) k ht hle)
        refine ⟨(Classical.choose (hCross1 (n + i) k ht hle), p (n + i) + (k : Int)), ?_, rfl⟩
        exact crossing_mem_descent_slots f n K _ r _ (by omega) (by omega) hcs.2.2
      · next hgt =>
        apply List.mem_append_right
        apply List.mem_map.mpr
        let d' := d1Of (n + i)
        let d1 := d' - 1
        let j := (p (n + i) + (k : Int) - p (lastAbove f n (r + 1) (d' - n)) - 1).toNat
        refine ⟨(d1, j), ?_, rfl⟩
        rw [List.mem_flatMap]
        refine ⟨d1 - n, ?_, ?_⟩
        · rw [mem_idxMarks]
          refine ⟨by omega, ?_⟩
          rw [Nat.add_sub_cancel' (show n ≤ d1 by omega)]
          refine ⟨hd1F, hd1A, ?_, by omega⟩
          rw [show d1 + 1 = d' by omega]
          exact hd'A
        · rw [List.mem_map]
          refine ⟨j, ?_, ?_⟩
          · rw [List.mem_range]; dsimp only [j, d']; omega
          · rw [Nat.add_sub_cancel' (show n ≤ d1 by omega)]
    · rw [List.mem_map] at hx2
      obtain ⟨i, hmem2, rfl⟩ := hx2
      rw [mem_idxMarks] at hmem2
      have hu : Good2 (n + i) := ⟨Nat.le_add_right n i, by omega, hmem2.2⟩
      dsimp only [phi]
      rw [dif_pos hu]
      obtain ⟨hnq, hqd', hd'u, hd1F, hd1A, _, hd'A, _, _, _, _⟩ := hSpec2 (n + i) hu
      obtain ⟨hna0, _, _, _, _, _⟩ := hEntry2 (n + i) hu
      split
      · next hlt =>
        apply List.mem_append_left
        apply List.mem_map.mpr
        have hcs := Classical.choose_spec (hCross2 (n + i) hu hlt)
        refine ⟨(Classical.choose (hCross2 (n + i) hu hlt), p (n + i)), ?_, rfl⟩
        exact crossing_mem_descent_slots f n K _ r _ (by omega) (by omega) hcs.2.2
      · next hge =>
        apply List.mem_append_right
        apply List.mem_map.mpr
        let d' := d2Of (n + i)
        let d1 := d' - 1
        refine ⟨(d1, 2 + δ), ?_, rfl⟩
        rw [List.mem_flatMap]
        refine ⟨d1 - n, ?_, ?_⟩
        · rw [mem_idxMarks]
          refine ⟨by omega, ?_⟩
          rw [Nat.add_sub_cancel' (show n ≤ d1 by omega)]
          refine ⟨hd1F, hd1A, ?_, by omega⟩
          rw [show d1 + 1 = d' by omega]
          exact hd'A
        · rw [List.mem_map]
          refine ⟨2 + δ, ?_, ?_⟩
          · rw [List.mem_range]; omega
          · rw [Nat.add_sub_cancel' (show n ≤ d1 by omega)]
  have h11_contra : ∀ i₁ k₁ i₂ k₂, (i₁, k₁) ∈ dom1 → (i₂, k₂) ∈ dom1 → i₁ < i₂ →
      d1Of (n + i₁) = d1Of (n + i₂) → p (n + i₁) + (k₁ : Int) = p (n + i₂) + (k₂ : Int) → False := by
    intro i₁ k₁ i₂ k₂ hm₁ hm₂ hlt hdEq hpEq
    obtain ⟨hiK₁, hiP₁, hk₁, hAA₁⟩ := hdom1_mem (i₁, k₁) hm₁
    obtain ⟨hiK₂, hiP₂, _, _⟩ := hdom1_mem (i₂, k₂) hm₂
    have ht₁ : Good1 (n + i₁) := ⟨Nat.le_add_right n i₁, by omega, hiP₁⟩
    have ht₂ : Good1 (n + i₂) := ⟨Nat.le_add_right n i₂, by omega, hiP₂⟩
    obtain ⟨_, _, hd₁t₁, _, _, _, _, _, _, _, _⟩ := hSpec1 (n + i₁) ht₁
    obtain ⟨_, hq₂d₂, _, _, _, _, _, _, _, _, hafter₂⟩ := hSpec1 (n + i₂) ht₂
    by_cases h3 : 3 ≤ k₁
    · have hsp := spacing_aa_rp1_rp1 f n (n + i₁) (n + i₂) (q1Of (n + i₂)) r
        (Nat.le_add_right n i₁) (by omega) (by omega) hiP₁.1 hiP₂.1 hiP₁.2.1 (hAA₁ h3) hafter₂
      change p (n + i₁) + 8 ≤ p (n + i₂) at hsp
      omega
    · have hsp := supply_potential_spacing_after_last_crossing f n (n + i₁) (n + i₂)
        (q1Of (n + i₂)) r (Nat.le_add_right n i₁) (by omega) (by omega)
        hiP₁.1 hiP₂.1 hiP₁.2.1 hafter₂
      change p (n + i₁) + 3 ≤ p (n + i₂) at hsp
      omega
  have h22_contra : ∀ i₁ i₂, i₁ ∈ dom2 → i₂ ∈ dom2 → i₁ < i₂ →
      d2Of (n + i₁) = d2Of (n + i₂) → p (n + i₁) = p (n + i₂) → False := by
    intro i₁ i₂ hm₁ hm₂ hlt hdEq hpEq
    rw [mem_idxMarks] at hm₁ hm₂
    have hu₁ : Good2 (n + i₁) := ⟨Nat.le_add_right n i₁, by omega, hm₁.2⟩
    have hu₂ : Good2 (n + i₂) := ⟨Nat.le_add_right n i₂, by omega, hm₂.2⟩
    obtain ⟨_, _, hd₁u₁, _, _, _, _, _, _, _, _⟩ := hSpec2 (n + i₁) hu₁
    obtain ⟨_, hq₂d₂, _, _, _, _, _, _, _, _, hafter₂⟩ := hSpec2 (n + i₂) hu₂
    have hsp := spacing_r_r f n (n + i₁) (n + i₂) (q2Of (n + i₂)) r
      (Nat.le_add_right n i₁) (by omega) (by omega) hm₁.2.1 hm₂.2.1 hm₁.2.2.1 hafter₂
    change p (n + i₁) + 1 ≤ p (n + i₂) at hsp
    omega
  have h12_contra : ∀ i₁ k₁ i₂, (i₁, k₁) ∈ dom1 → i₂ ∈ dom2 →
      d1Of (n + i₁) = d2Of (n + i₂) → p (n + i₁) + (k₁ : Int) = p (n + i₂) → False := by
    intro i₁ k₁ i₂ hm₁ hm₂ hdEq hpEq
    obtain ⟨hiK₁, hiP₁, hk₁, hAA₁⟩ := hdom1_mem (i₁, k₁) hm₁
    rw [mem_idxMarks] at hm₂
    have ht₁ : Good1 (n + i₁) := ⟨Nat.le_add_right n i₁, by omega, hiP₁⟩
    have hu₂ : Good2 (n + i₂) := ⟨Nat.le_add_right n i₂, by omega, hm₂.2⟩
    obtain ⟨_, hq₁d₁, hd₁t₁, _, _, _, _, _, _, _, hafter₁⟩ := hSpec1 (n + i₁) ht₁
    obtain ⟨_, hq₂d₂, hd₂u₂, _, _, _, _, _, _, _, hafter₂⟩ := hSpec2 (n + i₂) hu₂
    by_cases hord : i₁ < i₂
    · by_cases h3 : 3 ≤ k₁
      · have hsp := spacing_aa_rp1_r f n (n + i₁) (n + i₂) (q2Of (n + i₂)) r
          (Nat.le_add_right n i₁) (by omega) (by omega) hiP₁.1 hm₂.2.1 hiP₁.2.1 (hAA₁ h3) hafter₂
        change p (n + i₁) + 8 ≤ p (n + i₂) at hsp
        omega
      · have hsp := spacing_rp1_r f n (n + i₁) (n + i₂) (q2Of (n + i₂)) r
          (Nat.le_add_right n i₁) (by omega) (by omega) hiP₁.1 hm₂.2.1 hiP₁.2.1 hafter₂
        change p (n + i₁) + 3 ≤ p (n + i₂) at hsp
        omega
    · by_cases heq : i₁ = i₂
      · subst heq; have hF₁ : Fw f (n + i₁) = r + 1 := hiP₁.1; have hF₂ : Fw f (n + i₁) = r := hm₂.2.1; omega
      · have hsp := spacing_r_rp1 f n (n + i₂) (n + i₁) (q1Of (n + i₁)) r
          (Nat.le_add_right n i₂) (by omega) (by omega) hm₂.2.1 hiP₁.1 hm₂.2.2.1 hafter₁
        change p (n + i₂) + 1 ≤ p (n + i₁) at hsp
        omega
  have hinj : ∀ x, x ∈ dom → ∀ y, y ∈ dom → phi x = phi y → x = y := by
    intro x hx y hy hxy
    rw [List.mem_append] at hx hy
    rcases hx with hx1 | hx2 <;> rcases hy with hy1 | hy2
    · rw [List.mem_map] at hx1 hy1
      obtain ⟨⟨i₁, k₁⟩, hm₁, rfl⟩ := hx1
      obtain ⟨⟨i₂, k₂⟩, hm₂, rfl⟩ := hy1
      obtain ⟨hiK₁, hiP₁, hk₁, _⟩ := hdom1_mem (i₁, k₁) hm₁
      obtain ⟨hiK₂, hiP₂, hk₂, _⟩ := hdom1_mem (i₂, k₂) hm₂
      have ht₁ : Good1 (n + i₁) := ⟨Nat.le_add_right n i₁, by omega, hiP₁⟩
      have ht₂ : Good1 (n + i₂) := ⟨Nat.le_add_right n i₂, by omega, hiP₂⟩
      dsimp only [phi] at hxy
      rw [dif_pos ht₁, dif_pos ht₂] at hxy
      split at hxy <;> split at hxy
      · next hle₁ hle₂ =>
        have hpair := Sum.inl.inj hxy
        have hqEq : Classical.choose (hCross1 (n + i₁) k₁ ht₁ hle₁) =
            Classical.choose (hCross1 (n + i₂) k₂ ht₂ hle₂) := congrArg Prod.fst hpair
        have hpEq : p (n + i₁) + (k₁ : Int) = p (n + i₂) + (k₂ : Int) := congrArg Prod.snd hpair
        have hcs₁ := Classical.choose_spec (hCross1 (n + i₁) k₁ ht₁ hle₁)
        have hcs₂ := Classical.choose_spec (hCross1 (n + i₂) k₂ ht₂ hle₂)
        obtain ⟨_, _, _, _, _, _, _, hExit₁, _, _, _⟩ := hSpec1 (n + i₁) ht₁
        obtain ⟨_, _, _, _, _, _, _, hExit₂, _, _, _⟩ := hSpec1 (n + i₂) ht₂
        obtain ⟨_, _, _, hbelA₁, _, _⟩ := hEntry1 (n + i₁) ht₁
        obtain ⟨_, _, _, hbelA₂, _, _⟩ := hEntry1 (n + i₂) ht₂
        have hdEq : d1Of (n + i₁) = d1Of (n + i₂) :=
          extended_exit_unique f (Classical.choose (hCross1 (n + i₁) k₁ ht₁ hle₁))
            (d1Of (n + i₁)) (d1Of (n + i₂)) r
            hcs₁.2.1 hExit₁ (fun i hi1 hi2 => hbelA₁ i (by have := hcs₁.1; omega) hi2)
            (by rw [hqEq]; exact hcs₂.2.1) hExit₂
            (fun i hi1 hi2 => hbelA₂ i (by have := hcs₂.1; rw [← hqEq] at this; omega) hi2)
        by_cases hi : i₁ = i₂
        · subst hi
          have : k₁ = k₂ := by omega
          subst this; rfl
        · by_cases hlt : i₁ < i₂
          · exact (h11_contra i₁ k₁ i₂ k₂ hm₁ hm₂ hlt hdEq hpEq).elim
          · exact (h11_contra i₂ k₂ i₁ k₁ hm₂ hm₁ (by omega) hdEq.symm hpEq.symm).elim
      · cases hxy
      · cases hxy
      · next hgt₁ hgt₂ =>
        have hpair := Sum.inr.inj hxy
        have hd1Eq : d1Of (n + i₁) - 1 = d1Of (n + i₂) - 1 := congrArg Prod.fst hpair
        have hn₁ := (hSpec1 (n + i₁) ht₁).1
        have hq₁ := (hSpec1 (n + i₁) ht₁).2.1
        have hn₂ := (hSpec1 (n + i₂) ht₂).1
        have hq₂ := (hSpec1 (n + i₂) ht₂).2.1
        have hdEq : d1Of (n + i₁) = d1Of (n + i₂) := by omega
        have htoNat : (p (n + i₁) + (k₁ : Int) - p (lastAbove f n (r + 1) (d1Of (n + i₁) - n)) - 1).toNat =
            (p (n + i₂) + (k₂ : Int) - p (lastAbove f n (r + 1) (d1Of (n + i₂) - n)) - 1).toNat :=
          congrArg Prod.snd hpair
        have ha0Eq : p (lastAbove f n (r + 1) (d1Of (n + i₁) - n)) =
            p (lastAbove f n (r + 1) (d1Of (n + i₂) - n)) := by rw [hdEq]
        have hpEq : p (n + i₁) + (k₁ : Int) = p (n + i₂) + (k₂ : Int) := by omega
        by_cases hi : i₁ = i₂
        · subst hi
          have : k₁ = k₂ := by omega
          subst this; rfl
        · by_cases hlt : i₁ < i₂
          · exact (h11_contra i₁ k₁ i₂ k₂ hm₁ hm₂ hlt hdEq hpEq).elim
          · exact (h11_contra i₂ k₂ i₁ k₁ hm₂ hm₁ (by omega) hdEq.symm hpEq.symm).elim
    · rw [List.mem_map] at hx1 hy2
      obtain ⟨⟨i₁, k₁⟩, hm₁, rfl⟩ := hx1
      obtain ⟨i₂, hm₂, rfl⟩ := hy2
      obtain ⟨hiK₁, hiP₁, hk₁, _⟩ := hdom1_mem (i₁, k₁) hm₁
      have hm₂' := (mem_idxMarks P2 n K i₂).1 hm₂
      have ht₁ : Good1 (n + i₁) := ⟨Nat.le_add_right n i₁, by omega, hiP₁⟩
      have hu₂ : Good2 (n + i₂) := ⟨Nat.le_add_right n i₂, by omega, hm₂'.2⟩
      dsimp only [phi] at hxy
      rw [dif_pos ht₁, dif_pos hu₂] at hxy
      split at hxy <;> split at hxy
      · next hle₁ hlt₂ =>
        have hpair := Sum.inl.inj hxy
        have hqEq : Classical.choose (hCross1 (n + i₁) k₁ ht₁ hle₁) =
            Classical.choose (hCross2 (n + i₂) hu₂ hlt₂) := congrArg Prod.fst hpair
        have hpEq : p (n + i₁) + (k₁ : Int) = p (n + i₂) := congrArg Prod.snd hpair
        have hcs₁ := Classical.choose_spec (hCross1 (n + i₁) k₁ ht₁ hle₁)
        have hcs₂ := Classical.choose_spec (hCross2 (n + i₂) hu₂ hlt₂)
        obtain ⟨_, _, _, _, _, _, _, hExit₁, _, _, _⟩ := hSpec1 (n + i₁) ht₁
        obtain ⟨_, _, _, _, _, _, _, hExit₂, _, _, _⟩ := hSpec2 (n + i₂) hu₂
        obtain ⟨_, _, _, hbelA₁, _, _⟩ := hEntry1 (n + i₁) ht₁
        obtain ⟨_, _, _, hbelA₂, _, _⟩ := hEntry2 (n + i₂) hu₂
        have hdEq : d1Of (n + i₁) = d2Of (n + i₂) :=
          extended_exit_unique f (Classical.choose (hCross1 (n + i₁) k₁ ht₁ hle₁))
            (d1Of (n + i₁)) (d2Of (n + i₂)) r
            hcs₁.2.1 hExit₁ (fun i hi1 hi2 => hbelA₁ i (by have := hcs₁.1; omega) hi2)
            (by rw [hqEq]; exact hcs₂.2.1) hExit₂
            (fun i hi1 hi2 => hbelA₂ i (by have := hcs₂.1; rw [← hqEq] at this; omega) hi2)
        exact (h12_contra i₁ k₁ i₂ hm₁ hm₂ hdEq hpEq).elim
      · cases hxy
      · cases hxy
      · next hgt₁ _ =>
        have hpair := Sum.inr.inj hxy
        have hslot : (p (n + i₁) + (k₁ : Int) - p (lastAbove f n (r + 1) (d1Of (n + i₁) - n)) - 1).toNat = 2 + δ :=
          congrArg Prod.snd hpair
        have hpa0 := (hEntry1 (n + i₁) ht₁).2.2.2.2.2
        omega
    · rw [List.mem_map] at hx2 hy1
      obtain ⟨i₂, hm₂, rfl⟩ := hx2
      obtain ⟨⟨i₁, k₁⟩, hm₁, rfl⟩ := hy1
      obtain ⟨hiK₁, hiP₁, hk₁, _⟩ := hdom1_mem (i₁, k₁) hm₁
      have hm₂' := (mem_idxMarks P2 n K i₂).1 hm₂
      have ht₁ : Good1 (n + i₁) := ⟨Nat.le_add_right n i₁, by omega, hiP₁⟩
      have hu₂ : Good2 (n + i₂) := ⟨Nat.le_add_right n i₂, by omega, hm₂'.2⟩
      dsimp only [phi] at hxy
      rw [dif_pos hu₂, dif_pos ht₁] at hxy
      split at hxy <;> split at hxy
      · next hlt₂ hle₁ =>
        have hpair := Sum.inl.inj hxy
        have hqEq : Classical.choose (hCross2 (n + i₂) hu₂ hlt₂) =
            Classical.choose (hCross1 (n + i₁) k₁ ht₁ hle₁) := congrArg Prod.fst hpair
        have hpEq : p (n + i₂) = p (n + i₁) + (k₁ : Int) := congrArg Prod.snd hpair
        have hcs₁ := Classical.choose_spec (hCross1 (n + i₁) k₁ ht₁ hle₁)
        have hcs₂ := Classical.choose_spec (hCross2 (n + i₂) hu₂ hlt₂)
        obtain ⟨_, _, _, _, _, _, _, hExit₁, _, _, _⟩ := hSpec1 (n + i₁) ht₁
        obtain ⟨_, _, _, _, _, _, _, hExit₂, _, _, _⟩ := hSpec2 (n + i₂) hu₂
        obtain ⟨_, _, _, hbelA₁, _, _⟩ := hEntry1 (n + i₁) ht₁
        obtain ⟨_, _, _, hbelA₂, _, _⟩ := hEntry2 (n + i₂) hu₂
        have hdEq : d1Of (n + i₁) = d2Of (n + i₂) :=
          extended_exit_unique f (Classical.choose (hCross1 (n + i₁) k₁ ht₁ hle₁))
            (d1Of (n + i₁)) (d2Of (n + i₂)) r
            hcs₁.2.1 hExit₁ (fun i hi1 hi2 => hbelA₁ i (by have := hcs₁.1; omega) hi2)
            (by rw [← hqEq]; exact hcs₂.2.1) hExit₂
            (fun i hi1 hi2 => hbelA₂ i (by have := hcs₂.1; rw [hqEq] at this; omega) hi2)
        exact (h12_contra i₁ k₁ i₂ hm₁ hm₂ hdEq hpEq.symm).elim
      · cases hxy
      · cases hxy
      · next _ hgt₁ =>
        have hpair := Sum.inr.inj hxy
        have hslot : 2 + δ = (p (n + i₁) + (k₁ : Int) - p (lastAbove f n (r + 1) (d1Of (n + i₁) - n)) - 1).toNat :=
          congrArg Prod.snd hpair
        have hpa0 := (hEntry1 (n + i₁) ht₁).2.2.2.2.2
        omega
    · rw [List.mem_map] at hx2 hy2
      obtain ⟨i₁, hm₁, rfl⟩ := hx2
      obtain ⟨i₂, hm₂, rfl⟩ := hy2
      have hm₁' := (mem_idxMarks P2 n K i₁).1 hm₁
      have hm₂' := (mem_idxMarks P2 n K i₂).1 hm₂
      have hu₁ : Good2 (n + i₁) := ⟨Nat.le_add_right n i₁, by omega, hm₁'.2⟩
      have hu₂ : Good2 (n + i₂) := ⟨Nat.le_add_right n i₂, by omega, hm₂'.2⟩
      dsimp only [phi] at hxy
      rw [dif_pos hu₁, dif_pos hu₂] at hxy
      split at hxy <;> split at hxy
      · next hlt₁ hlt₂ =>
        have hpair := Sum.inl.inj hxy
        have hqEq : Classical.choose (hCross2 (n + i₁) hu₁ hlt₁) =
            Classical.choose (hCross2 (n + i₂) hu₂ hlt₂) := congrArg Prod.fst hpair
        have hpEq : p (n + i₁) = p (n + i₂) := congrArg Prod.snd hpair
        have hcs₁ := Classical.choose_spec (hCross2 (n + i₁) hu₁ hlt₁)
        have hcs₂ := Classical.choose_spec (hCross2 (n + i₂) hu₂ hlt₂)
        obtain ⟨_, _, _, _, _, _, _, hExit₁, _, _, _⟩ := hSpec2 (n + i₁) hu₁
        obtain ⟨_, _, _, _, _, _, _, hExit₂, _, _, _⟩ := hSpec2 (n + i₂) hu₂
        obtain ⟨_, _, _, hbelA₁, _, _⟩ := hEntry2 (n + i₁) hu₁
        obtain ⟨_, _, _, hbelA₂, _, _⟩ := hEntry2 (n + i₂) hu₂
        have hdEq : d2Of (n + i₁) = d2Of (n + i₂) :=
          extended_exit_unique f (Classical.choose (hCross2 (n + i₁) hu₁ hlt₁))
            (d2Of (n + i₁)) (d2Of (n + i₂)) r
            hcs₁.2.1 hExit₁ (fun i hi1 hi2 => hbelA₁ i (by have := hcs₁.1; omega) hi2)
            (by rw [hqEq]; exact hcs₂.2.1) hExit₂
            (fun i hi1 hi2 => hbelA₂ i (by have := hcs₂.1; rw [← hqEq] at this; omega) hi2)
        by_cases hi : i₁ = i₂
        · subst hi; rfl
        · by_cases hlt : i₁ < i₂
          · exact (h22_contra i₁ i₂ hm₁ hm₂ hlt hdEq hpEq).elim
          · exact (h22_contra i₂ i₁ hm₂ hm₁ (by omega) hdEq.symm hpEq.symm).elim
      · cases hxy
      · cases hxy
      · next hge₁ hge₂ =>
        have hpair := Sum.inr.inj hxy
        have hd1Eq : d2Of (n + i₁) - 1 = d2Of (n + i₂) - 1 := congrArg Prod.fst hpair
        have hn₁ := (hSpec2 (n + i₁) hu₁).1
        have hq₁ := (hSpec2 (n + i₁) hu₁).2.1
        have hn₂ := (hSpec2 (n + i₂) hu₂).1
        have hq₂ := (hSpec2 (n + i₂) hu₂).2.1
        have hdEq : d2Of (n + i₁) = d2Of (n + i₂) := by omega
        have hpd₁ := (hEntry2 (n + i₁) hu₁).2.2.2.2.1
        have hpd₂ := (hEntry2 (n + i₂) hu₂).2.2.2.2.1
        have hpEq : p (n + i₁) = p (n + i₂) := by rw [← hdEq] at hpd₂ hge₂; omega
        by_cases hi : i₁ = i₂
        · subst hi; rfl
        · by_cases hlt : i₁ < i₂
          · exact (h22_contra i₁ i₂ hm₁ hm₂ hlt hdEq hpEq).elim
          · exact (h22_contra i₂ i₁ hm₂ hm₁ (by omega) hdEq.symm hpEq.symm).elim
  have hsub : dom.map phi ⊆ target := by
    intro z hz
    rw [List.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact hmem x hx
  have hnd_img := nodup_map_of_inj dom phi hdom_nodup hinj
  have hlen := hnd_img.length_le_of_subset hsub
  rw [List.length_map, hdom_len, htgt_len] at hlen
  exact hlen

/-- Parameterized double-ascent excursion weight budget (`δ ≤ 5`):
  `3 * E_{r+1} + δ * EAA_{r+1} + E_r ≤ lowAdditionWeights f n r K + (3 + δ) * AA_{r-1}`. -/
theorem actual_double_ascent_spacing_budget (f : Nat → Bool) (n a K δ : Nat) (r : Int)
    (hδ : δ ≤ 5)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true) :
    ((3 * levelSupplied f n K (r + 1) + δ * suppliedDoubleAscent f n K (r + 1) +
      levelSupplied f n K r : Nat) : Int) ≤
      lowAdditionWeights f n r K + (((3 + δ) * doubleAscent f n K (r - 1) : Nat) : Int) := by
  let P1 := fun t => Fw f t = r + 1 ∧ EndN f 0 t
  let P2 := fun t => Fw f t = r ∧ EndN f 0 t
  let Pboth := fun t => (Fw f t = r + 1 ∨ Fw f t = r) ∧ EndN f 0 t
  obtain ⟨d0, hd0, hlast, hafter⟩ := last_markN Pboth n K
  by_cases hz : d0 = 0
  · have hE1 : levelSupplied f n K (r + 1) = 0 := by
      unfold levelSupplied
      apply cN_zero_of
      intro i hi hiK h1
      have h := hafter (i - n) (by omega) (by omega)
      rw [Nat.add_sub_cancel' hi] at h
      exact h ⟨Or.inl h1.1, h1.2⟩
    have hE2 : levelSupplied f n K r = 0 := by
      unfold levelSupplied
      apply cN_zero_of
      intro i hi hiK h2
      have h := hafter (i - n) (by omega) (by omega)
      rw [Nat.add_sub_cancel' hi] at h
      exact h ⟨Or.inr h2.1, h2.2⟩
    have hEAA : suppliedDoubleAscent f n K (r + 1) = 0 := by
      unfold suppliedDoubleAscent
      apply cN_zero_of
      intro i hi hiK h1
      have h := hafter (i - n) (by omega) (by omega)
      rw [Nat.add_sub_cancel' hi] at h
      exact h ⟨Or.inl h1.1, h1.2.1⟩
    have hnn := low_weights_nonnegative f n r K
    rw [hE1, hE2, hEAA]
    omega
  · have hp := hlast.resolve_left hz
    let t := n + d0 - 1
    have hpt : (Fw f t = r + 1 ∨ Fw f t = r) ∧ EndN f 0 t := hp
    let d := if Fw f t = r + 1 ∧ f (t + 1) = true ∧ t + 1 < n + K then d0 + 1 else d0
    have hd : d ≤ K := by
      dsimp only [d, t]
      split <;> omega
    have htd : d0 ≤ d := by
      dsimp only [d]
      split <;> omega
    have hend : r ≤ Fw f (n + d) := by
      have htA : f t = true := hpt.2.1
      dsimp only [d]
      split
      · next hAA =>
        have h1 : Fw f (t + 1) = r + 2 := by
          rcases fw_cases f t with ⟨h, _⟩ | ⟨_, h⟩
          · omega
          · simp [htA] at h
        rcases fw_cases f (t + 1) with ⟨h, _⟩ | ⟨_, h⟩
        · rw [show t + 1 + 1 = n + (d0 + 1) by dsimp only [t]; omega] at h; omega
        · simp [hAA.2.1] at h
      · rcases fw_cases f t with ⟨h, _⟩ | ⟨_, h⟩
        · rw [show t + 1 = n + d0 by dsimp only [t]; omega] at h
          rcases hpt.1 with h1 | h2 <;> omega
        · simp [htA] at h
    have htail1 : cN P1 (n + d) (K - d) = 0 := by
      apply cN_zero_of
      intro i hi hiK h1
      have h := hafter (i - n) (by omega) (by omega)
      rw [Nat.add_sub_cancel' (by omega)] at h
      exact h ⟨Or.inl h1.1, h1.2⟩
    have htail2 : cN P2 (n + d) (K - d) = 0 := by
      apply cN_zero_of
      intro i hi hiK h2
      have h := hafter (i - n) (by omega) (by omega)
      rw [Nat.add_sub_cancel' (by omega)] at h
      exact h ⟨Or.inr h2.1, h2.2⟩
    have hc1 := cN_add P1 n d (K - d)
    rw [show d + (K - d) = K by omega, htail1, Nat.add_zero] at hc1
    have hc2 := cN_add P2 n d (K - d)
    rw [show d + (K - d) = K by omega, htail2, Nat.add_zero] at hc2
    have hEAA_le : suppliedDoubleAscent f n K (r + 1) ≤ suppliedDoubleAscent f n d (r + 1) := by
      unfold suppliedDoubleAscent
      have hdiff := cN_add
        (fun i => Fw f i = r + 1 ∧ EndN f 0 i ∧ f (i + 1) = true ∧ i + 1 < n + K) n d (K - d)
      rw [show d + (K - d) = K by omega] at hdiff
      have htailE : cN (fun i => Fw f i = r + 1 ∧ EndN f 0 i ∧ f (i + 1) = true ∧ i + 1 < n + K)
          (n + d) (K - d) = 0 := by
        apply cN_zero_of
        intro i hi hiK hP
        have h := hafter (i - n) (by omega) (by omega)
        rw [Nat.add_sub_cancel' (by omega)] at h
        exact h ⟨Or.inl hP.1, hP.2.1⟩
      have hmono : cN (fun i => Fw f i = r + 1 ∧ EndN f 0 i ∧ f (i + 1) = true ∧ i + 1 < n + K) n d ≤
          cN (fun i => Fw f i = r + 1 ∧ EndN f 0 i ∧ f (i + 1) = true ∧ i + 1 < n + d) n d := by
        apply cN_mono
        intro i hi1 hi2 hP
        have hi_le : i ≤ t := by
          by_cases hgt : t < i
          · have h := hafter (i - n) (by omega) (by omega)
            rw [Nat.add_sub_cancel' hi1] at h
            exact (h ⟨Or.inl hP.1, hP.2.1⟩).elim
          · omega
        have hi1d : i + 1 < n + d := by
          by_cases hit : i = t
          · rw [hit] at hP ⊢
            have hcond : Fw f t = r + 1 ∧ f (t + 1) = true ∧ t + 1 < n + K :=
              ⟨hP.1, hP.2.2.1, hP.2.2.2⟩
            dsimp only [d]
            rw [if_pos hcond]
            omega
          · dsimp only [t] at hi_le hit
            omega
        exact ⟨hP.1, hP.2.1, hP.2.2.1, hi1d⟩
      omega
    have hslots := actual_double_ascent_spacing_slots f n a d δ r hδ hw hpre
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
    have hslotsI :
        ((3 * levelSupplied f n d (r + 1) + δ * suppliedDoubleAscent f n d (r + 1) +
          levelSupplied f n d r : Nat) : Int) ≤
        ((descentSlots f n r d).length : Int) + (((3 + δ) * doubleAscent f n d (r - 1) : Nat) : Int) := by
      exact_mod_cast hslots
    have hAAI : (((3 + δ) * doubleAscent f n d (r - 1) : Nat) : Int) ≤
        (((3 + δ) * doubleAscent f n K (r - 1) : Nat) : Int) := by
      exact_mod_cast Nat.mul_le_mul_left (3 + δ) hmonoAA
    have hEAAI : ((δ * suppliedDoubleAscent f n K (r + 1) : Nat) : Int) ≤
        ((δ * suppliedDoubleAscent f n d (r + 1) : Nat) : Int) := by
      exact_mod_cast Nat.mul_le_mul_left δ hEAA_le
    omega

/-- Sharp 8-slot (`δ = 5`) double-ascent excursion weight budget:
  `3 * E_{r+1} + 5 * EAA_{r+1} + E_r ≤ lowAdditionWeights f n r K + 8 * AA_{r-1}`.
The coefficient `5` is sharp (`δ = 6` fails on repeated `AASS` excursions at height `r + 1`). -/
theorem actual_eight_slot_double_ascent_budget (f : Nat → Bool) (n a K : Nat) (r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true) :
    ((3 * levelSupplied f n K (r + 1) + 5 * suppliedDoubleAscent f n K (r + 1) +
      levelSupplied f n K r : Nat) : Int) ≤
      lowAdditionWeights f n r K + ((8 * doubleAscent f n K (r - 1) : Nat) : Int) :=
  actual_double_ascent_spacing_budget f n a K 5 r (Nat.le_refl 5) hw hpre

/-! ## Level-sum identities and exact `5/3` telescoping invariant -/

private theorem level_additions_split (f : Nat → Bool) (n K : Nat) (h : Int) :
    levelAdditions f n K h = levelSupplied f n K h + levelFree f n K h := by
  unfold levelAdditions levelSupplied levelFree
  have hsp := cN_split (fun t => Fw f t = h ∧ f t = true) (fun t => EndN f 0 t) n K
  have h1 : cN (fun t => (Fw f t = h ∧ f t = true) ∧ EndN f 0 t) n K =
      cN (fun t => Fw f t = h ∧ EndN f 0 t) n K := by
    apply Nat.le_antisymm
    · exact cN_mono _ _ n K (fun _ _ _ ht => ⟨ht.1.1, ht.2⟩)
    · exact cN_mono _ _ n K (fun _ _ _ ht => ⟨⟨ht.1, ht.2.1⟩, ht.2⟩)
  have h2 : cN (fun t => (Fw f t = h ∧ f t = true) ∧ ¬ EndN f 0 t) n K =
      cN (fun t => Fw f t = h ∧ f t = true ∧ ¬ EndN f 0 t) n K := by
    apply Nat.le_antisymm
    · exact cN_mono _ _ n K (fun _ _ _ ht => ⟨ht.1.1, ht.1.2, ht.2⟩)
    · exact cN_mono _ _ n K (fun _ _ _ ht => ⟨⟨ht.1, ht.2.1⟩, ht.2.2⟩)
  omega

private theorem doubleAscent_le_supplied_add_free (f : Nat → Bool) (n K : Nat) (h : Int) :
    doubleAscent f n K h ≤ suppliedDoubleAscent f n K h + levelFree f n K h := by
  unfold doubleAscent suppliedDoubleAscent levelFree
  have hsp := cN_split
    (fun t => Fw f t = h ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < n + K)
    (fun t => EndN f 0 t) n K
  have h1 : cN (fun t => (Fw f t = h ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < n + K) ∧
      EndN f 0 t) n K ≤
      cN (fun t => Fw f t = h ∧ EndN f 0 t ∧ f (t + 1) = true ∧ t + 1 < n + K) n K :=
    cN_mono _ _ n K (fun _ _ _ ht => ⟨ht.1.1, ht.2, ht.1.2.2.1, ht.1.2.2.2⟩)
  have h2 : cN (fun t => (Fw f t = h ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < n + K) ∧
      ¬ EndN f 0 t) n K ≤
      cN (fun t => Fw f t = h ∧ f t = true ∧ ¬ EndN f 0 t) n K :=
    cN_mono _ _ n K (fun _ _ _ ht => ⟨ht.1.1, ht.1.2.1, ht.2⟩)
  omega

private theorem levelSum_free_le (f : Nat → Bool) (n K : Nat) (m : Int) :
    ∀ H, levelSum (fun h => levelFree f n K (m + (h : Int))) H ≤
      cN (fun t => f t = true ∧ ¬ EndN f 0 t ∧ Fw f t ≤ m + (H : Int)) n K
  | 0 => by
    simp only [levelSum, levelFree]
    exact cN_mono _ _ n K (fun _ _ _ ht => ⟨ht.2.1, ht.2.2, by omega⟩)
  | H + 1 => by
    have ih := levelSum_free_le f n K m H
    simp only [levelSum]
    have hsplit := cN_split
      (fun t => f t = true ∧ ¬ EndN f 0 t ∧ Fw f t ≤ m + ((H + 1 : Nat) : Int))
      (fun t => Fw f t ≤ m + (H : Int)) n K
    have h1 : cN (fun t => f t = true ∧ ¬ EndN f 0 t ∧ Fw f t ≤ m + (H : Int)) n K ≤
        cN (fun t => (f t = true ∧ ¬ EndN f 0 t ∧ Fw f t ≤ m + ((H + 1 : Nat) : Int)) ∧
          Fw f t ≤ m + (H : Int)) n K :=
      cN_mono _ _ n K (fun _ _ _ ht => ⟨⟨ht.1, ht.2.1, by omega⟩, ht.2.2⟩)
    have h2 : levelFree f n K (m + ((H + 1 : Nat) : Int)) ≤
        cN (fun t => (f t = true ∧ ¬ EndN f 0 t ∧ Fw f t ≤ m + ((H + 1 : Nat) : Int)) ∧
          ¬ Fw f t ≤ m + (H : Int)) n K := by
      unfold levelFree
      exact cN_mono _ _ n K (fun _ _ _ ht => ⟨⟨ht.2.1, ht.2.2, by omega⟩, by omega⟩)
    omega

private theorem levelSum_free_le_free (f : Nat → Bool) (n K : Nat) (m : Int) (H : Nat) :
    levelSum (fun h => levelFree f n K (m + (h : Int))) H ≤ free f n K := by
  have hls := levelSum_free_le f n K m H
  have hfr : cN (fun t => f t = true ∧ ¬ EndN f 0 t ∧ Fw f t ≤ m + (H : Int)) n K ≤
      free f n K := by
    unfold free
    exact cN_mono _ _ n K (fun _ _ _ ht => ⟨ht.1, ht.2.1⟩)
  exact Nat.le_trans hls hfr

private theorem additions_le_levelSum (f : Nat → Bool) (n K : Nat) (m : Int)
    (hfloor : ∀ i, n ≤ i → i < n + K → m ≤ Fw f i) (H : Nat) :
    cN (fun t => f t = true ∧ Fw f t ≤ m + (H : Int)) n K ≤
      levelSum (fun h => levelAdditions f n K (m + (h : Int))) H := by
  induction H with
  | zero =>
    simp only [levelSum, levelAdditions]
    exact cN_mono _ _ n K (fun t hnt htK ht => ⟨by have := hfloor t hnt htK; omega, ht.1⟩)
  | succ H ih =>
    simp only [levelSum]
    have hsplit := cN_split
      (fun t => f t = true ∧ Fw f t ≤ m + ((H + 1 : Nat) : Int))
      (fun t => Fw f t ≤ m + (H : Int)) n K
    have h1 : cN (fun t => (f t = true ∧ Fw f t ≤ m + ((H + 1 : Nat) : Int)) ∧
        Fw f t ≤ m + (H : Int)) n K ≤
        cN (fun t => f t = true ∧ Fw f t ≤ m + (H : Int)) n K :=
      cN_mono _ _ n K (fun _ _ _ ht => ⟨ht.1.1, ht.2⟩)
    have h2 : cN (fun t => (f t = true ∧ Fw f t ≤ m + ((H + 1 : Nat) : Int)) ∧
        ¬ Fw f t ≤ m + (H : Int)) n K ≤
        levelAdditions f n K (m + ((H + 1 : Nat) : Int)) := by
      unfold levelAdditions
      exact cN_mono _ _ n K (fun _ _ _ ht => ⟨by omega, ht.1.1⟩)
    omega

private theorem lowAdditionWeights_mono_r (f : Nat → Bool) (n : Nat) (r₁ r₂ : Int) (hr : r₁ ≤ r₂) :
    ∀ K, lowAdditionWeights f n r₁ K ≤ lowAdditionWeights f n r₂ K
  | 0 => Int.le_refl 0
  | k + 1 => by
    have ih := lowAdditionWeights_mono_r f n r₁ r₂ hr k
    simp only [lowAdditionWeights]
    have hstep : lowAdditionWeight f r₁ (n + k) ≤ lowAdditionWeight f r₂ (n + k) := by
      unfold lowAdditionWeight
      by_cases h1 : f (n + k) = true ∧ Fw f (n + k) < r₁
      · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]; omega
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
    simp only [lowAdditionWeights, ih]
    unfold lowAdditionWeight
    rw [if_neg (fun h => by omega)]
    omega

private theorem lowAdditionWeights_eq_levelWeightSum (f : Nat → Bool) (n : Nat) :
    ∀ K (m : Int), (∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) →
      ∀ d : Nat, lowAdditionWeights f n (m + (d : Int) + 1) K =
        (levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) d : Int)
  | 0, m, _, d => by
    have hzero : ∀ g : Nat → Nat, (∀ j, g j = 0) →
        ∀ k, levelSum g k = 0 ∧ levelWeightSum g k = 0 := by
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
    · have hAstep : ∀ j : Nat, levelAdditions f n (k + 1) (m + (j : Int)) =
          levelAdditions f n k (m + (j : Int)) +
            if Fw f (n + k) = m + (j : Int) then 1 else 0 := by
        intro j
        unfold levelAdditions
        by_cases heq : Fw f (n + k) = m + (j : Int)
        · rw [if_pos heq, cN_succ_pos _ n k ⟨heq, hf⟩]
        · rw [if_neg heq, cN_succ_neg _ n k (fun h => heq h.1), Nat.add_zero]
      have hUstep : ∀ d' : Nat,
          levelSum (fun j => levelAdditions f n (k + 1) (m + (j : Int))) d' =
            levelSum (fun j => levelAdditions f n k (m + (j : Int))) d' +
              if Fw f (n + k) ≤ m + (d' : Int) then 1 else 0 := by
        intro d'
        induction d' with
        | zero =>
          simp only [levelSum, hAstep 0]
          by_cases h0 : Fw f (n + k) = m + ((0 : Nat) : Int)
          · rw [if_pos h0, if_pos (by omega)]
          · rw [if_neg h0, if_neg (by omega)]
        | succ d' ih =>
          simp only [levelSum, ih, hAstep (d' + 1)]
          by_cases hle : Fw f (n + k) ≤ m + (d' : Int)
          · rw [if_pos hle, if_neg (by omega), if_pos (by omega)]; omega
          · by_cases heq : Fw f (n + k) = m + ((d' + 1 : Nat) : Int)
            · rw [if_neg hle, if_pos heq, if_pos (by omega)]; omega
            · rw [if_neg hle, if_neg heq, if_neg (by omega)]; omega
      induction d with
      | zero =>
        simp only [lowAdditionWeights, hbase 0, levelWeightSum, hAstep 0]
        unfold lowAdditionWeight
        by_cases h0 : Fw f (n + k) = m + ((0 : Nat) : Int)
        · rw [if_pos ⟨hf, by omega⟩, if_pos h0]; push_cast; omega
        · rw [if_neg (fun h => h0 (by omega)), if_neg h0]; omega
      | succ d ihd =>
        have hU := hUstep d
        have hbase_d := hbase d
        have hbase_d1 := hbase (d + 1)
        simp only [lowAdditionWeights, levelWeightSum] at ihd hbase_d1 ⊢
        rw [hU, hAstep (d + 1), hbase_d1]
        by_cases heq : Fw f (n + k) = m + ((d + 1 : Nat) : Int)
        · have hlw1 : lowAdditionWeight f (m + ((d + 1 : Nat) : Int) + 1) (n + k) = 1 := by
            unfold lowAdditionWeight; rw [if_pos ⟨hf, by omega⟩]; omega
          have hlw0 : lowAdditionWeight f (m + (d : Int) + 1) (n + k) = 0 := by
            unfold lowAdditionWeight; rw [if_neg (fun h => by omega)]
          rw [hlw1, if_pos heq, if_neg (by omega)]
          rw [hlw0, hbase_d] at ihd
          push_cast
          omega
        · rw [if_neg heq]
          by_cases hlow : Fw f (n + k) ≤ m + (d : Int)
          · have hlw1 : lowAdditionWeight f (m + ((d + 1 : Nat) : Int) + 1) (n + k) =
                lowAdditionWeight f (m + (d : Int) + 1) (n + k) + 2 := by
              unfold lowAdditionWeight; rw [if_pos ⟨hf, by omega⟩, if_pos ⟨hf, by omega⟩]; omega
            rw [hlw1, if_pos hlow]
            rw [hbase_d] at ihd
            push_cast
            omega
          · have hlw1 : lowAdditionWeight f (m + ((d + 1 : Nat) : Int) + 1) (n + k) = 0 := by
              unfold lowAdditionWeight; rw [if_neg (fun h => by omega)]
            have hlw0 : lowAdditionWeight f (m + (d : Int) + 1) (n + k) = 0 := by
              unfold lowAdditionWeight; rw [if_neg (fun h => by omega)]
            rw [hlw1, if_neg hlow]
            rw [hlw0, hbase_d] at ihd
            push_cast
            omega
    · have hAeq : ∀ j : Nat, levelAdditions f n (k + 1) (m + (j : Int)) =
          levelAdditions f n k (m + (j : Int)) := fun j =>
        cN_succ_neg _ n k (fun h => hf h.2)
      have hfn : (fun j : Nat => levelAdditions f n (k + 1) (m + (j : Int))) =
          (fun j : Nat => levelAdditions f n k (m + (j : Int))) := funext hAeq
      rw [lowAdditionWeights, hbase d, hfn]
      have hlw : lowAdditionWeight f (m + (d : Int) + 1) (n + k) = 0 := by
        unfold lowAdditionWeight; rw [if_neg (fun h => hf h.1)]
      rw [hlw]; omega

private theorem levelWeightSum_add_levelSum (g : Nat → Nat) :
    ∀ H, levelWeightSum g H + levelSum g H = 2 * triSum g H
  | 0 => by simp [levelWeightSum, levelSum, triSum]; omega
  | H + 1 => by
    have ih := levelWeightSum_add_levelSum g H
    simp only [levelWeightSum, levelSum, triSum]
    omega

private theorem triSum_five_thirds_ident (g : Nat → Nat) (H : Nat) :
    5 * triSum g (H + 1) + 3 * g (H + 2) + g (H + 1) =
      3 * triSum g (H + 2) + levelWeightSum g H := by
  have hWS := levelWeightSum_add_levelSum g H
  have h2 : H + 2 = (H + 1) + 1 := by omega
  rw [h2]
  simp only [triSum, levelSum]
  omega

private theorem levelSum_le_triSum (g : Nat → Nat) :
    ∀ H, levelSum g H ≤ triSum g H
  | 0 => by simp [levelSum, triSum]
  | H + 1 => by simp only [triSum]; omega

private theorem last_le_levelSum (g : Nat → Nat) :
    ∀ H, g H ≤ levelSum g H
  | 0 => by simp [levelSum]
  | H + 1 => by simp only [levelSum]; omega

private theorem eight_mul_pow_three_le_27_pow_five :
    ∀ H, 8 * 3 ^ (H + 2) ≤ 27 * 5 ^ (H + 1)
  | 0 => by decide
  | H + 1 => by
    have ih := eight_mul_pow_three_le_27_pow_five H
    rw [show H + 1 + 2 = (H + 2) + 1 by omega, Nat.pow_succ 3 (H + 2),
      show H + 1 + 1 = (H + 1) + 1 by omega, Nat.pow_succ 5 (H + 1)]
    have h1 : 8 * (3 ^ (H + 2) * 3) = 3 * (8 * 3 ^ (H + 2)) := by grind
    have h2 : 3 * (8 * 3 ^ (H + 2)) ≤ 3 * (27 * 5 ^ (H + 1)) := Nat.mul_le_mul_left 3 ih
    have h3 : 3 * (27 * 5 ^ (H + 1)) ≤ 5 * (27 * 5 ^ (H + 1)) := Nat.mul_le_mul_right _ (by omega)
    have h4 : 5 * (27 * 5 ^ (H + 1)) = 27 * (5 ^ (H + 1) * 5) := by grind
    exact Nat.le_trans (h1 ▸ h2) (h4 ▸ h3)

/-- Two-term inductive invariant at `q = 3/5` (`δ = 2`):
  `3 * 3^(H+1) * triAdditions(H+1) + 3^(H+2) * AA_H + 2 * 3^(H+1) * AA_{H+1} + 3^(H+2) * F_{H+1}`
    `≤ 27 * 5^H * levelSum(F, H+1)`. -/
private theorem exact_five_thirds_invariant (f : Nat → Bool) (n a K : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    ∀ H,
      3 * 3 ^ (H + 1) * triAdditions f n K m (H + 1) +
        3 ^ (H + 2) * doubleAscent f n K (m + (H : Int)) +
        2 * 3 ^ (H + 1) * doubleAscent f n K (m + ((H + 1 : Nat) : Int)) +
        3 ^ (H + 2) * levelFree f n K (m + ((H + 1 : Nat) : Int)) ≤
      27 * 5 ^ H * levelSum (fun h => levelFree f n K (m + (h : Int))) (H + 1) := by
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
    have hA0 := level_additions_split f n K (m + ((0 : Nat) : Int))
    have hA1 := level_additions_split f n K (m + ((1 : Nat) : Int))
    have hAA0 := doubleAscent_le_levelAdditions f n K (m + ((0 : Nat) : Int))
    have hAA1 := doubleAscent_le_levelAdditions f n K (m + ((1 : Nat) : Int))
    simp only [triAdditions, triSum, levelSum, Nat.zero_add, Nat.pow_zero, Nat.pow_one]
    have hp2 : (3 : Nat) ^ 2 = 9 := by decide
    rw [hp2]
    omega
  | succ H ih =>
    have hb := actual_double_ascent_spacing_budget f n a K 2 (m + (H : Int) + 1) (by omega) hw hpre
    have hW := lowAdditionWeights_eq_levelWeightSum f n K m hfloor H
    rw [hW] at hb
    have hrm1 : m + (H : Int) + 1 - 1 = m + (H : Int) := by omega
    have hr1 : m + (H : Int) + 1 + 1 = m + ((H + 2 : Nat) : Int) := by omega
    have hr0 : m + (H : Int) + 1 = m + ((H + 1 : Nat) : Int) := by omega
    rw [hrm1, hr1, hr0] at hb
    have hbNat :
        3 * levelSupplied f n K (m + ((H + 2 : Nat) : Int)) +
          2 * suppliedDoubleAscent f n K (m + ((H + 2 : Nat) : Int)) +
          levelSupplied f n K (m + ((H + 1 : Nat) : Int)) ≤
        levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) H +
          5 * doubleAscent f n K (m + (H : Int)) := by
      omega
    have hsp2 := level_additions_split f n K (m + ((H + 2 : Nat) : Int))
    have hsp1 := level_additions_split f n K (m + ((H + 1 : Nat) : Int))
    have hAAsp2 := doubleAscent_le_supplied_add_free f n K (m + ((H + 2 : Nat) : Int))
    have hstepA :
        3 * levelAdditions f n K (m + ((H + 2 : Nat) : Int)) +
          2 * doubleAscent f n K (m + ((H + 2 : Nat) : Int)) +
          levelAdditions f n K (m + ((H + 1 : Nat) : Int)) ≤
        levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) H +
          5 * doubleAscent f n K (m + (H : Int)) +
          5 * levelFree f n K (m + ((H + 2 : Nat) : Int)) +
          levelFree f n K (m + ((H + 1 : Nat) : Int)) := by
      omega
    have h5ih := Nat.mul_le_mul_left 5 ih
    have h3st := Nat.mul_le_mul_left (3 ^ (H + 2)) hstepA
    have htid := triSum_five_thirds_ident (fun j => levelAdditions f n K (m + (j : Int))) H
    have htid3 := congrArg (fun x => 3 ^ (H + 2) * x) htid
    have hpow3_1 : 3 ^ (H + 2) = 3 * 3 ^ (H + 1) := by
      rw [show H + 2 = (H + 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have hpow3_2 : 3 ^ (H + 3) = 3 * 3 ^ (H + 2) := by
      rw [show H + 3 = (H + 2) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have hpow5 : 5 ^ (H + 1) = 5 * 5 ^ H := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have h8le := eight_mul_pow_three_le_27_pow_five H
    have h8F : 8 * 3 ^ (H + 2) * levelFree f n K (m + ((H + 2 : Nat) : Int)) ≤
        27 * 5 ^ (H + 1) * levelFree f n K (m + ((H + 2 : Nat) : Int)) :=
      Nat.mul_le_mul_right _ h8le
    have hLS : levelSum (fun h => levelFree f n K (m + (h : Int))) (H + 2) =
        levelSum (fun h => levelFree f n K (m + (h : Int))) (H + 1) +
          levelFree f n K (m + ((H + 2 : Nat) : Int)) := rfl
    change 3 * 3 ^ (H + 2) * triSum (fun h => levelAdditions f n K (m + (h : Int))) (H + 2) +
        3 ^ (H + 3) * doubleAscent f n K (m + ((H + 1 : Nat) : Int)) +
        2 * 3 ^ (H + 2) * doubleAscent f n K (m + ((H + 2 : Nat) : Int)) +
        3 ^ (H + 3) * levelFree f n K (m + ((H + 2 : Nat) : Int)) ≤
      27 * 5 ^ (H + 1) * levelSum (fun h => levelFree f n K (m + (h : Int))) (H + 2)
    unfold triAdditions at ih h5ih
    rw [hLS, Nat.mul_add]
    have h1 : 5 * (3 * 3 ^ (H + 1) * triSum (fun h => levelAdditions f n K (m + (h : Int))) (H + 1)) +
        3 ^ (H + 2) * (3 * levelAdditions f n K (m + ((H + 2 : Nat) : Int))) +
        3 ^ (H + 2) * levelAdditions f n K (m + ((H + 1 : Nat) : Int)) =
        3 * 3 ^ (H + 2) * triSum (fun h => levelAdditions f n K (m + (h : Int))) (H + 2) +
          3 ^ (H + 2) * levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) H := by
      have h5T : 5 * (3 * 3 ^ (H + 1) * triSum (fun h => levelAdditions f n K (m + (h : Int))) (H + 1)) =
          3 ^ (H + 2) * (5 * triSum (fun h => levelAdditions f n K (m + (h : Int))) (H + 1)) := by
        rw [hpow3_1]; grind
      rw [h5T, ← Nat.mul_add, ← Nat.mul_add, htid3, Nat.mul_add]
      grind
    have h2 : 5 * (2 * 3 ^ (H + 1) * doubleAscent f n K (m + ((H + 1 : Nat) : Int))) ≥
        3 ^ (H + 3) * doubleAscent f n K (m + ((H + 1 : Nat) : Int)) := by
      rw [hpow3_2, hpow3_1]
      have hle : 9 * 3 ^ (H + 1) ≤ 10 * 3 ^ (H + 1) := by omega
      have hmul := Nat.mul_le_mul_right (doubleAscent f n K (m + ((H + 1 : Nat) : Int))) hle
      grind
    have h3 : 5 * (27 * 5 ^ H * levelSum (fun h => levelFree f n K (m + (h : Int))) (H + 1)) =
        27 * 5 ^ (H + 1) * levelSum (fun h => levelFree f n K (m + (h : Int))) (H + 1) := by
      rw [hpow5]; grind
    have h4 : 3 ^ (H + 2) * (5 * levelFree f n K (m + ((H + 2 : Nat) : Int))) +
        3 ^ (H + 3) * levelFree f n K (m + ((H + 2 : Nat) : Int)) =
        8 * 3 ^ (H + 2) * levelFree f n K (m + ((H + 2 : Nat) : Int)) := by
      rw [hpow3_2]; grind
    have h5 : 5 * (3 ^ (H + 2) * doubleAscent f n K (m + (H : Int))) =
        3 ^ (H + 2) * (5 * doubleAscent f n K (m + (H : Int))) := by grind
    have h6 : 3 ^ (H + 2) * (2 * doubleAscent f n K (m + ((H + 2 : Nat) : Int))) =
        2 * 3 ^ (H + 2) * doubleAscent f n K (m + ((H + 2 : Nat) : Int)) := by grind
    simp only [Nat.mul_add] at h5ih h3st
    omega

/-! ## Main exact `5/3` capacity, strip, low-weights, and free-gap theorems -/

/-- Exact `5/3` triangular-weighted capacity above floor `m`:
  `3 ^ (H + 1) * triAdditions f n K m (H + 1) ≤ 9 * 5 ^ H * free f n K`
for every `H : Nat`, unconditionally on actual `EndN`. -/
theorem exact_five_thirds_triangular_capacity (f : Nat → Bool) (n a K H : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    3 ^ (H + 1) * triAdditions f n K m (H + 1) ≤ 9 * 5 ^ H * free f n K := by
  have hinv := exact_five_thirds_invariant f n a K m hw hpre hfloor H
  have hfr := levelSum_free_le_free f n K m (H + 1)
  have hR : 27 * 5 ^ H * levelSum (fun h => levelFree f n K (m + (h : Int))) (H + 1) ≤
      27 * 5 ^ H * free f n K := Nat.mul_le_mul_left _ hfr
  have h3 : 3 * (3 ^ (H + 1) * triAdditions f n K m (H + 1)) ≤ 3 * (9 * 5 ^ H * free f n K) := by
    have hL : 3 * (3 ^ (H + 1) * triAdditions f n K m (H + 1)) =
        3 * 3 ^ (H + 1) * triAdditions f n K m (H + 1) := by grind
    have hRR : 3 * (9 * 5 ^ H * free f n K) = 27 * 5 ^ H * free f n K := by grind
    omega
  omega

/-- Exact `(5/3)^h` single-level actual-`EndN` capacity for every `h : Nat`:
  `5 * 3 ^ h * levelAdditions f n K (m + h) ≤ 9 * 5 ^ h * free f n K`.
Breaks `E-794`'s `190/107` (`1.77397` cone) barrier all the way down to exact `5/3`. -/
theorem exact_five_thirds_level_bound (f : Nat → Bool) (n a K h : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    5 * 3 ^ h * levelAdditions f n K (m + (h : Int)) ≤ 9 * 5 ^ h * free f n K := by
  cases h with
  | zero =>
    have hE0 : levelSupplied f n K (m + ((0 : Nat) : Int)) = 0 := by
      apply cN_zero_of
      intro t hnt htK ht
      exact block_prefix_low_clock_not_endable f n a t hw hpre hnt m
        (fun i hi hj => hfloor i hi (by omega)) (by omega) ht.2
    have hsp := level_additions_split f n K (m + ((0 : Nat) : Int))
    have hfr : levelFree f n K (m + ((0 : Nat) : Int)) ≤ free f n K := by
      unfold levelFree free
      exact cN_mono _ _ n K (fun _ _ _ ht => ⟨ht.2.1, ht.2.2⟩)
    simp only [Nat.pow_zero, Nat.mul_one]
    omega
  | succ H =>
    have htri := exact_five_thirds_triangular_capacity f n a K H m hw hpre hfloor
    have hle1 := last_le_levelSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1)
    have hle2 := levelSum_le_triSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1)
    have hle : levelAdditions f n K (m + ((H + 1 : Nat) : Int)) ≤ triAdditions f n K m (H + 1) :=
      Nat.le_trans hle1 hle2
    have hmul := Nat.mul_le_mul_left (5 * 3 ^ (H + 1)) hle
    have h5tri := Nat.mul_le_mul_left 5 htri
    have hL : 5 * (3 ^ (H + 1) * triAdditions f n K m (H + 1)) =
        5 * 3 ^ (H + 1) * triAdditions f n K m (H + 1) := by grind
    have hR : 5 * (9 * 5 ^ H * free f n K) = 9 * 5 ^ (H + 1) * free f n K := by
      rw [Nat.pow_succ 5 H]; grind
    omega

/-- Exact `(5/3)^H` total-strip additions capacity: whenever the walk stays in `[m, m + H]`
during `[n, n + K)`,
  `5 * 3 ^ H * additions f n K ≤ 9 * 5 ^ H * free f n K`.
Together with `E-786` (`2 * 5 ^ H * (free + O_c) ≤ 5 * 3 ^ H * additions` on `[0, H + 1]`),
this pins the actual-`EndN` exponential growth base to exact `5/3` within a factor of `9/2`. -/
theorem exact_five_thirds_strip_additions_bound (f : Nat → Bool) (n a K H : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i)
    (hceil : ∀ i, n ≤ i → i < n + K → Fw f i ≤ m + (H : Int)) :
    5 * 3 ^ H * additions f n K ≤ 9 * 5 ^ H * free f n K := by
  have hadd_le : additions f n K ≤ cN (fun t => f t = true ∧ Fw f t ≤ m + (H : Int)) n K := by
    unfold additions
    exact cN_mono _ _ n K (fun t hnt htK hf => ⟨hf, hceil t hnt htK⟩)
  have hls := additions_le_levelSum f n K m (fun i hi1 hi2 => hfloor i hi1 (by omega)) H
  have htot := Nat.le_trans hadd_le hls
  cases H with
  | zero =>
    have hE0 : levelSupplied f n K (m + ((0 : Nat) : Int)) = 0 := by
      apply cN_zero_of
      intro t hnt htK ht
      exact block_prefix_low_clock_not_endable f n a t hw hpre hnt m
        (fun i hi hj => hfloor i hi (by omega)) (by omega) ht.2
    have hsp := level_additions_split f n K (m + ((0 : Nat) : Int))
    have hfr : levelFree f n K (m + ((0 : Nat) : Int)) ≤ free f n K := by
      unfold levelFree free
      exact cN_mono _ _ n K (fun _ _ _ ht => ⟨ht.2.1, ht.2.2⟩)
    simp only [levelSum] at htot
    simp only [Nat.pow_zero, Nat.mul_one]
    omega
  | succ H =>
    have htri := exact_five_thirds_triangular_capacity f n a K H m hw hpre hfloor
    have hle := Nat.le_trans htot
      (levelSum_le_triSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1))
    have hmul := Nat.mul_le_mul_left (5 * 3 ^ (H + 1)) hle
    have h5tri := Nat.mul_le_mul_left 5 htri
    have hL : 5 * (3 ^ (H + 1) * triAdditions f n K m (H + 1)) =
        5 * 3 ^ (H + 1) * triAdditions f n K m (H + 1) := by grind
    have hR : 5 * (9 * 5 ^ H * free f n K) = 9 * 5 ^ (H + 1) * free f n K := by
      rw [Nat.pow_succ 5 H]; grind
    unfold triAdditions at h5tri hL
    omega

/-- Exact `(5/3)^d` arbitrary-depth low-addition weight bound: for every `d : Nat` and
every `r ≤ m + d`,
  `(25 * 3 ^ d : Int) * lowAdditionWeights f n r K ≤ (54 * 5 ^ d : Int) * free f n K`
(`W(m + d) ≤ 2.16 * (5/3)^d * free`), upgrading `E-787` (`2^d`) and `E-788` (`(199/110)^d`)
to the exact optimal base `5/3`. -/
theorem exact_five_thirds_low_weights_bound (f : Nat → Bool) (n a K d : Nat) (m r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) (hr : r ≤ m + (d : Int)) :
    ((25 * 3 ^ d : Nat) : Int) * lowAdditionWeights f n r K ≤
      ((54 * 5 ^ d : Nat) : Int) * (free f n K : Int) := by
  cases d with
  | zero =>
    have hz := lowAdditionWeights_zero_le_floor f n m r (by omega) K hfloor
    rw [hz, Int.mul_zero]
    exact Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  | succ d =>
    cases d with
    | zero =>
      have hmono := lowAdditionWeights_mono_r f n r (m + ((0 : Nat) : Int) + 1) (by omega) K
      have hW := lowAdditionWeights_eq_levelWeightSum f n K m hfloor 0
      have hE0 : levelSupplied f n K (m + ((0 : Nat) : Int)) = 0 := by
        apply cN_zero_of
        intro t hnt htK ht
        exact block_prefix_low_clock_not_endable f n a t hw hpre hnt m
          (fun i hi hj => hfloor i hi (by omega)) (by omega) ht.2
      have hsp := level_additions_split f n K (m + ((0 : Nat) : Int))
      have hfr : levelFree f n K (m + ((0 : Nat) : Int)) ≤ free f n K := by
        unfold levelFree free
        exact cN_mono _ _ n K (fun _ _ _ ht => ⟨ht.2.1, ht.2.2⟩)
      simp only [levelWeightSum] at hW
      have h1 : lowAdditionWeights f n r K ≤ (free f n K : Int) := by omega
      have hmul := Int.mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg (25 * 3 ^ 1))
      have hc : ((25 * 3 ^ 1 : Nat) : Int) ≤ ((54 * 5 ^ 1 : Nat) : Int) := by decide
      have h2 := Int.mul_le_mul_of_nonneg_right hc (Int.natCast_nonneg (free f n K))
      exact Int.le_trans hmul h2
    | succ H =>
      have hmono := lowAdditionWeights_mono_r f n r (m + ((H + 1 : Nat) : Int) + 1) (by omega) K
      have hW := lowAdditionWeights_eq_levelWeightSum f n K m hfloor (H + 1)
      have htri := exact_five_thirds_triangular_capacity f n a K H m hw hpre hfloor
      have hWS := levelWeightSum_add_levelSum
        (fun j => levelAdditions f n K (m + (j : Int))) (H + 1)
      have hWle : levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1) ≤
          2 * triAdditions f n K m (H + 1) := by
        unfold triAdditions; omega
      have hNat : 25 * 3 ^ (H + 2) *
          levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1) ≤
          54 * 5 ^ (H + 2) * free f n K := by
        have h1 := Nat.mul_le_mul_left (25 * 3 ^ (H + 2)) hWle
        have h2 := Nat.mul_le_mul_left 150 htri
        have hL : 25 * 3 ^ (H + 2) * (2 * triAdditions f n K m (H + 1)) =
            150 * (3 ^ (H + 1) * triAdditions f n K m (H + 1)) := by
          rw [show H + 2 = (H + 1) + 1 by omega, Nat.pow_succ 3 (H + 1)]; grind
        have hR : 150 * (9 * 5 ^ H * free f n K) = 54 * 5 ^ (H + 2) * free f n K := by
          rw [show H + 2 = (H + 1) + 1 by omega, Nat.pow_succ 5 (H + 1), Nat.pow_succ 5 H]; grind
        omega
      have hcast : ((25 * 3 ^ (H + 2) : Nat) : Int) *
          (levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1) : Int) ≤
          ((54 * 5 ^ (H + 2) : Nat) : Int) * (free f n K : Int) := by
        exact_mod_cast hNat
      have h1 := Int.mul_le_mul_of_nonneg_left hmono (Int.natCast_nonneg (25 * 3 ^ (H + 2)))
      rw [hW] at h1
      exact Int.le_trans h1 hcast

/-- Exact `(5/3)^d` arbitrary-depth free-gap square inequality WITHOUT `hpos` and WITHOUT
any height ceiling: whenever `Fw f (b + j) ≤ m + d + 1` after an all-`S` gap of length `j`,
  `(25 * 3 ^ d : Int) * (j + 1)^2 ≤ (54 * 5 ^ d : Int) * free f n (b - n)`. -/
theorem exact_five_thirds_free_gap_square (f : Nat → Bool) (n a b j d : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hnb : n < b) (hfloor : ∀ i, n ≤ i → i ≤ b → m ≤ Fw f i)
    (hS : ∀ i, b ≤ i → i < b + j → f i = false) (he : EndN f 0 (b + j))
    (hTarget : Fw f (b + j) ≤ m + (d : Int) + 1) :
    ((25 * 3 ^ d : Nat) : Int) * ((j : Int) + 1) ^ 2 ≤
      ((54 * 5 ^ d : Nat) : Int) * (free f n (b - n) : Int) := by
  have hs := supplied_gap_square_low_additions f n a b j hw hpre hnb hS he
  have hl := exact_five_thirds_low_weights_bound f n a (b - n) d m (Fw f (b + j) - 1)
    hw hpre (fun i hi hj => hfloor i hi (by omega)) (by omega)
  have h1 := Int.mul_le_mul_of_nonneg_left hs (Int.natCast_nonneg (25 * 3 ^ d))
  exact Int.le_trans h1 hl

end Recaman.ExactFiveThirdsCapacity
