import Recaman.SupplyExcursionSpacing

namespace Recaman.ArbitraryDepthFreeGap

open Recaman.SupplyExcursionSpacing Recaman.SupplyHeightWeightBudget Recaman.SupplyDescentWeight
open Recaman.SupplyDescentSlots Recaman.SupplyAreaCrossings Recaman.FloorSupplyPotential
open Recaman.FloorSupplyFreeBudget Recaman.LowTargetWeightedGap Recaman.GapSquareLowAdditions
open Recaman.GapTargetHeightBudget Recaman.BlockOldRay Recaman.LevelTriangleArea
open Recaman.AdditionRankSlack Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality
open Recaman.CapacityEqualityInduction Recaman.SuffixHallOwnerMap
open Classical

/-! # Arbitrary-depth low-addition weight bounds and free-gap profiles

Connecting the arbitrary-height excursion 3-spacing budget (`E-785`,
`Recaman.SupplyExcursionSpacing`) with the supplied gap-square bound (`E-662`,
`Recaman.GapSquareLowAdditions`) yields arbitrary-depth generalizations of the
fixed-depth free-gap theorems `E-663` (`depth 5`) and `E-666` (`depth 6`):

- `low_weights_le_two_dyadic_free`:
    `lowAdditionWeights f n (m + d + 1) K ≤ 2 * dyadicFree f n K m d` for every `d : Nat`.
- `low_weights_le_pow_two_free`:
    `r ≤ m + d → lowAdditionWeights f n r K ≤ 2 ^ d * free f n K` for every `d : Nat`.
- `low_weights_five_three_spacing`:
    `r ≤ m + 5 → 3 * lowAdditionWeights f n r K ≤ 59 * free f n K`
    (sharpening the `E-674` depth-5 weight bound from `25` down to `59 / 3 < 20`).
- `arbitrary_target_height_free_gap_square` and `arbitrary_target_height_free_gap`:
    for ANY target height `Fw f (b + j) ≤ m + d + 1`, WITHOUT `hpos` and WITHOUT
    any upper ceiling on intermediate heights,
    `((j : Int) + 1) ^ 2 ≤ 2 ^ d * free f n (b - n)` and `2 ^ d ≤ j + 2 → j + 1 ≤ free`.
- `positive_arbitrary_depth_free_gap_profile`:
    for ANY depth `D ≥ 2`, any positive-deficit free-gap counterexample satisfies
    `4 ≤ free ≤ j ≤ 2 ^ (D - 2) - 3`, `Fw f (b + j) ≤ Fw f n - 1`, and
    `((j : Int) + 1) ^ 2 ≤ 2 ^ (D - 2) * free`.
- `positive_depth_seven_counter_profile`:
    at depth `D = 7`, any positive-deficit counterexample satisfies `4 ≤ free ≤ j ≤ 17`
    and `3 * ((j : Int) + 1) ^ 2 ≤ 59 * free`.
-/

/-! ## Level sums and low-addition weight decomposition -/

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

private theorem dyadicSum_add (g₁ g₂ : Nat → Nat) :
    ∀ H, dyadicSum (fun h => g₁ h + g₂ h) H = dyadicSum g₁ H + dyadicSum g₂ H
  | 0 => rfl
  | H + 1 => by
    simp only [dyadicSum, dyadicSum_add g₁ g₂ H]
    omega

private theorem dyadic_additions_split (f : Nat → Bool) (n K : Nat) (m : Int) (H : Nat) :
    dyadicAdditions f n K m H = dyadicFree f n K m H + dyadicSupplied f n K m H := by
  unfold dyadicAdditions dyadicFree dyadicSupplied
  rw [← dyadicSum_add]
  congr 1
  funext h
  exact level_additions_split f n K (m + (h : Int))

private theorem dyadicSum_le_pow_mul_sum (g : Nat → Nat) :
    ∀ H, dyadicSum g H ≤ 2 ^ H * levelSum g H
  | 0 => by simp [dyadicSum, levelSum]
  | H + 1 => by
    have ih := dyadicSum_le_pow_mul_sum g H
    simp only [dyadicSum, levelSum, Nat.pow_succ, Nat.mul_add]
    have h1 : 2 * (2 ^ H * levelSum g H) = 2 ^ H * 2 * levelSum g H := by
      rw [Nat.mul_comm (2 ^ H) 2, Nat.mul_assoc]
    have h2 : g (H + 1) ≤ 2 ^ H * 2 * g (H + 1) := by
      have hge : 1 ≤ 2 ^ H := Nat.one_le_two_pow
      exact Nat.le_mul_of_pos_left _ (by omega)
    omega

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

private theorem levelSum_free_le_free (f : Nat → Bool) (n K : Nat) (m : Int) (H : Nat) :
    levelSum (fun h => levelFree f n K (m + (h : Int))) H ≤ free f n K := by
  have hls := levelSum_free_le f n K m H
  have hfr : cN (fun t => f t = true ∧ ¬ EndN f 0 t ∧ Fw f t ≤ m + (H : Int)) n K ≤
      free f n K := by
    unfold free
    exact cN_mono _ _ n K (fun t _ _ ht => ⟨ht.1, ht.2.1⟩)
  exact Nat.le_trans hls hfr

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

private theorem dyadic_weight_invariant (f : Nat → Bool) (n a K : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    ∀ H, 3 * dyadicSupplied f n K m (H + 1) +
        levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1) +
        levelAdditions f n K (m + ((H + 1 : Nat) : Int)) +
        levelAdditions f n K (m + (H : Int)) ≤
      2 * dyadicAdditions f n K m (H + 1) := by
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

/-! ## Arbitrary-depth low-addition weight bounds -/

/-- Arbitrary-height dyadic free bound on low-addition weights:
for every height offset `d : Nat` above floor `m`, the low-addition weight below
`m + d + 1` is at most twice the dyadic free sum up to `m + d`. -/
theorem low_weights_le_two_dyadic_free (f : Nat → Bool) (n a K d : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    lowAdditionWeights f n (m + (d : Int) + 1) K ≤ 2 * (dyadicFree f n K m d : Int) := by
  rw [lowAdditionWeights_eq_levelWeightSum f n K m hfloor d]
  cases d with
  | zero =>
    have hE0 : levelSupplied f n K (m + ((0 : Nat) : Int)) = 0 := by
      apply cN_zero_of
      intro t hnt htK ht
      exact block_prefix_low_clock_not_endable f n a t hw hpre hnt m
        (fun i hi hj => hfloor i hi (by omega)) (by omega) ht.2
    have hsp := level_additions_split f n K (m + ((0 : Nat) : Int))
    simp only [levelWeightSum, dyadicFree, dyadicSum]
    omega
  | succ H =>
    have hinv := dyadic_weight_invariant f n a K m hw hpre hfloor H
    have hsp := dyadic_additions_split f n K m (H + 1)
    omega

/-- Arbitrary-depth exponential-two low-addition weight bound:
for every `d : Nat` and `r ≤ m + d`, `lowAdditionWeights f n r K ≤ 2 ^ d * free f n K`. -/
theorem low_weights_le_pow_two_free (f : Nat → Bool) (n a K d : Nat) (m r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) (hr : r ≤ m + (d : Int)) :
    lowAdditionWeights f n r K ≤ ((2 ^ d : Nat) : Int) * (free f n K : Int) := by
  cases d with
  | zero =>
    have hz := lowAdditionWeights_zero_le_floor f n m r (by omega) K hfloor
    rw [hz]
    simp only [Nat.pow_zero]
    omega
  | succ d' =>
    have hmono := lowAdditionWeights_mono_r f n r (m + (d' : Int) + 1) (by omega) K
    have hdy := low_weights_le_two_dyadic_free f n a K d' m hw hpre hfloor
    have hpow := dyadicSum_le_pow_mul_sum (fun h => levelFree f n K (m + (h : Int))) d'
    have hls := levelSum_free_le_free f n K m d'
    have hmul : dyadicFree f n K m d' ≤ 2 ^ d' * free f n K :=
      Nat.le_trans hpow (Nat.mul_le_mul_left (2 ^ d') hls)
    have hmul2 : 2 * dyadicFree f n K m d' ≤ 2 ^ (d' + 1) * free f n K := by
      have h2 := Nat.mul_le_mul_left 2 hmul
      have heq : 2 * (2 ^ d' * free f n K) = 2 ^ (d' + 1) * free f n K := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ d') 2, Nat.mul_assoc]
      omega
    have hcast : (2 : Int) * (dyadicFree f n K m d' : Int) ≤
        ((2 ^ (d' + 1) : Nat) : Int) * (free f n K : Int) := by
      exact_mod_cast hmul2
    exact Int.le_trans hmono (Int.le_trans hdy hcast)

/-- Sharp depth-5 low-addition weight bound from excursion 3-spacing:
for `r ≤ m + 5`, `3 * lowAdditionWeights f n r K ≤ 59 * free f n K`
(strictly below `E-674`'s `25 * free` and the dyadic bound `32 * free`). -/
theorem low_weights_five_three_spacing (f : Nat → Bool) (n a K : Nat) (m r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) (hr : r ≤ m + 5) :
    3 * lowAdditionWeights f n r K ≤ 59 * (free f n K : Int) := by
  have hmono := lowAdditionWeights_mono_r f n r (m + ((4 : Nat) : Int) + 1) (by omega) K
  have hW4 := lowAdditionWeights_eq_levelWeightSum f n K m hfloor 4
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
  have hb2 := same_height_supply_three_spacing_budget f n a K (m + ((0 : Nat) : Int) + 1) hw hpre
  rw [lowAdditionWeights_eq_levelWeightSum f n K m hfloor 0] at hb2
  have hEqE2 : cN (fun t => Fw f t = m + ((0 : Nat) : Int) + 1 + 1 ∧ EndN f 0 t) n K =
      levelSupplied f n K (m + ((2 : Nat) : Int)) := by
    unfold levelSupplied
    rw [show m + ((0 : Nat) : Int) + 1 + 1 = m + ((2 : Nat) : Int) by omega]
  have hEqA0 : cN (fun t => Fw f t = m + ((0 : Nat) : Int) + 1 - 1 ∧ f t = true) n K =
      levelAdditions f n K (m + ((0 : Nat) : Int)) := by
    unfold levelAdditions
    rw [show m + ((0 : Nat) : Int) + 1 - 1 = m + ((0 : Nat) : Int) by omega]
  rw [hEqE2, hEqA0] at hb2
  have hb3 := same_height_supply_three_spacing_budget f n a K (m + ((1 : Nat) : Int) + 1) hw hpre
  rw [lowAdditionWeights_eq_levelWeightSum f n K m hfloor 1] at hb3
  have hEqE3 : cN (fun t => Fw f t = m + ((1 : Nat) : Int) + 1 + 1 ∧ EndN f 0 t) n K =
      levelSupplied f n K (m + ((3 : Nat) : Int)) := by
    unfold levelSupplied
    rw [show m + ((1 : Nat) : Int) + 1 + 1 = m + ((3 : Nat) : Int) by omega]
  have hEqA1 : cN (fun t => Fw f t = m + ((1 : Nat) : Int) + 1 - 1 ∧ f t = true) n K =
      levelAdditions f n K (m + ((1 : Nat) : Int)) := by
    unfold levelAdditions
    rw [show m + ((1 : Nat) : Int) + 1 - 1 = m + ((1 : Nat) : Int) by omega]
  rw [hEqE3, hEqA1] at hb3
  have hb4 := same_height_supply_three_spacing_budget f n a K (m + ((2 : Nat) : Int) + 1) hw hpre
  rw [lowAdditionWeights_eq_levelWeightSum f n K m hfloor 2] at hb4
  have hEqE4 : cN (fun t => Fw f t = m + ((2 : Nat) : Int) + 1 + 1 ∧ EndN f 0 t) n K =
      levelSupplied f n K (m + ((4 : Nat) : Int)) := by
    unfold levelSupplied
    rw [show m + ((2 : Nat) : Int) + 1 + 1 = m + ((4 : Nat) : Int) by omega]
  have hEqA2 : cN (fun t => Fw f t = m + ((2 : Nat) : Int) + 1 - 1 ∧ f t = true) n K =
      levelAdditions f n K (m + ((2 : Nat) : Int)) := by
    unfold levelAdditions
    rw [show m + ((2 : Nat) : Int) + 1 - 1 = m + ((2 : Nat) : Int) by omega]
  rw [hEqE4, hEqA2] at hb4
  have hs0 := level_additions_split f n K (m + ((0 : Nat) : Int))
  have hs1 := level_additions_split f n K (m + ((1 : Nat) : Int))
  have hs2 := level_additions_split f n K (m + ((2 : Nat) : Int))
  have hs3 := level_additions_split f n K (m + ((3 : Nat) : Int))
  have hs4 := level_additions_split f n K (m + ((4 : Nat) : Int))
  have hls := levelSum_free_le_free f n K m 4
  have hEqA2' : cN (fun t => Fw f t = m + ((2 : Nat) : Int) + 1 - 1 ∧ f t = true) n K =
      levelAdditions f n K (m + ((2 : Nat) : Int)) := hEqA2
  simp only [levelWeightSum, levelSum, Nat.reduceAdd] at hW4 hb2 hb3 hb4 hls
  omega

/-! ## Arbitrary-depth free-gap inequalities and positive-deficit profiles -/

private theorem sq_gt_mul_of_le_add_two (j C f : Nat) (hC : C ≤ j + 2) (hf : f ≤ j) :
    ((C : Int) * (f : Int)) < ((j : Int) + 1) ^ 2 := by
  have h1 : (C : Int) * (f : Int) ≤ ((j : Int) + 2) * (j : Int) := by
    have hCf : (C : Int) * (f : Int) ≤ (C : Int) * (j : Int) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have hCj : (C : Int) * (j : Int) ≤ ((j : Int) + 2) * (j : Int) :=
      Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    exact Int.le_trans hCf hCj
  have h2 : ((j : Int) + 1) ^ 2 = ((j : Int) + 2) * (j : Int) + 1 := by grind
  omega

private theorem le_sub_three_of_sq_le_mul (j C f : Nat)
    (hsq : ((j : Int) + 1) ^ 2 ≤ (C : Int) * (f : Int)) (hf : f ≤ j) :
    j + 3 ≤ C := by
  by_cases h : j + 3 ≤ C
  · exact h
  · have hlt := sq_gt_mul_of_le_add_two j C f (by omega) hf
    omega

private theorem le_seventeen_of_three_sq_le_59 (j f : Nat)
    (hsq : 3 * ((j : Int) + 1) ^ 2 ≤ 59 * (f : Int)) (hf : f ≤ j) :
    j ≤ 17 := by
  by_cases h : j ≤ 17
  · exact h
  · have hfj : 59 * (f : Int) ≤ 59 * (j : Int) := by omega
    have hnn : 0 ≤ ((j : Int) - 18) * (3 * (j : Int) + 1) :=
      Int.mul_nonneg (by omega) (by omega)
    have hpoly : 3 * ((j : Int) + 1) ^ 2 - 59 * (j : Int) =
        ((j : Int) - 18) * (3 * (j : Int) + 1) + 21 := by grind
    omega

/-- Arbitrary-height free-gap square bound WITHOUT `hpos` and WITHOUT any upper walk ceiling:
if a supplied target at `b + j` after `j` subtractions lies at most `d + 1` above floor `m`,
then `(j + 1)^2 ≤ 2^d * free f n (b - n)`. -/
theorem arbitrary_target_height_free_gap_square (f : Nat → Bool) (n a b j d : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hnb : n < b) (hfloor : ∀ i, n ≤ i → i ≤ b → m ≤ Fw f i)
    (hS : ∀ i, b ≤ i → i < b + j → f i = false) (he : EndN f 0 (b + j))
    (hTarget : Fw f (b + j) ≤ m + (d : Int) + 1) :
    ((j : Int) + 1) ^ 2 ≤ ((2 ^ d : Nat) : Int) * (free f n (b - n) : Int) := by
  have hs := supplied_gap_square_low_additions f n a b j hw hpre hnb hS he
  have hl := low_weights_le_pow_two_free f n a (b - n) d m (Fw f (b + j) - 1) hw hpre
    (fun i hi hj => hfloor i hi (by omega)) (by omega)
  exact Int.le_trans hs hl

/-- Arbitrary-height unconditional free-gap cutoff WITHOUT `hpos` and WITHOUT any upper ceiling:
for every `d : Nat`, if `Fw f (b + j) ≤ m + d + 1` and `2^d ≤ j + 2`, then `j + 1 ≤ free f n (b - n)`. -/
theorem arbitrary_target_height_free_gap (f : Nat → Bool) (n a b j d : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hnb : n < b) (hfloor : ∀ i, n ≤ i → i ≤ b → m ≤ Fw f i)
    (hS : ∀ i, b ≤ i → i < b + j → f i = false) (he : EndN f 0 (b + j))
    (hTarget : Fw f (b + j) ≤ m + (d : Int) + 1) (hgap : 2 ^ d ≤ j + 2) :
    j + 1 ≤ free f n (b - n) := by
  by_cases h : j + 1 ≤ free f n (b - n)
  · exact h
  · have hsq := arbitrary_target_height_free_gap_square f n a b j d m hw hpre hnb hfloor hS he hTarget
    have hlt := sq_gt_mul_of_le_add_two j (2 ^ d) (free f n (b - n)) hgap (by omega)
    omega

/-- Arbitrary-depth positive-deficit counterexample profile (generalizing `E-663` and `E-666`
to every depth `D ≥ 2` with no upper bound on intervening heights):
any positive-deficit free-gap counterexample (`free ≤ j`) obeys
`4 ≤ free`, `j + 3 ≤ 2 ^ (D - 2)`, `Fw f (b + j) ≤ Fw f n - 1`, and
`((j : Int) + 1) ^ 2 ≤ 2 ^ (D - 2) * free`. -/
theorem positive_arbitrary_depth_free_gap_profile (f : Nat → Bool) (n a b j D : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hnb : n < b) (hD : 2 ≤ D)
    (hfloor : ∀ i, n ≤ i → i ≤ b → Fw f n - (D : Int) ≤ Fw f i)
    (hpos : ∀ k, 0 < k → k ≤ b - n → cN (EndN f 0) n k + 1 ≤ cN (fun i => f i = false) n k)
    (hS : ∀ i, b ≤ i → i < b + j → f i = false) (he : EndN f 0 (b + j))
    (hcounter : free f n (b - n) ≤ j) :
    4 ≤ free f n (b - n) ∧
      j + 3 ≤ 2 ^ (D - 2) ∧
      Fw f (b + j) ≤ Fw f n - 1 ∧
      ((j : Int) + 1) ^ 2 ≤ ((2 ^ (D - 2) : Nat) : Int) * (free f n (b - n) : Int) := by
  have hfree : 4 ≤ free f n (b - n) := by
    by_cases h : 4 ≤ free f n (b - n)
    · exact h
    · have hgap := positive_r3_free_gap f n a (b - n) j hw hpre (by omega) hpos
        (show free f n (b - n) ≤ 3 by omega)
        (by rwa [show n + (b - n) = b by omega]) (by rwa [show n + (b - n) = b by omega])
      change j + 1 ≤ free f n (b - n) at hgap
      omega
  have hdown := fw_false_run f b j hS
  have hwalk := (cN_walk f n (b - n)).1
  rw [show n + (b - n) = b by omega] at hwalk
  change Fw f b = Fw f n + (additions f n (b - n) : Int) - subtractions f n (b - n) at hwalk
  have hP := hpos (b - n) (by omega) (by omega)
  change cN (EndN f 0) n (b - n) + 1 ≤ subtractions f n (b - n) at hP
  have hpart := additions_split f n (b - n)
  have hTarget_top : Fw f (b + j) ≤ Fw f n - 1 := by omega
  have hTarget_d : Fw f (b + j) ≤ (Fw f n - (D : Int)) + ((D - 2 : Nat) : Int) + 1 := by omega
  have hsq := arbitrary_target_height_free_gap_square f n a b j (D - 2) (Fw f n - (D : Int))
    hw hpre hnb hfloor hS he hTarget_d
  have hj := le_sub_three_of_sq_le_mul j (2 ^ (D - 2)) (free f n (b - n)) hsq hcounter
  exact ⟨hfree, hj, hTarget_top, hsq⟩

/-- Sharp depth-7 positive-deficit counterexample profile from the 3-spacing weight bound
`3 * W(m + 5) ≤ 59 * free`: any depth-7 counterexample obeys `4 ≤ free ≤ j ≤ 17`,
`Fw f (b + j) ≤ Fw f n - 1`, and `3 * (j + 1)^2 ≤ 59 * free`. -/
theorem positive_depth_seven_counter_profile (f : Nat → Bool) (n a b j : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hnb : n < b) (hfloor : ∀ i, n ≤ i → i ≤ b → Fw f n - 7 ≤ Fw f i)
    (hpos : ∀ k, 0 < k → k ≤ b - n → cN (EndN f 0) n k + 1 ≤ cN (fun i => f i = false) n k)
    (hS : ∀ i, b ≤ i → i < b + j → f i = false) (he : EndN f 0 (b + j))
    (hcounter : free f n (b - n) ≤ j) :
    4 ≤ free f n (b - n) ∧
      j ≤ 17 ∧
      Fw f (b + j) ≤ Fw f n - 1 ∧
      3 * ((j : Int) + 1) ^ 2 ≤ 59 * (free f n (b - n) : Int) := by
  have hfree : 4 ≤ free f n (b - n) := by
    by_cases h : 4 ≤ free f n (b - n)
    · exact h
    · have hgap := positive_r3_free_gap f n a (b - n) j hw hpre (by omega) hpos
        (show free f n (b - n) ≤ 3 by omega)
        (by rwa [show n + (b - n) = b by omega]) (by rwa [show n + (b - n) = b by omega])
      change j + 1 ≤ free f n (b - n) at hgap
      omega
  have hdown := fw_false_run f b j hS
  have hwalk := (cN_walk f n (b - n)).1
  rw [show n + (b - n) = b by omega] at hwalk
  change Fw f b = Fw f n + (additions f n (b - n) : Int) - subtractions f n (b - n) at hwalk
  have hP := hpos (b - n) (by omega) (by omega)
  change cN (EndN f 0) n (b - n) + 1 ≤ subtractions f n (b - n) at hP
  have hpart := additions_split f n (b - n)
  have hTarget_top : Fw f (b + j) ≤ Fw f n - 1 := by omega
  have hs := supplied_gap_square_low_additions f n a b j hw hpre hnb hS he
  have hl := low_weights_five_three_spacing f n a (b - n) (Fw f n - 7) (Fw f (b + j) - 1)
    hw hpre (fun i hi hj => hfloor i hi (by omega)) (by omega)
  have h3sq : 3 * ((j : Int) + 1) ^ 2 ≤ 59 * (free f n (b - n) : Int) := by omega
  have hj := le_seventeen_of_three_sq_le_59 j (free f n (b - n)) h3sq hcounter
  exact ⟨hfree, hj, hTarget_top, h3sq⟩

end Recaman.ArbitraryDepthFreeGap
