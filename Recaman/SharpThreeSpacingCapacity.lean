import Recaman.ArbitraryDepthFreeGap

namespace Recaman.SharpThreeSpacingCapacity

open Recaman.ArbitraryDepthFreeGap Recaman.SupplyExcursionSpacing
open Recaman.SupplyHeightWeightBudget Recaman.SupplyDescentWeight Recaman.SupplyDescentSlots
open Recaman.SupplyAreaCrossings Recaman.FloorSupplyPotential Recaman.FloorSupplyFreeBudget
open Recaman.LowTargetWeightedGap Recaman.GapSquareLowAdditions Recaman.LevelTriangleArea
open Recaman.AdditionRankSlack Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality
open Recaman.CapacityEqualityInduction
open Classical

/-! # Rational height-weighted capacity across the entire 3-spacing cone

Using the exact arbitrary-height excursion 3-spacing budget (`E-785`,
`same_height_supply_three_spacing_budget`) directly on actual `EndN`, this module
establishes a single zero-slack polynomial telescoping invariant parameterized by
EVERY rational weight `q = P / Q` satisfying `Q ≤ 2 * P`, `P < Q`, and
`coneM P Q ≤ 3 * coneK P Q` (i.e., `1 / 2 ≤ P / Q < κ ≈ 0.55350`, where
`2 q^4 - 3 q^3 + 6 q = 3`, `1 / κ ≈ 1.80669`):

- `coneK P Q = Q^2 * (Q - P)^2`
- `coneM P Q = P^2 * (3 * Q^2 - 3 * P * Q + 2 * P^2)`
- `ratSum P Q g H = ∑_{j=0}^H Q^(H - j) * P^j * g j`

Main theorems proved unconditionally on actual `EndN`:
1. `rational_height_weighted_capacity`:
     `(3 * coneK P Q - coneM P Q) * ratAdditions P Q ≤ 3 * coneK P Q * ratFree P Q`
2. `rational_height_exp_bound`:
     `(3 * coneK P Q - coneM P Q) * P^h * levelAdditions(m + h) ≤ 3 * coneK P Q * Q^h * free`
3. `rational_low_weights_bound` (without any `1 / (3K - M)` prefactor blowup):
     `r ≤ m + d → P^d * Q^3 * (Q - P) * lowAdditionWeights(r) ≤ coneM P Q * Q^d * free`
4. `rational_arbitrary_target_free_gap_square` (no `hpos`, no height ceiling):
     `Fw(b + j) ≤ m + d + 1 → P^d * Q^3 * (Q - P) * (j + 1)^2 ≤ coneM P Q * Q^d * free`
5. Concrete instantiations narrowing the PROVED-LEAN actual-`EndN` exponential
   upper base from `2` (`E-785`) down to `20 / 11 ≈ 1.8182` and `199 / 110 ≈ 1.8091`
   (within `0.13%` of the exact 3-spacing cone root `1.8067`):
     - `actual_height_exp_twenty_elevenths`
     - `actual_height_exp_199_110`
     - `low_weights_exp_199_110`
-/

/-! ## Rational cone constants and weighted level sums -/

def coneK (P Q : Nat) : Nat :=
  Q * Q * (Q - P) * (Q - P)

def coneM (P Q : Nat) : Nat :=
  P * P * (3 * Q * Q + 2 * P * P - 3 * P * Q)

noncomputable def ratSum (P Q : Nat) (g : Nat → Nat) : Nat → Nat
  | 0 => g 0
  | H + 1 => Q * ratSum P Q g H + P ^ (H + 1) * g (H + 1)

noncomputable def ratAdditions (P Q : Nat) (f : Nat → Bool) (n K : Nat) (m : Int) (H : Nat) : Nat :=
  ratSum P Q (fun h => levelAdditions f n K (m + (h : Int))) H

noncomputable def ratSupplied (P Q : Nat) (f : Nat → Bool) (n K : Nat) (m : Int) (H : Nat) : Nat :=
  ratSum P Q (fun h => levelSupplied f n K (m + (h : Int))) H

noncomputable def ratFree (P Q : Nat) (f : Nat → Bool) (n K : Nat) (m : Int) (H : Nat) : Nat :=
  ratSum P Q (fun h => levelFree f n K (m + (h : Int))) H

/-! ## Local level sums and arithmetic helpers -/

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
    simp only [ratSum, levelSum, Nat.pow_succ, Nat.mul_add]
    have h1 : Q * ratSum P Q g H ≤ Q * (Q ^ H * levelSum g H) := Nat.mul_le_mul_left Q ih
    have h1' : Q * (Q ^ H * levelSum g H) = Q ^ H * Q * levelSum g H := by
      rw [Nat.mul_comm (Q ^ H) Q, Nat.mul_assoc]
    have h2 : P ^ (H + 1) * g (H + 1) ≤ Q ^ H * Q * g (H + 1) := by
      rw [← Nat.pow_succ]
      exact Nat.mul_le_mul_right (g (H + 1)) hpow
    rw [← h1']
    exact Nat.add_le_add h1 h2

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

/-! ## Exact polynomial telescoping identities for `(P, Q)` -/

private def coeffV (P Q : Nat) : Nat := P * Q * Q * (Q - P)
private def coeffU (P Q : Nat) : Nat := P * Q * Q * (4 * P - 2 * Q)
private def coeffA0 (P Q : Nat) : Nat := 2 * P * Q * (Q - P) * (Q - P)
private def coeffA1 (P Q : Nat) : Nat := P * (Q - P) * (Q - P) * (Q + 2 * P)

private theorem coneM_sub_le (P Q : Nat) (hPQ : P < Q) :
    3 * P * Q ≤ 3 * Q * Q + 2 * P * P := by
  have h1 : P * Q ≤ Q * Q := Nat.mul_le_mul_right Q (Nat.le_of_lt hPQ)
  have h2 : 3 * (P * Q) ≤ 3 * (Q * Q) := Nat.mul_le_mul_left 3 h1
  rw [← Nat.mul_assoc, ← Nat.mul_assoc] at h2
  omega

private theorem poly_base_ident (P Q a0 a1 : Nat) (hPQ : P < Q) (h2P : Q ≤ 2 * P) :
    P * (coeffV P Q * (3 * a0 + a1) + coeffU P Q * (a0 + a1) +
        coeffA1 P Q * a1 + coeffA0 P Q * a0) =
      coneM P Q * (Q * a0 + P * a1) := by
  have hsub := coneM_sub_le P Q hPQ
  unfold coeffV coeffU coeffA0 coeffA1 coneM
  have hInt :
      ((P * (P * Q * Q * (Q - P) * (3 * a0 + a1) +
          P * Q * Q * (4 * P - 2 * Q) * (a0 + a1) +
          P * (Q - P) * (Q - P) * (Q + 2 * P) * a1 +
          2 * P * Q * (Q - P) * (Q - P) * a0) : Nat) : Int) =
      ((P * P * (3 * Q * Q + 2 * P * P - 3 * P * Q) * (Q * a0 + P * a1) : Nat) : Int) := by
    have h1 : ((Q - P : Nat) : Int) = (Q : Int) - (P : Int) := Int.ofNat_sub (Nat.le_of_lt hPQ)
    have h2 : ((4 * P - 2 * Q : Nat) : Int) = 4 * (P : Int) - 2 * (Q : Int) := by
      have : 2 * Q ≤ 4 * P := by omega
      exact Int.ofNat_sub this
    have h3 : ((3 * Q * Q + 2 * P * P - 3 * P * Q : Nat) : Int) =
        3 * (Q : Int) * (Q : Int) + 2 * (P : Int) * (P : Int) - 3 * (P : Int) * (Q : Int) :=
      Int.ofNat_sub hsub
    push_cast [h1, h2, h3]
    grind
  omega

private theorem poly_step_ident (P Q pPow e2 vh uh a0 a1 a2 : Nat)
    (hPQ : P < Q) (h2P : Q ≤ 2 * P) (hb : 3 * e2 ≤ vh + 2 * a0) :
    3 * coneK P Q * (pPow * P * e2) +
      pPow * P * (coeffV P Q * (vh + 4 * uh + 3 * a1 + a2) +
        coeffU P Q * (uh + a1 + a2) + coeffA1 P Q * a2 + coeffA0 P Q * a1) ≤
      Q * (pPow * (coeffV P Q * (vh + 2 * uh + a1) +
        coeffU P Q * (uh + a1) + coeffA1 P Q * a1 + coeffA0 P Q * a0)) +
      coneM P Q * (pPow * P * a2) := by
  have hsub := coneM_sub_le P Q hPQ
  unfold coeffV coeffU coeffA0 coeffA1 coneK coneM
  have hdiff :
      ((Q * (pPow * (P * Q * Q * (Q - P) * (vh + 2 * uh + a1) +
          P * Q * Q * (4 * P - 2 * Q) * (uh + a1) +
          P * (Q - P) * (Q - P) * (Q + 2 * P) * a1 +
          2 * P * Q * (Q - P) * (Q - P) * a0)) +
        P * P * (3 * Q * Q + 2 * P * P - 3 * P * Q) * (pPow * P * a2) : Nat) : Int) -
      ((3 * (Q * Q * (Q - P) * (Q - P)) * (pPow * P * e2) +
        pPow * P * (P * Q * Q * (Q - P) * (vh + 4 * uh + 3 * a1 + a2) +
          P * Q * Q * (4 * P - 2 * Q) * (uh + a1 + a2) +
          P * (Q - P) * (Q - P) * (Q + 2 * P) * a2 +
          2 * P * Q * (Q - P) * (Q - P) * a1) : Nat) : Int) =
      (pPow : Int) * (P : Int) * ((Q * Q * (Q - P) * (Q - P) : Nat) : Int) *
        (((vh + 2 * a0 : Nat) : Int) - (3 * e2 : Nat)) := by
    push_cast
    rw [Int.ofNat_sub (Nat.le_of_lt hPQ), Int.ofNat_sub (show 2 * Q ≤ 4 * P by omega),
      Int.ofNat_sub hsub]
    push_cast
    grind
  have hnn : 0 ≤ (pPow : Int) * (P : Int) * ((Q * Q * (Q - P) * (Q - P) : Nat) : Int) *
      (((vh + 2 * a0 : Nat) : Int) - (3 * e2 : Nat)) := by
    have hA : 0 ≤ (pPow : Int) * (P : Int) * ((Q * Q * (Q - P) * (Q - P) : Nat) : Int) := by
      exact Int.mul_nonneg (Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
        (Int.natCast_nonneg _)
    have hB : 0 ≤ (((vh + 2 * a0 : Nat) : Int) - (3 * e2 : Nat)) := by omega
    exact Int.mul_nonneg hA hB
  exact Int.ofNat_le.mp (by omega)

private theorem poly_d1_bound (P Q : Nat) (hPQ : P < Q) (h2P : Q ≤ 2 * P) :
    P * Q ^ 3 * (Q - P) ≤ coneM P Q * Q := by
  have hsub := coneM_sub_le P Q hPQ
  unfold coneM
  have hq3 : Q ^ 3 = Q * Q * Q := by rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_one]
  rw [hq3]
  have hdiff : ((P * P * (3 * Q * Q + 2 * P * P - 3 * P * Q) * Q : Nat) : Int) -
      ((P * (Q * Q * Q) * (Q - P) : Nat) : Int) =
      (P : Int) * (Q : Int) *
        ((4 * (P : Int) - 2 * (Q : Int)) * (Q : Int) * (Q : Int) +
          ((Q : Int) - (P : Int)) * ((Q : Int) - (P : Int)) * ((Q : Int) + 2 * (P : Int))) := by
    push_cast
    rw [Int.ofNat_sub (Nat.le_of_lt hPQ), Int.ofNat_sub hsub]
    push_cast
    grind
  have ht1 : 0 ≤ (4 * (P : Int) - 2 * (Q : Int)) * (Q : Int) * (Q : Int) :=
    Int.mul_nonneg (Int.mul_nonneg (by omega) (Int.natCast_nonneg _)) (Int.natCast_nonneg _)
  have ht2 : 0 ≤ ((Q : Int) - (P : Int)) * ((Q : Int) - (P : Int)) * ((Q : Int) + 2 * (P : Int)) :=
    Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega)
  have hnn : 0 ≤ (P : Int) * (Q : Int) *
      ((4 * (P : Int) - 2 * (Q : Int)) * (Q : Int) * (Q : Int) +
        ((Q : Int) - (P : Int)) * ((Q : Int) - (P : Int)) * ((Q : Int) + 2 * (P : Int))) :=
    Int.mul_nonneg (Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)) (by omega)
  exact Int.ofNat_le.mp (by omega)

private theorem rational_supplied_invariant (P Q : Nat) (hPQ : P < Q) (h2P : Q ≤ 2 * P)
    (f : Nat → Bool) (n a K : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    ∀ H, 3 * coneK P Q * ratSupplied P Q f n K m (H + 1) +
        P ^ (H + 1) * (
          coeffV P Q * levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1) +
          coeffU P Q * levelSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1) +
          coeffA1 P Q * levelAdditions f n K (m + ((H + 1 : Nat) : Int)) +
          coeffA0 P Q * levelAdditions f n K (m + (H : Int))) ≤
      coneM P Q * ratAdditions P Q f n K m (H + 1) := by
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
    simp only [ratSupplied, ratAdditions, ratSum, levelWeightSum, levelSum, Nat.reduceAdd, Nat.pow_one]
    rw [hE0, hE1]
    have hbase := poly_base_ident P Q (levelAdditions f n K (m + ((0 : Nat) : Int)))
      (levelAdditions f n K (m + ((1 : Nat) : Int))) hPQ h2P
    have h0 : levelAdditions f n K (m + ((0 : Nat) : Int)) +
        2 * levelAdditions f n K (m + ((0 : Nat) : Int)) +
        levelAdditions f n K (m + ((1 : Nat) : Int)) =
        3 * levelAdditions f n K (m + ((0 : Nat) : Int)) +
        levelAdditions f n K (m + ((1 : Nat) : Int)) := by omega
    rw [h0]
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
    have hQih := Nat.mul_le_mul_left Q ih
    have hstep := poly_step_ident P Q (P ^ (H + 1))
      (levelSupplied f n K (m + ((H + 1 + 1 : Nat) : Int)))
      (levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) H)
      (levelSum (fun j => levelAdditions f n K (m + (j : Int))) H)
      (levelAdditions f n K (m + (H : Int)))
      (levelAdditions f n K (m + ((H + 1 : Nat) : Int)))
      (levelAdditions f n K (m + ((H + 1 + 1 : Nat) : Int)))
      hPQ h2P hbNat
    have hRsup : ratSupplied P Q f n K m (H + 1 + 1) =
        Q * ratSupplied P Q f n K m (H + 1) +
          P ^ (H + 1) * P * levelSupplied f n K (m + ((H + 1 + 1 : Nat) : Int)) := by
      unfold ratSupplied
      rw [ratSum, Nat.pow_succ]
    have hRadd : ratAdditions P Q f n K m (H + 1 + 1) =
        Q * ratAdditions P Q f n K m (H + 1) +
          P ^ (H + 1) * P * levelAdditions f n K (m + ((H + 1 + 1 : Nat) : Int)) := by
      unfold ratAdditions
      rw [ratSum, Nat.pow_succ]
    have hPpow : P ^ (H + 1 + 1) = P ^ (H + 1) * P := Nat.pow_succ P (H + 1)
    have hV2 : levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1 + 1) =
        levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) H +
          4 * levelSum (fun j => levelAdditions f n K (m + (j : Int))) H +
          3 * levelAdditions f n K (m + ((H + 1 : Nat) : Int)) +
          levelAdditions f n K (m + ((H + 1 + 1 : Nat) : Int)) := by
      simp only [levelWeightSum, levelSum]
      omega
    have hV1 : levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1) =
        levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) H +
          2 * levelSum (fun j => levelAdditions f n K (m + (j : Int))) H +
          levelAdditions f n K (m + ((H + 1 : Nat) : Int)) := rfl
    have hU2 : levelSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1 + 1) =
        levelSum (fun j => levelAdditions f n K (m + (j : Int))) H +
          levelAdditions f n K (m + ((H + 1 : Nat) : Int)) +
          levelAdditions f n K (m + ((H + 1 + 1 : Nat) : Int)) := rfl
    have hU1 : levelSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1) =
        levelSum (fun j => levelAdditions f n K (m + (j : Int))) H +
          levelAdditions f n K (m + ((H + 1 : Nat) : Int)) := rfl
    rw [hRsup, hRadd, hPpow, hV2, hU2]
    rw [hV1, hU1] at hQih
    rw [Nat.mul_add Q, ← Nat.mul_assoc Q (3 * coneK P Q), Nat.mul_comm Q (3 * coneK P Q),
      Nat.mul_assoc (3 * coneK P Q), ← Nat.mul_assoc Q (coneM P Q), Nat.mul_comm Q (coneM P Q),
      Nat.mul_assoc (coneM P Q)] at hQih
    rw [Nat.mul_add (3 * coneK P Q), Nat.mul_add (coneM P Q)]
    omega

/-! ## General rational 3-spacing capacity and exponential bounds -/

/-- Uniform rational height-weighted capacity on actual `EndN` for EVERY rational
`P / Q` in the 3-spacing cone (`1/2 ≤ P / Q < κ ≈ 0.55350`, `coneM P Q ≤ 3 * coneK P Q`). -/
theorem rational_height_weighted_capacity (P Q : Nat) (hPQ : P < Q) (h2P : Q ≤ 2 * P)
    (hcone : coneM P Q ≤ 3 * coneK P Q)
    (f : Nat → Bool) (n a K H : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    (3 * coneK P Q - coneM P Q) * ratAdditions P Q f n K m H ≤
      3 * coneK P Q * ratFree P Q f n K m H := by
  have hsplit := rat_additions_split P Q f n K m H
  cases H with
  | zero =>
    have hE0 : levelSupplied f n K (m + ((0 : Nat) : Int)) = 0 := by
      apply cN_zero_of
      intro t hnt htK ht
      exact block_prefix_low_clock_not_endable f n a t hw hpre hnt m
        (fun i hi hj => hfloor i hi (by omega)) (by omega) ht.2
    have hz : ratSupplied P Q f n K m 0 = 0 := hE0
    rw [hz, Nat.add_zero] at hsplit
    rw [hsplit]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  | succ H =>
    have hinv := rational_supplied_invariant P Q hPQ h2P f n a K m hw hpre hfloor H
    have h1 : 3 * coneK P Q * ratSupplied P Q f n K m (H + 1) ≤
        coneM P Q * ratAdditions P Q f n K m (H + 1) := by omega
    have h2 : (3 * coneK P Q - coneM P Q) * ratAdditions P Q f n K m (H + 1) +
        coneM P Q * ratAdditions P Q f n K m (H + 1) =
        3 * coneK P Q * ratAdditions P Q f n K m (H + 1) := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hcone]
    have h3 : 3 * coneK P Q * ratAdditions P Q f n K m (H + 1) =
        3 * coneK P Q * ratFree P Q f n K m (H + 1) +
        3 * coneK P Q * ratSupplied P Q f n K m (H + 1) := by
      rw [hsplit, Nat.mul_add]
    omega

/-- Unweighted exponential actual-`EndN` level bound for EVERY rational `P / Q`
in the 3-spacing cone: `(3K - M) * P^h * A_{m+h} ≤ 3K * Q^h * free`. -/
theorem rational_height_exp_bound (P Q : Nat) (hPQ : P < Q) (h2P : Q ≤ 2 * P)
    (hcone : coneM P Q ≤ 3 * coneK P Q)
    (f : Nat → Bool) (n a K h : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    (3 * coneK P Q - coneM P Q) * P ^ h * levelAdditions f n K (m + (h : Int)) ≤
      3 * coneK P Q * Q ^ h * free f n K := by
  have hcap := rational_height_weighted_capacity P Q hPQ h2P hcone f n a K h m hw hpre hfloor
  have hlast : P ^ h * levelAdditions f n K (m + (h : Int)) ≤ ratAdditions P Q f n K m h :=
    ratSum_last_le P Q (fun j => levelAdditions f n K (m + (j : Int))) h
  have hrat : ratFree P Q f n K m h ≤
      Q ^ h * levelSum (fun j => levelFree f n K (m + (j : Int))) h :=
    ratSum_le_pow_mul_sum P Q (Nat.le_of_lt hPQ) (fun j => levelFree f n K (m + (j : Int))) h
  have hls := levelSum_free_le_free f n K m h
  have hL : (3 * coneK P Q - coneM P Q) * (P ^ h * levelAdditions f n K (m + (h : Int))) ≤
      (3 * coneK P Q - coneM P Q) * ratAdditions P Q f n K m h :=
    Nat.mul_le_mul_left _ hlast
  have hR : 3 * coneK P Q * ratFree P Q f n K m h ≤ 3 * coneK P Q * (Q ^ h * free f n K) :=
    Nat.mul_le_mul_left _ (Nat.le_trans hrat (Nat.mul_le_mul_left _ hls))
  rw [Nat.mul_assoc (3 * coneK P Q - coneM P Q), Nat.mul_assoc (3 * coneK P Q)]
  exact Nat.le_trans hL (Nat.le_trans hcap hR)

/-- Arbitrary-depth low-addition weight bound across the entire 3-spacing cone,
WITHOUT any `1 / (3K - M)` prefactor blowup: for every `d : Nat` and `r ≤ m + d`,
`P^d * Q^3 * (Q - P) * lowAdditionWeights f n r K ≤ coneM P Q * Q^d * free f n K`. -/
theorem rational_low_weights_bound (P Q : Nat) (hPQ : P < Q) (h2P : Q ≤ 2 * P)
    (hcone : coneM P Q ≤ 3 * coneK P Q)
    (f : Nat → Bool) (n a K d : Nat) (m r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) (hr : r ≤ m + (d : Int)) :
    ((P ^ d * Q ^ 3 * (Q - P) : Nat) : Int) * lowAdditionWeights f n r K ≤
      ((coneM P Q * Q ^ d : Nat) : Int) * (free f n K : Int) := by
  cases d with
  | zero =>
    have hz := lowAdditionWeights_zero_le_floor f n m r (by omega) K hfloor
    rw [hz, Int.mul_zero]
    exact Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  | succ d' =>
    cases d' with
    | zero =>
      have hmono := lowAdditionWeights_mono_r f n r (m + ((0 : Nat) : Int) + 1) (by omega) K
      have hW0 := lowAdditionWeights_eq_levelWeightSum f n K m hfloor 0
      have hE0 : levelSupplied f n K (m + ((0 : Nat) : Int)) = 0 := by
        apply cN_zero_of
        intro t hnt htK ht
        exact block_prefix_low_clock_not_endable f n a t hw hpre hnt m
          (fun i hi hj => hfloor i hi (by omega)) (by omega) ht.2
      have hsp := level_additions_split f n K (m + ((0 : Nat) : Int))
      have hls := levelSum_free_le_free f n K m 0
      simp only [levelWeightSum, levelSum] at hW0 hls
      have hWle : lowAdditionWeights f n r K ≤ (free f n K : Int) := by omega
      have hcoef := poly_d1_bound P Q hPQ h2P
      have hnat : P ^ 1 * Q ^ 3 * (Q - P) * free f n K ≤ coneM P Q * Q ^ 1 * free f n K := by
        simp only [Nat.pow_one]
        exact Nat.mul_le_mul_right (free f n K) hcoef
      have h1 : ((P ^ 1 * Q ^ 3 * (Q - P) : Nat) : Int) * lowAdditionWeights f n r K ≤
          ((P ^ 1 * Q ^ 3 * (Q - P) : Nat) : Int) * (free f n K : Int) :=
        Int.mul_le_mul_of_nonneg_left hWle (Int.natCast_nonneg _)
      have h2 : ((P ^ 1 * Q ^ 3 * (Q - P) : Nat) : Int) * (free f n K : Int) ≤
          ((coneM P Q * Q ^ 1 : Nat) : Int) * (free f n K : Int) := by
        exact_mod_cast hnat
      exact Int.le_trans h1 h2
    | succ H =>
      have hmono := lowAdditionWeights_mono_r f n r (m + ((H + 1 : Nat) : Int) + 1) (by omega) K
      have hW := lowAdditionWeights_eq_levelWeightSum f n K m hfloor (H + 1)
      have hinv := rational_supplied_invariant P Q hPQ h2P f n a K m hw hpre hfloor H
      have hsplit := rat_additions_split P Q f n K m (H + 1)
      have hMsup : coneM P Q * ratSupplied P Q f n K m (H + 1) ≤
          3 * coneK P Q * ratSupplied P Q f n K m (H + 1) :=
        Nat.mul_le_mul_right _ hcone
      have hRHS : coneM P Q * ratAdditions P Q f n K m (H + 1) =
          coneM P Q * ratFree P Q f n K m (H + 1) + coneM P Q * ratSupplied P Q f n K m (H + 1) := by
        rw [hsplit, Nat.mul_add]
      have hVle : P ^ (H + 1) * (coeffV P Q *
          levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1)) ≤
          coneM P Q * ratFree P Q f n K m (H + 1) := by
        have hdrop : P ^ (H + 1) * (coeffV P Q *
            levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1)) ≤
            P ^ (H + 1) * (
              coeffV P Q * levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1) +
              coeffU P Q * levelSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1) +
              coeffA1 P Q * levelAdditions f n K (m + ((H + 1 : Nat) : Int)) +
              coeffA0 P Q * levelAdditions f n K (m + (H : Int))) :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      have hrat := ratSum_le_pow_mul_sum P Q (Nat.le_of_lt hPQ)
        (fun j => levelFree f n K (m + (j : Int))) (H + 1)
      have hls := levelSum_free_le_free f n K m (H + 1)
      have hF : coneM P Q * ratFree P Q f n K m (H + 1) ≤
          coneM P Q * (Q ^ (H + 1) * free f n K) :=
        Nat.mul_le_mul_left _ (Nat.le_trans hrat (Nat.mul_le_mul_left _ hls))
      have hQmul := Nat.mul_le_mul_left Q (Nat.le_trans hVle hF)
      have hL_eq : Q * (P ^ (H + 1) * (coeffV P Q *
          levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1))) =
          P ^ (H + 2) * Q ^ 3 * (Q - P) *
            levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1) := by
        unfold coeffV
        rw [show H + 2 = (H + 1) + 1 by omega, Nat.pow_succ]
        have hq3 : Q ^ 3 = Q * Q * Q := by rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_one]
        rw [hq3]
        grind
      have hR_eq : Q * (coneM P Q * (Q ^ (H + 1) * free f n K)) =
          coneM P Q * Q ^ (H + 2) * free f n K := by
        rw [show H + 2 = (H + 1) + 1 by omega, Nat.pow_succ]
        grind
      rw [hL_eq, hR_eq] at hQmul
      have hcast : ((P ^ (H + 2) * Q ^ 3 * (Q - P) : Nat) : Int) *
          (levelWeightSum (fun j => levelAdditions f n K (m + (j : Int))) (H + 1) : Int) ≤
          ((coneM P Q * Q ^ (H + 2) : Nat) : Int) * (free f n K : Int) := by
        exact_mod_cast hQmul
      have h1 : ((P ^ (H + 2) * Q ^ 3 * (Q - P) : Nat) : Int) * lowAdditionWeights f n r K ≤
          ((P ^ (H + 2) * Q ^ 3 * (Q - P) : Nat) : Int) *
            lowAdditionWeights f n (m + ((H + 1 : Nat) : Int) + 1) K :=
        Int.mul_le_mul_of_nonneg_left hmono (Int.natCast_nonneg _)
      rw [hW] at h1
      exact Int.le_trans h1 hcast

/-- Arbitrary-height free-gap square inequality across the entire 3-spacing cone,
WITHOUT `hpos` and WITHOUT any upper ceiling on intermediate heights. -/
theorem rational_arbitrary_target_free_gap_square (P Q : Nat) (hPQ : P < Q) (h2P : Q ≤ 2 * P)
    (hcone : coneM P Q ≤ 3 * coneK P Q)
    (f : Nat → Bool) (n a b j d : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hnb : n < b) (hfloor : ∀ i, n ≤ i → i ≤ b → m ≤ Fw f i)
    (hS : ∀ i, b ≤ i → i < b + j → f i = false) (he : EndN f 0 (b + j))
    (hTarget : Fw f (b + j) ≤ m + (d : Int) + 1) :
    ((P ^ d * Q ^ 3 * (Q - P) : Nat) : Int) * ((j : Int) + 1) ^ 2 ≤
      ((coneM P Q * Q ^ d : Nat) : Int) * (free f n (b - n) : Int) := by
  have hs := supplied_gap_square_low_additions f n a b j hw hpre hnb hS he
  have hl := rational_low_weights_bound P Q hPQ h2P hcone f n a (b - n) d m (Fw f (b + j) - 1)
    hw hpre (fun i hi hj => hfloor i hi (by omega)) (by omega)
  have h1 := Int.mul_le_mul_of_nonneg_left hs (Int.natCast_nonneg (P ^ d * Q ^ 3 * (Q - P)))
  exact Int.le_trans h1 hl

/-! ## Concrete sharp instantiations narrowing `[5/3, 2]` to `[5/3, 199/110]` -/

/-- Concrete `q = 11 / 20` (`base = 20 / 11 ≈ 1.8182`) actual-`EndN` exponential bound:
`1289 * 11^h * levelAdditions(m + h) ≤ 48600 * 20^h * free`. -/
theorem actual_height_exp_twenty_elevenths (f : Nat → Bool) (n a K h : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    1289 * 11 ^ h * levelAdditions f n K (m + (h : Int)) ≤ 48600 * 20 ^ h * free f n K := by
  have hb := rational_height_exp_bound 11 20 (by omega) (by omega) (by decide) f n a K h m
    hw hpre hfloor
  have hc1 : 3 * coneK 11 20 - coneM 11 20 = 2 * 1289 := by decide
  have hc2 : 3 * coneK 11 20 = 2 * 48600 := by decide
  rw [hc1, hc2] at hb
  have hL : 2 * (1289 * 11 ^ h * levelAdditions f n K (m + (h : Int))) =
      2 * 1289 * 11 ^ h * levelAdditions f n K (m + (h : Int)) := by
    rw [Nat.mul_assoc 2, Nat.mul_assoc 2]
  have hR : 2 * (48600 * 20 ^ h * free f n K) = 2 * 48600 * 20 ^ h * free f n K := by
    rw [Nat.mul_assoc 2, Nat.mul_assoc 2]
  omega

/-- Concrete `q = 110 / 199` (`base = 199 / 110 ≈ 1.8091`, within `0.13%` of the
exact 3-spacing cone root `1.8067`) actual-`EndN` exponential bound. -/
theorem actual_height_exp_199_110 (f : Nat → Bool) (n a K h : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    5309263 * 110 ^ h * levelAdditions f n K (m + (h : Int)) ≤
      941038563 * 199 ^ h * free f n K := by
  have hb := rational_height_exp_bound 110 199 (by omega) (by omega) (by decide) f n a K h m
    hw hpre hfloor
  have hc1 : 3 * coneK 110 199 - coneM 110 199 = 5309263 := by decide
  have hc2 : 3 * coneK 110 199 = 941038563 := by decide
  rwa [hc1, hc2] at hb

/-- Concrete `q = 110 / 199` (`base = 199 / 110 ≈ 1.8091`) arbitrary-depth low-addition
weight bound (`W_d ≤ 1.3341 * (199/110)^d * free`), strictly improving `E-787`'s `2^d`
for all `d ≥ 3`. -/
theorem low_weights_exp_199_110 (f : Nat → Bool) (n a K d : Nat) (m r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) (hr : r ≤ m + (d : Int)) :
    ((110 ^ d * 701373311 : Nat) : Int) * lowAdditionWeights f n r K ≤
      ((935729300 * 199 ^ d : Nat) : Int) * (free f n K : Int) := by
  have hb := rational_low_weights_bound 110 199 (by omega) (by omega) (by decide) f n a K d m r
    hw hpre hfloor hr
  have hc1 : 199 ^ 3 * (199 - 110) = 701373311 := by decide
  have hc2 : coneM 110 199 = 935729300 := by decide
  have hL : 110 ^ d * 199 ^ 3 * (199 - 110) = 110 ^ d * 701373311 := by
    rw [Nat.mul_assoc, hc1]
  rwa [hL, hc2] at hb

end Recaman.SharpThreeSpacingCapacity
