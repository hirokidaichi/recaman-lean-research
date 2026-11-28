import Recaman.ExactFiveThirdsCapacity
import Recaman.ExcursionClimbSpacing
import Recaman.ArbitraryDepthFreeGap

namespace Recaman.HeightConvolutionCapacity

open Recaman.ExactFiveThirdsCapacity Recaman.ExcursionClimbSpacing
open Recaman.ArbitraryDepthFreeGap Recaman.SharpThreeSpacingCapacity
open Recaman.SupplyExcursionSpacing Recaman.SupplyHeightWeightBudget
open Recaman.FloorSupplyPotential Recaman.FloorSupplyFreeBudget Recaman.LowTargetWeightedGap
open Recaman.GapSquareLowAdditions Recaman.LevelTriangleArea Recaman.AdditionRankSlack
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality
open Recaman.CapacityEqualityInduction Recaman.SuffixHallOwnerMap
open Classical

/-! # Exponentially-decaying height convolution capacity, sharp `18/25` strip bound, and `D = 7, 8` compression (`E-800`)

Strengthens `E-797` (`Recaman/ExactFiveThirdsCapacity.lean`) and `E-787` (`Recaman/ArbitraryDepthFreeGap.lean`)
unconditionally on actual `EndN` supply across all padded `BlockWord` prefixes and all excursion depths:

1. **Exact exponentially-decaying free convolution kernel (`convFree2`)**:
   `5 * 3^(H + 2) * triAdditionsH f n K m (H + 1) ≤ convFree2 (levelFree) H`,
   where free additions at relative height `m + h` decay exponentially as `(3/5)^h` and free additions
   strictly above `m + H + 1` carry weight `0`.
2. **Quantitative `LOW-free` vs `HIGH-free` exponential separation**:
   for every cutoff `1 ≤ s ≤ H + 1`,
   `5 * 3^(H + 2) * triAdditionsH(H + 1) ≤ 135 * 5^H * lowFree(s) + 28 * 3^s * 5^(H + 1 - s) * highFree(s)`.
3. **Zero-remainder strip identity and sharp `18/25 * (5/3)^H` global strip capacity**:
   combining `2 * triSumH g (H + 1) + 3 * g (H + 2) + g (H + 1) = 3 * levelSumH g (H + 2) + levelWeightSumH g H`
   with the `δ = 3` (6-slot) convolution invariant `convFree3` yields
   `25 * 3^H * additions f n K ≤ 18 * 5^H * free f n K` for every `H ≥ 1` on every strip `[m, m + H]`,
   slashing `E-797`'s constant from `9/5 = 1.80` to `18/25 = 0.72` (within `9/5 = 1.80×` of `E-786`'s
   `(2/5) * (5/3)^H` lower bound for every `H ≥ 1`).
4. **Zero-remainder weight identity and sharp `1008/625 * (5/3)^d` arbitrary-depth `W(m + d)` & free-gap bounds**:
   from `8 * triSumH g (H + 1) + 3 * g (H + 2) + g (H + 1) = 3 * levelWeightSumH g (H + 2) + levelWeightSumH g H`,
   `(625 * 3^d) * lowAdditionWeights f n r K ≤ (1008 * 5^d) * free f n K` (`1.6128 * (5/3)^d` vs
   `E-797`'s `2.16 * (5/3)^d`) and `(625 * 3^d) * (j + 1)^2 ≤ (1008 * 5^d) * free` for all `d : Nat`.
5. **Sharp finite-depth `D = 7` and `D = 8` compressions**:
   - `3 * lowAdditionWeights f n r K ≤ 56 * free` (`r ≤ m + 5`, beating `E-787`'s `59 * free`) and
     `D = 7` counterexample profile `4 ≤ free ≤ j ≤ 16` (eliminating `j = 17`),
   - `lowAdditionWeights f n r K ≤ 32 * free` (`r ≤ m + 6`, using `δ = 5` 8-slot budget) and
     `D = 8` counterexample profile `4 ≤ free ≤ j ≤ 29` (cutting `E-787`'s `j ≤ 61` in half).
-/

/-! ## Transparent sum definitions and exact zero-remainder algebraic identities -/

/-- Level prefix sum `∑_{j=0}^H g j`. -/
def levelSumH (g : Nat → Nat) : Nat → Nat
  | 0 => g 0
  | H + 1 => levelSumH g H + g (H + 1)

/-- Low-addition weight sum `∑_{j=0}^H (2*(H - j) + 1) * g j`. -/
def levelWeightSumH (g : Nat → Nat) : Nat → Nat
  | 0 => g 0
  | H + 1 => levelWeightSumH g H + 2 * levelSumH g H + g (H + 1)

/-- Triangular level sum `∑_{j=0}^H (H - j + 1) * g j`. -/
def triSumH (g : Nat → Nat) : Nat → Nat
  | 0 => g 0
  | H + 1 => triSumH g H + levelSumH g (H + 1)

/-- Triangular height-weighted sum of additions above floor `m` up to `m + H`. -/
noncomputable def triAdditionsH (f : Nat → Bool) (n K : Nat) (m : Int) (H : Nat) : Nat :=
  triSumH (fun h => levelAdditions f n K (m + (h : Int))) H

/-- Tail sum `∑_{j=s}^H g j` (`0` when `H < s`). -/
def tailSumH (g : Nat → Nat) (s : Nat) : Nat → Nat
  | 0 => if s = 0 then g 0 else 0
  | H + 1 => tailSumH g s H + if s ≤ H + 1 then g (H + 1) else 0

/-- Exact `δ = 2` exponentially-decaying free convolution sum (sharper `H = 1` base via `E-792`). -/
def convFree2 (F : Nat → Nat) : Nat → Nat
  | 0 => 135 * F 0 + 84 * F 1
  | 1 => 630 * F 0 + 405 * F 1 + 252 * F 2
  | H + 2 => 5 * convFree2 F (H + 1) + 28 * 3 ^ (H + 3) * F (H + 3)

/-- Exact `δ = 3` exponentially-decaying free convolution sum (for the `18/25` strip bound). -/
def convFree3 (F : Nat → Nat) : Nat → Nat
  | 0 => 162 * F 0 + 99 * F 1
  | 1 => 675 * F 0 + 486 * F 1 + 297 * F 2
  | H + 2 => 5 * convFree3 F (H + 1) + 33 * 3 ^ (H + 3) * F (H + 3)

private theorem levelSumH_1 (g : Nat → Nat) : levelSumH g 1 = g 0 + g 1 := rfl
private theorem levelSumH_2 (g : Nat → Nat) : levelSumH g 2 = g 0 + g 1 + g 2 := rfl
private theorem levelSumH_3 (g : Nat → Nat) : levelSumH g 3 = g 0 + g 1 + g 2 + g 3 := rfl
private theorem levelSumH_4 (g : Nat → Nat) : levelSumH g 4 = g 0 + g 1 + g 2 + g 3 + g 4 := rfl
private theorem levelSumH_5 (g : Nat → Nat) :
    levelSumH g 5 = g 0 + g 1 + g 2 + g 3 + g 4 + g 5 := rfl

private theorem levelWeightSumH_0 (g : Nat → Nat) : levelWeightSumH g 0 = g 0 := rfl
private theorem levelWeightSumH_1 (g : Nat → Nat) :
    levelWeightSumH g 1 = 3 * g 0 + g 1 := by
  change g 0 + 2 * g 0 + g 1 = _; omega
private theorem levelWeightSumH_2 (g : Nat → Nat) :
    levelWeightSumH g 2 = 5 * g 0 + 3 * g 1 + g 2 := by
  change levelWeightSumH g 1 + 2 * levelSumH g 1 + g 2 = _
  rw [levelWeightSumH_1, levelSumH_1]; omega
private theorem levelWeightSumH_3 (g : Nat → Nat) :
    levelWeightSumH g 3 = 7 * g 0 + 5 * g 1 + 3 * g 2 + g 3 := by
  change levelWeightSumH g 2 + 2 * levelSumH g 2 + g 3 = _
  rw [levelWeightSumH_2, levelSumH_2]; omega
private theorem levelWeightSumH_4 (g : Nat → Nat) :
    levelWeightSumH g 4 = 9 * g 0 + 7 * g 1 + 5 * g 2 + 3 * g 3 + g 4 := by
  change levelWeightSumH g 3 + 2 * levelSumH g 3 + g 4 = _
  rw [levelWeightSumH_3, levelSumH_3]; omega
private theorem levelWeightSumH_5 (g : Nat → Nat) :
    levelWeightSumH g 5 = 11 * g 0 + 9 * g 1 + 7 * g 2 + 5 * g 3 + 3 * g 4 + g 5 := by
  change levelWeightSumH g 4 + 2 * levelSumH g 4 + g 5 = _
  rw [levelWeightSumH_4, levelSumH_4]; omega

private theorem triSumH_1 (g : Nat → Nat) : triSumH g 1 = 2 * g 0 + g 1 := by
  change g 0 + levelSumH g 1 = _; rw [levelSumH_1]; omega
private theorem triSumH_2 (g : Nat → Nat) : triSumH g 2 = 3 * g 0 + 2 * g 1 + g 2 := by
  change triSumH g 1 + levelSumH g 2 = _; rw [triSumH_1, levelSumH_2]; omega

private theorem levelWeightSumH_add_levelSumH (g : Nat → Nat) :
    ∀ H, levelWeightSumH g H + levelSumH g H = 2 * triSumH g H
  | 0 => by simp [levelWeightSumH, levelSumH, triSumH]; omega
  | H + 1 => by
    have ih := levelWeightSumH_add_levelSumH g H
    simp only [levelWeightSumH, levelSumH, triSumH] at ih ⊢
    omega

private theorem triSumH_five_thirds_step (g : Nat → Nat) (H : Nat) :
    5 * triSumH g (H + 1) + 3 * g (H + 2) + g (H + 1) =
      3 * triSumH g (H + 2) + levelWeightSumH g H := by
  have hWS := levelWeightSumH_add_levelSumH g H
  have h2 : H + 2 = (H + 1) + 1 := by omega
  rw [h2]
  simp only [triSumH, levelSumH]
  omega

/-- Exact zero-remainder strip identity:
  `2 * triSumH g (H + 1) + 3 * g (H + 2) + g (H + 1) = 3 * levelSumH g (H + 2) + levelWeightSumH g H`. -/
private theorem triSumH_strip_ident (g : Nat → Nat) (H : Nat) :
    2 * triSumH g (H + 1) + 3 * g (H + 2) + g (H + 1) =
      3 * levelSumH g (H + 2) + levelWeightSumH g H := by
  have hWS := levelWeightSumH_add_levelSumH g H
  have h2 : H + 2 = (H + 1) + 1 := by omega
  rw [h2]
  simp only [triSumH, levelSumH]
  omega

/-- Exact zero-remainder weight identity:
  `8 * triSumH g (H + 1) + 3 * g (H + 2) + g (H + 1) = 3 * levelWeightSumH g (H + 2) + levelWeightSumH g H`. -/
private theorem triSumH_weight_ident (g : Nat → Nat) (H : Nat) :
    8 * triSumH g (H + 1) + 3 * g (H + 2) + g (H + 1) =
      3 * levelWeightSumH g (H + 2) + levelWeightSumH g H := by
  have hWS := levelWeightSumH_add_levelSumH g H
  have h2 : H + 2 = (H + 1) + 1 := by omega
  rw [h2]
  simp only [triSumH, levelWeightSumH, levelSumH]
  omega

/-! ## Counting helpers bridging `lowAdditionWeights`, `additions`, and `free` -/

private theorem cN_split_prop_h (P Q : Nat → Prop) (n : Nat) :
    ∀ K, cN P n K = cN (fun t => P t ∧ Q t) n K + cN (fun t => P t ∧ ¬ Q t) n K
  | 0 => rfl
  | K + 1 => by
    have ih := cN_split_prop_h P Q n K
    by_cases hP : P (n + K)
    · by_cases hQ : Q (n + K)
      · rw [cN_succ_pos P n K hP, cN_succ_pos _ n K ⟨hP, hQ⟩,
          cN_succ_neg _ n K (fun h => h.2 hQ)]; omega
      · rw [cN_succ_pos P n K hP, cN_succ_neg _ n K (fun h => hQ h.2),
          cN_succ_pos _ n K ⟨hP, hQ⟩]; omega
    · rw [cN_succ_neg P n K hP, cN_succ_neg _ n K (fun h => hP h.1),
        cN_succ_neg _ n K (fun h => hP h.1)]; omega

private theorem level_additions_split_h (f : Nat → Bool) (n K : Nat) (h : Int) :
    levelAdditions f n K h = levelSupplied f n K h + levelFree f n K h := by
  unfold levelAdditions levelSupplied levelFree
  have hpart := cN_split_prop_h (fun t => Fw f t = h ∧ f t = true) (EndN f 0) n K
  have h1 : cN (fun t => (Fw f t = h ∧ f t = true) ∧ EndN f 0 t) n K =
      cN (fun t => Fw f t = h ∧ EndN f 0 t) n K := by
    apply cN_congr
    intro t _ _
    constructor
    · intro ht; exact ⟨ht.1.1, ht.2⟩
    · intro ht; exact ⟨⟨ht.1, ht.2.1⟩, ht.2⟩
  have h2 : cN (fun t => (Fw f t = h ∧ f t = true) ∧ ¬ EndN f 0 t) n K =
      cN (fun t => Fw f t = h ∧ f t = true ∧ ¬ EndN f 0 t) n K := by
    apply cN_congr
    intro t _ _
    exact ⟨fun ht => ⟨ht.1.1, ht.1.2, ht.2⟩, fun ht => ⟨⟨ht.1, ht.2.1⟩, ht.2.2⟩⟩
  rw [h1, h2] at hpart
  exact hpart

private theorem doubleAscent_le_additions_h (f : Nat → Bool) (n K : Nat) (h : Int) :
    doubleAscent f n K h ≤ levelAdditions f n K h := by
  unfold doubleAscent levelAdditions
  exact cN_mono _ _ n K (fun _ _ _ ht => ⟨ht.1, ht.2.1⟩)

private theorem doubleAscent_le_supplied_add_free_h (f : Nat → Bool) (n K : Nat) (h : Int) :
    doubleAscent f n K h ≤ suppliedDoubleAscent f n K h + levelFree f n K h := by
  have hsp := cN_split_prop_h
    (fun t => Fw f t = h ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < n + K) (EndN f 0) n K
  have h1 : cN (fun t => (Fw f t = h ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < n + K) ∧
      EndN f 0 t) n K = suppliedDoubleAscent f n K h := by
    unfold suppliedDoubleAscent
    apply cN_congr
    intro t _ _
    exact ⟨fun ht => ⟨ht.1.1, ht.2, ht.1.2.2.1, ht.1.2.2.2⟩,
      fun ht => ⟨⟨ht.1, ht.2.1.1, ht.2.2.1, ht.2.2.2⟩, ht.2.1⟩⟩
  have h2 : cN (fun t => (Fw f t = h ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < n + K) ∧
      ¬ EndN f 0 t) n K ≤ levelFree f n K h := by
    unfold levelFree
    exact cN_mono _ _ n K (fun _ _ _ ht => ⟨ht.1.1, ht.1.2.1, ht.2⟩)
  unfold doubleAscent
  omega

private theorem lowAdditionWeights_mono_h (f : Nat → Bool) (n : Nat) (r₁ r₂ : Int) (hr : r₁ ≤ r₂) :
    ∀ K, lowAdditionWeights f n r₁ K ≤ lowAdditionWeights f n r₂ K
  | 0 => Int.le_refl 0
  | k + 1 => by
    have ih := lowAdditionWeights_mono_h f n r₁ r₂ hr k
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

private theorem lowAdditionWeights_zero_below (f : Nat → Bool) (n : Nat) (m r : Int) (hr : r ≤ m) :
    ∀ K, (∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) → lowAdditionWeights f n r K = 0
  | 0, _ => rfl
  | k + 1, hfloor => by
    have ih := lowAdditionWeights_zero_below f n m r hr k (fun i hi1 hi2 => hfloor i hi1 (by omega))
    have hm := hfloor (n + k) (by omega) (by omega)
    simp only [lowAdditionWeights, ih]
    unfold lowAdditionWeight
    rw [if_neg (fun h => by omega)]
    omega

private theorem lowAdditionWeights_eq_levelWeightSumH (f : Nat → Bool) (n : Nat) :
    ∀ K (m : Int), (∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) →
      ∀ d : Nat, lowAdditionWeights f n (m + (d : Int) + 1) K =
        (levelWeightSumH (fun j => levelAdditions f n K (m + (j : Int))) d : Int)
  | 0, m, _, d => by
    have hzero : ∀ g : Nat → Nat, (∀ j, g j = 0) →
        ∀ k, levelSumH g k = 0 ∧ levelWeightSumH g k = 0 := by
      intro g hg k
      induction k with
      | zero => simp [levelSumH, levelWeightSumH, hg 0]
      | succ k ih => simp [levelSumH, levelWeightSumH, ih.1, ih.2, hg (k + 1)]
    have hz := (hzero (fun j => levelAdditions f n 0 (m + (j : Int))) (fun _ => rfl) d).2
    simp [lowAdditionWeights, hz]
  | k + 1, m, hfloor, d => by
    have hbase := lowAdditionWeights_eq_levelWeightSumH f n k m
      (fun i hi1 hi2 => hfloor i hi1 (by omega))
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
          levelSumH (fun j => levelAdditions f n (k + 1) (m + (j : Int))) d' =
            levelSumH (fun j => levelAdditions f n k (m + (j : Int))) d' +
              if Fw f (n + k) ≤ m + (d' : Int) then 1 else 0 := by
        intro d'
        induction d' with
        | zero =>
          simp only [levelSumH, hAstep 0]
          by_cases h0 : Fw f (n + k) = m + ((0 : Nat) : Int)
          · rw [if_pos h0, if_pos (by omega)]
          · rw [if_neg h0, if_neg (by omega)]
        | succ d' ih =>
          simp only [levelSumH, ih, hAstep (d' + 1)]
          by_cases hle : Fw f (n + k) ≤ m + (d' : Int)
          · rw [if_pos hle, if_neg (by omega), if_pos (by omega)]; omega
          · by_cases heq : Fw f (n + k) = m + ((d' + 1 : Nat) : Int)
            · rw [if_neg hle, if_pos heq, if_pos (by omega)]; omega
            · rw [if_neg hle, if_neg heq, if_neg (by omega)]; omega
      induction d with
      | zero =>
        simp only [lowAdditionWeights, hbase 0, levelWeightSumH, hAstep 0]
        unfold lowAdditionWeight
        by_cases h0 : Fw f (n + k) = m + ((0 : Nat) : Int)
        · rw [if_pos ⟨hf, by omega⟩, if_pos h0]; push_cast; omega
        · rw [if_neg (fun h => h0 (by omega)), if_neg h0]; omega
      | succ d ihd =>
        have hU := hUstep d
        have hbase_d := hbase d
        have hbase_d1 := hbase (d + 1)
        simp only [lowAdditionWeights, levelWeightSumH] at ihd hbase_d1 ⊢
        rw [hU, hAstep (d + 1), hbase_d1]
        by_cases heq : Fw f (n + k) = m + ((d + 1 : Nat) : Int)
        · have hlw1 : lowAdditionWeight f (m + ((d + 1 : Nat) : Int) + 1) (n + k) = 1 := by
            unfold lowAdditionWeight; rw [if_pos ⟨hf, by omega⟩]; omega
          have hlw0 : lowAdditionWeight f (m + (d : Int) + 1) (n + k) = 0 := by
            unfold lowAdditionWeight; rw [if_neg (fun h => by omega)]
          rw [hlw1, if_pos heq, if_neg (by omega)]
          rw [hlw0, hbase_d] at ihd
          push_cast; omega
        · rw [if_neg heq]
          by_cases hlow : Fw f (n + k) ≤ m + (d : Int)
          · have hlw1 : lowAdditionWeight f (m + ((d + 1 : Nat) : Int) + 1) (n + k) =
                lowAdditionWeight f (m + (d : Int) + 1) (n + k) + 2 := by
              unfold lowAdditionWeight; rw [if_pos ⟨hf, by omega⟩, if_pos ⟨hf, by omega⟩]; omega
            rw [hlw1, if_pos hlow]
            rw [hbase_d] at ihd
            push_cast; omega
          · have hlw1 : lowAdditionWeight f (m + ((d + 1 : Nat) : Int) + 1) (n + k) = 0 := by
              unfold lowAdditionWeight; rw [if_neg (fun h => by omega)]
            have hlw0 : lowAdditionWeight f (m + (d : Int) + 1) (n + k) = 0 := by
              unfold lowAdditionWeight; rw [if_neg (fun h => by omega)]
            rw [hlw1, if_neg hlow]
            rw [hbase_d] at ihd
            push_cast; omega
    · have hAeq : ∀ j : Nat, levelAdditions f n (k + 1) (m + (j : Int)) =
          levelAdditions f n k (m + (j : Int)) := fun j =>
        cN_succ_neg _ n k (fun h => hf h.2)
      have hfn : (fun j : Nat => levelAdditions f n (k + 1) (m + (j : Int))) =
          (fun j : Nat => levelAdditions f n k (m + (j : Int))) := funext hAeq
      rw [lowAdditionWeights, hbase d, hfn]
      have hlw : lowAdditionWeight f (m + (d : Int) + 1) (n + k) = 0 := by
        unfold lowAdditionWeight; rw [if_neg (fun h => hf h.1)]
      rw [hlw]; omega

private theorem levelSumH_free_le_free (f : Nat → Bool) (n K : Nat) (m : Int) :
    ∀ H, levelSumH (fun h => levelFree f n K (m + (h : Int))) H ≤ free f n K := by
  have hle : ∀ H, levelSumH (fun h => levelFree f n K (m + (h : Int))) H ≤
      cN (fun t => f t = true ∧ ¬ EndN f 0 t ∧ Fw f t ≤ m + (H : Int)) n K := by
    intro H
    induction H with
    | zero =>
      simp only [levelSumH, levelFree]
      exact cN_mono _ _ n K (fun _ _ _ ht => ⟨ht.2.1, ht.2.2, by omega⟩)
    | succ H ih =>
      simp only [levelSumH]
      have hsp := cN_split_prop_h
        (fun t => f t = true ∧ ¬ EndN f 0 t ∧ Fw f t ≤ m + ((H + 1 : Nat) : Int))
        (fun t => Fw f t = m + ((H + 1 : Nat) : Int)) n K
      have h1 : cN (fun t => (f t = true ∧ ¬ EndN f 0 t ∧ Fw f t ≤ m + ((H + 1 : Nat) : Int)) ∧
          Fw f t = m + ((H + 1 : Nat) : Int)) n K =
          levelFree f n K (m + ((H + 1 : Nat) : Int)) := by
        unfold levelFree
        apply cN_congr
        intro t _ _
        exact ⟨fun ht => ⟨ht.2, ht.1.1, ht.1.2.1⟩, fun ht => ⟨⟨ht.2.1, ht.2.2, by omega⟩, ht.1⟩⟩
      have h2 : cN (fun t => (f t = true ∧ ¬ EndN f 0 t ∧ Fw f t ≤ m + ((H + 1 : Nat) : Int)) ∧
          ¬ Fw f t = m + ((H + 1 : Nat) : Int)) n K =
          cN (fun t => f t = true ∧ ¬ EndN f 0 t ∧ Fw f t ≤ m + (H : Int)) n K := by
        apply cN_congr
        intro t _ _
        exact ⟨fun ht => ⟨ht.1.1, ht.1.2.1, by omega⟩, fun ht => ⟨⟨ht.1, ht.2.1, by omega⟩, by omega⟩⟩
      rw [h1, h2] at hsp
      omega
  intro H
  exact Nat.le_trans (hle H) (cN_mono _ _ n K (fun _ _ _ ht => ⟨ht.1, ht.2.1⟩))

private theorem additions_le_levelSumH (f : Nat → Bool) (n K : Nat) (m : Int)
    (hfloor : ∀ i, n ≤ i → i < n + K → m ≤ Fw f i) :
    ∀ H : Nat, cN (fun t => f t = true ∧ Fw f t ≤ m + (H : Int)) n K ≤
      levelSumH (fun h => levelAdditions f n K (m + (h : Int))) H := by
  intro H
  induction H with
  | zero =>
    simp only [levelSumH, levelAdditions]
    exact cN_mono _ _ n K (fun t hnt htK ht => ⟨by have := hfloor t hnt htK; omega, ht.1⟩)
  | succ H ih =>
    simp only [levelSumH]
    have hsp := cN_split_prop_h
      (fun t => f t = true ∧ Fw f t ≤ m + ((H + 1 : Nat) : Int))
      (fun t => Fw f t = m + ((H + 1 : Nat) : Int)) n K
    have h1 : cN (fun t => (f t = true ∧ Fw f t ≤ m + ((H + 1 : Nat) : Int)) ∧
        Fw f t = m + ((H + 1 : Nat) : Int)) n K =
        levelAdditions f n K (m + ((H + 1 : Nat) : Int)) := by
      unfold levelAdditions
      apply cN_congr
      intro t _ _
      exact ⟨fun ht => ⟨ht.2, ht.1.1⟩, fun ht => ⟨⟨ht.2, by omega⟩, ht.1⟩⟩
    have h2 : cN (fun t => (f t = true ∧ Fw f t ≤ m + ((H + 1 : Nat) : Int)) ∧
        ¬ Fw f t = m + ((H + 1 : Nat) : Int)) n K =
        cN (fun t => f t = true ∧ Fw f t ≤ m + (H : Int)) n K := by
      apply cN_congr
      intro t _ _
      exact ⟨fun ht => ⟨ht.1.1, by omega⟩, fun ht => ⟨⟨ht.1, by omega⟩, by omega⟩⟩
    rw [h1, h2] at hsp
    omega

/-! ## Floor-level supplied bounds (`E_0 = E_1 = 0`, `E_2 ≤ F_0`) -/

private theorem level_floor_basics (f : Nat → Bool) (n a K : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    levelSupplied f n K (m + ((0 : Nat) : Int)) = 0 ∧
    levelSupplied f n K (m + ((1 : Nat) : Int)) = 0 ∧
    levelSupplied f n K (m + ((2 : Nat) : Int)) ≤ levelFree f n K (m + ((0 : Nat) : Int)) := by
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
  have hE2 : levelSupplied f n K (m + ((2 : Nat) : Int)) ≤ levelFree f n K (m + ((0 : Nat) : Int)) := by
    have hb := floor_plus_two_aa_budget f n a K m hw hpre hfloor
    have hAA0 := doubleAscent_le_additions_h f n K (m + ((0 : Nat) : Int))
    have hsp0 := level_additions_split_h f n K (m + ((0 : Nat) : Int))
    have hm0 : m + ((0 : Nat) : Int) = m := by omega
    have hm2 : m + ((2 : Nat) : Int) = m + 2 := by omega
    rw [hm0] at hE0 hAA0 hsp0 ⊢
    rw [hm2]
    omega
  exact ⟨hE0, hE1, hE2⟩

/-! ## Core `δ = 2` and `δ = 3` exponentially-decaying convolution invariants -/

private theorem convFree2_invariant (f : Nat → Bool) (n a K : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) (H : Nat) :
      5 * 3 ^ (H + 2) * triAdditionsH f n K m (H + 1) +
        5 * 3 ^ (H + 2) * doubleAscent f n K (m + (H : Int)) +
        10 * 3 ^ (H + 1) * doubleAscent f n K (m + ((H + 1 : Nat) : Int)) +
        3 ^ (H + 2) * levelFree f n K (m + ((H + 1 : Nat) : Int)) ≤
      convFree2 (fun h => levelFree f n K (m + (h : Int))) H := by
  obtain ⟨hE0, hE1, hE2⟩ := level_floor_basics f n a K m hw hpre hfloor
  have hA0 := level_additions_split_h f n K (m + ((0 : Nat) : Int))
  have hA1 := level_additions_split_h f n K (m + ((1 : Nat) : Int))
  have hA2 := level_additions_split_h f n K (m + ((2 : Nat) : Int))
  have hAA0 := doubleAscent_le_additions_h f n K (m + ((0 : Nat) : Int))
  have hAA1 := doubleAscent_le_additions_h f n K (m + ((1 : Nat) : Int))
  have hAA2 := doubleAscent_le_additions_h f n K (m + ((2 : Nat) : Int))
  match H with
  | 0 =>
    unfold triAdditionsH
    rw [triSumH_1]
    simp only [convFree2, Nat.zero_add, Nat.pow_one]
    have hp2 : (3 : Nat) ^ 2 = 9 := by decide
    rw [hp2]
    omega
  | 1 =>
    unfold triAdditionsH
    rw [show (1 : Nat) + 1 = 2 by rfl, triSumH_2]
    simp only [convFree2]
    have hp2 : (3 : Nat) ^ 2 = 9 := by decide
    have hp3 : (3 : Nat) ^ 3 = 27 := by decide
    rw [show (1 : Nat) + 2 = 3 by rfl, hp2, hp3]
    omega
  | H' + 2 =>
    have ih0 := convFree2_invariant f n a K m hw hpre hfloor (H' + 1)
    let H := H' + 1
    have ih : 5 * 3 ^ (H + 2) * triAdditionsH f n K m (H + 1) +
        5 * 3 ^ (H + 2) * doubleAscent f n K (m + (H : Int)) +
        10 * 3 ^ (H + 1) * doubleAscent f n K (m + ((H + 1 : Nat) : Int)) +
        3 ^ (H + 2) * levelFree f n K (m + ((H + 1 : Nat) : Int)) ≤
      convFree2 (fun h => levelFree f n K (m + (h : Int))) H := ih0
    have hb := actual_double_ascent_spacing_budget f n a K 2 (m + (H : Int) + 1) (by omega) hw hpre
    have hW := lowAdditionWeights_eq_levelWeightSumH f n K m hfloor H
    rw [hW] at hb
    have hrm1 : m + (H : Int) + 1 - 1 = m + (H : Int) := by omega
    have hr1 : m + (H : Int) + 1 + 1 = m + ((H + 2 : Nat) : Int) := by omega
    have hr0 : m + (H : Int) + 1 = m + ((H + 1 : Nat) : Int) := by omega
    rw [hrm1, hr1, hr0] at hb
    have hbNat :
        3 * levelSupplied f n K (m + ((H + 2 : Nat) : Int)) +
          2 * suppliedDoubleAscent f n K (m + ((H + 2 : Nat) : Int)) +
          levelSupplied f n K (m + ((H + 1 : Nat) : Int)) ≤
        levelWeightSumH (fun j => levelAdditions f n K (m + (j : Int))) H +
          5 * doubleAscent f n K (m + (H : Int)) := by omega
    have hsp2 := level_additions_split_h f n K (m + ((H + 2 : Nat) : Int))
    have hsp1 := level_additions_split_h f n K (m + ((H + 1 : Nat) : Int))
    have hAAsp2 := doubleAscent_le_supplied_add_free_h f n K (m + ((H + 2 : Nat) : Int))
    have hstepA :
        3 * levelAdditions f n K (m + ((H + 2 : Nat) : Int)) +
          2 * doubleAscent f n K (m + ((H + 2 : Nat) : Int)) +
          levelAdditions f n K (m + ((H + 1 : Nat) : Int)) ≤
        levelWeightSumH (fun j => levelAdditions f n K (m + (j : Int))) H +
          5 * doubleAscent f n K (m + (H : Int)) +
          5 * levelFree f n K (m + ((H + 2 : Nat) : Int)) +
          levelFree f n K (m + ((H + 1 : Nat) : Int)) := by omega
    have h5ih := Nat.mul_le_mul_left 5 ih
    have h3st := Nat.mul_le_mul_left (5 * 3 ^ (H + 2)) hstepA
    have htid := triSumH_five_thirds_step (fun j => levelAdditions f n K (m + (j : Int))) H
    have htidM := congrArg (fun x => 5 * 3 ^ (H + 2) * x) htid
    have hpow3 : 3 ^ (H + 3) = 3 * 3 ^ (H + 2) := by
      rw [show H + 3 = (H + 2) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have hpow3_prev : 3 ^ (H + 2) = 3 * 3 ^ (H + 1) := by
      rw [show H + 2 = (H + 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have hgoal_conv : convFree2 (fun h => levelFree f n K (m + (h : Int))) (H' + 2) =
        5 * convFree2 (fun h => levelFree f n K (m + (h : Int))) H +
          28 * 3 ^ (H + 2) * levelFree f n K (m + ((H + 2 : Nat) : Int)) := rfl
    rw [hgoal_conv]
    change 5 * 3 ^ (H + 3) * triAdditionsH f n K m (H + 2) +
        5 * 3 ^ (H + 3) * doubleAscent f n K (m + ((H + 1 : Nat) : Int)) +
        10 * 3 ^ (H + 2) * doubleAscent f n K (m + ((H + 2 : Nat) : Int)) +
        3 ^ (H + 3) * levelFree f n K (m + ((H + 2 : Nat) : Int)) ≤ _
    unfold triAdditionsH at ih h5ih ⊢
    have hT : 5 * (5 * 3 ^ (H + 2) * triSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 1)) +
        5 * 3 ^ (H + 2) * (3 * levelAdditions f n K (m + ((H + 2 : Nat) : Int))) +
        5 * 3 ^ (H + 2) * levelAdditions f n K (m + ((H + 1 : Nat) : Int)) =
        5 * 3 ^ (H + 3) * triSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 2) +
          5 * 3 ^ (H + 2) * levelWeightSumH (fun j => levelAdditions f n K (m + (j : Int))) H := by
      rw [hpow3]
      have hL : 5 * (5 * 3 ^ (H + 2) * triSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 1)) +
          5 * 3 ^ (H + 2) * (3 * levelAdditions f n K (m + ((H + 2 : Nat) : Int))) +
          5 * 3 ^ (H + 2) * levelAdditions f n K (m + ((H + 1 : Nat) : Int)) =
          5 * 3 ^ (H + 2) * (5 * triSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 1) +
            3 * levelAdditions f n K (m + ((H + 2 : Nat) : Int)) +
            levelAdditions f n K (m + ((H + 1 : Nat) : Int))) := by grind
      rw [hL, htidM]; grind
    have hAA1_ge : 5 * 3 ^ (H + 3) * doubleAscent f n K (m + ((H + 1 : Nat) : Int)) ≤
        5 * (10 * 3 ^ (H + 1) * doubleAscent f n K (m + ((H + 1 : Nat) : Int))) := by
      rw [hpow3, hpow3_prev]
      have hle : 45 * 3 ^ (H + 1) ≤ 50 * 3 ^ (H + 1) := by omega
      have hm := Nat.mul_le_mul_right (doubleAscent f n K (m + ((H + 1 : Nat) : Int))) hle
      grind
    have hAA0_eq : 5 * (5 * 3 ^ (H + 2) * doubleAscent f n K (m + (H : Int))) =
        5 * 3 ^ (H + 2) * (5 * doubleAscent f n K (m + (H : Int))) := by grind
    have hAA2_eq : 5 * 3 ^ (H + 2) * (2 * doubleAscent f n K (m + ((H + 2 : Nat) : Int))) =
        10 * 3 ^ (H + 2) * doubleAscent f n K (m + ((H + 2 : Nat) : Int)) := by grind
    have hF1_eq : 5 * (3 ^ (H + 2) * levelFree f n K (m + ((H + 1 : Nat) : Int))) =
        5 * 3 ^ (H + 2) * levelFree f n K (m + ((H + 1 : Nat) : Int)) := by grind
    have hF2_eq : 5 * 3 ^ (H + 2) * (5 * levelFree f n K (m + ((H + 2 : Nat) : Int))) +
        3 ^ (H + 3) * levelFree f n K (m + ((H + 2 : Nat) : Int)) =
        28 * 3 ^ (H + 2) * levelFree f n K (m + ((H + 2 : Nat) : Int)) := by
      rw [hpow3]; grind
    simp only [Nat.mul_add] at h5ih h3st
    clear hE0 hE1 hE2 hA0 hA1 hA2 hAA0 hAA1 hAA2 hb hbNat hsp2 hsp1 hAAsp2 hstepA ih htid htidM hpow3 hpow3_prev hgoal_conv
    omega

private theorem convFree3_invariant (f : Nat → Bool) (n a K : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) (H : Nat) :
      5 * 3 ^ (H + 2) * triAdditionsH f n K m (H + 1) +
        8 * 3 ^ (H + 2) * doubleAscent f n K (m + (H : Int)) +
        15 * 3 ^ (H + 1) * doubleAscent f n K (m + ((H + 1 : Nat) : Int)) +
        3 ^ (H + 2) * levelFree f n K (m + ((H + 1 : Nat) : Int)) ≤
      convFree3 (fun h => levelFree f n K (m + (h : Int))) H := by
  obtain ⟨hE0, hE1, hE2⟩ := level_floor_basics f n a K m hw hpre hfloor
  have hA0 := level_additions_split_h f n K (m + ((0 : Nat) : Int))
  have hA1 := level_additions_split_h f n K (m + ((1 : Nat) : Int))
  have hA2 := level_additions_split_h f n K (m + ((2 : Nat) : Int))
  have hAA0 := doubleAscent_le_additions_h f n K (m + ((0 : Nat) : Int))
  have hAA1 := doubleAscent_le_additions_h f n K (m + ((1 : Nat) : Int))
  have hAA2 := doubleAscent_le_additions_h f n K (m + ((2 : Nat) : Int))
  match H with
  | 0 =>
    unfold triAdditionsH
    rw [triSumH_1]
    simp only [convFree3, Nat.zero_add, Nat.pow_one]
    have hp2 : (3 : Nat) ^ 2 = 9 := by decide
    rw [hp2]
    omega
  | 1 =>
    unfold triAdditionsH
    rw [show (1 : Nat) + 1 = 2 by rfl, triSumH_2]
    simp only [convFree3]
    have hp2 : (3 : Nat) ^ 2 = 9 := by decide
    have hp3 : (3 : Nat) ^ 3 = 27 := by decide
    rw [show (1 : Nat) + 2 = 3 by rfl, hp2, hp3]
    omega
  | H' + 2 =>
    have ih0 := convFree3_invariant f n a K m hw hpre hfloor (H' + 1)
    let H := H' + 1
    have ih : 5 * 3 ^ (H + 2) * triAdditionsH f n K m (H + 1) +
        8 * 3 ^ (H + 2) * doubleAscent f n K (m + (H : Int)) +
        15 * 3 ^ (H + 1) * doubleAscent f n K (m + ((H + 1 : Nat) : Int)) +
        3 ^ (H + 2) * levelFree f n K (m + ((H + 1 : Nat) : Int)) ≤
      convFree3 (fun h => levelFree f n K (m + (h : Int))) H := ih0
    have hb := actual_double_ascent_spacing_budget f n a K 3 (m + (H : Int) + 1) (by omega) hw hpre
    have hW := lowAdditionWeights_eq_levelWeightSumH f n K m hfloor H
    rw [hW] at hb
    have hrm1 : m + (H : Int) + 1 - 1 = m + (H : Int) := by omega
    have hr1 : m + (H : Int) + 1 + 1 = m + ((H + 2 : Nat) : Int) := by omega
    have hr0 : m + (H : Int) + 1 = m + ((H + 1 : Nat) : Int) := by omega
    rw [hrm1, hr1, hr0] at hb
    have hbNat :
        3 * levelSupplied f n K (m + ((H + 2 : Nat) : Int)) +
          3 * suppliedDoubleAscent f n K (m + ((H + 2 : Nat) : Int)) +
          levelSupplied f n K (m + ((H + 1 : Nat) : Int)) ≤
        levelWeightSumH (fun j => levelAdditions f n K (m + (j : Int))) H +
          6 * doubleAscent f n K (m + (H : Int)) := by omega
    have hsp2 := level_additions_split_h f n K (m + ((H + 2 : Nat) : Int))
    have hsp1 := level_additions_split_h f n K (m + ((H + 1 : Nat) : Int))
    have hAAsp2 := doubleAscent_le_supplied_add_free_h f n K (m + ((H + 2 : Nat) : Int))
    have hstepA :
        3 * levelAdditions f n K (m + ((H + 2 : Nat) : Int)) +
          3 * doubleAscent f n K (m + ((H + 2 : Nat) : Int)) +
          levelAdditions f n K (m + ((H + 1 : Nat) : Int)) ≤
        levelWeightSumH (fun j => levelAdditions f n K (m + (j : Int))) H +
          6 * doubleAscent f n K (m + (H : Int)) +
          6 * levelFree f n K (m + ((H + 2 : Nat) : Int)) +
          levelFree f n K (m + ((H + 1 : Nat) : Int)) := by omega
    have h5ih := Nat.mul_le_mul_left 5 ih
    have h3st := Nat.mul_le_mul_left (5 * 3 ^ (H + 2)) hstepA
    have htid := triSumH_five_thirds_step (fun j => levelAdditions f n K (m + (j : Int))) H
    have htidM := congrArg (fun x => 5 * 3 ^ (H + 2) * x) htid
    have hpow3 : 3 ^ (H + 3) = 3 * 3 ^ (H + 2) := by
      rw [show H + 3 = (H + 2) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have hpow3_prev : 3 ^ (H + 2) = 3 * 3 ^ (H + 1) := by
      rw [show H + 2 = (H + 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have hgoal_conv : convFree3 (fun h => levelFree f n K (m + (h : Int))) (H' + 2) =
        5 * convFree3 (fun h => levelFree f n K (m + (h : Int))) H +
          33 * 3 ^ (H + 2) * levelFree f n K (m + ((H + 2 : Nat) : Int)) := rfl
    rw [hgoal_conv]
    change 5 * 3 ^ (H + 3) * triAdditionsH f n K m (H + 2) +
        8 * 3 ^ (H + 3) * doubleAscent f n K (m + ((H + 1 : Nat) : Int)) +
        15 * 3 ^ (H + 2) * doubleAscent f n K (m + ((H + 2 : Nat) : Int)) +
        3 ^ (H + 3) * levelFree f n K (m + ((H + 2 : Nat) : Int)) ≤ _
    unfold triAdditionsH at ih h5ih ⊢
    have hT : 5 * (5 * 3 ^ (H + 2) * triSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 1)) +
        5 * 3 ^ (H + 2) * (3 * levelAdditions f n K (m + ((H + 2 : Nat) : Int))) +
        5 * 3 ^ (H + 2) * levelAdditions f n K (m + ((H + 1 : Nat) : Int)) =
        5 * 3 ^ (H + 3) * triSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 2) +
          5 * 3 ^ (H + 2) * levelWeightSumH (fun j => levelAdditions f n K (m + (j : Int))) H := by
      rw [hpow3]
      have hL : 5 * (5 * 3 ^ (H + 2) * triSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 1)) +
          5 * 3 ^ (H + 2) * (3 * levelAdditions f n K (m + ((H + 2 : Nat) : Int))) +
          5 * 3 ^ (H + 2) * levelAdditions f n K (m + ((H + 1 : Nat) : Int)) =
          5 * 3 ^ (H + 2) * (5 * triSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 1) +
            3 * levelAdditions f n K (m + ((H + 2 : Nat) : Int)) +
            levelAdditions f n K (m + ((H + 1 : Nat) : Int))) := by grind
      rw [hL, htidM]; grind
    have hAA0_ge : 5 * 3 ^ (H + 2) * (6 * doubleAscent f n K (m + (H : Int))) ≤
        5 * (8 * 3 ^ (H + 2) * doubleAscent f n K (m + (H : Int))) := by
      have hle : 30 * 3 ^ (H + 2) ≤ 40 * 3 ^ (H + 2) := by omega
      have hm := Nat.mul_le_mul_right (doubleAscent f n K (m + (H : Int))) hle
      grind
    have hAA1_ge : 8 * 3 ^ (H + 3) * doubleAscent f n K (m + ((H + 1 : Nat) : Int)) ≤
        5 * (15 * 3 ^ (H + 1) * doubleAscent f n K (m + ((H + 1 : Nat) : Int))) := by
      rw [hpow3, hpow3_prev]
      have hle : 72 * 3 ^ (H + 1) ≤ 75 * 3 ^ (H + 1) := by omega
      have hm := Nat.mul_le_mul_right (doubleAscent f n K (m + ((H + 1 : Nat) : Int))) hle
      grind
    have hAA2_eq : 5 * 3 ^ (H + 2) * (3 * doubleAscent f n K (m + ((H + 2 : Nat) : Int))) =
        15 * 3 ^ (H + 2) * doubleAscent f n K (m + ((H + 2 : Nat) : Int)) := by grind
    have hF1_eq : 5 * (3 ^ (H + 2) * levelFree f n K (m + ((H + 1 : Nat) : Int))) =
        5 * 3 ^ (H + 2) * levelFree f n K (m + ((H + 1 : Nat) : Int)) := by grind
    have hF2_eq : 5 * 3 ^ (H + 2) * (6 * levelFree f n K (m + ((H + 2 : Nat) : Int))) +
        3 ^ (H + 3) * levelFree f n K (m + ((H + 2 : Nat) : Int)) =
        33 * 3 ^ (H + 2) * levelFree f n K (m + ((H + 2 : Nat) : Int)) := by
      rw [hpow3]; grind
    simp only [Nat.mul_add] at h5ih h3st
    clear hE0 hE1 hE2 hA0 hA1 hA2 hAA0 hAA1 hAA2 hb hbNat hsp2 hsp1 hAAsp2 hstepA ih htid htidM hpow3 hpow3_prev hgoal_conv
    omega

/-! ## Convolution weight bounds (exponential decay and uniform upper bounds) -/

private theorem pow3_le_pow5_shift : ∀ k, 3 ^ k ≤ 5 ^ k
  | 0 => by omega
  | k + 1 => by
    have ih := pow3_le_pow5_shift k
    rw [Nat.pow_succ, Nat.pow_succ]
    exact Nat.le_trans (Nat.mul_le_mul_right 3 ih) (Nat.mul_le_mul_left (5 ^ k) (by omega))

private theorem tailSumH_zero_of_lt (F : Nat → Nat) (s : Nat) :
    ∀ k, k < s → tailSumH F s k = 0
  | 0, hk => by simp [tailSumH, show s ≠ 0 by omega]
  | k + 1, hk => by
    have ih := tailSumH_zero_of_lt F s k (by omega)
    simp only [tailSumH, ih, Nat.zero_add, if_neg (by omega : ¬ s ≤ k + 1)]

private theorem levelSumH_zero_add_tailSumH_one (F : Nat → Nat) :
    ∀ k, levelSumH F 0 + tailSumH F 1 k = levelSumH F k
  | 0 => by simp [levelSumH, tailSumH]
  | k + 1 => by
    have ih := levelSumH_zero_add_tailSumH_one F k
    simp only [levelSumH, tailSumH] at ih ⊢
    rw [if_pos (by omega : 1 ≤ k + 1)]
    omega

private theorem convFree2_split_bound (F : Nat → Nat) :
    ∀ H s, 1 ≤ s → s ≤ H + 1 →
      convFree2 F H ≤
        135 * 5 ^ H * levelSumH F (s - 1) +
          28 * 3 ^ s * 5 ^ (H + 1 - s) * tailSumH F s (H + 1)
  | 0, s, hs1, hsH => by
    have hs : s = 1 := by omega
    subst hs
    simp [convFree2, levelSumH, tailSumH]
  | 1, s, hs1, hsH => by
    by_cases hs : s = 1
    · subst hs
      have ht2 : tailSumH F 1 2 = F 1 + F 2 := by
        change tailSumH F 1 1 + F 2 = _
        change (tailSumH F 1 0 + F 1) + F 2 = _
        simp [tailSumH]
      rw [show (1 : Nat) - 1 = 0 by rfl, show (1 : Nat) + 1 = 2 by rfl, ht2]
      simp only [convFree2, levelSumH]
      have h1 : 135 * 5 ^ 1 = 675 := by decide
      have h2 : 28 * 3 ^ 1 * 5 ^ (2 - 1) = 420 := by decide
      rw [h1, h2]
      omega
    · have hs2 : s = 2 := by omega
      subst hs2
      have ht2 : tailSumH F 2 2 = F 2 := by
        change tailSumH F 2 1 + F 2 = _
        rw [tailSumH_zero_of_lt F 2 1 (by omega), Nat.zero_add]
      rw [show (2 : Nat) - 1 = 1 by rfl, show (1 : Nat) + 1 = 2 by rfl, ht2, levelSumH_1]
      simp only [convFree2]
      have h1 : 135 * 5 ^ 1 = 675 := by decide
      have h2 : 28 * 3 ^ 2 * 5 ^ (2 - 2) = 252 := by decide
      rw [h1, h2]
      omega
  | H' + 2, s, hs1, hsH => by
    by_cases hs_top : s = H' + 3
    · subst hs_top
      have hts_top : tailSumH F (H' + 3) (H' + 3) = F (H' + 3) := by
        have hstep : tailSumH F (H' + 3) ((H' + 2) + 1) =
            tailSumH F (H' + 3) (H' + 2) + if H' + 3 ≤ (H' + 2) + 1 then F ((H' + 2) + 1) else 0 := rfl
        rw [show H' + 3 = (H' + 2) + 1 by omega]
        rw [hstep, tailSumH_zero_of_lt F ((H' + 2) + 1) (H' + 2) (by omega), Nat.zero_add,
          if_pos (Nat.le_refl _)]
      have hconv_le : convFree2 F (H' + 1) ≤ 135 * 5 ^ (H' + 1) * levelSumH F (H' + 2) := by
        have h1 := convFree2_split_bound F (H' + 1) 1 (by omega) (by omega)
        have htail_le := levelSumH_zero_add_tailSumH_one F (H' + 2)
        have hc : 28 * 3 ^ 1 * 5 ^ (H' + 1 + 1 - 1) ≤ 135 * 5 ^ (H' + 1) := by
          rw [show H' + 1 + 1 - 1 = H' + 1 by omega]
          have : 28 * 3 ≤ 135 := by decide
          have := Nat.mul_le_mul_right (5 ^ (H' + 1)) this
          grind
        have hm := Nat.mul_le_mul_right (tailSumH F 1 (H' + 2)) hc
        rw [Nat.sub_self, show H' + 1 + 1 - 1 = H' + 1 by omega,
          show H' + 1 + 1 = H' + 2 by omega] at h1
        rw [show H' + 1 + 1 - 1 = H' + 1 by omega] at hm
        rw [← htail_le, Nat.mul_add]
        omega
      have h5 := Nat.mul_le_mul_left 5 hconv_le
      have hp5 : 5 * (135 * 5 ^ (H' + 1) * levelSumH F (H' + 2)) =
          135 * 5 ^ (H' + 2) * levelSumH F (H' + 2) := by
        rw [show H' + 2 = (H' + 1) + 1 by omega, Nat.pow_succ]; grind
      change 5 * convFree2 F (H' + 1) + 28 * 3 ^ (H' + 3) * F (H' + 3) ≤ _
      rw [show H' + 2 + 1 = H' + 3 by omega, hts_top, show H' + 3 - 1 = H' + 2 by omega,
        Nat.sub_self, Nat.pow_zero, Nat.mul_one]
      omega
    · have ih := convFree2_split_bound F (H' + 1) s hs1 (by omega)
      have h5 := Nat.mul_le_mul_left 5 ih
      have hp5 : 5 * (135 * 5 ^ (H' + 1) * levelSumH F (s - 1)) =
          135 * 5 ^ (H' + 2) * levelSumH F (s - 1) := by
        rw [show H' + 2 = (H' + 1) + 1 by omega, Nat.pow_succ]; grind
      have hp5t : 5 * (28 * 3 ^ s * 5 ^ (H' + 1 + 1 - s) * tailSumH F s (H' + 2)) =
          28 * 3 ^ s * 5 ^ (H' + 3 - s) * tailSumH F s (H' + 2) := by
        rw [show H' + 3 - s = (H' + 1 + 1 - s) + 1 by omega, Nat.pow_succ]; grind
      have hmono : 3 ^ (H' + 3) ≤ 3 ^ s * 5 ^ (H' + 3 - s) := by
        have h1 := pow3_le_pow5_shift (H' + 3 - s)
        have h2 := Nat.mul_le_mul_left (3 ^ s) h1
        rw [← Nat.pow_add, show s + (H' + 3 - s) = H' + 3 by omega] at h2
        exact h2
      have hFtop : 28 * 3 ^ (H' + 3) * F (H' + 3) ≤
          28 * 3 ^ s * 5 ^ (H' + 3 - s) * F (H' + 3) := by
        have h1 := Nat.mul_le_mul_left 28 hmono
        have h2 := Nat.mul_le_mul_right (F (H' + 3)) h1
        grind
      have hts : tailSumH F s (H' + 3) = tailSumH F s (H' + 2) + F (H' + 3) := by
        change tailSumH F s (H' + 2) + (if s ≤ H' + 3 then F (H' + 3) else 0) = _
        rw [if_pos (by omega : s ≤ H' + 3)]
      change 5 * convFree2 F (H' + 1) + 28 * 3 ^ (H' + 3) * F (H' + 3) ≤ _
      rw [show H' + 2 + 1 = H' + 3 by omega, hts, Nat.mul_add]
      rw [show H' + 1 + 1 = H' + 2 by omega, Nat.mul_add] at h5
      rw [show H' + 1 + 1 - s = H' + 2 - s by omega] at hp5t h5
      omega

private theorem convFree2_le_uniform (F : Nat → Nat) :
    ∀ H, 1 ≤ H → convFree2 F H ≤ 630 * 5 ^ (H - 1) * levelSumH F (H + 1) := by
  intro H hH
  match H with
  | 0 => omega
  | 1 =>
    rw [show (1 : Nat) + 1 = 2 by rfl, levelSumH_2]
    simp only [convFree2, Nat.sub_self, Nat.pow_zero, Nat.mul_one]
    omega
  | H' + 2 =>
    have ih := convFree2_le_uniform F (H' + 1) (by omega)
    have h5 := Nat.mul_le_mul_left 5 ih
    have hp5 : 5 * (630 * 5 ^ (H' + 1 - 1) * levelSumH F (H' + 2)) =
        630 * 5 ^ (H' + 1) * levelSumH F (H' + 2) := by
      rw [show H' + 1 - 1 = H' by omega, Nat.pow_succ]; grind
    have h35 : 28 * 3 ^ (H' + 3) ≤ 630 * 5 ^ (H' + 1) := by
      have h1 := pow3_le_pow5_shift (H' + 1)
      have h2 := Nat.mul_le_mul_left 252 h1
      have h3 : 28 * 3 ^ (H' + 3) = 252 * 3 ^ (H' + 1) := by
        rw [show H' + 3 = (H' + 1) + 2 by omega, Nat.pow_add]; grind
      have h4 : 252 * 5 ^ (H' + 1) ≤ 630 * 5 ^ (H' + 1) :=
        Nat.mul_le_mul_right _ (by decide)
      exact Nat.le_trans (h3 ▸ h2) h4
    have htop := Nat.mul_le_mul_right (F (H' + 3)) h35
    change 5 * convFree2 F (H' + 1) + 28 * 3 ^ (H' + 3) * F (H' + 3) ≤ _
    rw [show H' + 2 - 1 = H' + 1 by omega, show H' + 2 + 1 = H' + 3 by omega]
    have hLS : levelSumH F (H' + 3) = levelSumH F (H' + 2) + F (H' + 3) := rfl
    rw [show H' + 1 + 1 = H' + 2 by omega] at h5
    rw [hLS, Nat.mul_add]
    omega

private theorem convFree3_le_uniform (F : Nat → Nat) :
    ∀ H, 1 ≤ H → convFree3 F H ≤ 675 * 5 ^ (H - 1) * levelSumH F (H + 1) := by
  intro H hH
  match H with
  | 0 => omega
  | 1 =>
    rw [show (1 : Nat) + 1 = 2 by rfl, levelSumH_2]
    simp only [convFree3, Nat.sub_self, Nat.pow_zero, Nat.mul_one]
    omega
  | H' + 2 =>
    have ih := convFree3_le_uniform F (H' + 1) (by omega)
    have h5 := Nat.mul_le_mul_left 5 ih
    have hp5 : 5 * (675 * 5 ^ (H' + 1 - 1) * levelSumH F (H' + 2)) =
        675 * 5 ^ (H' + 1) * levelSumH F (H' + 2) := by
      rw [show H' + 1 - 1 = H' by omega, Nat.pow_succ]; grind
    have h35 : 33 * 3 ^ (H' + 3) ≤ 675 * 5 ^ (H' + 1) := by
      have h1 := pow3_le_pow5_shift (H' + 1)
      have h2 := Nat.mul_le_mul_left 297 h1
      have h3 : 33 * 3 ^ (H' + 3) = 297 * 3 ^ (H' + 1) := by
        rw [show H' + 3 = (H' + 1) + 2 by omega, Nat.pow_add]; grind
      have h4 : 297 * 5 ^ (H' + 1) ≤ 675 * 5 ^ (H' + 1) :=
        Nat.mul_le_mul_right _ (by decide)
      exact Nat.le_trans (h3 ▸ h2) h4
    have htop := Nat.mul_le_mul_right (F (H' + 3)) h35
    change 5 * convFree3 F (H' + 1) + 33 * 3 ^ (H' + 3) * F (H' + 3) ≤ _
    rw [show H' + 2 - 1 = H' + 1 by omega, show H' + 2 + 1 = H' + 3 by omega]
    have hLS : levelSumH F (H' + 3) = levelSumH F (H' + 2) + F (H' + 3) := rfl
    rw [show H' + 1 + 1 = H' + 2 by omega] at h5
    rw [hLS, Nat.mul_add]
    omega

/-! ## Public arbitrary-depth convolution, sharp `18/25` strip, and sharp `W(m+d)` theorems -/

/-- Exact exponentially-decaying height-convolution triangular capacity for ALL `H : Nat`:
  `5 * 3 ^ (H + 2) * triAdditionsH f n K m (H + 1) ≤ convFree2 (levelFree) H`.
Every free addition at height `m + h` decays by `(3/5)^h`, and free additions above `m + H + 1`
have exact weight `0`. -/
theorem convFree_triangular_capacity (f : Nat → Bool) (n a K H : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    5 * 3 ^ (H + 2) * triAdditionsH f n K m (H + 1) ≤
      convFree2 (fun h => levelFree f n K (m + (h : Int))) H := by
  have hinv := convFree2_invariant f n a K m hw hpre hfloor H
  omega

/-- Quantitative `LOW-free` vs `HIGH-free` exponential separation for every cutoff `1 ≤ s ≤ H + 1`:
high free additions at height `≥ m + s` are damped by `(3/5)^s` relative to low free additions
at heights `[m, m + s - 1]`. -/
theorem low_high_free_split_triangular_capacity (f : Nat → Bool) (n a K H s : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) (hs1 : 1 ≤ s) (hsH : s ≤ H + 1) :
    5 * 3 ^ (H + 2) * triAdditionsH f n K m (H + 1) ≤
      135 * 5 ^ H * levelSumH (fun h => levelFree f n K (m + (h : Int))) (s - 1) +
        28 * 3 ^ s * 5 ^ (H + 1 - s) *
          tailSumH (fun h => levelFree f n K (m + (h : Int))) s (H + 1) := by
  have h1 := convFree_triangular_capacity f n a K H m hw hpre hfloor
  have h2 := convFree2_split_bound (fun h => levelFree f n K (m + (h : Int))) H s hs1 hsH
  exact Nat.le_trans h1 h2

/-- Exact exponentially-decaying height-convolution strip bound (`∀ H : Nat`), proved via the
zero-remainder identity `2 * T(H + 1) + 3 * A_{H+2} + A_{H+1} = 3 * S(H + 2) + W(H)` and
the `δ = 3` (6-slot) convolution invariant `convFree3`. -/
theorem sharp_five_thirds_strip_convolution (f : Nat → Bool) (n a K H : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) :
    15 * 3 ^ (H + 2) *
        levelSumH (fun h => levelAdditions f n K (m + (h : Int))) (H + 2) ≤
      2 * convFree3 (fun h => levelFree f n K (m + (h : Int))) H +
        3 * 3 ^ (H + 2) * levelFree f n K (m + ((H + 1 : Nat) : Int)) +
        15 * 3 ^ (H + 2) * levelFree f n K (m + ((H + 2 : Nat) : Int)) := by
  have hinv := convFree3_invariant f n a K m hw hpre hfloor H
  have hb := actual_double_ascent_spacing_budget f n a K 0 (m + (H : Int) + 1) (by omega) hw hpre
  have hW := lowAdditionWeights_eq_levelWeightSumH f n K m hfloor H
  rw [hW] at hb
  have hrm1 : m + (H : Int) + 1 - 1 = m + (H : Int) := by omega
  have hr1 : m + (H : Int) + 1 + 1 = m + ((H + 2 : Nat) : Int) := by omega
  have hr0 : m + (H : Int) + 1 = m + ((H + 1 : Nat) : Int) := by omega
  rw [hrm1, hr1, hr0] at hb
  have hsp2 := level_additions_split_h f n K (m + ((H + 2 : Nat) : Int))
  have hsp1 := level_additions_split_h f n K (m + ((H + 1 : Nat) : Int))
  have hstepA :
      3 * levelAdditions f n K (m + ((H + 2 : Nat) : Int)) +
        levelAdditions f n K (m + ((H + 1 : Nat) : Int)) ≤
      levelWeightSumH (fun j => levelAdditions f n K (m + (j : Int))) H +
        3 * doubleAscent f n K (m + (H : Int)) +
        3 * levelFree f n K (m + ((H + 2 : Nat) : Int)) +
        levelFree f n K (m + ((H + 1 : Nat) : Int)) := by omega
  have h2inv := Nat.mul_le_mul_left 2 hinv
  have h5st := Nat.mul_le_mul_left (5 * 3 ^ (H + 2)) hstepA
  have hid := triSumH_strip_ident (fun j => levelAdditions f n K (m + (j : Int))) H
  have hidM := congrArg (fun x => 5 * 3 ^ (H + 2) * x) hid
  unfold triAdditionsH at hinv h2inv
  have hT : 2 * (5 * 3 ^ (H + 2) * triSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 1)) +
      5 * 3 ^ (H + 2) * (3 * levelAdditions f n K (m + ((H + 2 : Nat) : Int))) +
      5 * 3 ^ (H + 2) * levelAdditions f n K (m + ((H + 1 : Nat) : Int)) =
      15 * 3 ^ (H + 2) * levelSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 2) +
        5 * 3 ^ (H + 2) * levelWeightSumH (fun j => levelAdditions f n K (m + (j : Int))) H := by
    have hL : 2 * (5 * 3 ^ (H + 2) * triSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 1)) +
        5 * 3 ^ (H + 2) * (3 * levelAdditions f n K (m + ((H + 2 : Nat) : Int))) +
        5 * 3 ^ (H + 2) * levelAdditions f n K (m + ((H + 1 : Nat) : Int)) =
        5 * 3 ^ (H + 2) * (2 * triSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 1) +
          3 * levelAdditions f n K (m + ((H + 2 : Nat) : Int)) +
          levelAdditions f n K (m + ((H + 1 : Nat) : Int))) := by grind
    rw [hL, hidM]; grind
  have hAA_ge : 5 * 3 ^ (H + 2) * (3 * doubleAscent f n K (m + (H : Int))) ≤
      2 * (8 * 3 ^ (H + 2) * doubleAscent f n K (m + (H : Int))) := by
    have hle : 15 * 3 ^ (H + 2) ≤ 16 * 3 ^ (H + 2) := by omega
    have hm := Nat.mul_le_mul_right (doubleAscent f n K (m + (H : Int))) hle
    grind
  have hF1 : 5 * 3 ^ (H + 2) * levelFree f n K (m + ((H + 1 : Nat) : Int)) =
      2 * (3 ^ (H + 2) * levelFree f n K (m + ((H + 1 : Nat) : Int))) +
        3 * 3 ^ (H + 2) * levelFree f n K (m + ((H + 1 : Nat) : Int)) := by grind
  have hF2 : 5 * 3 ^ (H + 2) * (3 * levelFree f n K (m + ((H + 2 : Nat) : Int))) =
      15 * 3 ^ (H + 2) * levelFree f n K (m + ((H + 2 : Nat) : Int)) := by grind
  simp only [Nat.mul_add] at h2inv h5st
  omega

/-- Sharp global `(18/25) * (5/3)^H` total-strip additions capacity for ALL `H ≥ 1`:
whenever the walk stays in `[m, m + H]` during `[n, n + K)`,
  `25 * 3 ^ H * additions f n K ≤ 18 * 5 ^ H * free f n K`.
Slashes `E-797`'s constant `9/5 = 1.80` by `2.5×` to `18/25 = 0.72` (within `9/5 = 1.80×` of
`E-786`'s `(2/5) * (5/3)^H` lower bound for EVERY `H ≥ 1`). -/
theorem sharp_five_thirds_strip_capacity (f : Nat → Bool) (n a K H : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i)
    (hceil : ∀ i, n ≤ i → i < n + K → Fw f i ≤ m + (H : Int)) (hH : 1 ≤ H) :
    25 * 3 ^ H * additions f n K ≤ 18 * 5 ^ H * free f n K := by
  have hadd_le : additions f n K ≤ cN (fun t => f t = true ∧ Fw f t ≤ m + (H : Int)) n K := by
    unfold additions
    exact cN_mono _ _ n K (fun t hnt htK hf => ⟨hf, hceil t hnt htK⟩)
  have hls := additions_le_levelSumH f n K m (fun i hi1 hi2 => hfloor i hi1 (by omega)) H
  have htot := Nat.le_trans hadd_le hls
  obtain ⟨hE0, hE1, hE2⟩ := level_floor_basics f n a K m hw hpre hfloor
  have hA0 := level_additions_split_h f n K (m + ((0 : Nat) : Int))
  have hA1 := level_additions_split_h f n K (m + ((1 : Nat) : Int))
  have hA2 := level_additions_split_h f n K (m + ((2 : Nat) : Int))
  match H with
  | 0 => omega
  | 1 =>
    have hfr := levelSumH_free_le_free f n K m 1
    rw [levelSumH_1] at htot hfr
    have hS1 : additions f n K ≤ free f n K := by omega
    have hmul := Nat.mul_le_mul_left (25 * 3 ^ 1) hS1
    have hc : 25 * 3 ^ 1 ≤ 18 * 5 ^ 1 := by decide
    exact Nat.le_trans hmul (Nat.mul_le_mul_right _ hc)
  | 2 =>
    have hfr := levelSumH_free_le_free f n K m 2
    rw [levelSumH_2] at htot hfr
    have hS2 : additions f n K ≤ 2 * free f n K := by omega
    have hmul := Nat.mul_le_mul_left (25 * 3 ^ 2) hS2
    have hR : 25 * 3 ^ 2 * (2 * free f n K) = 18 * 5 ^ 2 * free f n K := by grind
    exact hR ▸ hmul
  | H' + 3 =>
    let H0 := H' + 1
    have hsc := sharp_five_thirds_strip_convolution f n a K H0 m hw hpre hfloor
    have hfr := levelSumH_free_le_free f n K m (H0 + 2)
    have hcomb :
        2 * convFree3 (fun h => levelFree f n K (m + (h : Int))) H0 +
          3 * 3 ^ (H0 + 2) * levelFree f n K (m + ((H0 + 1 : Nat) : Int)) +
          15 * 3 ^ (H0 + 2) * levelFree f n K (m + ((H0 + 2 : Nat) : Int)) ≤
        1350 * 5 ^ H' *
          levelSumH (fun h => levelFree f n K (m + (h : Int))) (H0 + 2) := by
      have h15 : 15 * 3 ^ (H0 + 2) ≤ 1350 * 5 ^ H' := by
        have h1 := pow3_le_pow5_shift H'
        have h2 := Nat.mul_le_mul_left 405 h1
        have h3 : 15 * 3 ^ (H0 + 2) = 405 * 3 ^ H' := by
          dsimp only [H0]
          rw [show H' + 1 + 2 = H' + 3 by omega, Nat.pow_add]; grind
        have h4 : 405 * 5 ^ H' ≤ 1350 * 5 ^ H' :=
          Nat.mul_le_mul_right _ (by decide)
        exact Nat.le_trans (h3 ▸ h2) h4
      have htop15 := Nat.mul_le_mul_right (levelFree f n K (m + ((H0 + 2 : Nat) : Int))) h15
      have hprev :
          2 * convFree3 (fun h => levelFree f n K (m + (h : Int))) H0 +
            3 * 3 ^ (H0 + 2) * levelFree f n K (m + ((H0 + 1 : Nat) : Int)) ≤
          1350 * 5 ^ H' *
            levelSumH (fun h => levelFree f n K (m + (h : Int))) (H0 + 1) := by
        cases H' with
        | zero =>
          dsimp only [H0]
          rw [show (0 : Nat) + 1 = 1 by rfl, show (1 : Nat) + 1 = 2 by rfl,
            show (1 : Nat) + 2 = 3 by rfl, levelSumH_2]
          simp only [convFree3, Nat.pow_zero, Nat.mul_one]
          have hp3 : (3 : Nat) ^ 3 = 27 := by decide
          rw [hp3]
          omega
        | succ k =>
          dsimp only [H0]
          have ih3 := convFree3_le_uniform (fun h => levelFree f n K (m + (h : Int))) (k + 1) (by omega)
          have h5ih := Nat.mul_le_mul_left 10 ih3
          have hp5 : 10 * (675 * 5 ^ (k + 1 - 1) *
              levelSumH (fun h => levelFree f n K (m + (h : Int))) (k + 2)) =
              1350 * 5 ^ (k + 1) *
                levelSumH (fun h => levelFree f n K (m + (h : Int))) (k + 2) := by
            rw [show k + 1 - 1 = k by omega, Nat.pow_succ]; grind
          have hcoeff : 2 * (33 * 3 ^ (k + 3)) + 3 * 3 ^ (k + 4) ≤ 1350 * 5 ^ (k + 1) := by
            have h1 := pow3_le_pow5_shift (k + 1)
            have h2 := Nat.mul_le_mul_left 675 h1
            have h3 : 2 * (33 * 3 ^ (k + 3)) + 3 * 3 ^ (k + 4) = 675 * 3 ^ (k + 1) := by
              rw [show k + 3 = (k + 1) + 2 by omega, show k + 4 = (k + 1) + 3 by omega,
                Nat.pow_add, Nat.pow_add]; grind
            have h4 : 675 * 5 ^ (k + 1) ≤ 1350 * 5 ^ (k + 1) :=
              Nat.mul_le_mul_right _ (by decide)
            exact Nat.le_trans (h3 ▸ h2) h4
          have htop := Nat.mul_le_mul_right (levelFree f n K (m + ((k + 3 : Nat) : Int))) hcoeff
          have hcv : convFree3 (fun h => levelFree f n K (m + (h : Int))) (k + 1 + 1) =
              5 * convFree3 (fun h => levelFree f n K (m + (h : Int))) (k + 1) +
                33 * 3 ^ (k + 3) * levelFree f n K (m + ((k + 3 : Nat) : Int)) := rfl
          have hls2 : levelSumH (fun h => levelFree f n K (m + (h : Int))) (k + 1 + 1 + 1) =
              levelSumH (fun h => levelFree f n K (m + (h : Int))) (k + 2) +
                levelFree f n K (m + ((k + 3 : Nat) : Int)) := rfl
          rw [hcv, hls2, show k + 1 + 1 + 1 = k + 3 by omega, show k + 1 + 1 + 2 = k + 4 by omega,
            Nat.mul_add, Nat.mul_add]
          rw [show k + 1 + 1 = k + 2 by omega] at h5ih
          have htop' : 2 * (33 * 3 ^ (k + 3) * levelFree f n K (m + ((k + 3 : Nat) : Int))) +
              3 * 3 ^ (k + 4) * levelFree f n K (m + ((k + 3 : Nat) : Int)) ≤
              1350 * 5 ^ (k + 1) * levelFree f n K (m + ((k + 3 : Nat) : Int)) := by
            have hl : 2 * (33 * 3 ^ (k + 3) * levelFree f n K (m + ((k + 3 : Nat) : Int))) +
                3 * 3 ^ (k + 4) * levelFree f n K (m + ((k + 3 : Nat) : Int)) =
                (2 * (33 * 3 ^ (k + 3)) + 3 * 3 ^ (k + 4)) *
                  levelFree f n K (m + ((k + 3 : Nat) : Int)) := by grind
            rw [hl]; exact htop
          have h25 : 2 * (5 * convFree3 (fun h => levelFree f n K (m + (h : Int))) (k + 1)) =
              10 * convFree3 (fun h => levelFree f n K (m + (h : Int))) (k + 1) := by grind
          omega
      have hLS : levelSumH (fun h => levelFree f n K (m + (h : Int))) (H0 + 2) =
          levelSumH (fun h => levelFree f n K (m + (h : Int))) (H0 + 1) +
            levelFree f n K (m + ((H0 + 2 : Nat) : Int)) := rfl
      rw [hLS, Nat.mul_add]
      omega
    have hfr_mul := Nat.mul_le_mul_left (1350 * 5 ^ H') hfr
    have hS_bound : 15 * 3 ^ (H' + 3) * additions f n K ≤ 1350 * 5 ^ H' * free f n K := by
      have hmul := Nat.mul_le_mul_left (15 * 3 ^ (H' + 3)) htot
      dsimp only [H0] at hsc hcomb hfr_mul
      rw [show H' + 1 + 2 = H' + 3 by omega] at hsc hcomb hfr_mul
      exact Nat.le_trans hmul (Nat.le_trans hsc (Nat.le_trans hcomb hfr_mul))
    have h5s := Nat.mul_le_mul_left 5 hS_bound
    have hL : 5 * (15 * 3 ^ (H' + 3) * additions f n K) =
        3 * (25 * 3 ^ (H' + 3) * additions f n K) := by grind
    have hR : 5 * (1350 * 5 ^ H' * free f n K) =
        3 * (18 * 5 ^ (H' + 3) * free f n K) := by
      rw [Nat.pow_add]; grind
    omega

/-- Sharp arbitrary-depth `(1008/625) * (5/3)^d` low-addition weight bound for EVERY `d : Nat`:
  `(625 * 3 ^ d : Int) * lowAdditionWeights f n r K ≤ (1008 * 5 ^ d : Int) * free f n K`.
Proved from the exact zero-remainder weight identity
`8 * T(H + 1) + 3 * A_{H+2} + A_{H+1} = 3 * W(H + 2) + W(H)` and `convFree2`;
improves `E-797`'s `54/25 = 2.16` by `25%` to `1008/625 = 1.6128` (within `3.5%` of the LP limit). -/
theorem sharp_five_thirds_low_weights_bound (f : Nat → Bool) (n a K d : Nat) (m r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) (hr : r ≤ m + (d : Int)) :
    ((625 * 3 ^ d : Nat) : Int) * lowAdditionWeights f n r K ≤
      ((1008 * 5 ^ d : Nat) : Int) * (free f n K : Int) := by
  obtain ⟨hE0, hE1, hE2⟩ := level_floor_basics f n a K m hw hpre hfloor
  have hA0 := level_additions_split_h f n K (m + ((0 : Nat) : Int))
  have hA1 := level_additions_split_h f n K (m + ((1 : Nat) : Int))
  have hA2 := level_additions_split_h f n K (m + ((2 : Nat) : Int))
  match d with
  | 0 =>
    have hz := lowAdditionWeights_zero_below f n m r (by omega) K hfloor
    rw [hz, Int.mul_zero]
    exact Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  | 1 =>
    have hmono := lowAdditionWeights_mono_h f n r (m + ((0 : Nat) : Int) + 1) (by omega) K
    have hW := lowAdditionWeights_eq_levelWeightSumH f n K m hfloor 0
    have hfr := levelSumH_free_le_free f n K m 0
    rw [levelWeightSumH_0] at hW
    simp only [levelSumH] at hfr
    have h1 : lowAdditionWeights f n r K ≤ (free f n K : Int) := by omega
    have hmul := Int.mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg (625 * 3 ^ 1))
    have hc : ((625 * 3 ^ 1 : Nat) : Int) ≤ ((1008 * 5 ^ 1 : Nat) : Int) := by decide
    exact Int.le_trans hmul (Int.mul_le_mul_of_nonneg_right hc (Int.natCast_nonneg _))
  | 2 =>
    have hmono := lowAdditionWeights_mono_h f n r (m + ((1 : Nat) : Int) + 1) (by omega) K
    have hW := lowAdditionWeights_eq_levelWeightSumH f n K m hfloor 1
    have hfr := levelSumH_free_le_free f n K m 1
    rw [levelWeightSumH_1] at hW
    rw [levelSumH_1] at hfr
    have h1 : lowAdditionWeights f n r K ≤ 3 * (free f n K : Int) := by omega
    have hmul := Int.mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg (625 * 3 ^ 2))
    have hc : ((625 * 3 ^ 2 * 3 : Nat) : Int) ≤ ((1008 * 5 ^ 2 : Nat) : Int) := by decide
    have h2 : ((625 * 3 ^ 2 : Nat) : Int) * (3 * (free f n K : Int)) =
        ((625 * 3 ^ 2 * 3 : Nat) : Int) * (free f n K : Int) := by
      have hp : ((625 * 3 ^ 2 * 3 : Nat) : Int) = ((625 * 3 ^ 2 : Nat) : Int) * 3 := by decide
      rw [hp]; grind
    exact Int.le_trans hmul (h2 ▸ Int.mul_le_mul_of_nonneg_right hc (Int.natCast_nonneg _))
  | 3 =>
    have hmono := lowAdditionWeights_mono_h f n r (m + ((2 : Nat) : Int) + 1) (by omega) K
    have hW := lowAdditionWeights_eq_levelWeightSumH f n K m hfloor 2
    have hfr := levelSumH_free_le_free f n K m 2
    rw [levelWeightSumH_2] at hW
    rw [levelSumH_2] at hfr
    have h1 : lowAdditionWeights f n r K ≤ 6 * (free f n K : Int) := by omega
    have hmul := Int.mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg (625 * 3 ^ 3))
    have hc : ((625 * 3 ^ 3 * 6 : Nat) : Int) ≤ ((1008 * 5 ^ 3 : Nat) : Int) := by decide
    have h2 : ((625 * 3 ^ 3 : Nat) : Int) * (6 * (free f n K : Int)) =
        ((625 * 3 ^ 3 * 6 : Nat) : Int) * (free f n K : Int) := by
      have hp : ((625 * 3 ^ 3 * 6 : Nat) : Int) = ((625 * 3 ^ 3 : Nat) : Int) * 6 := by decide
      rw [hp]; grind
    exact Int.le_trans hmul (h2 ▸ Int.mul_le_mul_of_nonneg_right hc (Int.natCast_nonneg _))
  | H' + 4 =>
    let H := H' + 1
    have hmono := lowAdditionWeights_mono_h f n r (m + ((H + 2 : Nat) : Int) + 1) (by omega) K
    have hW2 := lowAdditionWeights_eq_levelWeightSumH f n K m hfloor (H + 2)
    have hinv := convFree2_invariant f n a K m hw hpre hfloor H
    have hb := actual_double_ascent_spacing_budget f n a K 0 (m + (H : Int) + 1) (by omega) hw hpre
    have hW0 := lowAdditionWeights_eq_levelWeightSumH f n K m hfloor H
    rw [hW0] at hb
    have hrm1 : m + (H : Int) + 1 - 1 = m + (H : Int) := by omega
    have hr1 : m + (H : Int) + 1 + 1 = m + ((H + 2 : Nat) : Int) := by omega
    have hr0 : m + (H : Int) + 1 = m + ((H + 1 : Nat) : Int) := by omega
    rw [hrm1, hr1, hr0] at hb
    have hsp2 := level_additions_split_h f n K (m + ((H + 2 : Nat) : Int))
    have hsp1 := level_additions_split_h f n K (m + ((H + 1 : Nat) : Int))
    have hstepA :
        3 * levelAdditions f n K (m + ((H + 2 : Nat) : Int)) +
          levelAdditions f n K (m + ((H + 1 : Nat) : Int)) ≤
        levelWeightSumH (fun j => levelAdditions f n K (m + (j : Int))) H +
          3 * doubleAscent f n K (m + (H : Int)) +
          3 * levelFree f n K (m + ((H + 2 : Nat) : Int)) +
          levelFree f n K (m + ((H + 1 : Nat) : Int)) := by omega
    have h8inv := Nat.mul_le_mul_left 8 hinv
    have h5st := Nat.mul_le_mul_left (5 * 3 ^ (H + 2)) hstepA
    have hid := triSumH_weight_ident (fun j => levelAdditions f n K (m + (j : Int))) H
    have hidM := congrArg (fun x => 5 * 3 ^ (H + 2) * x) hid
    unfold triAdditionsH at hinv h8inv
    have hT : 8 * (5 * 3 ^ (H + 2) * triSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 1)) +
        5 * 3 ^ (H + 2) * (3 * levelAdditions f n K (m + ((H + 2 : Nat) : Int))) +
        5 * 3 ^ (H + 2) * levelAdditions f n K (m + ((H + 1 : Nat) : Int)) =
        15 * 3 ^ (H + 2) * levelWeightSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 2) +
          5 * 3 ^ (H + 2) * levelWeightSumH (fun j => levelAdditions f n K (m + (j : Int))) H := by
      have hL : 8 * (5 * 3 ^ (H + 2) * triSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 1)) +
          5 * 3 ^ (H + 2) * (3 * levelAdditions f n K (m + ((H + 2 : Nat) : Int))) +
          5 * 3 ^ (H + 2) * levelAdditions f n K (m + ((H + 1 : Nat) : Int)) =
          5 * 3 ^ (H + 2) * (8 * triSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 1) +
            3 * levelAdditions f n K (m + ((H + 2 : Nat) : Int)) +
            levelAdditions f n K (m + ((H + 1 : Nat) : Int))) := by grind
      rw [hL, hidM]; grind
    have hAA_ge : 5 * 3 ^ (H + 2) * (3 * doubleAscent f n K (m + (H : Int))) ≤
        8 * (5 * 3 ^ (H + 2) * doubleAscent f n K (m + (H : Int))) := by
      have hle : 15 * 3 ^ (H + 2) ≤ 40 * 3 ^ (H + 2) := by omega
      have hm := Nat.mul_le_mul_right (doubleAscent f n K (m + (H : Int))) hle
      grind
    have hF1_ge : 5 * 3 ^ (H + 2) * levelFree f n K (m + ((H + 1 : Nat) : Int)) ≤
        8 * (3 ^ (H + 2) * levelFree f n K (m + ((H + 1 : Nat) : Int))) := by
      have hle : 5 * 3 ^ (H + 2) ≤ 8 * 3 ^ (H + 2) := by omega
      have hm := Nat.mul_le_mul_right (levelFree f n K (m + ((H + 1 : Nat) : Int))) hle
      grind
    have hF2_eq : 5 * 3 ^ (H + 2) * (3 * levelFree f n K (m + ((H + 2 : Nat) : Int))) =
        15 * 3 ^ (H + 2) * levelFree f n K (m + ((H + 2 : Nat) : Int)) := by grind
    simp only [Nat.mul_add] at h8inv h5st
    have hWconv : 15 * 3 ^ (H + 2) *
        levelWeightSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 2) ≤
        8 * convFree2 (fun h => levelFree f n K (m + (h : Int))) H +
          15 * 3 ^ (H + 2) * levelFree f n K (m + ((H + 2 : Nat) : Int)) := by
      clear hE0 hE1 hE2 hA0 hA1 hA2 hmono hW2 hinv hb hW0 hrm1 hr1 hr0 hsp2 hsp1 hstepA hid hidM
      omega
    have hcu := convFree2_le_uniform (fun h => levelFree f n K (m + (h : Int))) H (by omega)
    have h8cu := Nat.mul_le_mul_left 8 hcu
    have h15 : 15 * 3 ^ (H + 2) ≤ 5040 * 5 ^ (H - 1) := by
      have h1 := pow3_le_pow5_shift (H - 1)
      have h2 := Nat.mul_le_mul_left 405 h1
      have h3 : 15 * 3 ^ (H + 2) = 405 * 3 ^ (H - 1) := by
        rw [show H + 2 = (H - 1) + 3 by omega, Nat.pow_add]; grind
      have h4 : 405 * 5 ^ (H - 1) ≤ 5040 * 5 ^ (H - 1) :=
        Nat.mul_le_mul_right _ (by decide)
      exact Nat.le_trans (h3 ▸ h2) h4
    have htop := Nat.mul_le_mul_right (levelFree f n K (m + ((H + 2 : Nat) : Int))) h15
    have hfr := levelSumH_free_le_free f n K m (H + 2)
    have hLS : levelSumH (fun h => levelFree f n K (m + (h : Int))) (H + 2) =
        levelSumH (fun h => levelFree f n K (m + (h : Int))) (H + 1) +
          levelFree f n K (m + ((H + 2 : Nat) : Int)) := rfl
    have hW_nat : 15 * 3 ^ (H + 2) *
        levelWeightSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 2) ≤
        5040 * 5 ^ (H - 1) * free f n K := by
      have h1 : 8 * (630 * 5 ^ (H - 1) *
          levelSumH (fun h => levelFree f n K (m + (h : Int))) (H + 1)) =
          5040 * 5 ^ (H - 1) *
            levelSumH (fun h => levelFree f n K (m + (h : Int))) (H + 1) := by grind
      have h2 := Nat.mul_le_mul_left (5040 * 5 ^ (H - 1)) hfr
      rw [hLS, Nat.mul_add] at h2
      omega
    have hfinalNat : 625 * 3 ^ (H' + 4) *
        levelWeightSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 2) ≤
        1008 * 5 ^ (H' + 4) * free f n K := by
      have h1 := Nat.mul_le_mul_left 125 hW_nat
      have hL : 125 * (15 * 3 ^ (H + 2) *
          levelWeightSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 2)) =
          625 * 3 ^ (H' + 4) *
            levelWeightSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 2) := by
        dsimp only [H]
        rw [show H' + 4 = (H' + 1 + 2) + 1 by omega, Nat.pow_succ]; grind
      have hR : 125 * (5040 * 5 ^ (H - 1) * free f n K) =
          1008 * 5 ^ (H' + 4) * free f n K := by
        dsimp only [H]
        rw [show H' + 1 - 1 = H' by omega, Nat.pow_add]; grind
      omega
    have hcast : ((625 * 3 ^ (H' + 4) : Nat) : Int) *
        (levelWeightSumH (fun j => levelAdditions f n K (m + (j : Int))) (H + 2) : Int) ≤
        ((1008 * 5 ^ (H' + 4) : Nat) : Int) * (free f n K : Int) := by
      exact_mod_cast hfinalNat
    have hm_int := Int.mul_le_mul_of_nonneg_left hmono (Int.natCast_nonneg (625 * 3 ^ (H' + 4)))
    rw [hW2] at hm_int
    exact Int.le_trans hm_int hcast

/-- Sharp `(1008/625) * (5/3)^d` arbitrary-depth free-gap square inequality WITHOUT `hpos`
and WITHOUT any height ceiling:
  `(625 * 3 ^ d : Int) * (j + 1)^2 ≤ (1008 * 5 ^ d : Int) * free f n (b - n)`. -/
theorem sharp_five_thirds_free_gap_square (f : Nat → Bool) (n a b j d : Nat) (m : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hnb : n < b) (hfloor : ∀ i, n ≤ i → i ≤ b → m ≤ Fw f i)
    (hS : ∀ i, b ≤ i → i < b + j → f i = false) (he : EndN f 0 (b + j))
    (hTarget : Fw f (b + j) ≤ m + (d : Int) + 1) :
    ((625 * 3 ^ d : Nat) : Int) * ((j : Int) + 1) ^ 2 ≤
      ((1008 * 5 ^ d : Nat) : Int) * (free f n (b - n) : Int) := by
  have hs := supplied_gap_square_low_additions f n a b j hw hpre hnb hS he
  have hl := sharp_five_thirds_low_weights_bound f n a (b - n) d m (Fw f (b + j) - 1)
    hw hpre (fun i hi hj => hfloor i hi (by omega)) (by omega)
  have h1 := Int.mul_le_mul_of_nonneg_left hs (Int.natCast_nonneg (625 * 3 ^ d))
  exact Int.le_trans h1 hl

/-! ## Sharp finite-depth `D = 7` (`56/3 * free`, `j ≤ 16`) and `D = 8` (`32 * free`, `j ≤ 29`) compressions -/

/-- Sharp depth-7 low-addition weight bound (`r ≤ m + 5`):
  `3 * lowAdditionWeights f n r K ≤ 56 * free f n K`,
strictly improving `E-787`'s `59 * free` via the exact `(5, 3, 1)` dual combination of
`E-792` (`r = 2, 4`) and `E-794` (`r = 3`). -/
theorem sharp_depth_seven_low_weights (f : Nat → Bool) (n a K : Nat) (m r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) (hr : r ≤ m + 5) :
    3 * lowAdditionWeights f n r K ≤ 56 * (free f n K : Int) := by
  obtain ⟨hE0, hE1, hE2⟩ := level_floor_basics f n a K m hw hpre hfloor
  have hA0 := level_additions_split_h f n K (m + ((0 : Nat) : Int))
  have hA1 := level_additions_split_h f n K (m + ((1 : Nat) : Int))
  have hA2 := level_additions_split_h f n K (m + ((2 : Nat) : Int))
  have hA3 := level_additions_split_h f n K (m + ((3 : Nat) : Int))
  have hA4 := level_additions_split_h f n K (m + ((4 : Nat) : Int))
  have hAA1 := doubleAscent_le_additions_h f n K (m + ((1 : Nat) : Int))
  have hAA2 := doubleAscent_le_additions_h f n K (m + ((2 : Nat) : Int))
  have hb3 := actual_double_ascent_spacing_budget f n a K 0 (m + 2) (by omega) hw hpre
  have hW1 := lowAdditionWeights_eq_levelWeightSumH f n K m hfloor 1
  rw [show m + ((1 : Nat) : Int) + 1 = m + 2 by omega, levelWeightSumH_1] at hW1
  rw [hW1] at hb3
  have hb4 := same_height_supply_aa_spacing_budget f n a K (m + 3) hw hpre
  have hW2 := lowAdditionWeights_eq_levelWeightSumH f n K m hfloor 2
  rw [show m + ((2 : Nat) : Int) + 1 = m + 3 by omega, levelWeightSumH_2] at hW2
  rw [hW2] at hb4
  change ((3 * levelSupplied f n K (m + 3 + 1) : Nat) : Int) ≤ _ at hb4
  have hmono := lowAdditionWeights_mono_h f n r (m + ((4 : Nat) : Int) + 1) (by omega) K
  have hW4 := lowAdditionWeights_eq_levelWeightSumH f n K m hfloor 4
  rw [levelWeightSumH_4] at hW4
  have hfr := levelSumH_free_le_free f n K m 4
  rw [levelSumH_4] at hfr
  have h2_1 : m + 2 - 1 = m + ((1 : Nat) : Int) := by omega
  have h2_2 : m + 2 = m + ((2 : Nat) : Int) := by omega
  have h2_3 : m + 2 + 1 = m + ((3 : Nat) : Int) := by omega
  have h3_2 : m + 3 - 1 = m + ((2 : Nat) : Int) := by omega
  have h3_4 : m + 3 + 1 = m + ((4 : Nat) : Int) := by omega
  rw [h2_1, h2_3, h2_2] at hb3
  rw [h3_2, h3_4] at hb4
  -- Explicit (5, 3, 1) dual linear combination of E_2 <= F_0, hb3, and hb4:
  have hE3 : (3 * levelSupplied f n K (m + ((3 : Nat) : Int)) +
      levelSupplied f n K (m + ((2 : Nat) : Int)) : Int) ≤
      3 * (levelFree f n K (m + ((0 : Nat) : Int)) : Int) +
        4 * (levelFree f n K (m + ((1 : Nat) : Int)) : Int) := by omega
  have hE4 : (3 * levelSupplied f n K (m + ((4 : Nat) : Int)) : Int) ≤
      5 * (levelFree f n K (m + ((0 : Nat) : Int)) : Int) +
        3 * (levelFree f n K (m + ((1 : Nat) : Int)) : Int) +
        3 * (levelSupplied f n K (m + ((2 : Nat) : Int)) : Int) +
        3 * (levelFree f n K (m + ((2 : Nat) : Int)) : Int) := by omega
  have hW_bound : 3 * lowAdditionWeights f n (m + ((4 : Nat) : Int) + 1) K ≤
      56 * (levelFree f n K (m + ((0 : Nat) : Int)) : Int) +
        36 * (levelFree f n K (m + ((1 : Nat) : Int)) : Int) +
        18 * (levelFree f n K (m + ((2 : Nat) : Int)) : Int) +
        9 * (levelFree f n K (m + ((3 : Nat) : Int)) : Int) +
        3 * (levelFree f n K (m + ((4 : Nat) : Int)) : Int) := by
    rw [hW4]
    omega
  omega

/-- Sharp depth-7 positive-deficit counterexample profile (strictly tightening `E-787` from
`j ≤ 17` down to `j ≤ 16`): every depth-7 positive-deficit counterexample (`free ≤ j`) obeys
`4 ≤ free`, `j ≤ 16`, `Fw f (b + j) ≤ Fw f n - 1`, and `3 * (j + 1)^2 ≤ 56 * free`. -/
theorem sharp_depth_seven_counter_profile (f : Nat → Bool) (n a b j : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hnb : n < b) (hfloor : ∀ i, n ≤ i → i ≤ b → Fw f n - 7 ≤ Fw f i)
    (hpos : ∀ k, 0 < k → k ≤ b - n → cN (EndN f 0) n k + 1 ≤ cN (fun i => f i = false) n k)
    (hS : ∀ i, b ≤ i → i < b + j → f i = false) (he : EndN f 0 (b + j))
    (hcounter : free f n (b - n) ≤ j) :
    4 ≤ free f n (b - n) ∧
      j ≤ 16 ∧
      Fw f (b + j) ≤ Fw f n - 1 ∧
      3 * ((j : Int) + 1) ^ 2 ≤ 56 * (free f n (b - n) : Int) := by
  have hprof := positive_depth_seven_counter_profile f n a b j hw hpre hnb hfloor hpos hS he hcounter
  have hs := supplied_gap_square_low_additions f n a b j hw hpre hnb hS he
  have hl := sharp_depth_seven_low_weights f n a (b - n) (Fw f n - 7) (Fw f (b + j) - 1)
    hw hpre (fun i hi hj => hfloor i hi (by omega)) (by omega)
  have h3sq : 3 * ((j : Int) + 1) ^ 2 ≤ 56 * (free f n (b - n) : Int) := by omega
  have hj16 : j ≤ 16 := by
    by_cases h : j ≤ 16
    · exact h
    · have hj17 : j = 17 := by omega
      subst hj17
      have hsq_val : (3 : Int) * ((17 : Nat) + 1 : Int) ^ 2 = 972 := by decide
      rw [hsq_val] at h3sq
      omega
  exact ⟨hprof.1, hj16, hprof.2.2.1, h3sq⟩

/-- Sharp depth-8 low-addition weight bound (`r ≤ m + 6`):
  `lowAdditionWeights f n r K ≤ 32 * free f n K`.
Proved from the exact LP-optimal `(400, 213, 27, 120, 45)` integer dual combination combining
`E-792` (`r = 2, 4`), `E-794` (`r = 3, 5`), and `E-797`'s 8-slot `δ = 5` budget (`r = 3`);
cuts `E-787`'s `64 * free` in HALF and beats `E-797`'s `46.3 * free` by `31%`. -/
theorem sharp_depth_eight_low_weights (f : Nat → Bool) (n a K : Nat) (m r : Int)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i) (hr : r ≤ m + 6) :
    lowAdditionWeights f n r K ≤ 32 * (free f n K : Int) := by
  obtain ⟨hE0, hE1, hE2⟩ := level_floor_basics f n a K m hw hpre hfloor
  have hA0 := level_additions_split_h f n K (m + ((0 : Nat) : Int))
  have hA1 := level_additions_split_h f n K (m + ((1 : Nat) : Int))
  have hA2 := level_additions_split_h f n K (m + ((2 : Nat) : Int))
  have hA3 := level_additions_split_h f n K (m + ((3 : Nat) : Int))
  have hA4 := level_additions_split_h f n K (m + ((4 : Nat) : Int))
  have hA5 := level_additions_split_h f n K (m + ((5 : Nat) : Int))
  have hAA1 := doubleAscent_le_additions_h f n K (m + ((1 : Nat) : Int))
  have hAA2 := doubleAscent_le_additions_h f n K (m + ((2 : Nat) : Int))
  have hAA3 := doubleAscent_le_supplied_add_free_h f n K (m + ((3 : Nat) : Int))
  have hb3_0 := actual_double_ascent_spacing_budget f n a K 0 (m + 2) (by omega) hw hpre
  have hb3_5 := actual_eight_slot_double_ascent_budget f n a K (m + 2) hw hpre
  have hW1 := lowAdditionWeights_eq_levelWeightSumH f n K m hfloor 1
  rw [show m + ((1 : Nat) : Int) + 1 = m + 2 by omega, levelWeightSumH_1] at hW1
  rw [hW1] at hb3_0 hb3_5
  have hb4 := same_height_supply_aa_spacing_budget f n a K (m + 3) hw hpre
  have hW2 := lowAdditionWeights_eq_levelWeightSumH f n K m hfloor 2
  rw [show m + ((2 : Nat) : Int) + 1 = m + 3 by omega, levelWeightSumH_2] at hW2
  rw [hW2] at hb4
  change ((3 * levelSupplied f n K (m + 3 + 1) : Nat) : Int) ≤ _ at hb4
  have hb5 := actual_double_ascent_spacing_budget f n a K 0 (m + 4) (by omega) hw hpre
  have hW3 := lowAdditionWeights_eq_levelWeightSumH f n K m hfloor 3
  rw [show m + ((3 : Nat) : Int) + 1 = m + 4 by omega, levelWeightSumH_3] at hW3
  rw [hW3] at hb5
  have hmono := lowAdditionWeights_mono_h f n r (m + ((5 : Nat) : Int) + 1) (by omega) K
  have hW5 := lowAdditionWeights_eq_levelWeightSumH f n K m hfloor 5
  rw [levelWeightSumH_5] at hW5
  have hfr := levelSumH_free_le_free f n K m 5
  rw [levelSumH_5] at hfr
  have h2_1 : m + 2 - 1 = m + ((1 : Nat) : Int) := by omega
  have h2_2 : m + 2 = m + ((2 : Nat) : Int) := by omega
  have h2_3 : m + 2 + 1 = m + ((3 : Nat) : Int) := by omega
  have h3_2 : m + 3 - 1 = m + ((2 : Nat) : Int) := by omega
  have h3_4 : m + 3 + 1 = m + ((4 : Nat) : Int) := by omega
  have h4_3 : m + 4 - 1 = m + ((3 : Nat) : Int) := by omega
  have h4_4 : m + 4 = m + ((4 : Nat) : Int) := by omega
  have h4_5 : m + 4 + 1 = m + ((5 : Nat) : Int) := by omega
  rw [h2_1, h2_3, h2_2] at hb3_0 hb3_5
  rw [h3_2, h3_4] at hb4
  rw [h4_3, h4_5, h4_4] at hb5
  -- Explicit LP-optimal (400, 213, 27, 120, 45) integer dual combination:
  have hd3_0 : (3 * levelSupplied f n K (m + ((3 : Nat) : Int)) +
      levelSupplied f n K (m + ((2 : Nat) : Int)) : Int) ≤
      3 * (levelFree f n K (m + ((0 : Nat) : Int)) : Int) +
        4 * (levelFree f n K (m + ((1 : Nat) : Int)) : Int) := by omega
  have hd3_5 : (3 * levelSupplied f n K (m + ((3 : Nat) : Int)) +
      5 * suppliedDoubleAscent f n K (m + ((3 : Nat) : Int)) +
      levelSupplied f n K (m + ((2 : Nat) : Int)) : Int) ≤
      3 * (levelFree f n K (m + ((0 : Nat) : Int)) : Int) +
        9 * (levelFree f n K (m + ((1 : Nat) : Int)) : Int) := by omega
  have hd4 : (3 * levelSupplied f n K (m + ((4 : Nat) : Int)) : Int) ≤
      5 * (levelFree f n K (m + ((0 : Nat) : Int)) : Int) +
        3 * (levelFree f n K (m + ((1 : Nat) : Int)) : Int) +
        3 * (levelSupplied f n K (m + ((2 : Nat) : Int)) : Int) +
        3 * (levelFree f n K (m + ((2 : Nat) : Int)) : Int) := by omega
  have hd5 : (3 * levelSupplied f n K (m + ((5 : Nat) : Int)) +
      levelSupplied f n K (m + ((4 : Nat) : Int)) : Int) ≤
      7 * (levelFree f n K (m + ((0 : Nat) : Int)) : Int) +
        5 * (levelFree f n K (m + ((1 : Nat) : Int)) : Int) +
        3 * (levelSupplied f n K (m + ((2 : Nat) : Int)) : Int) +
        3 * (levelFree f n K (m + ((2 : Nat) : Int)) : Int) +
        (levelSupplied f n K (m + ((3 : Nat) : Int)) : Int) +
        4 * (levelFree f n K (m + ((3 : Nat) : Int)) : Int) +
        3 * (suppliedDoubleAscent f n K (m + ((3 : Nat) : Int)) : Int) := by omega
  have hcomb : 135 * lowAdditionWeights f n (m + ((5 : Nat) : Int) + 1) K ≤
      4320 * (levelFree f n K (m + ((0 : Nat) : Int)) : Int) +
        2895 * (levelFree f n K (m + ((1 : Nat) : Int)) : Int) +
        1440 * (levelFree f n K (m + ((2 : Nat) : Int)) : Int) +
        855 * (levelFree f n K (m + ((3 : Nat) : Int)) : Int) +
        405 * (levelFree f n K (m + ((4 : Nat) : Int)) : Int) +
        135 * (levelFree f n K (m + ((5 : Nat) : Int)) : Int) := by
    rw [hW5]
    have h400 : 400 * (3 * (levelSupplied f n K (m + ((2 : Nat) : Int)) : Int)) ≤
        400 * (3 * (levelFree f n K (m + ((0 : Nat) : Int)) : Int)) := by omega
    have h213 := Int.mul_le_mul_of_nonneg_left hd3_0 (by decide : (0 : Int) ≤ 213)
    have h27 := Int.mul_le_mul_of_nonneg_left hd3_5 (by decide : (0 : Int) ≤ 27)
    have h120 := Int.mul_le_mul_of_nonneg_left hd4 (by decide : (0 : Int) ≤ 120)
    have h45 := Int.mul_le_mul_of_nonneg_left hd5 (by decide : (0 : Int) ≤ 45)
    have hWexp : 135 * (levelWeightSumH (fun j => levelAdditions f n K (m + (j : Int))) 5 : Int) =
        1485 * (levelFree f n K (m + ((0 : Nat) : Int)) : Int) +
          1215 * (levelFree f n K (m + ((1 : Nat) : Int)) : Int) +
          945 * (levelSupplied f n K (m + ((2 : Nat) : Int)) : Int) +
          945 * (levelFree f n K (m + ((2 : Nat) : Int)) : Int) +
          675 * (levelSupplied f n K (m + ((3 : Nat) : Int)) : Int) +
          675 * (levelFree f n K (m + ((3 : Nat) : Int)) : Int) +
          405 * (levelSupplied f n K (m + ((4 : Nat) : Int)) : Int) +
          405 * (levelFree f n K (m + ((4 : Nat) : Int)) : Int) +
          135 * (levelSupplied f n K (m + ((5 : Nat) : Int)) : Int) +
          135 * (levelFree f n K (m + ((5 : Nat) : Int)) : Int) := by
      rw [levelWeightSumH_5]
      push_cast [hA0, hA1, hA2, hA3, hA4, hA5, hE0, hE1]
      grind
    rw [levelWeightSumH_5] at hWexp
    clear hE0 hE1 hE2 hA0 hA1 hA2 hA3 hA4 hA5 hAA1 hAA2 hAA3 hb3_0 hb3_5 hW1 hb4 hW2 hb5 hW3 hmono hW5 hfr h2_1 h2_2 h2_3 h3_2 h3_4 h4_3 h4_4 h4_5 hd3_0 hd3_5 hd4 hd5
    omega
  clear hE0 hE1 hE2 hA0 hA1 hA2 hA3 hA4 hA5 hAA1 hAA2 hAA3 hb3_0 hb3_5 hW1 hb4 hW2 hb5 hW3 hW5 h2_1 h2_2 h2_3 h3_2 h3_4 h4_3 h4_4 h4_5 hd3_0 hd3_5 hd4 hd5
  omega

/-- Sharp depth-8 positive-deficit counterexample profile: every depth-8 positive-deficit
counterexample (`free ≤ j`) obeys `4 ≤ free`, `j ≤ 29`, `Fw f (b + j) ≤ Fw f n - 1`, and
`(j + 1)^2 ≤ 32 * free` (cutting `E-787`'s `j ≤ 61` in half). -/
theorem sharp_depth_eight_counter_profile (f : Nat → Bool) (n a b j : Nat)
    {w : List Bool} (hw : BlockWord w) (hpre : seg f 0 n = w ++ List.replicate a true)
    (hnb : n < b) (hfloor : ∀ i, n ≤ i → i ≤ b → Fw f n - 8 ≤ Fw f i)
    (hpos : ∀ k, 0 < k → k ≤ b - n → cN (EndN f 0) n k + 1 ≤ cN (fun i => f i = false) n k)
    (hS : ∀ i, b ≤ i → i < b + j → f i = false) (he : EndN f 0 (b + j))
    (hcounter : free f n (b - n) ≤ j) :
    4 ≤ free f n (b - n) ∧
      j ≤ 29 ∧
      Fw f (b + j) ≤ Fw f n - 1 ∧
      ((j : Int) + 1) ^ 2 ≤ 32 * (free f n (b - n) : Int) := by
  have hprof := positive_arbitrary_depth_free_gap_profile f n a b j 8 hw hpre hnb (by omega)
    hfloor hpos hS he hcounter
  have hs := supplied_gap_square_low_additions f n a b j hw hpre hnb hS he
  have hl := sharp_depth_eight_low_weights f n a (b - n) (Fw f n - 8) (Fw f (b + j) - 1)
    hw hpre (fun i hi hj => hfloor i hi (by omega)) (by omega)
  have hsq : ((j : Int) + 1) ^ 2 ≤ 32 * (free f n (b - n) : Int) := Int.le_trans hs hl
  have hj29 : j ≤ 29 := by
    by_cases h : j ≤ 29
    · exact h
    · have h30 : (30 : Int) ≤ (j : Int) := by omega
      have hmul : (32 : Int) * (free f n (b - n) : Int) ≤ 32 * (j : Int) := by omega
      have hsq' : ((j : Int) + 1) ^ 2 ≤ 32 * (j : Int) := Int.le_trans hsq hmul
      have hquad : 0 ≤ ((j : Int) - 30) * ((j : Int) - 30) :=
        Int.mul_nonneg (by omega) (by omega)
      have hexp : ((j : Int) + 1) ^ 2 =
          32 * (j : Int) + ((j : Int) - 30) * ((j : Int) - 30) + 30 * ((j : Int) - 30) + 1 := by
        grind
      omega
  exact ⟨hprof.1, hj29, hprof.2.2.1, hsq⟩

end Recaman.HeightConvolutionCapacity
