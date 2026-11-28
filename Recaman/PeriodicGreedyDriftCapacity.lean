import Recaman.CoherentGreedyFreshness
import Recaman.ExactFiveThirdsCapacity

namespace Recaman.PeriodicGreedyDriftCapacity

open Recaman Recaman.SeededReplay Recaman.CoherentGreedyFreshness
open Recaman.ExactFiveThirdsCapacity Recaman.ExcursionClimbSpacing
open Recaman.SupplyExcursionSpacing Recaman.FloorSupplyPotential
open Recaman.LevelTriangleArea Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction
open Recaman.CrossBlockReuseUnbounded Recaman.LineCapacityPeriodic
open Recaman.LeadingRunSupply
open Recaman.ShortPeriodicSupply (sign)
open Classical

/-! # Periodic drift dichotomy, `TypeIIFresh` residue-order obstruction, and golden-ratio capacity (`E-806`)

Extends `E-798` (`CoherentGreedyFreshness`) and `E-797` (`ExactFiveThirdsCapacity`) from
unit-drift (`|d| = 1`) to **every** drift `d = wordPotDrift V r : Int` and **arbitrary**
excursion depth `H` on every coherent finite-state greedy replay `SeededReplay.run b st`
(`st.value ∈ st.seen`) and on the canonical clock-0 Recamán orbit `Recaman.Basic.a`:

1. **Exact balanced word area-potential duality**: for every balanced word `V` (`mass V = 0`)
   and every relative height `r : Int`,
   - `wordSLandings V r = wordLevelAdditions V r`, and
   - `wordLowWeights V r + wordPotDrift V r = wordLevelAdditions V r + 3 * wordLevelAdditions V (r + 1) + wordUpperExcess V r`.

2. **Negative-drift golden-ratio law (`d ≤ 0`)**: whenever `wordPotDrift V r ≤ 0` and
   `repeatWord R V` occurs in any coherent `SeededReplay.run b st` (or `Recaman.Basic.a`),
   - `(R : Int) * (3 * A_{r+1}(V) + 2 * A_r(V)) + (R : Int) * upperExcess(V, r) ≤ (R : Int) * W(r)(V) + span(V, r) + |d| + 1`,
   - and for `R ≥ span(V, r) + |d| + 2`, the exact zero-error integer inequality
     `3 * A_{r+1}(V) + 2 * A_r(V) + upperExcess(V, r) ≤ W(r)(V)` holds unconditionally
     (characteristic root `φ = (1 + √5)/2 ≈ 1.618034 < 5/3`, and zero exponential growth
     above the unique sign-flip height `r*`).

3. **`TypeIIFresh` periodic residue-order obstruction and negative-drift `(AS)^a S` ceiling**:
   for every `SeededReplay.run b st` (even without coherence) and `Recaman.Basic.a`, whenever
   `d = wordPotDrift V r ≠ 0` and `R ≥ span(V, r) + 1`, every `S`-landing `t` at height `r`
   and every `A`-step `u` at height `r + 1` with `|d| ∣ (Φ_r(t + 1) - Φ_r(u))` obey:
   - `d < 0 → Φ_r(t + 1) ≤ Φ_r(u)` (and `t < u` on equality),
   - `0 < d → Φ_r(u) ≤ Φ_r(t + 1)` (and `t < u` on equality).
   In particular, every negative-drift `(AS)^a S` top-arch run at height `r + 1` satisfies
   `∀ k ∈ [1, a], ¬(|d| ∣ 3 * k)`, hence `a < |d|` and `(3 ∣ d) → 3 * a < |d|`.

4. **Positive-drift arbitrary-`d` top-level collapse (`d ≥ 0`) & sign-free golden-ratio law**:
   for every balanced `V` of max addition height `≤ H` repeated `R ≥ 1` times inside any
   coherent `SeededReplay.run b st` (or `Recaman.Basic.a`, with NO `BlockWord` prefix assumption):
   - When `0 ≤ wordPotDrift V (H - 1)` (arbitrary positive drift, not merely `|d| = 1`):
     `E_{H-1}(V^R) ≤ 3 * F_H(V^R) + 3 * AA_{H-2}(V^R) + span + |d| + 1 + prefixSlack`.
   - Unconditionally for ALL drifts `d : Int` (sign-free):
     `3 * E_H(V^R) + 2 * E_{H-1}(V^R) ≤ W(H - 1)(V^R) + 6 * AA_{H-2}(V^R) + 3 * F_H(V^R) + span + |d| + 1 + 2 * prefixSlack`.
   Raw non-fresh `E-786` (`d = 0`) violates both the negative-drift and sign-free bounds
   unboundedly as `R → ∞`.
-/

/-! ## Word-level addition counts, low-addition weights, and upper excess -/

/-- Prefix count of `A`-steps in `V` starting at relative height `h` over indices `< k`. -/
def wordLevelAdditionsUpTo (V : List Bool) (h : Int) : Nat → Nat
  | 0 => 0
  | k + 1 => wordLevelAdditionsUpTo V h k +
      if V[k]! = true ∧ wordHeight V k = h then 1 else 0

/-- Total number of `A`-steps in `V` starting at relative height `h`. -/
def wordLevelAdditions (V : List Bool) (h : Int) : Nat :=
  wordLevelAdditionsUpTo V h V.length

/-- Prefix count of `S`-steps in `V` landing at relative height `r` over indices `< k`. -/
def wordSLandingsUpTo (V : List Bool) (r : Int) : Nat → Nat
  | 0 => 0
  | k + 1 => wordSLandingsUpTo V r k +
      if V[k]! = false ∧ wordHeight V (k + 1) = r then 1 else 0

/-- Prefix sum of low-addition weights `2 * (r - h) - 1` for `A`-steps at height `h < r`. -/
def wordLowWeightsUpTo (V : List Bool) (r : Int) : Nat → Int
  | 0 => 0
  | k + 1 => wordLowWeightsUpTo V r k +
      if V[k]! = true ∧ wordHeight V k < r then 2 * (r - wordHeight V k) - 1 else 0

/-- Total low-addition weight `W(r)(V) = ∑_{h < r} (2*(r - h) - 1) * A_h(V)`. -/
def wordLowWeights (V : List Bool) (r : Int) : Int :=
  wordLowWeightsUpTo V r V.length

/-- Prefix sum of upper-excess weights `2 * (h - r) + 1` for `A`-steps at height `h ≥ r + 2`. -/
def wordUpperExcessUpTo (V : List Bool) (r : Int) : Nat → Int
  | 0 => 0
  | k + 1 => wordUpperExcessUpTo V r k +
      if V[k]! = true ∧ r + 2 ≤ wordHeight V k then 2 * (wordHeight V k - r) + 1 else 0

/-- Total upper-excess weight `∑_{h ≥ r + 2} (2*(h - r) + 1) * A_h(V)`. -/
def wordUpperExcess (V : List Bool) (r : Int) : Int :=
  wordUpperExcessUpTo V r V.length

/-- Prefix slack on `[0, s)` for lifting `E-797`'s `n = 0` budget to an arbitrary offset `s`.
Vanishes identically when `s = 0`. -/
noncomputable def prefixBudgetSlack (f : Nat → Bool) (s : Nat) (r_abs : Int) : Int :=
  lowAdditionWeights f 0 r_abs s +
    ((3 * (doubleAscent f 0 s (r_abs - 1) + if s = 0 then 0 else 1) : Nat) : Int)

/-! ## Step formulas for `wordHeight`, `wordRelPot`, and exact balanced duality -/

private theorem take_succ_eq_append_bang (V : List Bool) (k : Nat) (hk : k < V.length) :
    V.take (k + 1) = V.take k ++ [V[k]!] := by
  rw [List.take_succ_eq_append_getElem hk]
  simp [hk]

private theorem wordHeight_zero (V : List Bool) : wordHeight V 0 = 0 := by
  simp [wordHeight, mass]

private theorem wordHeight_length (V : List Bool) : wordHeight V V.length = mass V := by
  simp [wordHeight]

private theorem wordHeight_succ (V : List Bool) (k : Nat) (hk : k < V.length) :
    wordHeight V (k + 1) = wordHeight V k + sign V[k]! := by
  unfold wordHeight
  rw [take_succ_eq_append_bang V k hk, mass_append]
  simp [mass]

private theorem wordRelPot_zero (V : List Bool) (r : Int) : wordRelPot V r 0 = 0 := by
  simp [wordRelPot, areaW]

private theorem wordRelPot_succ (V : List Bool) (r : Int) (k : Nat) (hk : k < V.length) :
    wordRelPot V r (k + 1) = wordRelPot V r k + wordHeight V (k + 1) - r := by
  unfold wordRelPot
  rw [take_succ_eq_append_bang V k hk, areaW_append]
  have h1 : areaW [V[k]!] = sign V[k]! := by
    cases h : V[k]! <;> simp [areaW, sign]
  have h2 : mass (V.take k) = wordHeight V k := rfl
  have h3 : wordHeight V (k + 1) = wordHeight V k + sign V[k]! := wordHeight_succ V k hk
  simp only [List.length_singleton]
  rw [h1, h2]
  have hmul : ((k + 1 : Nat) : Int) * r = (k : Int) * r + r := by
    push_cast
    rw [Int.add_mul, Int.one_mul]
  have h1mul : ((1 : Nat) : Int) * wordHeight V k = wordHeight V k := by
    simp
  rw [hmul, h1mul]
  omega

private theorem wordSLandingsUpTo_eq_filter_range (V : List Bool) (r : Int) :
    ∀ k, wordSLandingsUpTo V r k =
      ((List.range k).filter (fun j => decide (V[j]! = false ∧ wordHeight V (j + 1) = r))).length
  | 0 => by simp [wordSLandingsUpTo]
  | k + 1 => by
    rw [wordSLandingsUpTo, wordSLandingsUpTo_eq_filter_range V r k,
      List.range_succ, List.filter_append, List.length_append]
    by_cases h : V[k]! = false ∧ wordHeight V (k + 1) = r
    · rw [if_pos h]
      have hd : decide (V[k]! = false ∧ wordHeight V (k + 1) = r) = true := decide_eq_true h
      simp only [List.filter_cons, List.filter_nil, hd, ↓reduceIte, List.length_cons, List.length_nil]
    · rw [if_neg h]
      have hd : decide (V[k]! = false ∧ wordHeight V (k + 1) = r) = false := decide_eq_false h
      simp only [List.filter_cons, List.filter_nil, hd, Bool.false_eq_true, ↓reduceIte,
        List.length_nil]

private theorem wordSLandingsUpTo_length (V : List Bool) (r : Int) :
    wordSLandingsUpTo V r V.length = wordSLandings V r := by
  unfold wordSLandings wordSLandingIndices
  exact wordSLandingsUpTo_eq_filter_range V r V.length

private theorem balanced_crossing_prefix_invariant (V : List Bool) (r : Int) :
    ∀ k, k ≤ V.length →
      (wordLevelAdditionsUpTo V r k : Int) - (wordSLandingsUpTo V r k : Int) =
        (if r < wordHeight V k then (1 : Int) else 0) - (if r < 0 then (1 : Int) else 0)
  | 0, _ => by
    simp [wordLevelAdditionsUpTo, wordSLandingsUpTo, wordHeight_zero]
  | k + 1, hk => by
    have ih := balanced_crossing_prefix_invariant V r k (by omega)
    have hstep := wordHeight_succ V k (by omega)
    simp only [wordLevelAdditionsUpTo, wordSLandingsUpTo]
    cases hVk : V[k]!
    · rw [hVk] at hstep
      simp [sign] at hstep
      have hfalse : ¬ (false = true ∧ wordHeight V k = r) := by simp
      rw [if_neg hfalse]
      by_cases heq : wordHeight V (k + 1) = r
      · rw [if_pos ⟨rfl, heq⟩]
        have hlt1 : ¬ (r < wordHeight V (k + 1)) := by omega
        have hlt2 : r < wordHeight V k := by omega
        rw [if_neg hlt1]
        rw [if_pos hlt2] at ih
        omega
      · rw [if_neg (fun h => heq h.2)]
        by_cases hlt1 : r < wordHeight V (k + 1)
        · have hlt2 : r < wordHeight V k := by omega
          rw [if_pos hlt1]
          rw [if_pos hlt2] at ih
          omega
        · have hlt2 : ¬ (r < wordHeight V k) := by omega
          rw [if_neg hlt1]
          rw [if_neg hlt2] at ih
          omega
    · rw [hVk] at hstep
      simp [sign] at hstep
      have hfalse : ¬ (true = false ∧ wordHeight V (k + 1) = r) := by simp
      rw [if_neg hfalse]
      by_cases heq : wordHeight V k = r
      · rw [if_pos ⟨rfl, heq⟩]
        have hlt1 : r < wordHeight V (k + 1) := by omega
        have hlt2 : ¬ (r < wordHeight V k) := by omega
        rw [if_pos hlt1]
        rw [if_neg hlt2] at ih
        omega
      · rw [if_neg (fun h => heq h.2)]
        by_cases hlt1 : r < wordHeight V (k + 1)
        · have hlt2 : r < wordHeight V k := by omega
          rw [if_pos hlt1]
          rw [if_pos hlt2] at ih
          omega
        · have hlt2 : ¬ (r < wordHeight V k) := by omega
          rw [if_neg hlt1]
          rw [if_neg hlt2] at ih
          omega

/-- For every balanced word `V` (`mass V = 0`) and every relative height `r : Int`,
the number of `S`-landings at height `r` equals the number of `A`-steps starting at height `r`. -/
theorem balanced_word_sLandings_eq_levelAdditions (V : List Bool) (r : Int) (hbal : mass V = 0) :
    wordSLandings V r = wordLevelAdditions V r := by
  have hinv := balanced_crossing_prefix_invariant V r V.length (Nat.le_refl _)
  rw [wordSLandingsUpTo_length, wordHeight_length, hbal] at hinv
  unfold wordLevelAdditions
  omega

private theorem area_potential_prefix_invariant (V : List Bool) (r : Int) :
    ∀ k, k ≤ V.length →
      2 * wordRelPot V r k + (wordHeight V k - r) * (wordHeight V k - r - 1) - (-r) * (-r - 1) =
        2 * ((wordLevelAdditionsUpTo V r k : Int) +
          3 * (wordLevelAdditionsUpTo V (r + 1) k : Int) +
          wordUpperExcessUpTo V r k - wordLowWeightsUpTo V r k)
  | 0, _ => by
    simp [wordRelPot_zero, wordHeight_zero, wordLevelAdditionsUpTo,
      wordUpperExcessUpTo, wordLowWeightsUpTo]
  | k + 1, hk => by
    have ih := area_potential_prefix_invariant V r k (by omega)
    have hstep := wordHeight_succ V k (by omega)
    have hpot := wordRelPot_succ V r k (by omega)
    simp only [wordLevelAdditionsUpTo, wordUpperExcessUpTo, wordLowWeightsUpTo]
    cases hVk : V[k]!
    · rw [hVk] at hstep
      simp [sign] at hstep
      have h1 : ¬ (false = true ∧ wordHeight V k = r) := by simp
      have h2 : ¬ (false = true ∧ wordHeight V k = r + 1) := by simp
      have h3 : ¬ (false = true ∧ r + 2 ≤ wordHeight V k) := by simp
      have h4 : ¬ (false = true ∧ wordHeight V k < r) := by simp
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
      have hquad :
          (wordHeight V (k + 1) - r) * (wordHeight V (k + 1) - r - 1) -
            (wordHeight V k - r) * (wordHeight V k - r - 1) =
          -(2 * (wordHeight V (k + 1) - r)) := by
        have hsub2 : wordHeight V k - r - 1 = wordHeight V (k + 1) - r := by omega
        have hsub : wordHeight V k - r = (wordHeight V (k + 1) - r) + 1 := by omega
        rw [hsub2, hsub]
        have hcomm : ((wordHeight V (k + 1) - r) + 1) * (wordHeight V (k + 1) - r) =
            (wordHeight V (k + 1) - r) * ((wordHeight V (k + 1) - r) + 1) := Int.mul_comm _ _
        rw [hcomm, ← Int.mul_sub]
        have hd : wordHeight V (k + 1) - r - 1 - (wordHeight V (k + 1) - r + 1) = -2 := by omega
        rw [hd]
        omega
      omega
    · rw [hVk] at hstep
      simp [sign] at hstep
      have hquad :
          (wordHeight V (k + 1) - r) * (wordHeight V (k + 1) - r - 1) -
            (wordHeight V k - r) * (wordHeight V k - r - 1) =
          2 * (wordHeight V k - r) := by
        have hsub2 : wordHeight V (k + 1) - r - 1 = wordHeight V k - r := by omega
        have hsub1 : wordHeight V (k + 1) - r = (wordHeight V k - r) + 1 := by omega
        rw [hsub2, hsub1]
        have hcomm : ((wordHeight V k - r) + 1) * (wordHeight V k - r) =
            (wordHeight V k - r) * ((wordHeight V k - r) + 1) := Int.mul_comm _ _
        rw [hcomm, ← Int.mul_sub]
        have hd : (wordHeight V k - r) + 1 - (wordHeight V k - r - 1) = 2 := by omega
        rw [hd]
        omega
      by_cases hlt : wordHeight V k < r
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨rfl, hlt⟩]
        omega
      · by_cases heq0 : wordHeight V k = r
        · rw [if_pos ⟨rfl, heq0⟩, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          omega
        · by_cases heq1 : wordHeight V k = r + 1
          · rw [if_neg (by omega), if_pos ⟨rfl, heq1⟩, if_neg (by omega), if_neg (by omega)]
            omega
          · have hge2 : r + 2 ≤ wordHeight V k := by omega
            rw [if_neg (by omega), if_neg (by omega), if_pos ⟨rfl, hge2⟩, if_neg (by omega)]
            omega

/-- Exact balanced word area-potential duality: for every balanced word `V` (`mass V = 0`)
and every relative height `r : Int`,
  `wordLowWeights V r + wordPotDrift V r = A_r(V) + 3 * A_{r+1}(V) + wordUpperExcess V r`. -/
theorem balanced_word_area_potential_identity (V : List Bool) (r : Int) (hbal : mass V = 0) :
    wordLowWeights V r + wordPotDrift V r =
      (wordLevelAdditions V r : Int) + 3 * (wordLevelAdditions V (r + 1) : Int) +
        wordUpperExcess V r := by
  have hinv := area_potential_prefix_invariant V r V.length (Nat.le_refl _)
  rw [wordHeight_length, hbal] at hinv
  simp only [Int.zero_sub] at hinv
  unfold wordLowWeights wordPotDrift wordLevelAdditions wordUpperExcess
  omega

private theorem wordUpperExcessUpTo_nonneg (V : List Bool) (r : Int) :
    ∀ k, 0 ≤ wordUpperExcessUpTo V r k
  | 0 => by simp [wordUpperExcessUpTo]
  | k + 1 => by
    have ih := wordUpperExcessUpTo_nonneg V r k
    simp only [wordUpperExcessUpTo]
    split <;> omega

private theorem wordUpperExcess_nonneg (V : List Bool) (r : Int) :
    0 ≤ wordUpperExcess V r :=
  wordUpperExcessUpTo_nonneg V r V.length

private theorem wordUpperExcessUpTo_zero_of_ceil (V : List Bool) (H : Int)
    (hceil : ∀ j, j < V.length → V[j]! = true → wordHeight V j ≤ H) :
    ∀ k, k ≤ V.length → wordUpperExcessUpTo V (H - 1) k = 0
  | 0, _ => rfl
  | k + 1, hk => by
    have ih := wordUpperExcessUpTo_zero_of_ceil V H hceil k (by omega)
    simp only [wordUpperExcessUpTo, ih, Int.zero_add]
    split
    · rename_i h
      have hle := hceil k (by omega) h.1
      omega
    · rfl

private theorem wordUpperExcess_zero_of_ceil (V : List Bool) (H : Int)
    (hceil : ∀ j, j < V.length → V[j]! = true → wordHeight V j ≤ H) :
    wordUpperExcess V (H - 1) = 0 :=
  wordUpperExcessUpTo_zero_of_ceil V H hceil V.length (Nat.le_refl _)

/-! ## Negative-drift golden-ratio capacity (`d ≤ 0`) -/

/-- Finite-`R` negative-drift golden-ratio law under `TypeIFresh`: whenever `wordPotDrift V r ≤ 0`
and `repeatWord R V` (`1 ≤ R`) matches a `TypeIFresh` sequence `f`,
  `R * (3 * A_{r+1}(V) + 2 * A_r(V) + upperExcess(V, r)) ≤ R * W(r)(V) + span(V, r) + |d| + 1`. -/
theorem typeIFresh_periodic_neg_drift_capacity (f : Nat → Bool) (s R : Nat) (V : List Bool) (r : Int)
    (hbal : mass V = 0) (hneg : wordPotDrift V r ≤ 0) (hR : 1 ≤ R)
    (hm : MatchesAt f s (repeatWord R V))
    (hfresh : TypeIFresh f (s + R * V.length)) :
    (R : Int) * ((3 * wordLevelAdditions V (r + 1) + 2 * wordLevelAdditions V r : Nat) : Int) +
      (R : Int) * wordUpperExcess V r ≤
        (R : Int) * wordLowWeights V r + (wordPotSpan V r : Int) +
          ((wordPotDrift V r).natAbs : Int) + 1 := by
  have hpig := typeIFresh_periodic_s_count_le_drift f s R V r hbal hR hm hfresh
  have hSA := balanced_word_sLandings_eq_levelAdditions V r hbal
  rw [hSA] at hpig
  have hid := balanced_word_area_potential_identity V r hbal
  have hd_abs : ((wordPotDrift V r).natAbs : Int) = -wordPotDrift V r := by omega
  have hpigI : (R : Int) * (wordLevelAdditions V r : Int) ≤
      (wordPotSpan V r : Int) + ((R - 1 : Nat) : Int) * ((wordPotDrift V r).natAbs : Int) + 1 := by
    exact_mod_cast hpig
  have hR1 : ((R - 1 : Nat) : Int) = (R : Int) - 1 := by omega
  rw [hR1, Int.sub_mul, Int.one_mul] at hpigI
  have hRd : (R : Int) * ((wordPotDrift V r).natAbs : Int) = -((R : Int) * wordPotDrift V r) := by
    rw [hd_abs, Int.mul_neg]
  have hidR : (R : Int) * (wordLowWeights V r + wordPotDrift V r) =
      (R : Int) * ((wordLevelAdditions V r : Int) + 3 * (wordLevelAdditions V (r + 1) : Int) +
        wordUpperExcess V r) := by rw [hid]
  rw [Int.mul_add, Int.mul_add, Int.mul_add] at hidR
  have hcast :
      (R : Int) * ((3 * wordLevelAdditions V (r + 1) + 2 * wordLevelAdditions V r : Nat) : Int) =
      (R : Int) * (3 * (wordLevelAdditions V (r + 1) : Int)) +
        (R : Int) * (wordLevelAdditions V r : Int) +
        (R : Int) * (wordLevelAdditions V r : Int) := by
    push_cast
    rw [Int.mul_add, show (2 : Int) * (wordLevelAdditions V r : Int) =
      (wordLevelAdditions V r : Int) + (wordLevelAdditions V r : Int) by omega, Int.mul_add]
    omega
  omega

/-- Direct coherent `SeededReplay` negative-drift golden-ratio capacity (finite-`R` form). -/
theorem seeded_replay_periodic_neg_drift_capacity (b s R : Nat) (st : State)
    (hs : st.value ∈ st.seen) (V : List Bool) (r : Int)
    (hbal : mass V = 0) (hneg : wordPotDrift V r ≤ 0) (hR : 1 ≤ R)
    (hm : MatchesAt (replaySign b st) s (repeatWord R V)) :
    (R : Int) * ((3 * wordLevelAdditions V (r + 1) + 2 * wordLevelAdditions V r : Nat) : Int) +
      (R : Int) * wordUpperExcess V r ≤
        (R : Int) * wordLowWeights V r + (wordPotSpan V r : Int) +
          ((wordPotDrift V r).natAbs : Int) + 1 :=
  typeIFresh_periodic_neg_drift_capacity (replaySign b st) s R V r hbal hneg hR hm
    (seeded_replay_typeIFresh b st hs (s + R * V.length))

/-- Exact zero-error negative-drift golden-ratio law on EVERY coherent `SeededReplay.run b st`:
whenever `wordPotDrift V r ≤ 0` and `R ≥ wordPotSpan V r + |wordPotDrift V r| + 2`,
  `3 * A_{r+1}(V) + 2 * A_r(V) + upperExcess(V, r) ≤ W(r)(V)`
with ZERO additive slack (characteristic root `φ = (1 + √5)/2 < 5/3`, and zero exponential
growth above the unique sign-flip height `r*`). -/
theorem seeded_replay_periodic_neg_drift_exact_capacity (b s R : Nat) (st : State)
    (hs : st.value ∈ st.seen) (V : List Bool) (r : Int)
    (hbal : mass V = 0) (hneg : wordPotDrift V r ≤ 0)
    (hR : wordPotSpan V r + (wordPotDrift V r).natAbs + 2 ≤ R)
    (hm : MatchesAt (replaySign b st) s (repeatWord R V)) :
    ((3 * wordLevelAdditions V (r + 1) + 2 * wordLevelAdditions V r : Nat) : Int) +
      wordUpperExcess V r ≤ wordLowWeights V r := by
  have hfin := seeded_replay_periodic_neg_drift_capacity b s R st hs V r hbal hneg (by omega) hm
  apply Classical.byContradiction
  intro hgt
  have h1 : wordLowWeights V r + 1 ≤
      ((3 * wordLevelAdditions V (r + 1) + 2 * wordLevelAdditions V r : Nat) : Int) +
        wordUpperExcess V r := by omega
  have hmul := Int.mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg R)
  rw [Int.mul_add, Int.mul_add, Int.mul_one] at hmul
  omega

/-- Canonical clock-0 Recamán specialization of the exact negative-drift golden-ratio law:
for any balanced word `V` with `wordPotDrift V r ≤ 0` repeating at least `span + |d| + 2`
consecutive times anywhere in `Recaman.Basic.a`,
  `3 * A_{r+1}(V) + 2 * A_r(V) + upperExcess(V, r) ≤ W(r)(V)`. -/
theorem canonical_periodic_neg_drift_exact_capacity (s R : Nat) (V : List Bool) (r : Int)
    (hbal : mass V = 0) (hneg : wordPotDrift V r ≤ 0)
    (hR : wordPotSpan V r + (wordPotDrift V r).natAbs + 2 ≤ R)
    (hm : MatchesAt canonicalOrbitSign s (repeatWord R V)) :
    ((3 * wordLevelAdditions V (r + 1) + 2 * wordLevelAdditions V r : Nat) : Int) +
      wordUpperExcess V r ≤ wordLowWeights V r := by
  have hs0 : initial.value ∈ initial.seen := by simp [initial]
  exact seeded_replay_periodic_neg_drift_exact_capacity 0 s R initial hs0 V r hbal hneg hR hm

/-! ## Periodic coordinate helpers for `TypeIIFresh` and window counts -/

private theorem repeatWord_length_local (R : Nat) (V : List Bool) :
    (repeatWord R V).length = R * V.length := by
  induction R with
  | zero => simp [repeatWord]
  | succ R ih =>
    simp only [repeatWord, List.length_append, ih]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

private theorem seg_eq_of_matchesAt_local (f : Nat → Bool) (s : Nat) (w : List Bool)
    (hm : MatchesAt f s w) :
    ∀ k, k ≤ w.length → seg f s k = w.take k
  | 0, _ => by simp [seg]
  | k + 1, hk => by
    have ih := seg_eq_of_matchesAt_local f s w hm k (by omega)
    rw [seg_succ, ih, hm k (by omega), take_succ_eq_append_bang w k (by omega)]

private theorem matchesAt_repeat_copy_local (f : Nat → Bool) (s : Nat) (V : List Bool) :
    ∀ R c, c < R → MatchesAt f s (repeatWord R V) → MatchesAt f (s + c * V.length) V
  | 0, _, hc, _ => by omega
  | R + 1, 0, _, hm => by
    intro i hi
    have hlen : V.length ≤ (repeatWord (R + 1) V).length := by
      rw [repeatWord_length_local]
      have : 1 * V.length ≤ (R + 1) * V.length := Nat.mul_le_mul_right _ (by omega)
      omega
    have h1 := hm i (by omega)
    simp only [Nat.zero_mul, Nat.add_zero]
    rw [h1]
    simp [repeatWord, List.getElem!_eq_getElem?_getD, List.getElem?_append_left hi]
  | R + 1, c + 1, hc, hm => by
    have htail : MatchesAt f (s + V.length) (repeatWord R V) := by
      intro i hi
      have hi' : V.length + i < (repeatWord (R + 1) V).length := by
        rw [repeatWord_length_local] at hi ⊢
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have h1 := hm (V.length + i) hi'
      rw [← Nat.add_assoc] at h1
      rw [h1]
      simp [repeatWord, List.getElem!_eq_getElem?_getD,
        List.getElem?_append_right (Nat.le_add_right V.length i)]
    have ih := matchesAt_repeat_copy_local f (s + V.length) V R c (by omega) htail
    intro i hi
    have h1 := ih i hi
    have hidx : s + V.length + c * V.length + i = s + (c + 1) * V.length + i := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    rwa [hidx] at h1

private theorem fw_and_ar_copy_local (f : Nat → Bool) (s : Nat) (V : List Bool) (hbal : mass V = 0)
    (R : Nat) (hm : MatchesAt f s (repeatWord R V)) :
    ∀ c, c ≤ R →
      Fw f (s + c * V.length) = Fw f s ∧
      Ar f s (c * V.length) = (c : Int) * areaW V
  | 0, _ => by simp [Ar]
  | c + 1, hc => by
    have ih := fw_and_ar_copy_local f s V hbal R hm c (by omega)
    have hm_c := matchesAt_repeat_copy_local f s V R c (by omega) hm
    have hseg := seg_eq_of_matchesAt_local f (s + c * V.length) V hm_c V.length (Nat.le_refl _)
    rw [List.take_length] at hseg
    have hFw_step : Fw f (s + (c + 1) * V.length) = Fw f (s + c * V.length) + mass V := by
      have h1 := seg_mass f (s + c * V.length) V.length
      rw [hseg] at h1
      rw [show s + (c + 1) * V.length = s + c * V.length + V.length by
        rw [Nat.add_mul, Nat.one_mul]; omega]
      omega
    have hAr_step : Ar f (s + c * V.length) V.length = areaW V := by
      rw [Ar_areaW, hseg]
    have hsplit := area_split_at f s (s + c * V.length) (s + (c + 1) * V.length)
      (Nat.le_add_right _ _) (by rw [Nat.add_mul, Nat.one_mul]; omega)
    have hlen1 : s + (c + 1) * V.length - s = (c + 1) * V.length := by omega
    have hlen2 : s + c * V.length - s = c * V.length := by omega
    have hlen3 : s + (c + 1) * V.length - (s + c * V.length) = V.length := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    rw [hlen1, hlen2, hlen3, ih.1, ih.2, hAr_step] at hsplit
    refine ⟨by omega, ?_⟩
    push_cast
    rw [Int.add_mul, Int.one_mul]
    omega

private theorem periodic_height_and_pot_local (f : Nat → Bool) (s : Nat) (V : List Bool)
    (hbal : mass V = 0) (R : Nat) (hm : MatchesAt f s (repeatWord R V))
    (c j : Nat) (hc : c < R) (hj : j ≤ V.length) (r : Int) :
    Fw f (s + c * V.length + j) = Fw f s + wordHeight V j ∧
    floorPotential f 0 (Fw f s + r - 1) (s + c * V.length + j) =
      floorPotential f 0 (Fw f s + r - 1) s +
        (c : Int) * wordPotDrift V r + wordRelPot V r j := by
  have hcopy := fw_and_ar_copy_local f s V hbal R hm c (Nat.le_of_lt hc)
  have hm_c := matchesAt_repeat_copy_local f s V R c hc hm
  have hseg := seg_eq_of_matchesAt_local f (s + c * V.length) V hm_c j hj
  have hFw_j : Fw f (s + c * V.length + j) = Fw f s + wordHeight V j := by
    have h1 := seg_mass f (s + c * V.length) j
    rw [hseg] at h1
    unfold wordHeight
    omega
  have hAr_j : Ar f (s + c * V.length) j = areaW (V.take j) := by
    rw [Ar_areaW, hseg]
  have hsp1 := area_split_at f 0 s (s + c * V.length + j) (Nat.zero_le _) (by omega)
  have hsp2 := area_split_at f s (s + c * V.length) (s + c * V.length + j)
    (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  simp only [Nat.sub_zero, Nat.add_sub_cancel_left] at hsp1 hsp2
  have hlen_s : s + c * V.length + j - s = c * V.length + j := by omega
  rw [hlen_s, hcopy.1, hcopy.2, hAr_j] at hsp2
  rw [hlen_s] at hsp1
  refine ⟨hFw_j, ?_⟩
  have hFw0 : Fw f 0 = 0 := rfl
  rw [hFw0] at hsp1
  unfold floorPotential wordPotDrift wordRelPot
  simp only [Nat.sub_zero, List.take_length]
  rw [hFw0, hsp1, hsp2]
  have hsub_s : (s + c * V.length + j : Nat) = s + (c * V.length + j) := by omega
  rw [hsub_s]
  push_cast
  have hmul1 : ((s : Int) + ((c : Int) * (V.length : Int) + (j : Int))) * (0 - (Fw f s + r - 1 + 1)) =
      (s : Int) * (0 - (Fw f s + r - 1 + 1)) +
      ((c : Int) * (V.length : Int) + (j : Int)) * (0 - (Fw f s + r - 1 + 1)) := Int.add_mul _ _ _
  have hmul2 : ((c : Int) * (V.length : Int) + (j : Int)) * (0 - (Fw f s + r - 1 + 1)) =
      ((c : Int) * (V.length : Int) + (j : Int)) * (-Fw f s) -
      ((c : Int) * (V.length : Int) + (j : Int)) * r := by
    have : 0 - (Fw f s + r - 1 + 1) = -Fw f s - r := by omega
    rw [this, Int.mul_sub]
  have hmul3 : ((c : Int) * (V.length : Int) + (j : Int)) * (-Fw f s) =
      -(((c : Int) * (V.length : Int) + (j : Int)) * (Fw f s - 0)) := by
    have : Fw f s - 0 = Fw f s := by omega
    rw [this, Int.mul_neg]
  have hmul4 : ((c : Int) * (V.length : Int) + (j : Int)) * r =
      (c : Int) * ((V.length : Int) * r) + (j : Int) * r := by
    rw [Int.add_mul, Int.mul_assoc]
  have hmul5 : (c : Int) * (areaW V - (V.length : Int) * r) =
      (c : Int) * areaW V - (c : Int) * ((V.length : Int) * r) := Int.mul_sub _ _ _
  rw [hmul1, hmul2, hmul3, hmul4, hmul5]
  omega

private theorem wordPotMinUpTo_le_local (V : List Bool) (r : Int) :
    ∀ k j, j ≤ k → wordPotMinUpTo V r k ≤ wordRelPot V r j
  | 0, j, hj => by
    have : j = 0 := by omega
    subst this
    simp [wordPotMinUpTo, wordRelPot, areaW]
  | k + 1, j, hj => by
    simp only [wordPotMinUpTo]
    by_cases hjk : j ≤ k
    · exact Int.le_trans (Int.min_le_left _ _) (wordPotMinUpTo_le_local V r k j hjk)
    · have : j = k + 1 := by omega
      subst this
      exact Int.min_le_right _ _

private theorem wordPotMaxUpTo_ge_local (V : List Bool) (r : Int) :
    ∀ k j, j ≤ k → wordRelPot V r j ≤ wordPotMaxUpTo V r k
  | 0, j, hj => by
    have : j = 0 := by omega
    subst this
    simp [wordPotMaxUpTo, wordRelPot, areaW]
  | k + 1, j, hj => by
    simp only [wordPotMaxUpTo]
    by_cases hjk : j ≤ k
    · exact Int.le_trans (wordPotMaxUpTo_ge_local V r k j hjk) (Int.le_max_left _ _)
    · have : j = k + 1 := by omega
      subst this
      exact Int.le_max_right _ _

private theorem wordRelPot_diff_le_span (V : List Bool) (r : Int) (j₁ j₂ : Nat)
    (hj₁ : j₁ ≤ V.length) (hj₂ : j₂ ≤ V.length) :
    wordRelPot V r j₁ - wordRelPot V r j₂ ≤ (wordPotSpan V r : Int) := by
  have hmin1 := wordPotMinUpTo_le_local V r V.length j₁ hj₁
  have hmax1 := wordPotMaxUpTo_ge_local V r V.length j₁ hj₁
  have hmin2 := wordPotMinUpTo_le_local V r V.length j₂ hj₂
  have hmax2 := wordPotMaxUpTo_ge_local V r V.length j₂ hj₂
  unfold wordPotSpan
  have hnn : 0 ≤ wordPotMaxUpTo V r V.length - wordPotMinUpTo V r V.length := by omega
  rw [Int.toNat_of_nonneg hnn]
  omega

/-! ## `TypeIIFresh` periodic residue-order obstruction and negative-drift `(AS)^a S` ceiling -/

/-- General `TypeIIFresh` periodic residue-order obstruction: if balanced `V` has nonzero drift
`d = wordPotDrift V r ≠ 0` and repeats `R ≥ wordPotSpan V r + 1` times in a `TypeIIFresh`
sequence `f`, then for every `S`-landing `t` of `V` at relative height `r` and every `A`-step
`u` of `V` at relative height `r + 1` whose potentials are congruent mod `|d|`:
- `d < 0 → wordRelPot V r (t + 1) ≤ wordRelPot V r u`,
- `0 < d → wordRelPot V r u ≤ wordRelPot V r (t + 1)`,
- `wordRelPot V r (t + 1) = wordRelPot V r u → t < u`. -/
theorem typeIIFresh_periodic_residue_order (f : Nat → Bool) (s R : Nat) (V : List Bool) (r : Int)
    (hbal : mass V = 0) (hdne : wordPotDrift V r ≠ 0)
    (hR : wordPotSpan V r + 1 ≤ R)
    (hm : MatchesAt f s (repeatWord R V))
    (hfresh2 : TypeIIFresh f (s + R * V.length))
    (t u : Nat) (ht : t < V.length) (hu : u < V.length)
    (hVt : V[t]! = false) (hht : wordHeight V (t + 1) = r)
    (hVu : V[u]! = true) (hhu : wordHeight V u = r + 1)
    (hdvd : ((wordPotDrift V r).natAbs : Int) ∣ (wordRelPot V r (t + 1) - wordRelPot V r u)) :
    (wordPotDrift V r < 0 → wordRelPot V r (t + 1) ≤ wordRelPot V r u) ∧
    (0 < wordPotDrift V r → wordRelPot V r u ≤ wordRelPot V r (t + 1)) ∧
    (wordRelPot V r (t + 1) = wordRelPot V r u → t < u) := by
  let d := wordPotDrift V r
  let L := V.length
  obtain ⟨q0, hq0⟩ := hdvd
  -- Rewrite s_val - c_val = q * d
  have hexq : ∃ q : Int, wordRelPot V r (t + 1) - wordRelPot V r u = q * d := by
    by_cases hdpos : 0 < d
    · refine ⟨q0, ?_⟩
      have ha : (d.natAbs : Int) = d := Int.natAbs_of_nonneg (by omega)
      rw [ha] at hq0
      rw [hq0, Int.mul_comm]
    · refine ⟨-q0, ?_⟩
      have ha : (d.natAbs : Int) = -d := by omega
      rw [ha] at hq0
      have : (-q0) * d = (-d) * q0 := by rw [Int.neg_mul, Int.mul_comm, ← Int.neg_mul]
      omega
  obtain ⟨q, hq⟩ := hexq
  have hq_nonneg : 0 ≤ q := by
    apply Classical.byContradiction
    intro hqneg
    have hqlt : q < 0 := by omega
    let p : Nat := (-q).toNat
    have hp_pos : 1 ≤ p := by omega
    have hp_eq : (p : Int) = -q := by omega
    have hspan1 := wordRelPot_diff_le_span V r (t + 1) u (by omega) (by omega)
    have hspan2 := wordRelPot_diff_le_span V r u (t + 1) (by omega) (by omega)
    have hp_le_span : p ≤ wordPotSpan V r := by
      have habs : (p : Int) * (d.natAbs : Int) ≤ (wordPotSpan V r : Int) := by
        by_cases hdpos : 0 < d
        · have ha : (d.natAbs : Int) = d := Int.natAbs_of_nonneg (by omega)
          rw [ha, hp_eq, Int.neg_mul]; omega
        · have ha : (d.natAbs : Int) = -d := by omega
          rw [ha, hp_eq, Int.neg_mul, Int.mul_neg, Int.neg_neg]; omega
      have hd1 : (1 : Int) ≤ (d.natAbs : Int) := by omega
      have hp1 : (p : Int) * 1 ≤ (p : Int) * (d.natAbs : Int) :=
        Int.mul_le_mul_of_nonneg_left hd1 (Int.natCast_nonneg p)
      omega
    have hp_lt_R : p < R := by omega
    have h0_lt_R : 0 < R := by omega
    let tc := s + p * L + t
    let uc := s + 0 * L + u
    have htc_lt : tc < s + R * L := by
      have hmul : (p + 1) * L ≤ R * L := Nat.mul_le_mul_right L (by omega)
      rw [Nat.add_mul, Nat.one_mul] at hmul
      dsimp only [tc]; omega
    have huc_lt_tc : uc < tc := by
      have hmul : 1 * L ≤ p * L := Nat.mul_le_mul_right L hp_pos
      dsimp only [uc, tc]; omega
    have hftc : f tc = false := by
      have := matchesAt_repeat_copy_local f s V R p hp_lt_R hm t ht
      rw [this, hVt]
    have hfuc : f uc = true := by
      have := matchesAt_repeat_copy_local f s V R 0 h0_lt_R hm u hu
      rw [this, hVu]
    have hpt := periodic_height_and_pot_local f s V hbal R hm p (t + 1) hp_lt_R (by omega) r
    have hpu := periodic_height_and_pot_local f s V hbal R hm 0 u h0_lt_R (by omega) r
    have hidx : s + p * L + (t + 1) = tc + 1 := by dsimp only [tc]; omega
    rw [hidx] at hpt
    have hFtc : Fw f (tc + 1) = Fw f s + r := by rw [hpt.1, hht]
    have hFuc : Fw f uc = Fw f (tc + 1) + 1 := by rw [hFtc, hpu.1, hhu]; omega
    have hpeq : floorPotential f 0 (Fw f (tc + 1) - 1) (tc + 1) =
        floorPotential f 0 (Fw f (tc + 1) - 1) uc := by
      rw [hFtc, hpt.2, hpu.2]
      simp only [Int.ofNat_zero, Int.zero_mul, Int.add_zero]
      have hpd : (p : Int) * d = -(q * d) := by rw [hp_eq, Int.neg_mul]
      change floorPotential f 0 (Fw f s + r - 1) s + (p : Int) * d + wordRelPot V r (t + 1) =
        floorPotential f 0 (Fw f s + r - 1) s + wordRelPot V r u
      omega
    exact hfresh2 tc htc_lt hftc uc huc_lt_tc hfuc hFuc hpeq
  refine ⟨?_, ?_, ?_⟩
  · intro hdneg
    have hqd : q * d ≤ 0 := by
      have := Int.mul_nonneg hq_nonneg (show 0 ≤ -d by omega)
      rw [Int.mul_neg] at this; omega
    omega
  · intro hdpos
    have hqd : 0 ≤ q * d := Int.mul_nonneg hq_nonneg (by omega)
    omega
  · intro heq
    have h0_lt_R : 0 < R := by omega
    apply Classical.byContradiction
    intro hnotlt
    by_cases htu : u = t
    · rw [htu] at hVu; rw [hVt] at hVu; exact Bool.false_ne_true hVu
    · have hut : u < t := by omega
      let tc := s + 0 * L + t
      let uc := s + 0 * L + u
      have htc_lt : tc < s + R * L := by
        have hmul : 1 * L ≤ R * L := Nat.mul_le_mul_right L (by omega)
        dsimp only [tc]; omega
      have hftc : f tc = false := by
        have := matchesAt_repeat_copy_local f s V R 0 h0_lt_R hm t ht
        rw [this, hVt]
      have hfuc : f uc = true := by
        have := matchesAt_repeat_copy_local f s V R 0 h0_lt_R hm u hu
        rw [this, hVu]
      have hpt := periodic_height_and_pot_local f s V hbal R hm 0 (t + 1) h0_lt_R (by omega) r
      have hpu := periodic_height_and_pot_local f s V hbal R hm 0 u h0_lt_R (by omega) r
      have hidx : s + 0 * L + (t + 1) = tc + 1 := by dsimp only [tc]; omega
      rw [hidx] at hpt
      have hFtc : Fw f (tc + 1) = Fw f s + r := by rw [hpt.1, hht]
      have hFuc : Fw f uc = Fw f (tc + 1) + 1 := by rw [hFtc, hpu.1, hhu]; omega
      have hpeq : floorPotential f 0 (Fw f (tc + 1) - 1) (tc + 1) =
          floorPotential f 0 (Fw f (tc + 1) - 1) uc := by
        rw [hFtc, hpt.2, hpu.2, heq]
      exact hfresh2 tc htc_lt hftc uc (by dsimp only [uc, tc]; omega) hfuc hFuc hpeq

/-- Direct `SeededReplay` specialization of the `TypeIIFresh` periodic residue-order obstruction
(holds for EVERY finite-state greedy replay `(b, st)`, even without coherence). -/
theorem seeded_replay_periodic_typeIIFresh_residue_order (b s R : Nat) (st : State)
    (V : List Bool) (r : Int) (hbal : mass V = 0) (hdne : wordPotDrift V r ≠ 0)
    (hR : wordPotSpan V r + 1 ≤ R)
    (hm : MatchesAt (replaySign b st) s (repeatWord R V))
    (t u : Nat) (ht : t < V.length) (hu : u < V.length)
    (hVt : V[t]! = false) (hht : wordHeight V (t + 1) = r)
    (hVu : V[u]! = true) (hhu : wordHeight V u = r + 1)
    (hdvd : ((wordPotDrift V r).natAbs : Int) ∣ (wordRelPot V r (t + 1) - wordRelPot V r u)) :
    (wordPotDrift V r < 0 → wordRelPot V r (t + 1) ≤ wordRelPot V r u) ∧
    (0 < wordPotDrift V r → wordRelPot V r u ≤ wordRelPot V r (t + 1)) ∧
    (wordRelPot V r (t + 1) = wordRelPot V r u → t < u) :=
  typeIIFresh_periodic_residue_order (replaySign b st) s R V r hbal hdne hR hm
    (seeded_replay_typeIIFresh b st (s + R * V.length))
    t u ht hu hVt hht hVu hhu hdvd

private theorem as_run_height_and_pot (V : List Bool) (r : Int) (j a : Nat)
    (hlen : j + 2 * a ≤ V.length) (hh0 : wordHeight V j = r + 1)
    (has : ∀ i, i < a → V[j + 2 * i]! = true ∧ V[j + 2 * i + 1]! = false) :
    ∀ k, k ≤ a →
      wordHeight V (j + 2 * k) = r + 1 ∧
      wordRelPot V r (j + 2 * k) = wordRelPot V r j + 3 * (k : Int)
  | 0, _ => by simp [hh0]
  | k + 1, hk => by
    have ih := as_run_height_and_pot V r j a hlen hh0 has k (by omega)
    have hstepA := wordHeight_succ V (j + 2 * k) (by omega)
    have hstepS := wordHeight_succ V (j + 2 * k + 1) (by omega)
    have hpotA := wordRelPot_succ V r (j + 2 * k) (by omega)
    have hpotS := wordRelPot_succ V r (j + 2 * k + 1) (by omega)
    have hpair := has k (by omega)
    rw [hpair.1] at hstepA
    rw [hpair.2] at hstepS
    simp [sign] at hstepA hstepS
    have hidx : j + 2 * (k + 1) = j + 2 * k + 1 + 1 := by omega
    rw [hidx]
    refine ⟨by omega, ?_⟩
    push_cast
    omega

/-- Negative-drift `(AS)^a S` top-arch run ceiling on EVERY `SeededReplay.run b st` (and
`Recaman.Basic.a`): in any balanced cycle `V` with `wordPotDrift V r < 0` repeated
`R ≥ wordPotSpan V r + 1` times, no `(AS)^a S` arch run at height `r + 1` inside `V`
can satisfy `|d| ∣ 3 * k` for any `1 ≤ k ≤ a`; in particular `a < |d|` and, when
`3 ∣ d`, `3 * a < |d|`. -/
theorem seeded_replay_periodic_neg_drift_as_run_bound (b s R : Nat) (st : State)
    (V : List Bool) (r : Int) (hbal : mass V = 0) (hneg : wordPotDrift V r < 0)
    (hR : wordPotSpan V r + 1 ≤ R)
    (hm : MatchesAt (replaySign b st) s (repeatWord R V))
    (j a : Nat) (hlen : j + 2 * a + 1 ≤ V.length)
    (hh0 : wordHeight V j = r + 1)
    (has : ∀ i, i < a → V[j + 2 * i]! = true ∧ V[j + 2 * i + 1]! = false)
    (hS : V[j + 2 * a]! = false) :
    (∀ k, 1 ≤ k → k ≤ a → ¬ (((wordPotDrift V r).natAbs : Int) ∣ (3 * (k : Int)))) ∧
    a < (wordPotDrift V r).natAbs ∧
    ((3 : Int) ∣ wordPotDrift V r → 3 * a < (wordPotDrift V r).natAbs) := by
  have hrun := as_run_height_and_pot V r j a (by omega) hh0 has
  have hfa := hrun a (Nat.le_refl _)
  have ht_lt : j + 2 * a < V.length := by omega
  have hht : wordHeight V (j + 2 * a + 1) = r := by
    have hst := wordHeight_succ V (j + 2 * a) ht_lt
    rw [hS] at hst; simp [sign] at hst; omega
  have hpt : wordRelPot V r (j + 2 * a + 1) = wordRelPot V r j + 3 * (a : Int) := by
    have hp := wordRelPot_succ V r (j + 2 * a) ht_lt
    rw [hht, hfa.2] at hp; omega
  have hnodiv : ∀ k, 1 ≤ k → k ≤ a → ¬ (((wordPotDrift V r).natAbs : Int) ∣ (3 * (k : Int))) := by
    intro k hk1 hka hdvd
    let u := j + 2 * (a - k)
    have hu_lt : u < V.length := by dsimp only [u]; omega
    have hfu := hrun (a - k) (by omega)
    have hVu : V[u]! = true := (has (a - k) (by omega)).1
    have hdiff : wordRelPot V r (j + 2 * a + 1) - wordRelPot V r u = 3 * (k : Int) := by
      rw [hpt, hfu.2]
      have : ((a - k : Nat) : Int) = (a : Int) - (k : Int) := by omega
      omega
    rw [← hdiff] at hdvd
    have hord := seeded_replay_periodic_typeIIFresh_residue_order b s R st V r hbal (by omega) hR hm
      (j + 2 * a) u ht_lt hu_lt hS hht hVu hfu.1 hdvd
    have hle := hord.1 hneg
    omega
  refine ⟨hnodiv, ?_, ?_⟩
  · apply Classical.byContradiction
    intro hge
    have hdpos : 1 ≤ (wordPotDrift V r).natAbs := by omega
    have hdvd : ((wordPotDrift V r).natAbs : Int) ∣ (3 * ((wordPotDrift V r).natAbs : Int)) :=
      ⟨3, by omega⟩
    exact hnodiv (wordPotDrift V r).natAbs hdpos (by omega) hdvd
  · intro h3d
    obtain ⟨q, hq⟩ := h3d
    have hm_pos : 1 ≤ (-q).toNat := by omega
    have hm_eq : (wordPotDrift V r).natAbs = 3 * (-q).toNat := by omega
    apply Classical.byContradiction
    intro hge
    have hm_le : (-q).toNat ≤ a := by omega
    have hdvd : ((wordPotDrift V r).natAbs : Int) ∣ (3 * (((-q).toNat : Nat) : Int)) := by
      refine ⟨1, ?_⟩
      omega
    exact hnodiv (-q).toNat hm_pos hm_le hdvd

/-! ## Window count splitting and periodic aggregation -/

private theorem lowAdditionWeights_split (f : Nat → Bool) (r : Int) (s : Nat) :
    ∀ K, lowAdditionWeights f 0 r (s + K) =
      lowAdditionWeights f 0 r s + lowAdditionWeights f s r K
  | 0 => by simp [lowAdditionWeights]
  | K + 1 => by
    have ih := lowAdditionWeights_split f r s K
    rw [show s + (K + 1) = (s + K) + 1 by omega]
    simp only [lowAdditionWeights, Nat.zero_add]
    omega

private theorem cN_add_split (P : Nat → Prop) (s : Nat) :
    ∀ K, cN P 0 (s + K) = cN P 0 s + cN P s K
  | 0 => by simp [cN]
  | K + 1 => by
    have ih := cN_add_split P s K
    rw [show s + (K + 1) = (s + K) + 1 by omega]
    simp only [cN, Nat.zero_add]
    omega

private theorem doubleAscent_split_le (f : Nat → Bool) (s K : Nat) (h : Int) :
    doubleAscent f 0 (s + K) h ≤
      doubleAscent f 0 s h + (if s = 0 then 0 else 1) + doubleAscent f s K h := by
  unfold doubleAscent
  rw [cN_add_split]
  have htail :
      cN (fun t => Fw f t = h ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < 0 + (s + K)) s K =
      cN (fun t => Fw f t = h ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < s + K) s K := by
    simp only [Nat.zero_add]
  rw [htail]
  cases s with
  | zero =>
    simp [cN]
  | succ s' =>
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    have hhead :
        cN (fun t => Fw f t = h ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < 0 + (s' + 1 + K)) 0 (s' + 1) ≤
        cN (fun t => Fw f t = h ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < 0 + (s' + 1)) 0 (s' + 1) + 1 := by
      simp only [cN, Nat.zero_add]
      have hsub :
          cN (fun t => Fw f t = h ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < s' + 1 + K) 0 s' ≤
          cN (fun t => Fw f t = h ∧ f t = true ∧ f (t + 1) = true ∧ t + 1 < s' + 1) 0 s' := by
        apply cN_mono
        intro t _ ht htP
        exact ⟨htP.1, htP.2.1, htP.2.2.1, by omega⟩
      split <;> split <;> omega
    omega

private theorem levelSupplied_le_prefix (f : Nat → Bool) (s K : Nat) (h : Int) :
    levelSupplied f s K h ≤ levelSupplied f 0 (s + K) h := by
  unfold levelSupplied
  rw [cN_add_split]
  omega

private theorem levelAdditions_split_supplied_free (f : Nat → Bool) (s K : Nat) (h : Int) :
    levelAdditions f s K h = levelSupplied f s K h + levelFree f s K h := by
  unfold levelAdditions levelSupplied levelFree
  induction K with
  | zero => simp [cN]
  | succ K ih =>
    simp only [cN]
    by_cases hA : Fw f (s + K) = h ∧ f (s + K) = true
    · by_cases hE : EndN f 0 (s + K)
      · rw [if_pos hA, if_pos ⟨hA.1, hE⟩, if_neg (fun hx => hx.2.2 hE)]; omega
      · rw [if_pos hA, if_neg (fun hx => hE hx.2), if_pos ⟨hA.1, hA.2, hE⟩]; omega
    · have h1 : ¬ (Fw f (s + K) = h ∧ EndN f 0 (s + K)) := fun hx => hA ⟨hx.1, hx.2.1⟩
      have h2 : ¬ (Fw f (s + K) = h ∧ f (s + K) = true ∧ ¬ EndN f 0 (s + K)) :=
        fun hx => hA ⟨hx.1, hx.2.1⟩
      rw [if_neg hA, if_neg h1, if_neg h2]; omega

private theorem single_copy_lowWeights (f : Nat → Bool) (s : Nat) (V : List Bool)
    (hbal : mass V = 0) (R c : Nat) (hc : c < R)
    (hm : MatchesAt f s (repeatWord R V)) (r : Int) :
    ∀ k, k ≤ V.length →
      lowAdditionWeights f (s + c * V.length) (Fw f s + r) k = wordLowWeightsUpTo V r k
  | 0, _ => by simp [lowAdditionWeights, wordLowWeightsUpTo]
  | k + 1, hk => by
    have ih := single_copy_lowWeights f s V hbal R c hc hm r k (by omega)
    simp only [lowAdditionWeights, wordLowWeightsUpTo, ih]
    have hper := periodic_height_and_pot_local f s V hbal R hm c k hc (by omega) r
    have hmc := matchesAt_repeat_copy_local f s V R c hc hm k (by omega)
    unfold lowAdditionWeight
    rw [hmc, hper.1]
    by_cases h : V[k]! = true ∧ wordHeight V k < r
    · have h' : V[k]! = true ∧ Fw f s + wordHeight V k < Fw f s + r := ⟨h.1, by omega⟩
      rw [if_pos h', if_pos h]; omega
    · have h' : ¬ (V[k]! = true ∧ Fw f s + wordHeight V k < Fw f s + r) := by
        intro hx; exact h ⟨hx.1, by omega⟩
      rw [if_neg h', if_neg h]

private theorem periodic_lowWeights_eq (f : Nat → Bool) (s : Nat) (V : List Bool)
    (hbal : mass V = 0) (R : Nat) (hm : MatchesAt f s (repeatWord R V)) (r : Int) :
    ∀ c, c ≤ R →
      lowAdditionWeights f s (Fw f s + r) (c * V.length) = (c : Int) * wordLowWeights V r
  | 0, _ => by simp [lowAdditionWeights]
  | c + 1, hc => by
    have ih := periodic_lowWeights_eq f s V hbal R hm r c (by omega)
    have hsplit : lowAdditionWeights f s (Fw f s + r) ((c + 1) * V.length) =
        lowAdditionWeights f s (Fw f s + r) (c * V.length) +
        lowAdditionWeights f (s + c * V.length) (Fw f s + r) V.length := by
      have h1 := lowAdditionWeights_split f (Fw f s + r) s ((c + 1) * V.length)
      have h2 := lowAdditionWeights_split f (Fw f s + r) s (c * V.length)
      have h3 := lowAdditionWeights_split f (Fw f s + r) (s + c * V.length) V.length
      have hidx : s + (c + 1) * V.length = s + c * V.length + V.length := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      rw [hidx] at h1
      omega
    rw [hsplit, ih, single_copy_lowWeights f s V hbal R c (by omega) hm r V.length (Nat.le_refl _)]
    unfold wordLowWeights
    push_cast
    rw [Int.add_mul, Int.one_mul]

private theorem single_copy_levelAdditions (f : Nat → Bool) (s : Nat) (V : List Bool)
    (hbal : mass V = 0) (R c : Nat) (hc : c < R)
    (hm : MatchesAt f s (repeatWord R V)) (h : Int) :
    ∀ k, k ≤ V.length →
      levelAdditions f (s + c * V.length) k (Fw f s + h) = wordLevelAdditionsUpTo V h k
  | 0, _ => by simp [levelAdditions, cN, wordLevelAdditionsUpTo]
  | k + 1, hk => by
    have ih := single_copy_levelAdditions f s V hbal R c hc hm h k (by omega)
    unfold levelAdditions at ih ⊢
    simp only [cN, wordLevelAdditionsUpTo, ih]
    have hper := periodic_height_and_pot_local f s V hbal R hm c k hc (by omega) h
    have hmc := matchesAt_repeat_copy_local f s V R c hc hm k (by omega)
    by_cases hp : V[k]! = true ∧ wordHeight V k = h
    · have hp' : Fw f (s + c * V.length + k) = Fw f s + h ∧ f (s + c * V.length + k) = true :=
        ⟨by rw [hper.1, hp.2], by rw [hmc, hp.1]⟩
      rw [if_pos hp', if_pos hp]
    · have hp' : ¬ (Fw f (s + c * V.length + k) = Fw f s + h ∧ f (s + c * V.length + k) = true) := by
        intro hx
        rw [hper.1] at hx
        rw [hmc] at hx
        exact hp ⟨hx.2, by omega⟩
      rw [if_neg hp', if_neg hp]

private theorem periodic_levelAdditions_eq (f : Nat → Bool) (s : Nat) (V : List Bool)
    (hbal : mass V = 0) (R : Nat) (hm : MatchesAt f s (repeatWord R V)) (h : Int) :
    ∀ c, c ≤ R →
      levelAdditions f s (c * V.length) (Fw f s + h) = c * wordLevelAdditions V h
  | 0, _ => by simp [levelAdditions, cN]
  | c + 1, hc => by
    have ih := periodic_levelAdditions_eq f s V hbal R hm h c (by omega)
    have hsplit : levelAdditions f s ((c + 1) * V.length) (Fw f s + h) =
        levelAdditions f s (c * V.length) (Fw f s + h) +
        levelAdditions f (s + c * V.length) V.length (Fw f s + h) := by
      unfold levelAdditions
      have h1 := cN_add_split (fun t => Fw f t = Fw f s + h ∧ f t = true) s ((c + 1) * V.length)
      have h2 := cN_add_split (fun t => Fw f t = Fw f s + h ∧ f t = true) s (c * V.length)
      have h3 := cN_add_split (fun t => Fw f t = Fw f s + h ∧ f t = true) (s + c * V.length) V.length
      have hidx : s + (c + 1) * V.length = s + c * V.length + V.length := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      rw [hidx] at h1
      omega
    rw [hsplit, ih, single_copy_levelAdditions f s V hbal R c (by omega) hm h V.length (Nat.le_refl _)]
    unfold wordLevelAdditions
    rw [Nat.add_mul, Nat.one_mul]

private theorem arbitrary_offset_two_height_budget (f : Nat → Bool) (s K : Nat) (r_abs : Int) :
    ((3 * levelSupplied f s K (r_abs + 1) + levelSupplied f s K r_abs : Nat) : Int) ≤
      lowAdditionWeights f s r_abs K + ((3 * doubleAscent f s K (r_abs - 1) : Nat) : Int) +
        prefixBudgetSlack f s r_abs := by
  have hbud := actual_double_ascent_spacing_budget f 0 0 (s + K) 0 r_abs (by omega)
    BlockWord.nil (by simp [seg])
  simp only [Nat.zero_mul, Nat.add_zero] at hbud
  have hE1 := levelSupplied_le_prefix f s K (r_abs + 1)
  have hE0 := levelSupplied_le_prefix f s K r_abs
  have hW := lowAdditionWeights_split f r_abs s K
  have hAA := doubleAscent_split_le f s K (r_abs - 1)
  unfold prefixBudgetSlack
  omega

/-! ## Positive-drift top-level collapse (`d ≥ 0`) & sign-free golden-ratio law -/

/-- Positive-drift arbitrary-`d` top-level `E_{H-1}` collapse on EVERY coherent
`SeededReplay.run b st` (with ZERO `BlockWord` assumption!): whenever balanced `V` has max
addition height `≤ H`, nonnegative drift `0 ≤ wordPotDrift V (H - 1)` (arbitrary `d ≥ 0`,
extending `E-798`'s unit-drift `|d| = 1`), and repeats `R ≥ 1` times at offset `s`:
  `E_{H-1}(V^R) ≤ 3 * F_H(V^R) + 3 * AA_{H-2}(V^R) + span + |d| + 1 + prefixBudgetSlack`. -/
theorem seeded_replay_periodic_pos_drift_top_collapse (b s R : Nat) (st : State)
    (hs : st.value ∈ st.seen) (V : List Bool) (H : Int)
    (hbal : mass V = 0)
    (hceil : ∀ j, j < V.length → V[j]! = true → wordHeight V j ≤ H)
    (hpos : 0 ≤ wordPotDrift V (H - 1)) (hR : 1 ≤ R)
    (hm : MatchesAt (replaySign b st) s (repeatWord R V)) :
    (levelSupplied (replaySign b st) s (R * V.length) (Fw (replaySign b st) s + (H - 1)) : Int) ≤
      ((3 * levelFree (replaySign b st) s (R * V.length) (Fw (replaySign b st) s + H) +
        3 * doubleAscent (replaySign b st) s (R * V.length)
          (Fw (replaySign b st) s + (H - 1) - 1) : Nat) : Int) +
      (wordPotSpan V (H - 1) : Int) + ((wordPotDrift V (H - 1)).natAbs : Int) + 1 +
      prefixBudgetSlack (replaySign b st) s (Fw (replaySign b st) s + (H - 1)) := by
  let f := replaySign b st
  let r := H - 1
  let r_abs := Fw f s + r
  let K := R * V.length
  change (levelSupplied f s K r_abs : Int) ≤
    ((3 * levelFree f s K (Fw f s + H) +
      3 * doubleAscent f s K (r_abs - 1) : Nat) : Int) +
    (wordPotSpan V r : Int) + ((wordPotDrift V r).natAbs : Int) + 1 +
    prefixBudgetSlack f s r_abs
  have hr1 : r + 1 = H := by dsimp only [r]; omega
  have hr_abs1 : r_abs + 1 = Fw f s + H := by dsimp only [r_abs, r]; omega
  -- 1. E-797 two-height budget lifted to offset s
  have hbud := arbitrary_offset_two_height_budget f s K r_abs
  rw [hr_abs1] at hbud
  -- 2. E-798 periodic S-freshness pigeonhole bound: R * A_{H-1} <= span + (R - 1) * d + 1
  have hpig := seeded_replay_periodic_s_count_le_drift b s R st hs V r hbal hR hm
  rw [balanced_word_sLandings_eq_levelAdditions V r hbal] at hpig
  have hpigI : (R : Int) * (wordLevelAdditions V r : Int) ≤
      (wordPotSpan V r : Int) + ((R - 1 : Nat) : Int) * ((wordPotDrift V r).natAbs : Int) + 1 := by
    exact_mod_cast hpig
  have hR1 : ((R - 1 : Nat) : Int) = (R : Int) - 1 := by omega
  have hd_abs : ((wordPotDrift V r).natAbs : Int) = wordPotDrift V r :=
    Int.natAbs_of_nonneg hpos
  rw [hR1, Int.sub_mul, Int.one_mul, hd_abs] at hpigI
  -- 3. Exact balanced area-potential identity with upperExcess = 0
  have hid := balanced_word_area_potential_identity V r hbal
  rw [hr1, wordUpperExcess_zero_of_ceil V H hceil, Int.add_zero] at hid
  have hidR : (R : Int) * wordLowWeights V r + (R : Int) * wordPotDrift V r =
      (R : Int) * (wordLevelAdditions V r : Int) +
        3 * ((R : Int) * (wordLevelAdditions V H : Int)) := by
    have h1 : (R : Int) * (wordLowWeights V r + wordPotDrift V r) =
        (R : Int) * ((wordLevelAdditions V r : Int) + 3 * (wordLevelAdditions V H : Int)) := by
      rw [hid]
    rw [Int.mul_add, Int.mul_add] at h1
    have hassoc : (R : Int) * (3 * (wordLevelAdditions V H : Int)) =
        3 * ((R : Int) * (wordLevelAdditions V H : Int)) := by
      rw [← Int.mul_assoc, Int.mul_comm (R : Int) 3, Int.mul_assoc]
    omega
  -- 4. Bridge word counts to window counts
  have hW_eq : lowAdditionWeights f s r_abs K = (R : Int) * wordLowWeights V r :=
    periodic_lowWeights_eq f s V hbal R hm r R (Nat.le_refl _)
  have hAH_eq : levelAdditions f s K (Fw f s + H) = R * wordLevelAdditions V H :=
    periodic_levelAdditions_eq f s V hbal R hm H R (Nat.le_refl _)
  have hAH_sp := levelAdditions_split_supplied_free f s K (Fw f s + H)
  have hAH_I : (R : Int) * (wordLevelAdditions V H : Int) =
      (levelSupplied f s K (Fw f s + H) : Int) + (levelFree f s K (Fw f s + H) : Int) := by
    have hNat : R * wordLevelAdditions V H =
        levelSupplied f s K (Fw f s + H) + levelFree f s K (Fw f s + H) := by
      rw [← hAH_eq, hAH_sp]
    exact_mod_cast hNat
  -- Combine: W(H-1) <= 3*E_H + 3*F_H + span + d + 1, and 3*E_H + E_{H-1} <= W(H-1) + 3*AA_{H-2} + pref
  have hW_le : lowAdditionWeights f s r_abs K ≤
      3 * ((levelSupplied f s K (Fw f s + H) : Int) + (levelFree f s K (Fw f s + H) : Int)) +
        (wordPotSpan V r : Int) + wordPotDrift V r + 1 := by
    rw [hW_eq, ← hAH_I]
    omega
  rw [hd_abs]
  omega

/-- Unconditional sign-free top-level golden-ratio capacity on EVERY coherent
`SeededReplay.run b st` (valid for ALL drifts `wordPotDrift V (H - 1) : Int`, with ZERO
`BlockWord` assumption!):
  `3 * E_H(V^R) + 2 * E_{H-1}(V^R) ≤ W(H - 1)(V^R) + 6 * AA_{H-2}(V^R) + 3 * F_H(V^R) + span + |d| + 1 + 2 * prefixBudgetSlack`.
Raw non-fresh `E-786` (`d = 0`) violates this inequality unboundedly as `R → ∞`. -/
theorem seeded_replay_periodic_top_golden_capacity (b s R : Nat) (st : State)
    (hs : st.value ∈ st.seen) (V : List Bool) (H : Int)
    (hbal : mass V = 0)
    (hceil : ∀ j, j < V.length → V[j]! = true → wordHeight V j ≤ H)
    (hR : 1 ≤ R)
    (hm : MatchesAt (replaySign b st) s (repeatWord R V)) :
    ((3 * levelSupplied (replaySign b st) s (R * V.length) (Fw (replaySign b st) s + H) +
      2 * levelSupplied (replaySign b st) s (R * V.length)
        (Fw (replaySign b st) s + (H - 1)) : Nat) : Int) ≤
      lowAdditionWeights (replaySign b st) s (Fw (replaySign b st) s + (H - 1)) (R * V.length) +
      ((6 * doubleAscent (replaySign b st) s (R * V.length)
          (Fw (replaySign b st) s + (H - 1) - 1) +
        3 * levelFree (replaySign b st) s (R * V.length) (Fw (replaySign b st) s + H) : Nat) : Int) +
      (wordPotSpan V (H - 1) : Int) + ((wordPotDrift V (H - 1)).natAbs : Int) + 1 +
      2 * prefixBudgetSlack (replaySign b st) s (Fw (replaySign b st) s + (H - 1)) := by
  let f := replaySign b st
  let r := H - 1
  let r_abs := Fw f s + r
  let K := R * V.length
  change ((3 * levelSupplied f s K (Fw f s + H) +
      2 * levelSupplied f s K r_abs : Nat) : Int) ≤
    lowAdditionWeights f s r_abs K +
    ((6 * doubleAscent f s K (r_abs - 1) +
      3 * levelFree f s K (Fw f s + H) : Nat) : Int) +
    (wordPotSpan V r : Int) + ((wordPotDrift V r).natAbs : Int) + 1 +
    2 * prefixBudgetSlack f s r_abs
  have hr1 : r + 1 = H := by dsimp only [r]; omega
  have hr_abs1 : r_abs + 1 = Fw f s + H := by dsimp only [r_abs, r]; omega
  by_cases hpos : 0 ≤ wordPotDrift V r
  · have hcol : (levelSupplied f s K r_abs : Int) ≤
        ((3 * levelFree f s K (Fw f s + H) +
          3 * doubleAscent f s K (r_abs - 1) : Nat) : Int) +
        (wordPotSpan V r : Int) + ((wordPotDrift V r).natAbs : Int) + 1 +
        prefixBudgetSlack f s r_abs :=
      seeded_replay_periodic_pos_drift_top_collapse b s R st hs V H hbal hceil hpos hR hm
    have hbud := arbitrary_offset_two_height_budget f s K r_abs
    rw [hr_abs1] at hbud
    omega
  · have hneg : wordPotDrift V r ≤ 0 := by omega
    have hnd := seeded_replay_periodic_neg_drift_capacity b s R st hs V r hbal hneg hR hm
    rw [hr1, wordUpperExcess_zero_of_ceil V H hceil, Int.mul_zero, Int.add_zero] at hnd
    have hW_eq : lowAdditionWeights f s r_abs K = (R : Int) * wordLowWeights V r :=
      periodic_lowWeights_eq f s V hbal R hm r R (Nat.le_refl _)
    have hAH_eq : levelAdditions f s K (Fw f s + H) = R * wordLevelAdditions V H :=
      periodic_levelAdditions_eq f s V hbal R hm H R (Nat.le_refl _)
    have hAr_eq : levelAdditions f s K r_abs = R * wordLevelAdditions V r :=
      periodic_levelAdditions_eq f s V hbal R hm r R (Nat.le_refl _)
    have hEH_le : levelSupplied f s K (Fw f s + H) ≤ R * wordLevelAdditions V H := by
      rw [← hAH_eq, levelAdditions_split_supplied_free]; omega
    have hEr_le : levelSupplied f s K r_abs ≤ R * wordLevelAdditions V r := by
      rw [← hAr_eq, levelAdditions_split_supplied_free]; omega
    have hpref_nn : 0 ≤ prefixBudgetSlack f s r_abs := by
      unfold prefixBudgetSlack
      have hwn := low_weights_nonnegative f 0 r_abs s
      omega
    have hcast :
        (R : Int) * ((3 * wordLevelAdditions V H + 2 * wordLevelAdditions V r : Nat) : Int) =
        ((3 * (R * wordLevelAdditions V H) + 2 * (R * wordLevelAdditions V r) : Nat) : Int) := by
      push_cast
      rw [Int.mul_add]
      have h1 : (R : Int) * (3 * (wordLevelAdditions V H : Int)) =
          3 * ((R : Int) * (wordLevelAdditions V H : Int)) := by
        rw [← Int.mul_assoc, Int.mul_comm (R : Int) 3, Int.mul_assoc]
      have h2 : (R : Int) * (2 * (wordLevelAdditions V r : Int)) =
          2 * ((R : Int) * (wordLevelAdditions V r : Int)) := by
        rw [← Int.mul_assoc, Int.mul_comm (R : Int) 2, Int.mul_assoc]
      omega
    rw [hcast] at hnd
    rw [hW_eq]
    omega

/-- Canonical clock-0 Recamán specialization of the sign-free top-level golden-ratio law:
holds unconditionally at EVERY clock `s : Nat`, EVERY balanced word `V` of max addition
height `≤ H`, and EVERY repetition count `R ≥ 1` in `Recaman.Basic.a`. -/
theorem canonical_periodic_top_golden_capacity (s R : Nat) (V : List Bool) (H : Int)
    (hbal : mass V = 0)
    (hceil : ∀ j, j < V.length → V[j]! = true → wordHeight V j ≤ H)
    (hR : 1 ≤ R)
    (hm : MatchesAt canonicalOrbitSign s (repeatWord R V)) :
    ((3 * levelSupplied canonicalOrbitSign s (R * V.length) (Fw canonicalOrbitSign s + H) +
      2 * levelSupplied canonicalOrbitSign s (R * V.length)
        (Fw canonicalOrbitSign s + (H - 1)) : Nat) : Int) ≤
      lowAdditionWeights canonicalOrbitSign s (Fw canonicalOrbitSign s + (H - 1)) (R * V.length) +
      ((6 * doubleAscent canonicalOrbitSign s (R * V.length)
          (Fw canonicalOrbitSign s + (H - 1) - 1) +
        3 * levelFree canonicalOrbitSign s (R * V.length)
          (Fw canonicalOrbitSign s + H) : Nat) : Int) +
      (wordPotSpan V (H - 1) : Int) + ((wordPotDrift V (H - 1)).natAbs : Int) + 1 +
      2 * prefixBudgetSlack canonicalOrbitSign s (Fw canonicalOrbitSign s + (H - 1)) := by
  have hs0 : initial.value ∈ initial.seen := by simp [initial]
  exact seeded_replay_periodic_top_golden_capacity 0 s R initial hs0 V H hbal hceil hR hm

end Recaman.PeriodicGreedyDriftCapacity
