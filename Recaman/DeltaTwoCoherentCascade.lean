import Recaman.DynamicPredecessorObstruction
import Recaman.ExponentialHeightCascade

namespace Recaman.DeltaTwoCoherentCascade

open Recaman Recaman.SeededReplay Recaman.CoherentGreedyFreshness
open Recaman.DynamicPredecessorObstruction Recaman.ExponentialHeightCascade
open Recaman.FloorSupplyPotential Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction
open Recaman.CrossBlockReuseUnbounded Recaman.LineCapacityPeriodic
open Recaman.LeadingRunSupply Recaman.AdditionRankSlack
open Recaman.ShortPeriodicSupply (sign)

/-! # Optimal Unit-Drift `Δ = 2` Coherent Greedy Exponential Cascade (`E-805`)

Upgrades `E-799` (`PROVED-PAPER`) to `PROVED-LEAN`, establishing the first
unconditional `PROVED-LEAN` exponential growth lower bound **`ρ_greedy ≥ √(7/3) ≈ 1.527525`**
directly on actual coherent finite-state greedy continuations `SeededReplay.run b st`
(`st.value ∈ st.seen`):

1. Compositional freshness algebra (`FreshWord`, `KeyAt`, `SLandAt`, `fresh_append`,
   `fresh_repeatWord`) proving `TypeIFresh ∧ TypeIIFresh` from corridor separation.
2. Exact stage-lift construction `V_k = (AS)^q ++ (SA)^p ++ B_{k-1} ++ A^h (AS)^a S^h`,
   `V_{0, k} = A^{h-1} (SA)^{bank} A (AS)^{lift} S^h`, `B_k = V_{0, k} ++ V_k^{R_k}`
   on height ladder `h_k = 2k + 2` (relative height band `[-1, 2k + 3]`) satisfying:
   - `TypeIFresh ∧ TypeIIFresh` (hence coherent `SeededReplay.run` realizable by `E-801`),
   - 100% bank + self-extending `S`-landing supply of `(AS)^a` across all `R_k` copies,
   - One-step `7/3` growth lift: for every `k ≥ 1` and scale parameter `M ≥ 200`,
     `A(B_k) / F(B_k)` grows by `(2 * (21 * M - 1)) / (3 * (6 * M + 1))` per stage (`Δ = 2` height step).
3. Direct `SeededReplay.run` theorem: for every rational base `P / Q < √(7/3)`
   (`3 * P^2 < 7 * Q^2`) and every constant `C : Nat`, there exist `k ≥ 1`, a base clock `b`,
   a coherent state `st` (`st.value ∈ st.seen`), and an actual greedy continuation of length
   `L` confined to height band `[-1, 2k + 3]` satisfying
   `C * P ^ (2 * k + 4) * free (replaySign b st) 0 L < Q ^ (2 * k + 4) * additions (replaySign b st) 0 L`.
-/

/-- Word-level height-`r` potential at prefix index `i`: `areaW (w.take i) - i * r`. -/
def wordPot (w : List Bool) (r : Int) (i : Nat) : Int :=
  areaW (w.take i) - (i : Int) * r

/-- Total height-`r` potential drift of a finite word `w`: `areaW w - w.length * r`. -/
def dphiW (w : List Bool) (r : Int) : Int :=
  areaW w - (w.length : Int) * r

/-- Combined `E-759` freshness predicate for a finite word `w`. -/
def FreshWord (w : List Bool) : Prop :=
  TypeIFresh (wordSign w) w.length ∧ TypeIIFresh (wordSign w) w.length

/-- Output visit key `(r, ϕ)` in `w` (including index `0` and index `w.length`). -/
def VisitsAt (w : List Bool) (r ϕ : Int) : Prop :=
  ∃ i, i ≤ w.length ∧ wordHeight w i = r ∧ wordPot w r i = ϕ

/-- Rejected `A`-candidate key `(r, ϕ)` in `w` (from an `A`-step at height `r + 1`). -/
def CandAt (w : List Bool) (r ϕ : Int) : Prop :=
  ∃ i, i < w.length ∧ w[i]! = true ∧ wordHeight w i = r + 1 ∧ wordPot w r i = ϕ

/-- Any prior blocking key `(r, ϕ)` in `w` (either output visit or rejected `A`-candidate). -/
def KeyAt (w : List Bool) (r ϕ : Int) : Prop :=
  VisitsAt w r ϕ ∨ CandAt w r ϕ

/-- `S`-landing key `(r, ϕ)` in `w` (from an `S`-step landing at height `r`). -/
def SLandAt (w : List Bool) (r ϕ : Int) : Prop :=
  ∃ i, i < w.length ∧ w[i]! = false ∧ wordHeight w (i + 1) = r ∧ wordPot w r (i + 1) = ϕ

/-! ## Basic `wordPot` / `dphiW` / `FreshWord` composition lemmas -/

private theorem seg_wordSign_eq_take (w : List Bool) :
    ∀ i, i ≤ w.length → seg (wordSign w) 0 i = w.take i
  | 0, _ => by simp [seg]
  | k + 1, hk => by
    rw [seg_succ, seg_wordSign_eq_take w k (by omega)]
    have hlt : k < w.length := by omega
    rw [List.take_succ_eq_append_getElem hlt]
    simp [wordSign, Nat.zero_add, hlt]

private theorem wordHeight_eq_Fw_wordSign (w : List Bool) (i : Nat) (hi : i ≤ w.length) :
    wordHeight w i = Fw (wordSign w) i := by
  have h1 := seg_mass (wordSign w) 0 i
  rw [seg_wordSign_eq_take w i hi, Nat.zero_add] at h1
  have h0 : Fw (wordSign w) 0 = 0 := rfl
  unfold wordHeight
  omega

private theorem wordPot_eq_floorPotential (w : List Bool) (r : Int) (i : Nat) (hi : i ≤ w.length) :
    wordPot w r i = floorPotential (wordSign w) 0 (r - 1) i := by
  unfold wordPot floorPotential
  have h0 : Fw (wordSign w) 0 = 0 := rfl
  have hAr : Ar (wordSign w) 0 i = areaW (w.take i) := by
    rw [Ar_areaW, seg_wordSign_eq_take w i hi]
  simp only [Nat.sub_zero, h0, hAr]
  grind

private theorem areaW_append_of_mass_zero {u v : List Bool} (hm : mass u = 0) :
    areaW (u ++ v) = areaW u + areaW v := by
  have h1 := area_split_at (wordSign (u ++ v)) 0 u.length (u.length + v.length)
    (Nat.zero_le _) (Nat.le_add_right _ _)
  rw [Nat.sub_zero, Nat.sub_zero, Nat.add_sub_cancel_left] at h1
  have hseg_uv : seg (wordSign (u ++ v)) 0 (u.length + v.length) = u ++ v := by
    have h := seg_wordSign_eq_take (u ++ v) (u ++ v).length (Nat.le_refl _)
    rw [List.take_length] at h
    simpa [List.length_append] using h
  have hseg_u : seg (wordSign (u ++ v)) 0 u.length = u := by
    have h := seg_wordSign_eq_take (u ++ v) u.length (by simp)
    simpa [List.take_left] using h
  have hseg_v : seg (wordSign (u ++ v)) u.length v.length = v := by
    have haux : ∀ k, k ≤ v.length → seg (wordSign (u ++ v)) u.length k = v.take k := by
      intro k
      induction k with
      | zero => intro _; simp [seg]
      | succ k ih =>
        intro hk
        rw [seg_succ, ih (by omega), List.take_succ_eq_append_getElem (by omega)]
        simp [wordSign, show k < v.length by omega]
    simpa using haux v.length (Nat.le_refl _)
  rw [Ar_areaW, hseg_uv, Ar_areaW, hseg_u, Ar_areaW, hseg_v] at h1
  have hFu : Fw (wordSign (u ++ v)) u.length = 0 := by
    have hm1 := seg_mass (wordSign (u ++ v)) 0 u.length
    rw [hseg_u, hm, Nat.zero_add] at hm1
    have h0 : Fw (wordSign (u ++ v)) 0 = 0 := rfl
    omega
  have h0 : Fw (wordSign (u ++ v)) 0 = 0 := rfl
  rw [hFu, h0] at h1
  omega

private theorem dphiW_append {u v : List Bool} (hm : mass u = 0) (r : Int) :
    dphiW (u ++ v) r = dphiW u r + dphiW v r := by
  unfold dphiW
  rw [areaW_append_of_mass_zero hm, List.length_append]
  push_cast
  grind

private theorem dphiW_shift (w : List Bool) (r d : Int) :
    dphiW w (r + d) = dphiW w r - d * (w.length : Int) := by
  unfold dphiW
  grind

private theorem wordHeight_append_left {u v : List Bool} (i : Nat) (hi : i ≤ u.length) :
    wordHeight (u ++ v) i = wordHeight u i := by
  unfold wordHeight
  rw [List.take_append_of_le_length hi]

private theorem wordHeight_append_right {u v : List Bool} (hm : mass u = 0)
    (j : Nat) (_hj : j ≤ v.length) :
    wordHeight (u ++ v) (u.length + j) = wordHeight v j := by
  unfold wordHeight
  rw [List.take_append, List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    mass_append, hm, Int.zero_add]

private theorem wordPot_append_left {u v : List Bool} (r : Int) (i : Nat) (hi : i ≤ u.length) :
    wordPot (u ++ v) r i = wordPot u r i := by
  unfold wordPot
  rw [List.take_append_of_le_length hi]

private theorem wordPot_append_right {u v : List Bool} (hm : mass u = 0) (r : Int)
    (j : Nat) (_hj : j ≤ v.length) :
    wordPot (u ++ v) r (u.length + j) = dphiW u r + wordPot v r j := by
  unfold wordPot dphiW
  rw [List.take_append, List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    areaW_append_of_mass_zero hm]
  push_cast
  grind

/-- Master compositional freshness lemma (`E-805`): concatenating balanced `u` and `v`
preserves `FreshWord` (`TypeIFresh ∧ TypeIIFresh`) whenever every `S`-landing `(r, ϕ)` of `v`
shifted by `dphiW u r` avoids every output visit and rejected `A`-candidate `KeyAt u r`. -/
theorem fresh_append {u v : List Bool} (hm : mass u = 0)
    (hu : FreshWord u) (hv : FreshWord v)
    (hdisj : ∀ r ϕ, SLandAt v r ϕ → ¬ KeyAt u r (dphiW u r + ϕ)) :
    FreshWord (u ++ v) := by
  have hget_left : ∀ i, i < u.length → (u ++ v)[i]! = u[i]! := by
    intro i hi
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hi]
  have hget_right : ∀ j, j < v.length → (u ++ v)[u.length + j]! = v[j]! := by
    intro j hj
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right u.length j)]
  have hws_left : ∀ i, i < u.length → wordSign (u ++ v) i = wordSign u i := by
    intro i hi; exact hget_left i hi
  have hws_right : ∀ j, j < v.length → wordSign (u ++ v) (u.length + j) = wordSign v j := by
    intro j hj; exact hget_right j hj
  constructor
  · -- TypeIFresh
    intro t ht hft k hkt hFk hpeq
    rw [List.length_append] at ht
    by_cases htu : t < u.length
    · -- Both `k ≤ t < u.length` lie inside `u`
      have hft' : wordSign u t = false := by rw [← hws_left t htu]; exact hft
      rw [← wordHeight_eq_Fw_wordSign (u ++ v) k (by simp; omega),
        ← wordHeight_eq_Fw_wordSign (u ++ v) (t + 1) (by simp; omega),
        wordHeight_append_left k (by omega),
        wordHeight_append_left (t + 1) (by omega),
        wordHeight_eq_Fw_wordSign u k (by omega),
        wordHeight_eq_Fw_wordSign u (t + 1) (by omega)] at hFk
      rw [← wordPot_eq_floorPotential (u ++ v) (Fw (wordSign (u ++ v)) (t + 1)) (t + 1) (by simp; omega),
        ← wordPot_eq_floorPotential (u ++ v) (Fw (wordSign (u ++ v)) (t + 1)) k (by simp; omega),
        ← wordHeight_eq_Fw_wordSign (u ++ v) (t + 1) (by simp; omega),
        wordHeight_append_left (t + 1) (by omega),
        wordPot_append_left _ (t + 1) (by omega),
        wordPot_append_left _ k (by omega),
        wordHeight_eq_Fw_wordSign u (t + 1) (by omega),
        wordPot_eq_floorPotential u _ (t + 1) (by omega),
        wordPot_eq_floorPotential u _ k (by omega)] at hpeq
      exact hu.1 t htu hft' k hkt hFk hpeq
    · -- `t = u.length + j` lies inside `v`
      let j := t - u.length
      have ht_eq : t = u.length + j := by omega
      have hjv : j < v.length := by omega
      have hfj : wordSign v j = false := by rw [← hws_right j hjv, ← ht_eq]; exact hft
      have hvj_false : v[j]! = false := hfj
      let r := wordHeight v (j + 1)
      have hFw_t1 : Fw (wordSign (u ++ v)) (t + 1) = r := by
        rw [← wordHeight_eq_Fw_wordSign (u ++ v) (t + 1) (by simp; omega),
          show t + 1 = u.length + (j + 1) by omega, wordHeight_append_right hm (j + 1) (by omega)]
      have hpot_t1 : floorPotential (wordSign (u ++ v)) 0 (Fw (wordSign (u ++ v)) (t + 1) - 1) (t + 1) =
          dphiW u r + wordPot v r (j + 1) := by
        rw [← wordPot_eq_floorPotential (u ++ v) _ (t + 1) (by simp; omega), hFw_t1,
          show t + 1 = u.length + (j + 1) by omega, wordPot_append_right hm r (j + 1) (by omega)]
      by_cases hku : k ≤ u.length
      · -- `k` is in `u`, `t` is in `v` -> contradicts `hdisj`!
        have hFk' : wordHeight u k = r := by
          rw [← wordHeight_append_left k hku, wordHeight_eq_Fw_wordSign (u ++ v) k (by simp; omega),
            hFk, hFw_t1]
        have hpot_k : floorPotential (wordSign (u ++ v)) 0 (Fw (wordSign (u ++ v)) (t + 1) - 1) k =
            wordPot u r k := by
          rw [← wordPot_eq_floorPotential (u ++ v) _ k (by simp; omega), hFw_t1,
            wordPot_append_left r k hku]
        have hS : SLandAt v r (wordPot v r (j + 1)) := ⟨j, hjv, hvj_false, rfl, rfl⟩
        have hV : KeyAt u r (dphiW u r + wordPot v r (j + 1)) :=
          Or.inl ⟨k, hku, hFk', by omega⟩
        exact hdisj r (wordPot v r (j + 1)) hS hV
      · -- Both `k = u.length + i` and `t = u.length + j` lie in `v` -> contradicts `hv.1`!
        let i := k - u.length
        have hk_eq : k = u.length + i := by omega
        have hiv : i ≤ j := by omega
        have hFi : Fw (wordSign v) i = Fw (wordSign v) (j + 1) := by
          rw [← wordHeight_eq_Fw_wordSign v i (by omega),
            ← wordHeight_eq_Fw_wordSign v (j + 1) (by omega),
            ← wordHeight_append_right hm i (by omega), ← hk_eq,
            wordHeight_eq_Fw_wordSign (u ++ v) k (by simp; omega), hFk, hFw_t1]
        have hpot_k : floorPotential (wordSign (u ++ v)) 0 (Fw (wordSign (u ++ v)) (t + 1) - 1) k =
            dphiW u r + wordPot v r i := by
          rw [← wordPot_eq_floorPotential (u ++ v) _ k (by simp; omega), hFw_t1,
            hk_eq, wordPot_append_right hm r i (by omega)]
        have hpeq_v : floorPotential (wordSign v) 0 (Fw (wordSign v) (j + 1) - 1) (j + 1) =
            floorPotential (wordSign v) 0 (Fw (wordSign v) (j + 1) - 1) i := by
          rw [← wordPot_eq_floorPotential v _ (j + 1) (by omega),
            ← wordPot_eq_floorPotential v _ i (by omega),
            ← wordHeight_eq_Fw_wordSign v (j + 1) (by omega)]
          change wordPot v r (j + 1) = wordPot v r i
          omega
        exact hv.1 j hjv hfj i hiv hFi hpeq_v
  · -- TypeIIFresh
    intro t ht hft k hkt hfk hFk hpeq
    rw [List.length_append] at ht
    by_cases htu : t < u.length
    · have hft' : wordSign u t = false := by rw [← hws_left t htu]; exact hft
      have hfk' : wordSign u k = true := by rw [← hws_left k (by omega)]; exact hfk
      rw [← wordHeight_eq_Fw_wordSign (u ++ v) k (by simp; omega),
        ← wordHeight_eq_Fw_wordSign (u ++ v) (t + 1) (by simp; omega),
        wordHeight_append_left k (by omega),
        wordHeight_append_left (t + 1) (by omega),
        wordHeight_eq_Fw_wordSign u k (by omega),
        wordHeight_eq_Fw_wordSign u (t + 1) (by omega)] at hFk
      rw [← wordPot_eq_floorPotential (u ++ v) (Fw (wordSign (u ++ v)) (t + 1)) (t + 1) (by simp; omega),
        ← wordPot_eq_floorPotential (u ++ v) (Fw (wordSign (u ++ v)) (t + 1)) k (by simp; omega),
        ← wordHeight_eq_Fw_wordSign (u ++ v) (t + 1) (by simp; omega),
        wordHeight_append_left (t + 1) (by omega),
        wordPot_append_left _ (t + 1) (by omega),
        wordPot_append_left _ k (by omega),
        wordHeight_eq_Fw_wordSign u (t + 1) (by omega),
        wordPot_eq_floorPotential u _ (t + 1) (by omega),
        wordPot_eq_floorPotential u _ k (by omega)] at hpeq
      exact hu.2 t htu hft' k hkt hfk' hFk hpeq
    · let j := t - u.length
      have ht_eq : t = u.length + j := by omega
      have hjv : j < v.length := by omega
      have hfj : wordSign v j = false := by rw [← hws_right j hjv, ← ht_eq]; exact hft
      have hvj_false : v[j]! = false := hfj
      let r := wordHeight v (j + 1)
      have hFw_t1 : Fw (wordSign (u ++ v)) (t + 1) = r := by
        rw [← wordHeight_eq_Fw_wordSign (u ++ v) (t + 1) (by simp; omega),
          show t + 1 = u.length + (j + 1) by omega, wordHeight_append_right hm (j + 1) (by omega)]
      have hpot_t1 : floorPotential (wordSign (u ++ v)) 0 (Fw (wordSign (u ++ v)) (t + 1) - 1) (t + 1) =
          dphiW u r + wordPot v r (j + 1) := by
        rw [← wordPot_eq_floorPotential (u ++ v) _ (t + 1) (by simp; omega), hFw_t1,
          show t + 1 = u.length + (j + 1) by omega, wordPot_append_right hm r (j + 1) (by omega)]
      by_cases hku : k < u.length
      · have huk_true : u[k]! = true := by
          rw [← hget_left k hku]; exact hfk
        have hFk' : wordHeight u k = r + 1 := by
          rw [← wordHeight_append_left k (by omega),
            wordHeight_eq_Fw_wordSign (u ++ v) k (by simp; omega), hFk, hFw_t1]
        have hpot_k : floorPotential (wordSign (u ++ v)) 0 (Fw (wordSign (u ++ v)) (t + 1) - 1) k =
            wordPot u r k := by
          rw [← wordPot_eq_floorPotential (u ++ v) _ k (by simp; omega), hFw_t1,
            wordPot_append_left r k (by omega)]
        have hS : SLandAt v r (wordPot v r (j + 1)) := ⟨j, hjv, hvj_false, rfl, rfl⟩
        have hC : KeyAt u r (dphiW u r + wordPot v r (j + 1)) :=
          Or.inr ⟨k, hku, huk_true, hFk', by omega⟩
        exact hdisj r (wordPot v r (j + 1)) hS hC
      · let i := k - u.length
        have hk_eq : k = u.length + i := by omega
        have hij : i < j := by omega
        have hfi : wordSign v i = true := by rw [← hws_right i (by omega), ← hk_eq]; exact hfk
        have hFi : Fw (wordSign v) i = Fw (wordSign v) (j + 1) + 1 := by
          rw [← wordHeight_eq_Fw_wordSign v i (by omega),
            ← wordHeight_eq_Fw_wordSign v (j + 1) (by omega),
            ← wordHeight_append_right hm i (by omega), ← hk_eq,
            wordHeight_eq_Fw_wordSign (u ++ v) k (by simp; omega), hFk, hFw_t1]
        have hpot_k : floorPotential (wordSign (u ++ v)) 0 (Fw (wordSign (u ++ v)) (t + 1) - 1) k =
            dphiW u r + wordPot v r i := by
          rw [← wordPot_eq_floorPotential (u ++ v) _ k (by simp; omega), hFw_t1,
            hk_eq, wordPot_append_right hm r i (by omega)]
        have hpeq_v : floorPotential (wordSign v) 0 (Fw (wordSign v) (j + 1) - 1) (j + 1) =
            floorPotential (wordSign v) 0 (Fw (wordSign v) (j + 1) - 1) i := by
          rw [← wordPot_eq_floorPotential v _ (j + 1) (by omega),
            ← wordPot_eq_floorPotential v _ i (by omega),
            ← wordHeight_eq_Fw_wordSign v (j + 1) (by omega)]
          change wordPot v r (j + 1) = wordPot v r i
          omega
        exact hv.2 j hjv hfj i hij hfi hFi hpeq_v

theorem keyAt_append {u v : List Bool} (hm : mass u = 0) (r ϕ : Int) :
    KeyAt (u ++ v) r ϕ ↔ KeyAt u r ϕ ∨ KeyAt v r (ϕ - dphiW u r) := by
  have hget_left : ∀ i, i < u.length → (u ++ v)[i]! = u[i]! := by
    intro i hi; simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hi]
  have hget_right : ∀ j, j < v.length → (u ++ v)[u.length + j]! = v[j]! := by
    intro j hj; simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right u.length j)]
  constructor
  · rintro (⟨i, hi, hH, hP⟩ | ⟨i, hi, hA, hH, hP⟩)
    · rw [List.length_append] at hi
      by_cases hiu : i ≤ u.length
      · left; left
        exact ⟨i, hiu, by rw [← wordHeight_append_left i hiu]; exact hH,
          by rw [← wordPot_append_left r i hiu]; exact hP⟩
      · right; left
        let j := i - u.length
        have hij : i = u.length + j := by omega
        rw [hij, wordHeight_append_right hm j (by omega)] at hH
        rw [hij, wordPot_append_right hm r j (by omega)] at hP
        exact ⟨j, by omega, hH, by omega⟩
    · rw [List.length_append] at hi
      by_cases hiu : i < u.length
      · left; right
        exact ⟨i, hiu, by rw [← hget_left i hiu]; exact hA,
          by rw [← wordHeight_append_left i (by omega)]; exact hH,
          by rw [← wordPot_append_left r i (by omega)]; exact hP⟩
      · right; right
        let j := i - u.length
        have hij : i = u.length + j := by omega
        rw [hij, hget_right j (by omega)] at hA
        rw [hij, wordHeight_append_right hm j (by omega)] at hH
        rw [hij, wordPot_append_right hm r j (by omega)] at hP
        exact ⟨j, by omega, hA, hH, by omega⟩
  · rintro ((⟨i, hi, hH, hP⟩ | ⟨i, hi, hA, hH, hP⟩) | (⟨j, hj, hH, hP⟩ | ⟨j, hj, hA, hH, hP⟩))
    · left; exact ⟨i, by simp; omega, by rw [wordHeight_append_left i hi]; exact hH,
        by rw [wordPot_append_left r i hi]; exact hP⟩
    · right; exact ⟨i, by simp; omega, by rw [hget_left i hi]; exact hA,
        by rw [wordHeight_append_left i (by omega)]; exact hH,
        by rw [wordPot_append_left r i (by omega)]; exact hP⟩
    · left; exact ⟨u.length + j, by simp; omega, by rw [wordHeight_append_right hm j hj]; exact hH,
        by rw [wordPot_append_right hm r j hj]; omega⟩
    · right; exact ⟨u.length + j, by simp; omega, by rw [hget_right j hj]; exact hA,
        by rw [wordHeight_append_right hm j (by omega)]; exact hH,
        by rw [wordPot_append_right hm r j (by omega)]; omega⟩

theorem sLandAt_append {u v : List Bool} (hm : mass u = 0) (r ϕ : Int) :
    SLandAt (u ++ v) r ϕ ↔ SLandAt u r ϕ ∨ SLandAt v r (ϕ - dphiW u r) := by
  have hget_left : ∀ i, i < u.length → (u ++ v)[i]! = u[i]! := by
    intro i hi; simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hi]
  have hget_right : ∀ j, j < v.length → (u ++ v)[u.length + j]! = v[j]! := by
    intro j hj; simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right u.length j)]
  constructor
  · rintro ⟨i, hi, hS, hH, hP⟩
    rw [List.length_append] at hi
    by_cases hiu : i < u.length
    · left
      exact ⟨i, hiu, by rw [← hget_left i hiu]; exact hS,
        by rw [← wordHeight_append_left (i + 1) (by omega)]; exact hH,
        by rw [← wordPot_append_left r (i + 1) (by omega)]; exact hP⟩
    · right
      let j := i - u.length
      have hij : i = u.length + j := by omega
      rw [hij, hget_right j (by omega)] at hS
      rw [show i + 1 = u.length + (j + 1) by omega, wordHeight_append_right hm (j + 1) (by omega)] at hH
      rw [show i + 1 = u.length + (j + 1) by omega, wordPot_append_right hm r (j + 1) (by omega)] at hP
      exact ⟨j, by omega, hS, hH, by omega⟩
  · rintro (⟨i, hi, hS, hH, hP⟩ | ⟨j, hj, hS, hH, hP⟩)
    · exact ⟨i, by simp; omega, by rw [hget_left i hi]; exact hS,
        by rw [wordHeight_append_left (i + 1) (by omega)]; exact hH,
        by rw [wordPot_append_left r (i + 1) (by omega)]; exact hP⟩
    · exact ⟨u.length + j, by simp; omega, by rw [hget_right j hj]; exact hS,
        by rw [show u.length + j + 1 = u.length + (j + 1) by omega,
          wordHeight_append_right hm (j + 1) (by omega)]; exact hH,
        by rw [show u.length + j + 1 = u.length + (j + 1) by omega,
          wordPot_append_right hm r (j + 1) (by omega)]; omega⟩

private theorem mass_repeatWord_zero {V : List Bool} (hm : mass V = 0) :
    ∀ R, mass (repeatWord R V) = 0
  | 0 => rfl
  | R + 1 => by simp [repeatWord, mass_append, hm, mass_repeatWord_zero hm R]

private theorem dphiW_repeatWord {V : List Bool} (hm : mass V = 0) (r : Int) :
    ∀ R, dphiW (repeatWord R V) r = (R : Int) * dphiW V r
  | 0 => by simp [repeatWord, dphiW, areaW]
  | R + 1 => by
    unfold repeatWord
    rw [dphiW_append hm r, dphiW_repeatWord hm r R]
    push_cast
    grind

theorem keyAt_repeatWord {V : List Bool} (hm : mass V = 0) (r ϕ : Int) :
    ∀ R, KeyAt (repeatWord R V) r ϕ →
      (R = 0 ∧ r = 0 ∧ ϕ = 0) ∨ ∃ c, c < R ∧ KeyAt V r (ϕ - (c : Int) * dphiW V r)
  | 0 => by
    rintro (⟨i, hi, hH, hP⟩ | ⟨i, hi, _⟩)
    · simp only [repeatWord, List.length_nil] at hi
      have : i = 0 := by omega
      subst this
      left; exact ⟨rfl, by simpa [wordHeight] using hH.symm, by simpa [wordPot, areaW] using hP.symm⟩
    · simp [repeatWord] at hi
  | R + 1 => by
    intro hK
    unfold repeatWord at hK
    rcases (keyAt_append hm r ϕ).mp hK with hhead | htail
    · right; exact ⟨0, Nat.zero_lt_succ R, by simpa using hhead⟩
    · rcases keyAt_repeatWord hm r (ϕ - dphiW V r) R htail with ⟨rfl, rfl, hϕ⟩ | ⟨c, hcR, hKc⟩
      · -- `ϕ - dphiW V 0 = 0`, which is the terminal visit `i = V.length` of copy `0` (`c = 0`)!
        right
        refine ⟨0, Nat.zero_lt_succ 0, Or.inl ⟨V.length, Nat.le_refl _, ?_, ?_⟩⟩
        · simpa [wordHeight] using hm
        · unfold wordPot
          unfold dphiW at hϕ
          simp only [List.take_length]
          omega
      · right
        refine ⟨c + 1, Nat.succ_lt_succ hcR, ?_⟩
        have hshift : ϕ - ((c + 1 : Nat) : Int) * dphiW V r =
            (ϕ - dphiW V r) - (c : Int) * dphiW V r := by push_cast; grind
        rwa [hshift]

/-- Master periodic freshness lemma (`E-805`): if balanced `V` satisfies `FreshWord V` and
for every shift `c ≥ 1` no `S`-landing `(r, ϕ)` of `V` collides with a shifted earlier
key `(r, ϕ + c * dphiW V r)` of `V` (i.e. `¬ KeyAt V r (ϕ + c * dphiW V r)`), then
`repeatWord R V` satisfies `FreshWord` for EVERY `R : Nat`! -/
theorem fresh_repeatWord {V : List Bool} (hm : mass V = 0) (hV : FreshWord V)
    (hdisj : ∀ c : Nat, 1 ≤ c → ∀ r ϕ, SLandAt V r ϕ → ¬ KeyAt V r (ϕ + (c : Int) * dphiW V r)) :
    ∀ R, FreshWord (repeatWord R V) := by
  intro R
  induction R with
  | zero => exact ⟨fun _ ht => by simp [repeatWord] at ht, fun _ ht => by simp [repeatWord] at ht⟩
  | succ R ih =>
    unfold repeatWord
    refine fresh_append hm hV ih ?_
    -- Wait: `repeatWord (R + 1) V = V ++ repeatWord R V`!
    -- For `SLandAt (repeatWord R V) r ϕ`, extract `c < R` with `SLandAt V r (ϕ - c * dphiW V r)`!
    intro r ϕ hS hK
    have hs_extract : ∀ m r ϕ, SLandAt (repeatWord m V) r ϕ →
        ∃ c, c < m ∧ SLandAt V r (ϕ - (c : Int) * dphiW V r) := by
      intro m
      induction m with
      | zero => rintro r ϕ ⟨i, hi, _⟩; simp [repeatWord] at hi
      | succ m ih =>
        intro r ϕ hSm
        unfold repeatWord at hSm
        rcases (sLandAt_append hm r ϕ).mp hSm with h0 | hrest
        · exact ⟨0, Nat.zero_lt_succ m, by simpa using h0⟩
        · obtain ⟨c, hcm, hSc⟩ := ih r (ϕ - dphiW V r) hrest
          refine ⟨c + 1, Nat.succ_lt_succ hcm, ?_⟩
          have hsh : ϕ - ((c + 1 : Nat) : Int) * dphiW V r =
              (ϕ - dphiW V r) - (c : Int) * dphiW V r := by push_cast; grind
          rwa [hsh]
    obtain ⟨c, _, hSc⟩ := hs_extract R r ϕ hS
    have hshift : dphiW V r + ϕ =
        (ϕ - (c : Int) * dphiW V r) + ((c + 1 : Nat) : Int) * dphiW V r := by push_cast; grind
    rw [hshift] at hK
    exact hdisj (c + 1) (by omega) r (ϕ - (c : Int) * dphiW V r) hSc hK

/-! ## Building-block characterizations (`asRep`, `saRep`, `asRep ++ saRep`) -/

private theorem mass_asRep (m : Nat) : mass (asRep m) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    unfold asRep
    rw [mass_append, ih]
    rfl

private theorem mass_saRep (m : Nat) : mass (saRep m) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    unfold saRep
    rw [mass_append, ih]
    rfl

private theorem dphiW_asRep (m : Nat) (r : Int) :
    dphiW (asRep m) r = (m : Int) * (1 - 2 * r) := by
  induction m with
  | zero => simp [asRep, dphiW, areaW]
  | succ m ih =>
    unfold asRep
    have hm1 : mass [true, false] = 0 := rfl
    rw [dphiW_append hm1 r, ih]
    have hd1 : dphiW [true, false] r = 1 - 2 * r := by
      have ha : areaW [true, false] = 1 := rfl
      unfold dphiW; rw [ha]; simp
    rw [hd1]
    push_cast
    grind

private theorem dphiW_saRep (m : Nat) (r : Int) :
    dphiW (saRep m) r = -(m : Int) * (2 * r + 1) := by
  induction m with
  | zero => simp [saRep, dphiW, areaW]
  | succ m ih =>
    unfold saRep
    have hm1 : mass [false, true] = 0 := rfl
    rw [dphiW_append hm1 r, ih]
    have hd1 : dphiW [false, true] r = -(2 * r + 1) := by
      have ha : areaW [false, true] = -1 := rfl
      unfold dphiW; rw [ha]; simp; omega
    rw [hd1]
    push_cast
    grind

private theorem keyAt_as_one (r ϕ : Int) :
    KeyAt [true, false] r ϕ →
      (r = -1 ∧ ϕ = 0) ∨ (r = 0 ∧ (ϕ = 0 ∨ ϕ = 1)) ∨ (r = 1 ∧ ϕ = 0) := by
  rintro (⟨i, hi, hH, hP⟩ | ⟨i, hi, hA, hH, hP⟩)
  · have hi2 : i = 0 ∨ i = 1 ∨ i = 2 := by simp at hi; omega
    rcases hi2 with rfl | rfl | rfl <;>
      simp [wordHeight, wordPot, areaW, sign] at hH hP <;> omega
  · have hi2 : i = 0 ∨ i = 1 := by simp at hi; omega
    rcases hi2 with rfl | rfl <;>
      simp [wordHeight, wordPot, areaW] at hA hH hP <;> omega

private theorem sLandAt_as_one (r ϕ : Int) :
    SLandAt [true, false] r ϕ → r = 0 ∧ ϕ = 1 := by
  rintro ⟨i, hi, hS, hH, hP⟩
  have hi2 : i = 0 ∨ i = 1 := by simp at hi; omega
  rcases hi2 with rfl | rfl <;>
    simp [wordHeight, wordPot, areaW, sign] at hS hH hP <;> omega

private theorem keyAt_sa_one (r ϕ : Int) :
    KeyAt [false, true] r ϕ →
      (r = -2 ∧ ϕ = 1) ∨ (r = -1 ∧ ϕ = 0) ∨ (r = 0 ∧ (ϕ = 0 ∨ ϕ = -1)) := by
  rintro (⟨i, hi, hH, hP⟩ | ⟨i, hi, hA, hH, hP⟩)
  · have hi2 : i = 0 ∨ i = 1 ∨ i = 2 := by simp at hi; omega
    rcases hi2 with rfl | rfl | rfl <;>
      simp [wordHeight, wordPot, areaW, sign] at hH hP <;> omega
  · have hi2 : i = 0 ∨ i = 1 := by simp at hi; omega
    rcases hi2 with rfl | rfl <;>
      simp [wordHeight, wordPot, areaW, sign] at hA hH hP <;> omega

private theorem sLandAt_sa_one (r ϕ : Int) :
    SLandAt [false, true] r ϕ → r = -1 ∧ ϕ = 0 := by
  rintro ⟨i, hi, hS, hH, hP⟩
  have hi2 : i = 0 ∨ i = 1 := by simp at hi; omega
  rcases hi2 with rfl | rfl <;>
    simp [wordHeight, wordPot, areaW, sign] at hS hH hP <;> omega

private theorem fresh_as_one : FreshWord [true, false] := by
  constructor
  · intro t ht hft u hut hFu hpeq
    have ht2 : t = 0 ∨ t = 1 := by simp at ht; omega
    rcases ht2 with rfl | rfl
    · simp [wordSign] at hft
    · have hu2 : u = 0 ∨ u = 1 := by omega
      rcases hu2 with rfl | rfl <;>
        simp [Fw, floorPotential, Ar, wordSign, sign] at hFu hpeq
  · intro t ht hft u hut hfu hFu hpeq
    have ht2 : t = 0 ∨ t = 1 := by simp at ht; omega
    rcases ht2 with rfl | rfl
    · simp [wordSign] at hft
    · have hu0 : u = 0 := by omega
      subst hu0
      simp [Fw, wordSign, sign] at hFu

private theorem fresh_sa_one : FreshWord [false, true] := by
  constructor
  · intro t ht hft u hut hFu hpeq
    have ht2 : t = 0 ∨ t = 1 := by simp at ht; omega
    rcases ht2 with rfl | rfl
    · have hu0 : u = 0 := by omega
      subst hu0
      simp [Fw, wordSign, sign] at hFu
    · simp [wordSign] at hft
  · intro t ht hft u hut hfu hFu hpeq
    have ht2 : t = 0 ∨ t = 1 := by simp at ht; omega
    rcases ht2 with rfl | rfl
    · omega
    · simp [wordSign] at hft

private theorem asRep_keyAt_sLandAt_fresh (m : Nat) :
    FreshWord (asRep m) ∧
    (∀ r ϕ, KeyAt (asRep m) r ϕ →
      (r = -1 ∧ 0 ≤ ϕ ∧ ϕ < 3 * (m : Int)) ∨
      (r = 0 ∧ 0 ≤ ϕ ∧ ϕ ≤ (m : Int)) ∨
      (r = 1 ∧ -((m : Int)) < ϕ ∧ ϕ ≤ 0)) ∧
    (∀ r ϕ, SLandAt (asRep m) r ϕ → r = 0 ∧ 1 ≤ ϕ ∧ ϕ ≤ (m : Int)) := by
  induction m with
  | zero =>
    refine ⟨⟨fun _ h => by simp [asRep] at h, fun _ h => by simp [asRep] at h⟩, ?_, ?_⟩
    · rintro r ϕ (⟨i, hi, hH, hP⟩ | ⟨i, hi, _⟩)
      · simp [asRep] at hi; subst hi; right; left
        simp [asRep, wordHeight, wordPot, areaW] at hH hP; omega
      · simp [asRep] at hi
    · rintro r ϕ ⟨i, hi, _⟩; simp [asRep] at hi
  | succ m ih =>
    obtain ⟨hfr, hkey, hsland⟩ := ih
    have hm1 : mass [true, false] = 0 := rfl
    have hd1 : ∀ r, dphiW [true, false] r = 1 - 2 * r := fun r => by
      have ha : areaW [true, false] = 1 := rfl
      unfold dphiW; rw [ha]; simp
    have hfr' : FreshWord (asRep (m + 1)) := by
      unfold asRep
      refine fresh_append hm1 fresh_as_one hfr ?_
      intro r ϕ hS hK
      have hSr := hsland r ϕ hS
      have hKr := keyAt_as_one r (dphiW [true, false] r + ϕ) hK
      rw [hd1] at hKr
      omega
    refine ⟨hfr', ?_, ?_⟩
    · intro r ϕ hK
      unfold asRep at hK
      rcases (keyAt_append hm1 r ϕ).mp hK with h1 | h2
      · have := keyAt_as_one r ϕ h1; omega
      · have := hkey r (ϕ - dphiW [true, false] r) h2
        rw [hd1] at this; push_cast; omega
    · intro r ϕ hS
      unfold asRep at hS
      rcases (sLandAt_append hm1 r ϕ).mp hS with h1 | h2
      · have := sLandAt_as_one r ϕ h1; omega
      · have := hsland r (ϕ - dphiW [true, false] r) h2
        rw [hd1] at this; push_cast; omega

private theorem saRep_keyAt_sLandAt_fresh (m : Nat) :
    FreshWord (saRep m) ∧
    (∀ r ϕ, KeyAt (saRep m) r ϕ →
      (r = -2 ∧ 1 ≤ ϕ ∧ ϕ ≤ 3 * (m : Int) - 2) ∨
      (r = -1 ∧ 0 ≤ ϕ ∧ ϕ < (m : Int)) ∨
      (r = 0 ∧ -((m : Int)) ≤ ϕ ∧ ϕ ≤ 0)) ∧
    (∀ r ϕ, SLandAt (saRep m) r ϕ → r = -1 ∧ 0 ≤ ϕ ∧ ϕ < (m : Int)) := by
  induction m with
  | zero =>
    refine ⟨⟨fun _ h => by simp [saRep] at h, fun _ h => by simp [saRep] at h⟩, ?_, ?_⟩
    · rintro r ϕ (⟨i, hi, hH, hP⟩ | ⟨i, hi, _⟩)
      · simp [saRep] at hi; subst hi; right; right
        simp [saRep, wordHeight, wordPot, areaW] at hH hP; omega
      · simp [saRep] at hi
    · rintro r ϕ ⟨i, hi, _⟩; simp [saRep] at hi
  | succ m ih =>
    obtain ⟨hfr, hkey, hsland⟩ := ih
    have hm1 : mass [false, true] = 0 := rfl
    have hd1 : ∀ r, dphiW [false, true] r = -(2 * r + 1) := fun r => by
      have ha : areaW [false, true] = -1 := rfl
      unfold dphiW; rw [ha]; simp; omega
    have hfr' : FreshWord (saRep (m + 1)) := by
      unfold saRep
      refine fresh_append hm1 fresh_sa_one hfr ?_
      intro r ϕ hS hK
      have hSr := hsland r ϕ hS
      have hKr := keyAt_sa_one r (dphiW [false, true] r + ϕ) hK
      rw [hd1] at hKr
      omega
    refine ⟨hfr', ?_, ?_⟩
    · intro r ϕ hK
      unfold saRep at hK
      rcases (keyAt_append hm1 r ϕ).mp hK with h1 | h2
      · have := keyAt_sa_one r ϕ h1; omega
      · have := hkey r (ϕ - dphiW [false, true] r) h2
        rw [hd1] at this; push_cast; omega
    · intro r ϕ hS
      unfold saRep at hS
      rcases (sLandAt_append hm1 r ϕ).mp hS with h1 | h2
      · have := sLandAt_sa_one r ϕ h1; omega
      · have := hsland r (ϕ - dphiW [false, true] r) h2
        rw [hd1] at this; push_cast; omega

/-- Critical ordering lemma (`E-799` / `E-805`): `(AS)^q ++ (SA)^p` is `FreshWord` for ALL
`q, p : Nat` (whereas `(SA)^p ++ (AS)^q` fails at height `0` whenever `p ≥ 1, q ≥ 1`). -/
theorem fresh_asRep_append_saRep (q p : Nat) :
    FreshWord (asRep q ++ saRep p) := by
  have has := asRep_keyAt_sLandAt_fresh q
  have hsa := saRep_keyAt_sLandAt_fresh p
  refine fresh_append (mass_asRep q) has.1 hsa.1 ?_
  intro r ϕ hS hK
  have hSr := hsa.2.2 r ϕ hS
  have hKr := has.2.1 r (dphiW (asRep q) r + ϕ) hK
  rw [dphiW_asRep] at hKr
  rcases hSr with ⟨rfl, _, _⟩
  grind

/-! ## Height-elevation combinator `elevateWord h w = A^h ++ w ++ S^h` -/

/-- Elevate a balanced word `w` by height `h`: `A^h ++ w ++ S^h`. -/
def elevateWord (h : Nat) (w : List Bool) : List Bool :=
  List.replicate h true ++ w ++ List.replicate h false

private theorem elevateWord_length (h : Nat) (w : List Bool) :
    (elevateWord h w).length = w.length + 2 * h := by
  unfold elevateWord
  simp only [List.length_append, List.length_replicate]
  omega

private theorem mass_replicate_bool (k : Nat) (b : Bool) :
    mass (List.replicate k b) = (k : Int) * sign b := by
  induction k with
  | zero => simp [mass]
  | succ k ih =>
    rw [List.replicate_succ]
    change sign b + mass (List.replicate k b) = _
    rw [ih]
    push_cast
    grind

private theorem mass_elevateWord (h : Nat) {w : List Bool} (hm : mass w = 0) :
    mass (elevateWord h w) = 0 := by
  unfold elevateWord
  rw [mass_append, mass_append, mass_replicate_bool, mass_replicate_bool, hm]
  simp [sign]; omega

private theorem areaW_append_general (u v : List Bool) :
    areaW (u ++ v) = areaW u + areaW v + (v.length : Int) * mass u := by
  have h1 := area_split_at (wordSign (u ++ v)) 0 u.length (u.length + v.length)
    (Nat.zero_le _) (Nat.le_add_right _ _)
  rw [Nat.sub_zero, Nat.sub_zero, Nat.add_sub_cancel_left] at h1
  have hseg_uv : seg (wordSign (u ++ v)) 0 (u.length + v.length) = u ++ v := by
    have h := seg_wordSign_eq_take (u ++ v) (u ++ v).length (Nat.le_refl _)
    rw [List.take_length] at h
    simpa [List.length_append] using h
  have hseg_u : seg (wordSign (u ++ v)) 0 u.length = u := by
    have h := seg_wordSign_eq_take (u ++ v) u.length (by simp)
    simpa [List.take_left] using h
  have hseg_v : seg (wordSign (u ++ v)) u.length v.length = v := by
    have haux : ∀ k, k ≤ v.length → seg (wordSign (u ++ v)) u.length k = v.take k := by
      intro k
      induction k with
      | zero => intro _; simp [seg]
      | succ k ih =>
        intro hk
        rw [seg_succ, ih (by omega), List.take_succ_eq_append_getElem (by omega)]
        simp [wordSign, show k < v.length by omega]
    simpa using haux v.length (Nat.le_refl _)
  rw [Ar_areaW, hseg_uv, Ar_areaW, hseg_u, Ar_areaW, hseg_v] at h1
  have hFu : Fw (wordSign (u ++ v)) u.length = mass u := by
    have hm1 := seg_mass (wordSign (u ++ v)) 0 u.length
    rw [hseg_u, Nat.zero_add] at hm1
    have h0 : Fw (wordSign (u ++ v)) 0 = 0 := rfl
    omega
  have h0 : Fw (wordSign (u ++ v)) 0 = 0 := rfl
  rw [hFu, h0] at h1
  grind

private theorem areaW_replicate_true : ∀ k : Nat, 2 * areaW (List.replicate k true) = (k : Int) * (k + 1)
  | 0 => by simp [areaW]
  | k + 1 => by
    have hrep : List.replicate (k + 1) true = List.replicate k true ++ [true] := by
      rw [List.replicate_succ']
    rw [hrep, areaW_append_general, mass_replicate_bool]
    have ih := areaW_replicate_true k
    have ha1 : areaW [true] = 1 := by simp [areaW, sign]
    simp only [ha1, List.length_singleton, sign]
    push_cast at ih ⊢
    grind

private theorem areaW_replicate_false : ∀ k : Nat, 2 * areaW (List.replicate k false) = -((k : Int) * (k + 1))
  | 0 => by simp [areaW]
  | k + 1 => by
    have hrep : List.replicate (k + 1) false = List.replicate k false ++ [false] := by
      rw [List.replicate_succ']
    rw [hrep, areaW_append_general, mass_replicate_bool]
    have ih := areaW_replicate_false k
    have ha1 : areaW [false] = -1 := by simp [areaW, sign]
    simp only [ha1, List.length_singleton, sign]
    push_cast at ih ⊢
    grind

private theorem dphiW_elevateWord (h : Nat) {w : List Bool} (hm : mass w = 0) (r : Int) :
    dphiW (elevateWord h w) r = dphiW w (r - (h : Int)) + (h : Int) * ((h : Int) - 2 * r) := by
  unfold dphiW elevateWord
  rw [areaW_append_general, areaW_append_general, mass_append, mass_replicate_bool, hm]
  simp only [List.length_append, List.length_replicate, sign, Int.add_zero]
  have ht := areaW_replicate_true h
  have hf := areaW_replicate_false h
  push_cast at ht hf ⊢
  grind

private theorem wordHeight_elevateWord (h : Nat) {w : List Bool} (hm : mass w = 0) :
    (∀ i, i ≤ h → wordHeight (elevateWord h w) i = (i : Int)) ∧
    (∀ j, j ≤ w.length → wordHeight (elevateWord h w) (h + j) = (h : Int) + wordHeight w j) ∧
    (∀ k, k ≤ h → wordHeight (elevateWord h w) (h + w.length + k) = (h : Int) - (k : Int)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    unfold wordHeight elevateWord
    rw [List.append_assoc, List.take_append_of_le_length (by simp; omega), List.take_replicate,
      Nat.min_eq_left hi, mass_replicate_bool]
    simp [sign]
  · intro j hj
    unfold wordHeight elevateWord
    rw [List.append_assoc, List.take_append, List.take_of_length_le (by simp),
      List.length_replicate, Nat.add_sub_cancel_left, List.take_append_of_le_length hj,
      mass_append, mass_replicate_bool]
    simp [sign]
  · intro k hk
    unfold wordHeight elevateWord
    rw [List.take_append, List.take_of_length_le (by simp),
      List.length_append, List.length_replicate, Nat.add_sub_cancel_left,
      List.take_replicate, Nat.min_eq_left hk, mass_append, mass_append,
      mass_replicate_bool, mass_replicate_bool, hm]
    simp [sign]
    omega

private theorem wordPot_elevateWord (h : Nat) {w : List Bool} (hm : mass w = 0) (r : Int) :
    (∀ i, i ≤ h → 2 * wordPot (elevateWord h w) r i = (i : Int) * ((i : Int) + 1 - 2 * r)) ∧
    (∀ j, j ≤ w.length →
      2 * wordPot (elevateWord h w) r (h + j) =
        (h : Int) * ((h : Int) + 1 - 2 * r) + 2 * wordPot w (r - (h : Int)) j) ∧
    (∀ k, k ≤ h →
      2 * wordPot (elevateWord h w) ((h : Int) - (k : Int)) (h + w.length + k) =
        2 * dphiW (elevateWord h w) ((h : Int) - (k : Int)) +
          ((h : Int) - (k : Int)) * ((h : Int) - (k : Int) + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    unfold wordPot elevateWord
    rw [List.append_assoc, List.take_append_of_le_length (by simp; omega), List.take_replicate,
      Nat.min_eq_left hi]
    have ht := areaW_replicate_true i
    grind
  · intro j hj
    unfold wordPot elevateWord
    rw [List.append_assoc, List.take_append, List.take_of_length_le (by simp),
      List.length_replicate, Nat.add_sub_cancel_left, List.take_append_of_le_length hj,
      areaW_append_general, mass_replicate_bool]
    have ht := areaW_replicate_true h
    have hlen : (w.take j).length = j := by rw [List.length_take, Nat.min_eq_left hj]
    rw [hlen]
    simp only [sign]
    push_cast at ht ⊢
    grind
  · intro k hk
    unfold wordPot elevateWord dphiW
    rw [List.take_append, List.take_of_length_le (by simp),
      List.length_append, List.length_replicate, Nat.add_sub_cancel_left,
      List.take_replicate, Nat.min_eq_left hk]
    rw [areaW_append_general, areaW_append_general, areaW_append_general, areaW_append_general,
      mass_append, mass_replicate_bool, hm]
    simp only [List.length_append, List.length_replicate, sign, Int.add_zero]
    have ht := areaW_replicate_true h
    have hf_h := areaW_replicate_false h
    have hf_k := areaW_replicate_false k
    push_cast at ht hf_h hf_k ⊢
    grind

private theorem two_dvd_mul_sub_two (h : Nat) (r : Int) :
    2 ∣ ((h : Int) * ((h : Int) + 1 - 2 * r)) := by
  by_cases he : h % 2 = 0
  · refine ⟨((h / 2 : Nat) : Int) * ((h : Int) + 1 - 2 * r), ?_⟩
    have : (h : Int) = 2 * ((h / 2 : Nat) : Int) := by omega
    rw [this]; grind
  · refine ⟨(h : Int) * (((h / 2 : Nat) : Int) + 1 - r), ?_⟩
    have : (h : Int) = 2 * ((h / 2 : Nat) : Int) + 1 := by omega
    grind

private theorem elevateWord_sLandAt (h : Nat) {w : List Bool} (hm : mass w = 0) (r ϕ : Int) :
    SLandAt (elevateWord h w) r ϕ →
      (SLandAt w (r - (h : Int)) (ϕ - ((h : Int) * ((h : Int) + 1 - 2 * r)) / 2)) ∨
      (0 ≤ r ∧ r < (h : Int) ∧ 2 * ϕ = 2 * dphiW (elevateWord h w) r + r * (r + 1)) := by
  rintro ⟨i, hi, hS, hH, hP⟩
  rw [elevateWord_length] at hi
  have hget_A : ∀ j, j < h → (elevateWord h w)[j]! = true := by
    intro j hj
    unfold elevateWord
    rw [List.append_assoc, List.getElem!_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
      List.getElem?_replicate]
    simp [hj]
  have hget_w : ∀ j, j < w.length → (elevateWord h w)[h + j]! = w[j]! := by
    intro j hj
    unfold elevateWord
    rw [List.append_assoc, List.getElem!_eq_getElem?_getD,
      List.getElem?_append_right (by simp), List.length_replicate, Nat.add_sub_cancel_left,
      List.getElem?_append_left hj, ← List.getElem!_eq_getElem?_getD]
  by_cases hi1 : i < h
  · rw [hget_A i hi1] at hS; cases hS
  · by_cases hi2 : i < h + w.length
    · left
      let j := i - h
      have hij : i = h + j := by omega
      have hwh := (wordHeight_elevateWord h hm).2.1 (j + 1) (by omega)
      have hwp := (wordPot_elevateWord h hm r).2.1 (j + 1) (by omega)
      rw [show h + (j + 1) = i + 1 by omega] at hwh hwp
      have heven : 2 ∣ ((h : Int) * ((h : Int) + 1 - 2 * r)) := two_dvd_mul_sub_two h r
      refine ⟨j, by omega, by rw [← hget_w j (by omega), ← hij]; exact hS, by omega, by omega⟩
    · right
      let k := i + 1 - (h + w.length)
      have hk1 : 1 ≤ k ∧ k ≤ h := by omega
      have hwh := (wordHeight_elevateWord h hm).2.2 k hk1.2
      rw [show h + w.length + k = i + 1 by omega] at hwh
      have hwp := (wordPot_elevateWord h hm r).2.2 k hk1.2
      rw [show h + w.length + k = i + 1 by omega] at hwp
      have hr_eq : r = (h : Int) - (k : Int) := by omega
      rw [← hr_eq] at hwp
      refine ⟨by omega, by omega, by omega⟩

private theorem elevateWord_keyAt (h : Nat) {w : List Bool} (hm : mass w = 0) (r ϕ : Int) :
    KeyAt (elevateWord h w) r ϕ →
      (0 ≤ r ∧ r ≤ (h : Int) ∧ 2 * ϕ = -(r * (r - 1))) ∨
      (-1 ≤ r ∧ r + 2 ≤ (h : Int) ∧ 2 * ϕ = -((r + 1) * (r - 2))) ∨
      KeyAt w (r - (h : Int)) (ϕ - ((h : Int) * ((h : Int) + 1 - 2 * r)) / 2) ∨
      (0 ≤ r ∧ r < (h : Int) ∧ 2 * ϕ = 2 * dphiW (elevateWord h w) r + r * (r + 1)) := by
  have hget_A : ∀ j, j < h → (elevateWord h w)[j]! = true := by
    intro j hj
    unfold elevateWord
    rw [List.append_assoc, List.getElem!_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
      List.getElem?_replicate]
    simp [hj]
  have hget_w : ∀ j, j < w.length → (elevateWord h w)[h + j]! = w[j]! := by
    intro j hj
    unfold elevateWord
    rw [List.append_assoc, List.getElem!_eq_getElem?_getD,
      List.getElem?_append_right (by simp), List.length_replicate, Nat.add_sub_cancel_left,
      List.getElem?_append_left hj, ← List.getElem!_eq_getElem?_getD]
  have hget_S : ∀ k, k < h → (elevateWord h w)[h + w.length + k]! = false := by
    intro k hk
    unfold elevateWord
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by simp),
      List.length_append, List.length_replicate, Nat.add_sub_cancel_left, List.getElem?_replicate]
    simp [hk]
  have heven : 2 ∣ ((h : Int) * ((h : Int) + 1 - 2 * r)) := two_dvd_mul_sub_two h r
  rintro (⟨i, hi, hH, hP⟩ | ⟨i, hi, hA, hH, hP⟩)
  · rw [elevateWord_length] at hi
    by_cases hi1 : i ≤ h
    · left
      have hwh := (wordHeight_elevateWord h hm).1 i hi1
      have hwp := (wordPot_elevateWord h hm r).1 i hi1
      rw [hH] at hwh; rw [hP] at hwp
      have hr : r = (i : Int) := hwh
      rw [hr] at hwp ⊢
      refine ⟨by omega, by omega, by grind⟩
    · by_cases hi2 : i ≤ h + w.length
      · right; right; left
        let j := i - h
        have hij : i = h + j := by omega
        have hwh := (wordHeight_elevateWord h hm).2.1 j (by omega)
        have hwp := (wordPot_elevateWord h hm r).2.1 j (by omega)
        rw [← hij] at hwh hwp
        exact Or.inl ⟨j, by omega, by omega, by omega⟩
      · right; right; right
        let k := i - (h + w.length)
        have hk : 1 ≤ k ∧ k ≤ h := by omega
        have hwh := (wordHeight_elevateWord h hm).2.2 k hk.2
        have hwp := (wordPot_elevateWord h hm r).2.2 k hk.2
        rw [show h + w.length + k = i by omega] at hwh hwp
        have hr : r = (h : Int) - (k : Int) := by omega
        rw [← hr] at hwp
        refine ⟨by omega, by omega, by omega⟩
  · rw [elevateWord_length] at hi
    by_cases hi1 : i < h
    · right; left
      have hwh := (wordHeight_elevateWord h hm).1 i (by omega)
      have hwp := (wordPot_elevateWord h hm r).1 i (by omega)
      rw [hH] at hwh; rw [hP] at hwp
      have hr : (i : Int) = r + 1 := by omega
      rw [hr] at hwp
      refine ⟨by omega, by omega, by grind⟩
    · by_cases hi2 : i < h + w.length
      · right; right; left
        let j := i - h
        have hij : i = h + j := by omega
        have hwh := (wordHeight_elevateWord h hm).2.1 j (by omega)
        have hwp := (wordPot_elevateWord h hm r).2.1 j (by omega)
        rw [← hij] at hwh hwp
        exact Or.inr ⟨j, by omega, by rw [← hget_w j (by omega), ← hij]; exact hA, by omega, by omega⟩
      · let k := i - (h + w.length)
        have hk : k < h := by omega
        have hS := hget_S k hk
        rw [show h + w.length + k = i by omega] at hS
        rw [hS] at hA; cases hA

/-- Freshness elevation lemma (`E-805`): `elevateWord h w = A^h ++ w ++ S^h` is `FreshWord`
whenever `w` is balanced and `FreshWord`, every `S`-landing of `w` avoids `A^h`'s visits and
candidates, and every `S^h` descent landing (`0 ≤ r < h`) avoids `A^h` and `w`. -/
private theorem elevateWord_fresh (h : Nat) {w : List Bool} (hm : mass w = 0) (hw : FreshWord w)
    (h_w_vs_A : ∀ r ϕ, SLandAt w (r - (h : Int)) ϕ →
      let ψ := ϕ + ((h : Int) * ((h : Int) + 1 - 2 * r)) / 2
      (0 ≤ r → r ≤ (h : Int) → 2 * ψ ≠ -(r * (r - 1))) ∧
      (-1 ≤ r → r + 2 ≤ (h : Int) → 2 * ψ ≠ -((r + 1) * (r - 2))))
    (h_S_vs_Aw : ∀ r : Int, 0 ≤ r → r < (h : Int) →
      let ψ2 := 2 * dphiW (elevateWord h w) r + r * (r + 1)
      ψ2 ≠ -(r * (r - 1)) ∧
      (r + 2 ≤ (h : Int) → ψ2 ≠ -((r + 1) * (r - 2))) ∧
      (∀ ϕ, 2 * ϕ = ψ2 → ¬ KeyAt w (r - (h : Int)) (ϕ - ((h : Int) * ((h : Int) + 1 - 2 * r)) / 2))) :
    FreshWord (elevateWord h w) := by
  let u := elevateWord h w
  have hget_A : ∀ j, j < h → u[j]! = true := by
    intro j hj
    dsimp only [u]; unfold elevateWord
    rw [List.append_assoc, List.getElem!_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
      List.getElem?_replicate]
    simp [hj]
  have hget_w : ∀ j, j < w.length → u[h + j]! = w[j]! := by
    intro j hj
    dsimp only [u]; unfold elevateWord
    rw [List.append_assoc, List.getElem!_eq_getElem?_getD,
      List.getElem?_append_right (by simp), List.length_replicate, Nat.add_sub_cancel_left,
      List.getElem?_append_left hj, ← List.getElem!_eq_getElem?_getD]
  have hget_S : ∀ k, k < h → u[h + w.length + k]! = false := by
    intro k hk
    dsimp only [u]; unfold elevateWord
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by simp),
      List.length_append, List.length_replicate, Nat.add_sub_cancel_left, List.getElem?_replicate]
    simp [hk]
  -- Helper: given an `S`-landing at `t < u.length` and an earlier index `k` (`k ≤ t` for Type-I, `k < t` with `A` for Type-II):
  -- since `u` has no `S` in `A^h`, `t ≥ h`; split `t < h + w.length` (`w` vs `A^h` or `w` vs `w`) and `t ≥ h + w.length` (`S^h` vs `A^h`/`w`/`S^h`).
  have hhelper : ∀ t, t < (elevateWord h w).length → (elevateWord h w)[t]! = false →
      ∀ r, r = wordHeight (elevateWord h w) (t + 1) →
        (∀ k, k ≤ t → wordHeight (elevateWord h w) k = r →
          wordPot (elevateWord h w) r (t + 1) ≠ wordPot (elevateWord h w) r k) ∧
        (∀ k, k < t → (elevateWord h w)[k]! = true → wordHeight (elevateWord h w) k = r + 1 →
          wordPot (elevateWord h w) r (t + 1) ≠ wordPot (elevateWord h w) r k) := by
    intro t ht hSt r hr
    have hlen_u : (elevateWord h w).length = w.length + 2 * h := elevateWord_length h w
    have ht_ge : h ≤ t := by
      by_cases hlt : t < h
      · rw [hget_A t hlt] at hSt; cases hSt
      · omega
    have heven : 2 ∣ ((h : Int) * ((h : Int) + 1 - 2 * r)) := two_dvd_mul_sub_two h r
    by_cases ht_w : t < h + w.length
    · let j := t - h
      have htj : t = h + j := by omega
      have hjv : j < w.length := by omega
      have hwj : w[j]! = false := by rw [← hget_w j hjv, ← htj]; exact hSt
      have hwh_t1 := (wordHeight_elevateWord h hm).2.1 (j + 1) (by omega)
      have hwp_t1 := (wordPot_elevateWord h hm r).2.1 (j + 1) (by omega)
      rw [show h + (j + 1) = t + 1 by omega] at hwh_t1 hwp_t1
      have hSL : SLandAt w (r - (h : Int)) (wordPot w (r - (h : Int)) (j + 1)) :=
        ⟨j, hjv, hwj, by omega, rfl⟩
      have hvsA := h_w_vs_A r (wordPot w (r - (h : Int)) (j + 1)) hSL
      constructor
      · intro k hkt hHk hpeq
        by_cases hkA : k ≤ h
        · have hwh_k := (wordHeight_elevateWord h hm).1 k hkA
          have hwp_k := (wordPot_elevateWord h hm r).1 k hkA
          have hrk : r = (k : Int) := by omega
          have h1 := hvsA.1 (by omega) (by omega)
          rw [hrk] at hwp_k h1
          grind
        · let i := k - h
          have hki : k = h + i := by omega
          have hwh_k := (wordHeight_elevateWord h hm).2.1 i (by omega)
          have hwp_k := (wordPot_elevateWord h hm r).2.1 i (by omega)
          rw [← hki] at hwh_k hwp_k
          have hfj_s : wordSign w j = false := hwj
          have hFi : Fw (wordSign w) i = Fw (wordSign w) (j + 1) := by
            rw [← wordHeight_eq_Fw_wordSign w i (by omega),
              ← wordHeight_eq_Fw_wordSign w (j + 1) (by omega)]
            omega
          have hp_eq_w : floorPotential (wordSign w) 0 (Fw (wordSign w) (j + 1) - 1) (j + 1) =
              floorPotential (wordSign w) 0 (Fw (wordSign w) (j + 1) - 1) i := by
            rw [← wordPot_eq_floorPotential w _ (j + 1) (by omega),
              ← wordPot_eq_floorPotential w _ i (by omega),
              ← wordHeight_eq_Fw_wordSign w (j + 1) (by omega)]
            have hr_eq : wordHeight w (j + 1) = r - (h : Int) := by omega
            rw [hr_eq]
            omega
          exact hw.1 j hjv hfj_s i (by omega) hFi hp_eq_w
      · intro k hkt hAk hHk hpeq
        by_cases hkA : k < h
        · have hwh_k := (wordHeight_elevateWord h hm).1 k (by omega)
          have hwp_k := (wordPot_elevateWord h hm r).1 k (by omega)
          have hrk : (k : Int) = r + 1 := by omega
          have h2 := hvsA.2 (by omega) (by omega)
          rw [hrk] at hwp_k
          grind
        · let i := k - h
          have hki : k = h + i := by omega
          have hwi : w[i]! = true := by rw [← hget_w i (by omega), ← hki]; exact hAk
          have hwh_k := (wordHeight_elevateWord h hm).2.1 i (by omega)
          have hwp_k := (wordPot_elevateWord h hm r).2.1 i (by omega)
          rw [← hki] at hwh_k hwp_k
          have hfj_s : wordSign w j = false := hwj
          have hfi_s : wordSign w i = true := hwi
          have hFi : Fw (wordSign w) i = Fw (wordSign w) (j + 1) + 1 := by
            rw [← wordHeight_eq_Fw_wordSign w i (by omega),
              ← wordHeight_eq_Fw_wordSign w (j + 1) (by omega)]
            omega
          have hp_eq_w : floorPotential (wordSign w) 0 (Fw (wordSign w) (j + 1) - 1) (j + 1) =
              floorPotential (wordSign w) 0 (Fw (wordSign w) (j + 1) - 1) i := by
            rw [← wordPot_eq_floorPotential w _ (j + 1) (by omega),
              ← wordPot_eq_floorPotential w _ i (by omega),
              ← wordHeight_eq_Fw_wordSign w (j + 1) (by omega)]
            have hr_eq : wordHeight w (j + 1) = r - (h : Int) := by omega
            rw [hr_eq]
            omega
          exact hw.2 j hjv hfj_s i (by omega) hfi_s hFi hp_eq_w
    · -- `t` is in `S^h`!
      let m := t + 1 - (h + w.length)
      have hm1 : 1 ≤ m ∧ m ≤ h := by omega
      have hwh_t1 := (wordHeight_elevateWord h hm).2.2 m hm1.2
      have hwp_t1 := (wordPot_elevateWord h hm r).2.2 m hm1.2
      rw [show h + w.length + m = t + 1 by omega] at hwh_t1 hwp_t1
      have hrm : r = (h : Int) - (m : Int) := by omega
      rw [← hrm] at hwp_t1
      have hSvs := h_S_vs_Aw r (by omega) (by omega)
      constructor
      · intro k hkt hHk hpeq
        by_cases hkA : k ≤ h
        · have hwh_k := (wordHeight_elevateWord h hm).1 k hkA
          have hwp_k := (wordPot_elevateWord h hm r).1 k hkA
          have hrk : r = (k : Int) := by omega
          rw [hrk] at hwp_k
          have := hSvs.1; grind
        · by_cases hkw : k ≤ h + w.length
          · let i := k - h
            have hki : k = h + i := by omega
            have hwh_k := (wordHeight_elevateWord h hm).2.1 i (by omega)
            have hwp_k := (wordPot_elevateWord h hm r).2.1 i (by omega)
            rw [← hki] at hwh_k hwp_k
            exact hSvs.2.2 (wordPot (elevateWord h w) r (t + 1)) hwp_t1 (Or.inl ⟨i, by omega, by omega, by omega⟩)
          · let m' := k - (h + w.length)
            have hm' : m' < m := by omega
            have hwh_k := (wordHeight_elevateWord h hm).2.2 m' (by omega)
            rw [show h + w.length + m' = k by omega] at hwh_k
            omega
      · intro k hkt hAk hHk hpeq
        by_cases hkA : k < h
        · have hwh_k := (wordHeight_elevateWord h hm).1 k (by omega)
          have hwp_k := (wordPot_elevateWord h hm r).1 k (by omega)
          have hrk : (k : Int) = r + 1 := by omega
          rw [hrk] at hwp_k
          have := hSvs.2.1 (by omega); grind
        · by_cases hkw : k < h + w.length
          · let i := k - h
            have hki : k = h + i := by omega
            have hwi : w[i]! = true := by rw [← hget_w i (by omega), ← hki]; exact hAk
            have hwh_k := (wordHeight_elevateWord h hm).2.1 i (by omega)
            have hwp_k := (wordPot_elevateWord h hm r).2.1 i (by omega)
            rw [← hki] at hwh_k hwp_k
            exact hSvs.2.2 (wordPot (elevateWord h w) r (t + 1)) hwp_t1 (Or.inr ⟨i, by omega, hwi, by omega, by omega⟩)
          · let m' := k - (h + w.length)
            have hSk := hget_S m' (by omega)
            rw [show h + w.length + m' = k by omega] at hSk
            rw [hSk] at hAk; cases hAk
  constructor
  · intro t ht hft k hkt hFk hpeq
    have hres := (hhelper t ht hft (wordHeight (elevateWord h w) (t + 1)) rfl).1 k hkt
    rw [← wordHeight_eq_Fw_wordSign (elevateWord h w) k (by omega),
      ← wordHeight_eq_Fw_wordSign (elevateWord h w) (t + 1) (by omega)] at hFk
    rw [← wordPot_eq_floorPotential (elevateWord h w) _ (t + 1) (by omega),
      ← wordPot_eq_floorPotential (elevateWord h w) _ k (by omega),
      ← wordHeight_eq_Fw_wordSign (elevateWord h w) (t + 1) (by omega)] at hpeq
    exact hres hFk hpeq
  · intro t ht hft k hkt hfk hFk hpeq
    have hres := (hhelper t ht hft (wordHeight (elevateWord h w) (t + 1)) rfl).2 k hkt hfk
    rw [← wordHeight_eq_Fw_wordSign (elevateWord h w) k (by omega),
      ← wordHeight_eq_Fw_wordSign (elevateWord h w) (t + 1) (by omega)] at hFk
    rw [← wordPot_eq_floorPotential (elevateWord h w) _ (t + 1) (by omega),
      ← wordPot_eq_floorPotential (elevateWord h w) _ k (by omega),
      ← wordHeight_eq_Fw_wordSign (elevateWord h w) (t + 1) (by omega)] at hpeq
    exact hres hFk hpeq

/-! ## Closed-form arch word `archWord h a` and bank word `v0Word h a` -/

/-- Arch word `A^h ++ (AS)^a ++ S^h` (`E-799` / `E-805`). -/
def archWord (h a : Nat) : List Bool :=
  elevateWord h (asRep a)

/-- Bank word `A^{h-1} ++ (SA)^{3a-1} ++ A ++ (AS)^a ++ S^h` (`E-799` / `E-805`). -/
def v0Word (h a : Nat) : List Bool :=
  elevateWord (h - 1) (saRep (3 * a - 1) ++ elevateWord 1 (asRep a))

private theorem archWord_length (h a : Nat) :
    (archWord h a).length = 2 * a + 2 * h := by
  unfold archWord
  rw [elevateWord_length, asRep_length]

private theorem mass_archWord (h a : Nat) : mass (archWord h a) = 0 :=
  mass_elevateWord h (mass_asRep a)

private theorem dphiW_archWord (h a : Nat) (r : Int) :
    dphiW (archWord h a) r = (a : Int) * (1 + 2 * ((h : Int) - r)) + (h : Int) * ((h : Int) - 2 * r) := by
  unfold archWord
  rw [dphiW_elevateWord h (mass_asRep a), dphiW_asRep]
  grind

private theorem wordHeight_archWord (h a i : Nat) (hi : i ≤ (archWord h a).length) :
    0 ≤ wordHeight (archWord h a) i ∧ wordHeight (archWord h a) i ≤ (h : Int) + 1 := by
  have hm := mass_asRep a
  rw [archWord_length] at hi
  unfold archWord
  by_cases h1 : i ≤ h
  · rw [(wordHeight_elevateWord h hm).1 i h1]; omega
  · by_cases h2 : i ≤ h + (asRep a).length
    · let j := i - h
      have hj : i = h + j := by omega
      rw [hj, (wordHeight_elevateWord h hm).2.1 j (by omega)]
      have hK : KeyAt (asRep a) (wordHeight (asRep a) j) (wordPot (asRep a) (wordHeight (asRep a) j) j) :=
        Or.inl ⟨j, by omega, rfl, rfl⟩
      have hKey := (asRep_keyAt_sLandAt_fresh a).2.1 _ _ hK
      -- Wait: `wordHeight (asRep a) j` is 0 or 1!
      have h_wh : 0 ≤ wordHeight (asRep a) j ∧ wordHeight (asRep a) j ≤ 1 := by
        rcases hKey with ⟨hr, _, _⟩ | ⟨hr, _, _⟩ | ⟨hr, _, _⟩
        · -- Cannot be -1 for VisitsAt of asRep! Prove directly by induction on a.
          exfalso
          have hnonneg : ∀ m k, k ≤ (asRep m).length → 0 ≤ wordHeight (asRep m) k := by
            intro m
            induction m with
            | zero => intro k hk; simp [asRep] at hk; subst hk; simp [wordHeight, mass]
            | succ m ih =>
              intro k hk
              unfold asRep at hk ⊢
              by_cases hk2 : k ≤ 2
              · have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
                rcases hk3 with rfl | rfl | rfl <;>
                  simp [wordHeight, mass, sign]
              · have htake : ([true, false] ++ asRep m).take k = [true, false] ++ (asRep m).take (k - 2) := by
                  rw [List.take_append, List.take_of_length_le (by simp; omega)]; rfl
                unfold wordHeight; rw [htake, mass_append]
                have hm1 : mass [true, false] = 0 := rfl
                rw [hm1, Int.zero_add]
                exact ih (k - 2) (by rw [List.length_append] at hk; simp only [List.length_cons, List.length_nil] at hk; omega)
          have := hnonneg a j (by omega)
          omega
        · omega
        · omega
      omega
    · let k := i - (h + (asRep a).length)
      have hk : i = h + (asRep a).length + k := by omega
      rw [hk, (wordHeight_elevateWord h hm).2.2 k (by rw [asRep_length] at *; omega)]
      rw [asRep_length] at *
      omega

private theorem fresh_archWord (h a : Nat) (hh : 1 ≤ h) (ha : h * h ≤ a) :
    FreshWord (archWord h a) := by
  have hm := mass_asRep a
  have has := asRep_keyAt_sLandAt_fresh a
  unfold archWord
  refine elevateWord_fresh h hm has.1 ?_ ?_
  · intro r ϕ hS
    have hSr := has.2.2 (r - (h : Int)) ϕ hS
    have hev := two_dvd_mul_sub_two h r
    have hmul : 2 * (((h : Int) * ((h : Int) + 1 - 2 * r)) / 2) =
        (h : Int) * ((h : Int) + 1 - 2 * r) := by
      rcases hev with ⟨q, hq⟩; omega
    constructor
    · intro _ _
      have hr : r = (h : Int) := by omega
      rw [hr] at hmul ⊢
      grind
    · intro _ _; omega
  · intro r hr0 hrh
    have hd : dphiW (elevateWord h (asRep a)) r =
        (a : Int) * (1 + 2 * ((h : Int) - r)) + (h : Int) * ((h : Int) - 2 * r) :=
      dphiW_archWord h a r
    have hha : (h : Int) * (h : Int) ≤ (a : Int) := by exact_mod_cast ha
    have h_a_ge : 3 * (h : Int) * (h : Int) ≤ (a : Int) * (1 + 2 * ((h : Int) - r)) := by
      have h1 : 3 ≤ 1 + 2 * ((h : Int) - r) := by omega
      have h2 := Int.mul_le_mul_of_nonneg_left h1 (by omega : (0 : Int) ≤ (a : Int))
      grind
    have hh2 : (1 : Int) ≤ (h : Int) * (h : Int) := by
      have : 1 ≤ h * h := Nat.mul_le_mul hh hh
      exact_mod_cast this
    have hpos : 2 < 2 * dphiW (elevateWord h (asRep a)) r + r * (r + 1) := by
      rw [hd]
      have hr2 : 0 ≤ r * (r + 1) := Int.mul_nonneg (by omega) (by omega)
      have hhr : (h : Int) * ((h : Int) - 2 * r) ≥ -((h : Int) * (h : Int)) := by
        have h1 : 2 * r ≤ 2 * (h : Int) := by omega
        have h2 := Int.mul_le_mul_of_nonneg_left h1 (by omega : (0 : Int) ≤ (h : Int))
        grind
      have h3 : 3 * (h : Int) * (h : Int) = 3 * ((h : Int) * (h : Int)) := by grind
      omega
    refine ⟨?_, ?_, ?_⟩
    · have hrr : 0 ≤ r * (r - 1) := by
        by_cases hr1 : r = 0
        · rw [hr1]; simp
        · exact Int.mul_nonneg (by omega) (by omega)
      omega
    · intro _
      have hrr : -2 ≤ (r + 1) * (r - 2) := by
        by_cases hr0' : r = 0
        · rw [hr0']; decide
        · by_cases hr1' : r = 1
          · rw [hr1']; decide
          · exact Int.le_trans (by decide : (-2 : Int) ≤ 0) (Int.mul_nonneg (by omega) (by omega))
      omega
    · intro ϕ hϕ hK
      have hKr := has.2.1 (r - (h : Int)) (ϕ - ((h : Int) * ((h : Int) + 1 - 2 * r)) / 2) hK
      have hev := two_dvd_mul_sub_two h r
      have hmul : 2 * (((h : Int) * ((h : Int) + 1 - 2 * r)) / 2) =
          (h : Int) * ((h : Int) + 1 - 2 * r) := by
        rcases hev with ⟨q, hq⟩; omega
      rcases hKr with ⟨hr1, _, hlt⟩ | ⟨hr0', _, _⟩ | ⟨hr1', _, _⟩
      · have hr_eq : r = (h : Int) - 1 := by omega
        rw [hr_eq] at hd hϕ hmul
        grind
      · omega
      · omega

private theorem v0Inner_mass (a : Nat) :
    mass (saRep (3 * a - 1) ++ elevateWord 1 (asRep a)) = 0 := by
  rw [mass_append, mass_saRep, mass_elevateWord 1 (mass_asRep a)]
  rfl

private theorem v0Inner_length (a : Nat) (ha : 1 ≤ a) :
    (saRep (3 * a - 1) ++ elevateWord 1 (asRep a)).length = 8 * a := by
  rw [List.length_append, saRep_length, elevateWord_length, asRep_length]
  omega

private theorem dphiW_v0Inner (a : Nat) (ha : 1 ≤ a) (r : Int) :
    dphiW (saRep (3 * a - 1) ++ elevateWord 1 (asRep a)) r = 2 - 8 * (a : Int) * r := by
  rw [dphiW_append (mass_saRep (3 * a - 1)), dphiW_saRep,
    dphiW_elevateWord 1 (mass_asRep a), dphiW_asRep]
  have h3a : ((3 * a - 1 : Nat) : Int) = 3 * (a : Int) - 1 := by omega
  rw [h3a]
  grind

private theorem v0Word_length (h a : Nat) (hh : 1 ≤ h) (ha : 1 ≤ a) :
    (v0Word h a).length = 2 * h - 2 + 8 * a := by
  unfold v0Word
  rw [elevateWord_length, v0Inner_length a ha]
  omega

private theorem mass_v0Word (h a : Nat) : mass (v0Word h a) = 0 :=
  mass_elevateWord (h - 1) (v0Inner_mass a)

private theorem dphiW_v0Word (h a : Nat) (hh : 1 ≤ h) (ha : 1 ≤ a) (r : Int) :
    dphiW (v0Word h a) r =
      2 + 8 * (a : Int) * (((h : Int) - 1) - r) + ((h : Int) - 1) * (((h : Int) - 1) - 2 * r) := by
  unfold v0Word
  rw [dphiW_elevateWord (h - 1) (v0Inner_mass a), dphiW_v0Inner a ha]
  have hh1 : ((h - 1 : Nat) : Int) = (h : Int) - 1 := by omega
  rw [hh1]
  grind

private theorem fresh_v0Inner (a : Nat) (ha : 1 ≤ a) :
    FreshWord (saRep (3 * a - 1) ++ elevateWord 1 (asRep a)) := by
  have hsa := saRep_keyAt_sLandAt_fresh (3 * a - 1)
  have har := fresh_archWord 1 a (by omega) (by omega)
  refine fresh_append (mass_saRep (3 * a - 1)) hsa.1 har ?_
  intro r ϕ hS hK
  have hKr := hsa.2.1 r (dphiW (saRep (3 * a - 1)) r + ϕ) hK
  rw [dphiW_saRep] at hKr
  have hSr := elevateWord_sLandAt 1 (mass_asRep a) r ϕ hS
  rcases hSr with h1 | ⟨hr0, hr1, h2⟩
  · have hS1 := (asRep_keyAt_sLandAt_fresh a).2.2 _ _ h1
    omega
  · have hr_eq : r = 0 := by omega
    rw [hr_eq] at h2 hKr
    have hd : dphiW (elevateWord 1 (asRep a)) 0 = 3 * (a : Int) + 1 := by
      have := dphiW_archWord 1 a 0
      unfold archWord at this
      grind
    rw [hd] at h2
    have h3a : ((3 * a - 1 : Nat) : Int) = 3 * (a : Int) - 1 := by omega
    rw [h3a] at hKr
    omega

private theorem v0Inner_sLandAt (a : Nat) (ha : 1 ≤ a) (r ϕ : Int) :
    SLandAt (saRep (3 * a - 1) ++ elevateWord 1 (asRep a)) r ϕ →
      (r = -1 ∧ 0 ≤ ϕ ∧ ϕ ≤ 3 * (a : Int) - 1) ∨
      (r = 0 ∧ ϕ = 2) ∨
      (r = 1 ∧ 1 - 3 * (3 * (a : Int) - 1) ≤ ϕ ∧ ϕ ≤ (a : Int) - 3 * (3 * (a : Int) - 1)) := by
  intro hS
  have hsa := saRep_keyAt_sLandAt_fresh (3 * a - 1)
  have has := asRep_keyAt_sLandAt_fresh a
  have h3a : ((3 * a - 1 : Nat) : Int) = 3 * (a : Int) - 1 := by omega
  rcases (sLandAt_append (mass_saRep (3 * a - 1)) r ϕ).mp hS with h1 | h2
  · have h := hsa.2.2 r ϕ h1
    rw [h3a] at h
    exact Or.inl ⟨h.1, h.2.1, by omega⟩
  · have h := elevateWord_sLandAt 1 (mass_asRep a) r (ϕ - dphiW (saRep (3 * a - 1)) r) h2
    rw [dphiW_saRep, h3a] at h
    rcases h with h2a | ⟨hr0, hr1, h2b⟩
    · have hS1 := has.2.2 _ _ h2a
      right; right
      have hr : r = 1 := by omega
      rw [hr] at hS1 ⊢
      omega
    · have hr : r = 0 := by omega
      rw [hr] at h2b
      have hd : dphiW (elevateWord 1 (asRep a)) 0 = 3 * (a : Int) + 1 := by
        have := dphiW_archWord 1 a 0
        unfold archWord at this; grind
      rw [hd] at h2b
      right; left; omega

private theorem v0Inner_keyAt (a : Nat) (ha : 1 ≤ a) (r ϕ : Int) :
    KeyAt (saRep (3 * a - 1) ++ elevateWord 1 (asRep a)) r ϕ →
      (r = -2 ∧ 0 ≤ ϕ ∧ ϕ < 3 * (3 * (a : Int) - 1)) ∨
      (r = -1 ∧ 0 ≤ ϕ ∧ ϕ ≤ 3 * (a : Int) - 1) ∨
      (r = 0 ∧ -(3 * (a : Int) - 1) ≤ ϕ ∧ ϕ ≤ 2) ∨
      (r = 1 ∧ -3 * (3 * (a : Int) - 1) ≤ ϕ ∧ ϕ ≤ (a : Int) - 3 * (3 * (a : Int) - 1)) ∨
      (r = 2 ∧ ϕ ≤ -5 * (3 * (a : Int) - 1)) := by
  intro hK
  have hsa := saRep_keyAt_sLandAt_fresh (3 * a - 1)
  have has := asRep_keyAt_sLandAt_fresh a
  have h3a : ((3 * a - 1 : Nat) : Int) = 3 * (a : Int) - 1 := by omega
  rcases (keyAt_append (mass_saRep (3 * a - 1)) r ϕ).mp hK with h1 | h2
  · have h := hsa.2.1 r ϕ h1
    rw [h3a] at h
    rcases h with h | h | h
    · exact Or.inl ⟨h.1, by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨h.1, h.2.1, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2.1, by omega⟩))
  · have h := elevateWord_keyAt 1 (mass_asRep a) r (ϕ - dphiW (saRep (3 * a - 1)) r) h2
    rw [dphiW_saRep, h3a] at h
    rcases h with ⟨hr0, hr1, h2a⟩ | ⟨hr0, hr1, h2a⟩ | h2b | ⟨hr0, hr1, h2c⟩
    · have hr2 : r = 0 ∨ r = 1 := by omega
      rcases hr2 with rfl | rfl
      · right; right; left; omega
      · right; right; right; left; omega
    · have hr : r = -1 := by omega
      rw [hr] at h2a ⊢
      right; left; omega
    · have hKey := has.2.1 _ _ h2b
      rcases hKey with ⟨hr, hlo, hhi⟩ | ⟨hr, hlo, hhi⟩ | ⟨hr, hlo, hhi⟩
      · have hr0 : r = 0 := by omega
        rw [hr0] at hlo hhi ⊢
        right; right; left; omega
      · have hr1 : r = 1 := by omega
        rw [hr1] at hlo hhi ⊢
        right; right; right; left; omega
      · have hr2 : r = 2 := by omega
        rw [hr2] at hlo hhi ⊢
        right; right; right; right; omega
    · have hr0 : r = 0 := by omega
      rw [hr0] at h2c
      have hd : dphiW (elevateWord 1 (asRep a)) 0 = 3 * (a : Int) + 1 := by
        have := dphiW_archWord 1 a 0
        unfold archWord at this; grind
      rw [hd] at h2c
      right; right; left; omega

private theorem fresh_v0Word (h a : Nat) (hh : 4 ≤ h) (ha : h * h ≤ a) :
    FreshWord (v0Word h a) := by
  have ha1 : 1 ≤ a := by
    have : 16 ≤ h * h := Nat.mul_le_mul hh hh
    omega
  have hm := v0Inner_mass a
  unfold v0Word
  refine elevateWord_fresh (h - 1) hm (fresh_v0Inner a ha1) ?_ ?_
  · intro r ϕ hS
    have hSr := v0Inner_sLandAt a ha1 (r - ((h - 1 : Nat) : Int)) ϕ hS
    have hev := two_dvd_mul_sub_two (h - 1) r
    have hmul : 2 * ((((h - 1 : Nat) : Int) * (((h - 1 : Nat) : Int) + 1 - 2 * r)) / 2) =
        ((h - 1 : Nat) : Int) * (((h - 1 : Nat) : Int) + 1 - 2 * r) := by
      rcases hev with ⟨q, hq⟩; omega
    have hh1 : ((h - 1 : Nat) : Int) = (h : Int) - 1 := by omega
    constructor
    · intro hr0 hrh
      rcases hSr with ⟨hr, hlo, _⟩ | ⟨hr, hphi⟩ | ⟨hr, _, _⟩
      · have hreq : r = (h : Int) - 2 := by omega
        rw [hreq, hh1] at hmul ⊢; grind
      · have hreq : r = (h : Int) - 1 := by omega
        rw [hreq, hh1] at hmul ⊢; grind
      · omega
    · intro _ hrh
      rcases hSr with ⟨hr, _, _⟩ | ⟨hr, _⟩ | ⟨hr, _, _⟩ <;> omega
  · intro r hr0 hrh
    have hh1 : ((h - 1 : Nat) : Int) = (h : Int) - 1 := by omega
    have hd : dphiW (elevateWord (h - 1) (saRep (3 * a - 1) ++ elevateWord 1 (asRep a))) r =
        2 + 8 * (a : Int) * (((h : Int) - 1) - r) + ((h : Int) - 1) * (((h : Int) - 1) - 2 * r) :=
      dphiW_v0Word h a (by omega) ha1 r
    have hha : (h : Int) * (h : Int) ≤ (a : Int) := by exact_mod_cast ha
    have h1ge : 1 ≤ ((h : Int) - 1) - r := by omega
    have h8a : 8 * (a : Int) ≤ 8 * (a : Int) * (((h : Int) - 1) - r) := by
      have := Int.mul_le_mul_of_nonneg_left h1ge (by omega : (0 : Int) ≤ 8 * (a : Int))
      grind
    have hhr : ((h : Int) - 1) * (((h : Int) - 1) - 2 * r) ≥ -((h : Int) * (h : Int)) := by
      have h1 : 2 * r ≤ 2 * (h : Int) := by omega
      have h2 := Int.mul_le_mul_of_nonneg_left h1 (by omega : (0 : Int) ≤ (h : Int) - 1)
      grind
    have hr2 : 0 ≤ r * (r + 1) := Int.mul_nonneg (by omega) (by omega)
    have hpos : 2 < 2 * dphiW (elevateWord (h - 1) (saRep (3 * a - 1) ++ elevateWord 1 (asRep a))) r + r * (r + 1) := by
      rw [hd]; grind
    refine ⟨?_, ?_, ?_⟩
    · have hrr : 0 ≤ r * (r - 1) := by
        by_cases hr1 : r = 0
        · rw [hr1]; simp
        · exact Int.mul_nonneg (by omega) (by omega)
      omega
    · intro _
      have hrr : -2 ≤ (r + 1) * (r - 2) := by
        by_cases hr0' : r = 0
        · rw [hr0']; decide
        · by_cases hr1' : r = 1
          · rw [hr1']; decide
          · exact Int.le_trans (by decide : (-2 : Int) ≤ 0) (Int.mul_nonneg (by omega) (by omega))
      omega
    · intro ϕ hϕ hK
      have hKr := v0Inner_keyAt a ha1 (r - ((h - 1 : Nat) : Int))
        (ϕ - (((h - 1 : Nat) : Int) * (((h - 1 : Nat) : Int) + 1 - 2 * r)) / 2) hK
      have hev := two_dvd_mul_sub_two (h - 1) r
      have hmul : 2 * ((((h - 1 : Nat) : Int) * (((h - 1 : Nat) : Int) + 1 - 2 * r)) / 2) =
          ((h - 1 : Nat) : Int) * (((h - 1 : Nat) : Int) + 1 - 2 * r) := by
        rcases hev with ⟨q, hq⟩; omega
      rcases hKr with ⟨hr, _, hhi⟩ | ⟨hr, _, hhi⟩ | ⟨hr, _, _⟩ | ⟨hr, _, _⟩ | ⟨hr, _⟩
      · have hreq : r = (h : Int) - 3 := by omega
        rw [hreq] at hd hϕ hmul hhi
        rw [hh1] at hmul hhi
        grind
      · have hreq : r = (h : Int) - 2 := by omega
        rw [hreq] at hd hϕ hmul hhi
        rw [hh1] at hmul hhi
        grind
      · omega
      · omega
      · omega

/-! ## `additions` and `free` subadditivity & conveyor-belt supply on `V0 ++ V^R` -/

private theorem endN_of_earlier_visit (w : List Bool) (t u : Nat)
    (ht : t < w.length) (hAt : w[t]! = true) (hut : u < t)
    (hH : wordHeight w t = wordHeight w u + 1)
    (hP : wordPot w (wordHeight w u) t = wordPot w (wordHeight w u) u) :
    EndN (wordSign w) 0 t := by
  refine ⟨hAt, u, t - u, Nat.zero_le u, by omega, by omega, ?_, ?_⟩
  · rw [show u + (t - u) = t by omega,
      ← wordHeight_eq_Fw_wordSign w t (by omega), ← wordHeight_eq_Fw_wordSign w u (by omega)]
    exact hH
  · have hsp := area_split_at (wordSign w) 0 u t (Nat.zero_le u) (by omega)
    rw [Nat.sub_zero, Nat.sub_zero, Ar_areaW, Ar_areaW,
      seg_wordSign_eq_take w t (by omega), seg_wordSign_eq_take w u (by omega),
      ← wordHeight_eq_Fw_wordSign w u (by omega)] at hsp
    have h0 : Fw (wordSign w) 0 = 0 := rfl
    rw [h0] at hsp
    unfold wordPot at hP
    have htu : ((t - u : Nat) : Int) = (t : Int) - (u : Int) := by omega
    rw [htu] at hsp
    grind

private theorem endN_congr_prefix (f g : Nat → Bool) (L t : Nat) (ht : t < L)
    (hfg : ∀ i, i < L → f i = g i) :
    EndN f 0 t ↔ EndN g 0 t := by
  have hFw : ∀ k, k ≤ L → Fw f k = Fw g k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [Fw_succ, Fw_succ, ih (by omega), hfg k (by omega)]
  have hAr : ∀ a k, a + k ≤ L → Ar f a k = Ar g a k := by
    intro a k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [Ar_succ, Ar_succ, ih (by omega), hFw (a + k + 1) (by omega), hFw a (by omega)]
  constructor
  · rintro ⟨hft, u, k, hu, htk, hk, hL, hA⟩
    refine ⟨by rw [← hfg t ht]; exact hft, u, k, hu, htk, hk, ?_, ?_⟩
    · rw [← hFw (u + k) (by omega), ← hFw u (by omega)]; exact hL
    · rw [← hAr u k (by omega)]; exact hA
  · rintro ⟨hgt, u, k, hu, htk, hk, hL, hA⟩
    refine ⟨by rw [hfg t ht]; exact hgt, u, k, hu, htk, hk, ?_, ?_⟩
    · rw [hFw (u + k) (by omega), hFw u (by omega)]; exact hL
    · rw [hAr u k (by omega)]; exact hA

private theorem additions_congr_prefix (f g : Nat → Bool) (L : Nat)
    (hfg : ∀ i, i < L → f i = g i) :
    additions f 0 L = additions g 0 L := by
  unfold additions
  have haux : ∀ k, k ≤ L → cN (fun x => f x = true) 0 k = cN (fun x => g x = true) 0 k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      by_cases hfk : f k = true
      · rw [cN_succ_pos _ 0 k (by simpa using hfk),
          cN_succ_pos _ 0 k (by simpa [← hfg k (by omega)] using hfk), ih (by omega)]
      · rw [cN_succ_neg _ 0 k (by simpa using hfk),
          cN_succ_neg _ 0 k (by simpa [← hfg k (by omega)] using hfk), ih (by omega)]
  exact haux L (Nat.le_refl L)

private theorem free_congr_prefix (f g : Nat → Bool) (L : Nat)
    (hfg : ∀ i, i < L → f i = g i) :
    free f 0 L = free g 0 L := by
  unfold free
  have haux : ∀ k, k ≤ L →
      cN (fun x => f x = true ∧ ¬ EndN f 0 x) 0 k =
      cN (fun x => g x = true ∧ ¬ EndN g 0 x) 0 k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have heq : (f k = true ∧ ¬ EndN f 0 k) ↔ (g k = true ∧ ¬ EndN g 0 k) := by
        rw [hfg k (by omega), endN_congr_prefix f g L k (by omega) hfg]
      by_cases h : f k = true ∧ ¬ EndN f 0 k
      · rw [cN_succ_pos _ 0 k (by simpa using h),
          cN_succ_pos _ 0 k (by simpa using heq.mp h), ih (by omega)]
      · rw [cN_succ_neg _ 0 k (by simpa using h),
          cN_succ_neg _ 0 k (by simpa using fun hg => h (heq.mpr hg)), ih (by omega)]
  exact haux L (Nat.le_refl L)

private theorem cN_add_split (P : Nat → Prop) (n a b : Nat) :
    cN P n (a + b) = cN P n a + cN P (n + a) b := by
  induction b with
  | zero => simp [cN]
  | succ b ih =>
    rw [← Nat.add_assoc]
    by_cases h : P (n + a + b)
    · rw [cN_succ_pos P n (a + b) (by simpa [Nat.add_assoc] using h),
        cN_succ_pos P (n + a) b h, ih]
      omega
    · rw [cN_succ_neg P n (a + b) (by simpa [Nat.add_assoc] using h),
        cN_succ_neg P (n + a) b h, ih]

private theorem cN_le_of_imp (P Q : Nat → Prop) (n k : Nat)
    (h : ∀ i, i < k → P (n + i) → Q (n + i)) :
    cN P n k ≤ cN Q n k := by
  induction k with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    have ih' := ih (fun i hi => h i (by omega))
    by_cases hp : P (n + k)
    · rw [cN_succ_pos P n k hp, cN_succ_pos Q n k (h k (by omega) hp)]
      omega
    · rw [cN_succ_neg P n k hp]
      by_cases hq : Q (n + k)
      · rw [cN_succ_pos Q n k hq]; omega
      · rw [cN_succ_neg Q n k hq]; exact ih'

private theorem cN_le_one_of_unique (P : Nat → Prop) (n k : Nat)
    (h : ∀ i j, i < k → j < k → P (n + i) → P (n + j) → i = j) :
    cN P n k ≤ 1 := by
  induction k with
  | zero => simp [cN]
  | succ k ih =>
    by_cases hp : P (n + k)
    · rw [cN_succ_pos P n k hp]
      have hzero : cN P n k = 0 := by
        have hle := cN_le_of_imp P (fun _ => False) n k (fun i hi hpi => by
          have := h i k (by omega) (by omega) hpi hp; omega)
        have hfalse : ∀ m, cN (fun _ => False) n m = 0 := by
          intro m; induction m with
          | zero => rfl
          | succ m ihm => rw [cN_succ_neg _ n m (fun x => x), ihm]
        rw [hfalse] at hle; omega
      omega
    · rw [cN_succ_neg P n k hp]
      exact ih (fun i j hi hj => h i j (by omega) (by omega))

private theorem free_le_additions (f : Nat → Bool) (n k : Nat) :
    free f n k ≤ additions f n k :=
  cN_le_of_imp _ _ n k (fun _ _ h => h.1)

private theorem additions_eq_half_len_of_mass_zero (w : List Bool) (hm : mass w = 0) :
    2 * additions (wordSign w) 0 w.length = w.length := by
  have h1 := cN_walk (wordSign w) 0 w.length
  have h2 := seg_mass (wordSign w) 0 w.length
  rw [seg_wordSign_eq_take w w.length (Nat.le_refl _), List.take_length, hm] at h2
  have h0 : Fw (wordSign w) 0 = 0 := rfl
  unfold additions
  omega

private theorem free_shift_le_of_slice (f : Nat → Bool) (s : Nat) (v : List Bool)
    (hmatch : ∀ i, i < v.length → f (s + i) = v[i]!) :
    free f s v.length ≤ free (wordSign v) 0 v.length := by
  have hFw_rel : ∀ i, i ≤ v.length → Fw f (s + i) - Fw f s = Fw (wordSign v) i := by
    intro i
    induction i with
    | zero => intro _; simp [Fw]
    | succ i ih =>
      intro hi
      rw [show s + (i + 1) = (s + i) + 1 by omega, Fw_succ, Fw_succ, hmatch i (by omega)]
      have hvs : wordSign v i = v[i]! := by unfold wordSign; simp [show i < v.length by omega]
      rw [hvs]
      have := ih (by omega)
      omega
  have hAr_rel : ∀ a k, a + k ≤ v.length → Ar f (s + a) k = Ar (wordSign v) a k := by
    intro a k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [Ar_succ, Ar_succ, ih (by omega),
        show s + a + k + 1 = s + (a + k + 1) by omega]
      have h1 := hFw_rel (a + k + 1) (by omega)
      have h2 := hFw_rel a (by omega)
      omega
  -- Prove `cN (P f) s k ≤ cN (P (wordSign v)) 0 k` by induction on `k ≤ v.length`!
  have haux : ∀ k, k ≤ v.length →
      cN (fun x => f x = true ∧ ¬ EndN f 0 x) s k ≤
      cN (fun x => wordSign v x = true ∧ ¬ EndN (wordSign v) 0 x) 0 k := by
    intro k
    induction k with
    | zero => intro _; exact Nat.le_refl 0
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have himp : (f (s + k) = true ∧ ¬ EndN f 0 (s + k)) →
          (wordSign v k = true ∧ ¬ EndN (wordSign v) 0 k) := by
        rintro ⟨hfk, hnot⟩
        have hvk : wordSign v k = true := by
          unfold wordSign; rw [← hmatch k (by omega)]; exact hfk
        refine ⟨hvk, fun hend => hnot ?_⟩
        obtain ⟨_, u, d, _, hkd, hd, hL, hA⟩ := hend
        refine ⟨hfk, s + u, d, Nat.zero_le _, by omega, hd, ?_, ?_⟩
        · rw [show s + u + d = s + (u + d) by omega]
          have h1 := hFw_rel (u + d) (by omega)
          have h2 := hFw_rel u (by omega)
          omega
        · rw [hAr_rel u d (by omega)]; exact hA
      by_cases h1 : f (s + k) = true ∧ ¬ EndN f 0 (s + k)
      · rw [cN_succ_pos _ s k h1, cN_succ_pos _ 0 k (by simpa using himp h1)]; omega
      · rw [cN_succ_neg _ s k h1]
        by_cases h2 : wordSign v (0 + k) = true ∧ ¬ EndN (wordSign v) 0 (0 + k)
        · rw [cN_succ_pos _ 0 k h2]; omega
        · rw [cN_succ_neg _ 0 k h2]; exact ih'
  exact haux v.length (Nat.le_refl _)

private theorem mass_repeatWord {v : List Bool} (hm : mass v = 0) :
    ∀ n : Nat, mass (repeatWord n v) = 0
  | 0 => rfl
  | n + 1 => by
    unfold repeatWord
    rw [mass_append, hm, mass_repeatWord hm n]
    rfl

private theorem repeatWord_split (v : List Bool) (m R : Nat) (hm : m < R) :
    repeatWord R v = repeatWord m v ++ v ++ repeatWord (R - m - 1) v := by
  induction R generalizing m with
  | zero => omega
  | succ R ih =>
    cases m with
    | zero =>
      simp [repeatWord]
    | succ m =>
      have h1 : repeatWord (R + 1) v = v ++ repeatWord R v := rfl
      rw [h1, ih m (by omega)]
      simp [repeatWord, List.append_assoc]

private theorem wordHeight_asRep_even (a j : Nat) (hj : j ≤ a) :
    wordHeight (asRep a) (2 * j) = 0 := by
  induction a generalizing j with
  | zero =>
    have : j = 0 := by omega
    subst this; simp [asRep, wordHeight, mass]
  | succ a ih =>
    cases j with
    | zero => simp [asRep, wordHeight, mass]
    | succ j =>
      unfold asRep
      have h1 : ([true, false] ++ asRep a).take (2 * (j + 1)) = [true, false] ++ (asRep a).take (2 * j) := by
        rw [List.take_append, List.take_of_length_le (by simp; omega)]; simp; congr 1; omega
      unfold wordHeight; rw [h1, mass_append]
      have hm1 : mass [true, false] = 0 := rfl
      rw [hm1, Int.zero_add]
      exact ih j (by omega)

private theorem wordPot_asRep_even (a j : Nat) (hj : j ≤ a) (r : Int) :
    wordPot (asRep a) r (2 * j) = (j : Int) * (1 - 2 * r) := by
  induction a generalizing j with
  | zero =>
    have : j = 0 := by omega
    subst this; simp [asRep, wordPot, areaW]
  | succ a ih =>
    cases j with
    | zero => simp [asRep, wordPot, areaW]
    | succ j =>
      unfold asRep
      have h1 : ([true, false] ++ asRep a).take (2 * (j + 1)) = [true, false] ++ (asRep a).take (2 * j) := by
        rw [List.take_append, List.take_of_length_le (by simp; omega)]; simp; congr 1; omega
      unfold wordPot
      rw [h1, areaW_append_of_mass_zero (by rfl : mass [true, false] = 0)]
      have ha1 : areaW [true, false] = 1 := by simp [areaW, sign]
      have ih' := ih j (by omega)
      unfold wordPot at ih'
      rw [ha1]
      push_cast
      grind

private theorem wordHeight_saRep_even (b j : Nat) (hj : j ≤ b) :
    wordHeight (saRep b) (2 * j) = 0 := by
  induction b generalizing j with
  | zero =>
    have : j = 0 := by omega
    subst this; simp [saRep, wordHeight, mass]
  | succ b ih =>
    cases j with
    | zero => simp [saRep, wordHeight, mass]
    | succ j =>
      unfold saRep
      have h1 : ([false, true] ++ saRep b).take (2 * (j + 1)) = [false, true] ++ (saRep b).take (2 * j) := by
        rw [List.take_append, List.take_of_length_le (by simp; omega)]; simp; congr 1; omega
      unfold wordHeight; rw [h1, mass_append]
      have hm1 : mass [false, true] = 0 := rfl
      rw [hm1, Int.zero_add]
      exact ih j (by omega)

private theorem wordPot_saRep_even (b j : Nat) (hj : j ≤ b) (r : Int) :
    wordPot (saRep b) r (2 * j) = (j : Int) * (-1 - 2 * r) := by
  induction b generalizing j with
  | zero =>
    have : j = 0 := by omega
    subst this; simp [saRep, wordPot, areaW]
  | succ b ih =>
    cases j with
    | zero => simp [saRep, wordPot, areaW]
    | succ j =>
      unfold saRep
      have h1 : ([false, true] ++ saRep b).take (2 * (j + 1)) = [false, true] ++ (saRep b).take (2 * j) := by
        rw [List.take_append, List.take_of_length_le (by simp; omega)]; simp; congr 1; omega
      unfold wordPot
      rw [h1, areaW_append_of_mass_zero (by rfl : mass [false, true] = 0)]
      have ha1 : areaW [false, true] = -1 := by simp [areaW, sign]
      have ih' := ih j (by omega)
      unfold wordPot at ih'
      rw [ha1]
      push_cast
      grind

private theorem asRep_getElem! (a i : Nat) (hi : i < 2 * a) :
    (asRep a)[i]! = if i % 2 = 0 then true else false := by
  induction a generalizing i with
  | zero => omega
  | succ a ih =>
    unfold asRep
    by_cases h2 : i < 2
    · have : i = 0 ∨ i = 1 := by omega
      rcases this with rfl | rfl <;> rfl
    · have hget : ([true, false] ++ asRep a)[i]! = (asRep a)[i - 2]! := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by simp; omega),
          List.length_cons, List.length_singleton, ← List.getElem!_eq_getElem?_getD]
      rw [hget, ih (i - 2) (by omega)]
      have : (i - 2) % 2 = i % 2 := by omega
      rw [this]

/-- Self-extending `S`-landing conveyor-belt theorem (`E-805`): inside `w = V0 ++ V^R`
where `V = P ++ archWord h a` has exact unit drift `dphiW V (h - 1) = 1`, every `A`-step
of `(AS)^a` inside copy `m` (`0 ≤ m < R`) is supplied by either `V0`'s `(SA)^{3a-1}` bank,
`V0`'s `S^h` landing, or an earlier copy's `S^h` landing, with AT MOST ONE free step! -/
private theorem free_conveyor_arch_le_one (h a R m : Nat) (P : List Bool)
    (hh : 4 ≤ h) (ha : 1 ≤ a) (hmP : mass P = 0) (hmR : m < R)
    (hdV : dphiW (P ++ archWord h a) ((h : Int) - 1) = 1) :
    let V := P ++ archWord h a
    let w := v0Word h a ++ repeatWord R V
    let sArch := (v0Word h a).length + m * V.length + P.length + h
    free (wordSign w) sArch (2 * a) ≤ 1 := by
  intro V w sArch
  have hmV : mass V = 0 := by rw [mass_append, hmP, mass_archWord]; rfl
  have hlenV0 : (v0Word h a).length = 2 * h - 2 + 8 * a := v0Word_length h a (by omega) ha
  have hlenA : (archWord h a).length = 2 * a + 2 * h := archWord_length h a
  have hlenV : V.length = P.length + (2 * a + 2 * h) := by
    dsimp only [V]; rw [List.length_append, hlenA]
  have hlenW : w.length = (v0Word h a).length + R * V.length := by
    dsimp only [w]; rw [List.length_append, repeatWord_length]
  have hsplit_m : w = (v0Word h a ++ repeatWord m V ++ P) ++ archWord h a ++ repeatWord (R - m - 1) V := by
    dsimp only [w]
    rw [repeatWord_split V m R hmR]
    dsimp only [V]
    simp only [List.append_assoc]
  have hmPre : mass (v0Word h a ++ repeatWord m V ++ P) = 0 := by
    rw [mass_append, mass_append, mass_v0Word, mass_repeatWord hmV, hmP]; rfl
  have hlenPre : (v0Word h a ++ repeatWord m V ++ P).length = (v0Word h a).length + m * V.length + P.length := by
    rw [List.length_append, List.length_append, repeatWord_length]
  -- Exact height & potential of `V0`'s bank peak `u = (h - 1) + 2*d` (`0 ≤ d ≤ 3*a - 1`)
  have hBank : ∀ d, d ≤ 3 * a - 1 →
      let u := (h - 1) + 2 * d
      u < (v0Word h a).length ∧
      wordHeight w u = (h : Int) - 1 ∧
      2 * wordPot w ((h : Int) - 1) u = -(((h : Int) - 1) * ((h : Int) - 2)) - 2 * (d : Int) := by
    intro d hd
    have hu_lt : (h - 1) + 2 * d < (v0Word h a).length := by omega
    refine ⟨hu_lt, ?_, ?_⟩
    · rw [wordHeight_append_left _ (by omega)]
      unfold v0Word
      have h2d_le : 2 * d ≤ (saRep (3 * a - 1) ++ elevateWord 1 (asRep a)).length := by
        rw [v0Inner_length a ha]; omega
      rw [(wordHeight_elevateWord (h - 1) (v0Inner_mass a)).2.1 (2 * d) h2d_le,
        wordHeight_append_left (2 * d) (by rw [saRep_length]; omega),
        wordHeight_saRep_even (3 * a - 1) d hd]
      omega
    · rw [wordPot_append_left _ _ (by omega)]
      unfold v0Word
      have h2d_le : 2 * d ≤ (saRep (3 * a - 1) ++ elevateWord 1 (asRep a)).length := by
        rw [v0Inner_length a ha]; omega
      have hwp := (wordPot_elevateWord (h - 1) (v0Inner_mass a) ((h : Int) - 1)).2.1 (2 * d) h2d_le
      rw [wordPot_append_left _ (2 * d) (by rw [saRep_length]; omega),
        wordPot_saRep_even (3 * a - 1) d hd] at hwp
      have hh1 : ((h - 1 : Nat) : Int) = (h : Int) - 1 := by omega
      rw [hh1] at hwp
      grind
  -- Exact height & potential of `V0`'s `S^h` landing at `h - 1`: index `u = (v0Word h a).length - (h - 1)`
  have hV0_S : let u := (v0Word h a).length - (h - 1)
      u < (v0Word h a).length ∧
      wordHeight w u = (h : Int) - 1 ∧
      2 * wordPot w ((h : Int) - 1) u = -(((h : Int) - 1) * ((h : Int) - 2)) + 4 := by
    have hu_lt : (v0Word h a).length - (h - 1) < (v0Word h a).length := by omega
    refine ⟨hu_lt, ?_, ?_⟩
    · rw [wordHeight_append_left _ (by omega)]
      have hidx : (v0Word h a).length - (h - 1) =
          (h - 1) + (saRep (3 * a - 1) ++ elevateWord 1 (asRep a)).length + 0 := by
        rw [hlenV0, v0Inner_length a ha]; omega
      rw [hidx]; unfold v0Word
      rw [(wordHeight_elevateWord (h - 1) (v0Inner_mass a)).2.2 0 (Nat.zero_le _)]
      omega
    · rw [wordPot_append_left _ _ (by omega)]
      have hidx : (v0Word h a).length - (h - 1) =
          (h - 1) + (saRep (3 * a - 1) ++ elevateWord 1 (asRep a)).length + 0 := by
        rw [hlenV0, v0Inner_length a ha]; omega
      have hwp := (wordPot_elevateWord (h - 1) (v0Inner_mass a) ((h : Int) - 1)).2.2 0 (Nat.zero_le _)
      have hh1 : ((h - 1 : Nat) : Int) = (h : Int) - 1 := by omega
      rw [hh1, Int.natCast_zero, Int.sub_zero] at hwp
      have hdv := dphiW_v0Word h a (by omega) ha ((h : Int) - 1)
      rw [hidx]; unfold v0Word at hdv ⊢
      rw [hwp, hdv]
      grind
  -- Exact height & potential of copy `t - 1`'s `S^h` landing at `h - 1` (`1 ≤ t ≤ m`):
  -- index `u = (v0Word h a).length + t * V.length - (h - 1)`
  have hCopy_S : ∀ t, 1 ≤ t → t ≤ m →
      let u := (v0Word h a).length + t * V.length - (h - 1)
      u < sArch ∧
      wordHeight w u = (h : Int) - 1 ∧
      2 * wordPot w ((h : Int) - 1) u = -(((h : Int) - 1) * ((h : Int) - 2)) + 4 + 2 * (t : Int) := by
    intro t ht1 htm
    have hu_lt : (v0Word h a).length + t * V.length - (h - 1) < sArch := by
      dsimp only [sArch]
      have : t * V.length ≤ m * V.length := Nat.mul_le_mul_right V.length htm
      omega
    have hsplit_t : w = (v0Word h a ++ repeatWord (t - 1) V ++ P) ++ archWord h a ++ repeatWord (R - t) V := by
      dsimp only [w]
      have h1 := repeatWord_split V (t - 1) R (by omega)
      rw [show R - (t - 1) - 1 = R - t by omega] at h1
      rw [h1]; dsimp only [V]; simp only [List.append_assoc]
    have hmPre_t : mass (v0Word h a ++ repeatWord (t - 1) V ++ P) = 0 := by
      rw [mass_append, mass_append, mass_v0Word, mass_repeatWord hmV, hmP]; rfl
    have hlenPre_t : (v0Word h a ++ repeatWord (t - 1) V ++ P).length =
        (v0Word h a).length + (t - 1) * V.length + P.length := by
      rw [List.length_append, List.length_append, repeatWord_length]
    have hidx : (v0Word h a).length + t * V.length - (h - 1) =
        (v0Word h a ++ repeatWord (t - 1) V ++ P).length + (h + (asRep a).length + 1) := by
      rw [hlenPre_t, asRep_length, hlenV]
      have htmul : t * (P.length + (2 * a + 2 * h)) = (t - 1) * (P.length + (2 * a + 2 * h)) + (P.length + (2 * a + 2 * h)) := by
        cases t with
        | zero => omega
        | succ t' => simp [Nat.succ_mul]
      omega
    refine ⟨hu_lt, ?_, ?_⟩
    · rw [hsplit_t, hidx,
        wordHeight_append_left _ (by simp only [List.length_append, hlenA, asRep_length]; omega),
        wordHeight_append_right hmPre_t _ (by rw [hlenA, asRep_length]; omega)]
      unfold archWord
      rw [(wordHeight_elevateWord h (mass_asRep a)).2.2 1 (by omega)]
      omega
    · rw [hsplit_t, hidx,
        wordPot_append_left _ _ (by simp only [List.length_append, hlenA, asRep_length]; omega),
        wordPot_append_right hmPre_t _ _ (by rw [hlenA, asRep_length]; omega)]
      have hwp := (wordPot_elevateWord h (mass_asRep a) ((h : Int) - 1)).2.2 1 (by omega)
      have hdPre : dphiW (v0Word h a ++ repeatWord (t - 1) V ++ P) ((h : Int) - 1) +
          dphiW (archWord h a) ((h : Int) - 1) =
          dphiW (v0Word h a) ((h : Int) - 1) + (t : Int) := by
        rw [dphiW_append (by rw [mass_append, mass_v0Word, mass_repeatWord hmV]; rfl),
          dphiW_append (mass_v0Word h a), dphiW_repeatWord hmV, hdV]
        have hdPA : dphiW P ((h : Int) - 1) + dphiW (archWord h a) ((h : Int) - 1) = 1 := by
          rw [← dphiW_append hmP]; exact hdV
        have ht1' : ((t - 1 : Nat) : Int) = (t : Int) - 1 := by omega
        rw [ht1']
        grind
      have hdv := dphiW_v0Word h a (by omega) ha ((h : Int) - 1)
      unfold archWord at hdPre ⊢
      grind
  -- Now prove uniqueness of any free index `i < 2 * a` via `cN_le_one_of_unique`!
  unfold free
  refine cN_le_one_of_unique _ sArch (2 * a) ?_
  intro i1 i2 hi1 hi2 hp1 hp2
  -- Helper: any free index `i < 2*a` must be `2*j` with `m = 3*(a - 1 - j) + 1`!
  have huniq : ∀ i, i < 2 * a → (wordSign w (sArch + i) = true ∧ ¬ EndN (wordSign w) 0 (sArch + i)) →
      i % 2 = 0 ∧ (m : Int) = 3 * ((a : Int) - 1 - ((i / 2 : Nat) : Int)) + 1 := by
    intro i hi ⟨hAi, hnot⟩
    have hget_i : w[sArch + i]! = (asRep a)[i]! := by
      have hs1 : sArch + i = (v0Word h a ++ repeatWord m V ++ P).length + (h + i) := by
        rw [hlenPre]; dsimp only [sArch]; omega
      rw [hsplit_m, hs1, List.getElem!_eq_getElem?_getD,
        List.getElem?_append_left (by simp only [List.length_append, hlenA]; omega),
        List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      unfold archWord elevateWord
      rw [List.append_assoc, List.getElem?_append_right (by simp), List.length_replicate,
        Nat.add_sub_cancel_left, List.getElem?_append_left (by rw [asRep_length]; omega),
        ← List.getElem!_eq_getElem?_getD]
    have hAi' : w[sArch + i]! = true := hAi
    rw [hget_i, asRep_getElem! a i hi] at hAi'
    have heven : i % 2 = 0 := by
      by_cases h0 : i % 2 = 0
      · exact h0
      · simp [h0] at hAi'
    refine ⟨heven, ?_⟩
    let j := i / 2
    have hij : i = 2 * j := by omega
    have hj : j < a := by omega
    -- Compute height & potential of `t = sArch + i` at `r = h - 1`:
    have hs1 : sArch + i = (v0Word h a ++ repeatWord m V ++ P).length + (h + 2 * j) := by
      rw [hlenPre]; dsimp only [sArch]; omega
    have ht_lt : sArch + i < w.length := by
      rw [hlenW]; dsimp only [sArch]
      have : (m + 1) * V.length ≤ R * V.length := Nat.mul_le_mul_right V.length (by omega)
      simp [Nat.add_mul] at this
      omega
    have hHt : wordHeight w (sArch + i) = (h : Int) := by
      rw [hsplit_m, hs1, wordHeight_append_left _ (by simp only [List.length_append, hlenA]; omega),
        wordHeight_append_right hmPre _ (by rw [hlenA]; omega)]
      unfold archWord
      rw [(wordHeight_elevateWord h (mass_asRep a)).2.1 (2 * j) (by rw [asRep_length]; omega),
        wordHeight_asRep_even a j (by omega)]
      omega
    have hPt : 2 * wordPot w ((h : Int) - 1) (sArch + i) =
        -(((h : Int) - 1) * ((h : Int) - 2)) + 2 * (m : Int) - 6 * ((a : Int) - 1 - (j : Int)) := by
      rw [hsplit_m, hs1, wordPot_append_left _ _ (by simp only [List.length_append, hlenA]; omega),
        wordPot_append_right hmPre _ _ (by rw [hlenA]; omega)]
      have hwp := (wordPot_elevateWord h (mass_asRep a) ((h : Int) - 1)).2.1 (2 * j) (by rw [asRep_length]; omega)
      rw [show ((h : Int) - 1) - (h : Int) = -1 by omega, wordPot_asRep_even a j (by omega) (-1)] at hwp
      have hdPre : dphiW (v0Word h a ++ repeatWord m V ++ P) ((h : Int) - 1) =
          dphiW (v0Word h a) ((h : Int) - 1) + (m : Int) + (1 - dphiW (archWord h a) ((h : Int) - 1)) := by
        rw [dphiW_append (by rw [mass_append, mass_v0Word, mass_repeatWord hmV]; rfl),
          dphiW_append (mass_v0Word h a), dphiW_repeatWord hmV, hdV]
        have hdPA : dphiW P ((h : Int) - 1) + dphiW (archWord h a) ((h : Int) - 1) = 1 := by
          rw [← dphiW_append hmP]; exact hdV
        grind
      have hdv := dphiW_v0Word h a (by omega) ha ((h : Int) - 1)
      have hda := dphiW_archWord h a ((h : Int) - 1)
      unfold archWord at hda hdPre ⊢
      grind
    -- Now rule out `m ≠ 3*(a - 1 - j) + 1` by supplying an earlier visit `u < sArch + i`!
    by_cases hcase1 : (m : Int) ≤ 3 * ((a : Int) - 1 - (j : Int))
    · exfalso; apply hnot
      let d := 3 * (a - 1 - j) - m
      have hd_le : d ≤ 3 * a - 1 := by omega
      obtain ⟨hu_lt, huH, huP⟩ := hBank d hd_le
      exact endN_of_earlier_visit w (sArch + i) ((h - 1) + 2 * d) ht_lt
        hAi
        (by dsimp only [sArch]; omega)
        (by rw [hHt, huH]; omega)
        (by rw [huH]; omega)
    · by_cases hcase2 : (m : Int) = 3 * ((a : Int) - 1 - (j : Int)) + 1
      · exact hcase2
      · exfalso; apply hnot
        let t := m - 3 * (a - 1 - j) - 2
        by_cases ht0 : t = 0
        · obtain ⟨hu_lt, huH, huP⟩ := hV0_S
          exact endN_of_earlier_visit w (sArch + i) ((v0Word h a).length - (h - 1)) ht_lt
            hAi
            (by dsimp only [sArch]; omega)
            (by rw [hHt, huH]; omega)
            (by rw [huH]; omega)
        · obtain ⟨hu_lt, huH, huP⟩ := hCopy_S t (by omega) (by omega)
          exact endN_of_earlier_visit w (sArch + i) ((v0Word h a).length + t * V.length - (h - 1)) ht_lt
            hAi
            (by omega)
            (by rw [hHt, huH]; omega)
            (by rw [huH]; omega)
  have h1 := huniq i1 hi1 hp1
  have h2 := huniq i2 hi2 hp2
  omega

/-- Stage-lift `free` bound (`E-805`): on `B' = V0 ++ V^R` with `V = prefix ++ B ++ archWord h a`,
the total number of free additions satisfies
`free (wordSign B') 0 B'.length ≤ (h + 4 * a - 1) + R * (q + p + free (wordSign B) 0 B.length + h + 1)`. -/
private theorem free_stage_lift_le (h q p a R : Nat) (B : List Bool)
    (hh : 4 ≤ h) (ha : 1 ≤ a) (hmB : mass B = 0)
    (hdV : dphiW ((asRep q ++ saRep p) ++ B ++ archWord h a) ((h : Int) - 1) = 1) :
    let V := (asRep q ++ saRep p) ++ B ++ archWord h a
    let w := v0Word h a ++ repeatWord R V
    free (wordSign w) 0 w.length ≤
      (h + 4 * a - 1) + R * (q + p + free (wordSign B) 0 B.length + h + 1) := by
  intro V w
  have hmPre : mass (asRep q ++ saRep p) = 0 := by rw [mass_append, mass_asRep, mass_saRep]; rfl
  have hmPB : mass ((asRep q ++ saRep p) ++ B) = 0 := by rw [mass_append, hmPre, hmB]; rfl
  have hmV : mass V = 0 := by dsimp only [V]; rw [mass_append, hmPB, mass_archWord]; rfl
  have hlenV0 : (v0Word h a).length = 2 * h - 2 + 8 * a := v0Word_length h a (by omega) ha
  have hlenPre : (asRep q ++ saRep p).length = 2 * q + 2 * p := by
    rw [List.length_append, asRep_length, saRep_length]
  have hlenA : (archWord h a).length = 2 * a + 2 * h := archWord_length h a
  have hlenV : V.length = (2 * q + 2 * p) + B.length + (2 * a + 2 * h) := by
    dsimp only [V]; rw [List.length_append, List.length_append, hlenPre, hlenA]
  have hlenW : w.length = (v0Word h a).length + R * V.length := by
    dsimp only [w]; rw [List.length_append, repeatWord_length]
  -- Split `free w` into `V0` and `R` copies of `V`
  have hV0_le : free (wordSign w) 0 (v0Word h a).length ≤ h + 4 * a - 1 := by
    have h1 := free_shift_le_of_slice (wordSign w) 0 (v0Word h a) (fun i hi => by
      unfold wordSign
      rw [Nat.zero_add]
      dsimp only [w]
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getElem!_eq_getElem?_getD])
    have h2 := free_le_additions (wordSign (v0Word h a)) 0 (v0Word h a).length
    have h3 := additions_eq_half_len_of_mass_zero (v0Word h a) (mass_v0Word h a)
    omega
  -- Per-copy bound on `free (wordSign w) (V0.length + m * V.length) V.length`
  have hCopy_le : ∀ m, m < R →
      free (wordSign w) ((v0Word h a).length + m * V.length) V.length ≤
        q + p + free (wordSign B) 0 B.length + h + 1 := by
    intro m hmR
    let s0 := (v0Word h a).length + m * V.length
    have hsplit_m : w = (v0Word h a ++ repeatWord m V) ++ V ++ repeatWord (R - m - 1) V := by
      dsimp only [w]; rw [repeatWord_split V m R hmR]; simp only [List.append_assoc]
    have hlen_m : (v0Word h a ++ repeatWord m V).length = s0 := by
      rw [List.length_append, repeatWord_length]
    have hgetV : ∀ i, i < V.length → wordSign w (s0 + i) = V[i]! := by
      intro i hi
      unfold wordSign
      rw [hsplit_m, ← hlen_m, List.getElem!_eq_getElem?_getD,
        List.getElem?_append_left (by simp only [List.length_append]; omega),
        List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
        ← List.getElem!_eq_getElem?_getD]
    -- Split `V` into `prefix` (`2q+2p`), `B`, `A^h`, `asRep a` (`2a`), `S^h` (`h`)
    have hlenV_eq : V.length = ((asRep q ++ saRep p).length + B.length) + (h + (2 * a + h)) := by
      rw [hlenV, hlenPre]; omega
    have hsplit_len : free (wordSign w) s0 V.length =
        free (wordSign w) s0 (((asRep q ++ saRep p).length + B.length) + (h + (2 * a + h))) :=
      congrArg (free (wordSign w) s0) hlenV_eq
    change free (wordSign w) s0 V.length ≤ _
    rw [hsplit_len]
    unfold free
    rw [cN_add_split, cN_add_split, cN_add_split, cN_add_split]
    -- 1. prefix: ≤ q + p
    have h1 : free (wordSign w) s0 (asRep q ++ saRep p).length ≤ q + p := by
      have hle := free_shift_le_of_slice (wordSign w) s0 (asRep q ++ saRep p) (fun i hi => by
        rw [hgetV i (by rw [hlenV, hlenPre] at *; omega)]
        dsimp only [V]
        rw [List.append_assoc, List.getElem!_eq_getElem?_getD, List.getElem?_append_left hi,
          ← List.getElem!_eq_getElem?_getD])
      have hle2 := free_le_additions (wordSign (asRep q ++ saRep p)) 0 (asRep q ++ saRep p).length
      have hhalf := additions_eq_half_len_of_mass_zero (asRep q ++ saRep p) hmPre
      omega
    -- 2. B: ≤ free (wordSign B) 0 B.length
    have h2 : free (wordSign w) (s0 + (asRep q ++ saRep p).length) B.length ≤
        free (wordSign B) 0 B.length := by
      refine free_shift_le_of_slice (wordSign w) (s0 + (asRep q ++ saRep p).length) B (fun i hi => ?_)
      rw [Nat.add_assoc, hgetV _ (by rw [hlenV, hlenPre]; omega)]
      dsimp only [V]
      rw [List.getElem!_eq_getElem?_getD,
        List.getElem?_append_left (by simp only [List.length_append, hlenPre]; omega),
        List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
        ← List.getElem!_eq_getElem?_getD]
    -- 3. A^h: ≤ h
    have h3 : free (wordSign w) (s0 + ((asRep q ++ saRep p).length + B.length)) h ≤ h := by
      have hle := free_le_additions (wordSign w) (s0 + ((asRep q ++ saRep p).length + B.length)) h
      have hle2 : additions (wordSign w) (s0 + ((asRep q ++ saRep p).length + B.length)) h ≤ h := by
        unfold additions
        have hc := cN_walk (wordSign w) (s0 + ((asRep q ++ saRep p).length + B.length)) h
        omega
      omega
    -- 4. asRep a: ≤ 1 by `free_conveyor_arch_le_one`!
    have h4 : free (wordSign w) (s0 + ((asRep q ++ saRep p).length + B.length) + h) (2 * a) ≤ 1 := by
      have hconv := free_conveyor_arch_le_one h a R m ((asRep q ++ saRep p) ++ B)
        hh ha hmPB hmR hdV
      have heq_idx : s0 + ((asRep q ++ saRep p).length + B.length) + h =
          (v0Word h a).length + m * V.length + ((asRep q ++ saRep p) ++ B).length + h := by
        dsimp only [s0]; simp only [List.length_append, Nat.add_assoc]
      rw [heq_idx]
      exact hconv
    -- 5. S^h: = 0 (all steps are `false`!)
    have h5 : free (wordSign w) (s0 + ((asRep q ++ saRep p).length + B.length) + h + 2 * a) h = 0 := by
      have hle := cN_le_of_imp
        (fun x => wordSign w x = true ∧ ¬ EndN (wordSign w) 0 x)
        (fun _ => False)
        (s0 + ((asRep q ++ saRep p).length + B.length) + h + 2 * a) h (fun i hi hpi => by
          have hgi : wordSign w (s0 + ((asRep q ++ saRep p).length + B.length) + h + 2 * a + i) = false := by
            have hidx : s0 + ((asRep q ++ saRep p).length + B.length) + h + 2 * a + i =
                s0 + (((asRep q ++ saRep p) ++ B).length + (h + 2 * a + i)) := by
              simp only [List.length_append]; omega
            rw [hidx, hgetV _ (by simp only [List.length_append, hlenV, hlenPre]; omega)]
            dsimp only [V]
            rw [List.getElem!_eq_getElem?_getD,
              List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
            unfold archWord elevateWord
            rw [List.getElem?_append_right (by simp only [List.length_append, List.length_replicate, asRep_length]; omega),
              List.length_append, List.length_replicate, asRep_length, Nat.add_sub_cancel_left,
              List.getElem?_replicate]
            simp [hi]
          rw [hgi] at hpi; cases hpi.1)
      have hfalse : ∀ k n, cN (fun _ => False) n k = 0 := by
        intro k n; induction k with
        | zero => rfl
        | succ k ih => rw [cN_succ_neg _ n k (fun x => x), ih]
      unfold free; rw [hfalse] at hle; omega
    unfold free at h1 h2 h3 h4 h5
    dsimp only [s0] at h1 h2 h3 h4 h5 ⊢
    simp only [Nat.add_assoc] at h1 h2 h3 h4 h5 ⊢
    omega
  -- Sum over `0 ≤ m < R`
  have hsum : ∀ n, n ≤ R →
      free (wordSign w) (v0Word h a).length (n * V.length) ≤
        n * (q + p + free (wordSign B) 0 B.length + h + 1) := by
    intro n
    induction n with
    | zero => intro _; simp [free, cN]
    | succ n ih =>
      intro hn
      have hmul : (n + 1) * V.length = n * V.length + V.length := by rw [Nat.add_mul, Nat.one_mul]
      unfold free at ih ⊢
      rw [hmul, cN_add_split]
      have h1 := ih (by omega)
      have h2 := hCopy_le n (by omega)
      unfold free at h2
      rw [Nat.add_mul, Nat.one_mul]
      omega
  unfold free at hV0_le hsum ⊢
  rw [hlenW, cN_add_split, Nat.zero_add]
  have hR := hsum R (Nat.le_refl R)
  omega

/-! ## Inductive stage invariant `StageInv` and one-step `Δ = 2` lift (`E-805`) -/

/-- Exact 6-clause inductive corridor invariant for stage `k ≥ 1` (`h = 2k + 2`,
band `[-1, 2k + 3]`) in the `Δ = 2` coherent greedy cascade (`E-805`). -/
structure StageInv (k : Nat) (B : List Bool) (bank : Nat) : Prop where
  hk : 1 ≤ k
  hbank_large : 20 * (2 * k + 6) * (2 * k + 6) ≤ bank
  hlen_ge : 30 * bank ≤ B.length
  hmass : mass B = 0
  hfresh : FreshWord B
  hband : ∀ i, i ≤ B.length → -1 ≤ wordHeight B i ∧ wordHeight B i ≤ (2 * k + 2 : Int) + 1
  hdphi_hm1 : -(((2 * k + 2 : Int)) * ((2 * k + 2 : Int))) ≤ dphiW B ((2 * k + 2 : Int) - 1) ∧
    dphiW B ((2 * k + 2 : Int) - 1) ≤ (bank : Int) + 2
  hkey_hp1 : ∀ ϕ, KeyAt B ((2 * k + 2 : Int) + 1) ϕ → ϕ ≤ 0
  hkey_h : ∀ ϕ, KeyAt B (2 * k + 2 : Int) ϕ → ϕ ≤ 0
  hsland_h : ∀ ϕ, SLandAt B (2 * k + 2 : Int) ϕ →
    dphiW B (2 * k + 2 : Int) - (bank : Int) ≤ ϕ ∧ ϕ ≤ 0
  hkey_hm1 : ∀ ϕ, KeyAt B ((2 * k + 2 : Int) - 1) ϕ → ϕ ≤ (bank : Int) + 2
  hsland_hm1 : ∀ ϕ, SLandAt B ((2 * k + 2 : Int) - 1) ϕ →
    -((2 * k + 2 : Int) * (2 * k + 2 : Int)) ≤ ϕ ∧ ϕ ≤ (bank : Int) + 2
  hsland_hm2 : ∀ ϕ, SLandAt B ((2 * k + 2 : Int) - 2) ϕ →
    -((2 * k + 2 : Int) * (2 * k + 2 : Int)) ≤ ϕ ∧
    (ϕ ≤ (bank : Int) ∨ 2 * (bank : Int) ≤ ϕ)
  hsland_low : ∀ r ϕ, r ≤ (2 * k + 2 : Int) - 3 → SLandAt B r ϕ → 2 * (bank : Int) ≤ ϕ
  hkey_le_dphi : ∀ r ϕ, r ≤ (2 * k + 2 : Int) - 2 → KeyAt B r ϕ →
    ϕ ≤ dphiW B r + (2 * k + 2 : Int) * (2 * k + 2 : Int)

/-! ## Exact KeyAt / SLandAt bounds for `prefix`, `archWord`, and `v0Word` -/

private theorem wordHeight_asRep_band (m k : Nat) (hk : k ≤ (asRep m).length) :
    0 ≤ wordHeight (asRep m) k ∧ wordHeight (asRep m) k ≤ 1 := by
  induction m generalizing k with
  | zero => simp [asRep] at hk; subst hk; simp [wordHeight, mass]
  | succ m ih =>
    unfold asRep at hk ⊢
    by_cases hk2 : k ≤ 2
    · have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases this with rfl | rfl | rfl <;> simp [wordHeight, mass, sign]
    · have htake : ([true, false] ++ asRep m).take k = [true, false] ++ (asRep m).take (k - 2) := by
        rw [List.take_append, List.take_of_length_le (by simp; omega)]; rfl
      unfold wordHeight; rw [htake, mass_append]
      have hm1 : mass [true, false] = 0 := rfl
      rw [hm1, Int.zero_add]
      exact ih (k - 2) (by rw [List.length_append] at hk; simp only [List.length_cons, List.length_nil] at hk; omega)

private theorem wordHeight_saRep_band (m k : Nat) (hk : k ≤ (saRep m).length) :
    -1 ≤ wordHeight (saRep m) k ∧ wordHeight (saRep m) k ≤ 0 := by
  induction m generalizing k with
  | zero => simp [saRep] at hk; subst hk; simp [wordHeight, mass]
  | succ m ih =>
    unfold saRep at hk ⊢
    by_cases hk2 : k ≤ 2
    · have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases this with rfl | rfl | rfl <;> simp [wordHeight, mass, sign]
    · have htake : ([false, true] ++ saRep m).take k = [false, true] ++ (saRep m).take (k - 2) := by
        rw [List.take_append, List.take_of_length_le (by simp; omega)]; rfl
      unfold wordHeight; rw [htake, mass_append]
      have hm1 : mass [false, true] = 0 := rfl
      rw [hm1, Int.zero_add]
      exact ih (k - 2) (by rw [List.length_append] at hk; simp only [List.length_cons, List.length_nil] at hk; omega)

private theorem prefix_bounds (q p : Nat) :
    mass (asRep q ++ saRep p) = 0 ∧
    (∀ r, dphiW (asRep q ++ saRep p) r = (q : Int) * (1 - 2 * r) + (p : Int) * (-1 - 2 * r)) ∧
    (∀ i, i ≤ (asRep q ++ saRep p).length → -1 ≤ wordHeight (asRep q ++ saRep p) i ∧ wordHeight (asRep q ++ saRep p) i ≤ 1) ∧
    (∀ r ϕ, KeyAt (asRep q ++ saRep p) r ϕ →
      (r = -2 ∧ 5 * (q : Int) ≤ ϕ ∧ ϕ < 5 * (q : Int) + 3 * (p : Int)) ∨
      (r = -1 ∧ 0 ≤ ϕ ∧ ϕ ≤ 3 * (q : Int) + (p : Int)) ∨
      (r = 0 ∧ -(p : Int) ≤ ϕ ∧ ϕ ≤ (q : Int)) ∨
      (r = 1 ∧ -((q : Int)) < ϕ ∧ ϕ ≤ 0)) ∧
    (∀ r ϕ, SLandAt (asRep q ++ saRep p) r ϕ →
      (r = 0 ∧ 1 ≤ ϕ ∧ ϕ ≤ (q : Int)) ∨
      (r = -1 ∧ 3 * (q : Int) ≤ ϕ ∧ ϕ ≤ 3 * (q : Int) + (p : Int))) := by
  have has := asRep_keyAt_sLandAt_fresh q
  have hsa := saRep_keyAt_sLandAt_fresh p
  refine ⟨by rw [mass_append, mass_asRep, mass_saRep]; rfl, ?_, ?_, ?_, ?_⟩
  · intro r; rw [dphiW_append (mass_asRep q), dphiW_asRep, dphiW_saRep]; grind
  · intro i hi
    by_cases hi1 : i ≤ (asRep q).length
    · rw [wordHeight_append_left i hi1]; have := wordHeight_asRep_band q i hi1; omega
    · let j := i - (asRep q).length
      have hij : i = (asRep q).length + j := by omega
      rw [hij, wordHeight_append_right (mass_asRep q) j (by rw [List.length_append] at hi; omega)]
      have := wordHeight_saRep_band p j (by rw [List.length_append] at hi; omega); omega
  · intro r ϕ hK
    rcases (keyAt_append (mass_asRep q) r ϕ).mp hK with h1 | h2
    · rcases has.2.1 r ϕ h1 with h | h | h
      · right; left; omega
      · right; right; left; omega
      · right; right; right; omega
    · have h := hsa.2.1 r (ϕ - dphiW (asRep q) r) h2
      rw [dphiW_asRep] at h
      rcases h with ⟨rfl, hlo, hhi⟩ | ⟨rfl, hlo, hhi⟩ | ⟨rfl, hlo, hhi⟩
      · left; omega
      · right; left; omega
      · right; right; left; omega
  · intro r ϕ hS
    rcases (sLandAt_append (mass_asRep q) r ϕ).mp hS with h1 | h2
    · left; exact has.2.2 r ϕ h1
    · right
      have h := hsa.2.2 r (ϕ - dphiW (asRep q) r) h2
      rw [dphiW_asRep] at h
      rcases h with ⟨rfl, hlo, hhi⟩
      omega

private theorem archWord_bounds (h a : Nat) (_hh : 4 ≤ h) (ha : h * h ≤ a) :
    (∀ r ϕ, SLandAt (archWord h a) r ϕ →
      (r = (h : Int) ∧ 2 * ϕ ≥ 2 - (h : Int) * ((h : Int) - 1) ∧
        2 * ϕ ≤ 2 * (a : Int) - (h : Int) * ((h : Int) - 1)) ∨
      (0 ≤ r ∧ r < (h : Int) ∧ 2 * ϕ = 2 * dphiW (archWord h a) r + r * (r + 1))) ∧
    (∀ r ϕ, KeyAt (archWord h a) r ϕ →
      (r = (h : Int) + 1 ∧ 2 * ϕ ≤ -(h : Int) * ((h : Int) + 1)) ∨
      (r = (h : Int) ∧ 2 * ϕ ≥ -(h : Int) * ((h : Int) - 1) ∧
        2 * ϕ ≤ 2 * (a : Int) - (h : Int) * ((h : Int) - 1)) ∨
      (r = (h : Int) - 1 ∧
        2 * ϕ ≤ 2 * dphiW (archWord h a) ((h : Int) - 1) + ((h : Int) - 1) * (h : Int)) ∨
      (0 ≤ r ∧ r ≤ (h : Int) - 2 ∧
        (2 * ϕ ≤ 2 ∨ 2 * ϕ = 2 * dphiW (archWord h a) r + r * (r + 1))) ∨
      (r = -1 ∧ 2 * ϕ = 0)) := by
  have has := asRep_keyAt_sLandAt_fresh a
  have hda_hm1 : dphiW (archWord h a) ((h : Int) - 1) = 3 * (a : Int) + (h : Int) * (2 - (h : Int)) := by
    rw [dphiW_archWord]; grind
  have hha : (h : Int) * (h : Int) ≤ (a : Int) := by exact_mod_cast ha
  constructor
  · intro r ϕ hS
    rcases elevateWord_sLandAt h (mass_asRep a) r ϕ hS with h1 | h2
    · have hSr := has.2.2 _ _ h1
      have hev := two_dvd_mul_sub_two h r
      have hmul : 2 * (((h : Int) * ((h : Int) + 1 - 2 * r)) / 2) =
          (h : Int) * ((h : Int) + 1 - 2 * r) := by rcases hev with ⟨q, hq⟩; omega
      left
      have hreq : r = (h : Int) := by omega
      rw [hreq] at hmul ⊢; grind
    · right; exact h2
  · intro r ϕ hK
    rcases elevateWord_keyAt h (mass_asRep a) r ϕ hK with
      ⟨hr0, hrh, h1⟩ | ⟨hr0, hrh, h1⟩ | h2 | ⟨hr0, hrh, h3⟩
    · by_cases hreq : r = (h : Int)
      · right; left; rw [hreq] at h1 ⊢; grind
      · by_cases hreq1 : r = (h : Int) - 1
        · right; right; left; rw [hreq1] at h1 ⊢
          refine ⟨rfl, ?_⟩; rw [hda_hm1]; grind
        · right; right; right; left
          have hrr : 0 ≤ r * (r - 1) := by
            by_cases hr0' : r = 0
            · rw [hr0']; simp
            · exact Int.mul_nonneg (by omega) (by omega)
          refine ⟨hr0, by omega, Or.inl (by omega)⟩
    · by_cases hrm1 : r = -1
      · right; right; right; right; rw [hrm1] at h1 ⊢; omega
      · right; right; right; left
        have hrr : -2 ≤ (r + 1) * (r - 2) := by
          by_cases hr0' : r = 0
          · rw [hr0']; decide
          · by_cases hr1' : r = 1
            · rw [hr1']; decide
            · exact Int.le_trans (by decide : (-2 : Int) ≤ 0) (Int.mul_nonneg (by omega) (by omega))
        refine ⟨by omega, by omega, Or.inl (by omega)⟩
    · have hev := two_dvd_mul_sub_two h r
      have hmul : 2 * (((h : Int) * ((h : Int) + 1 - 2 * r)) / 2) =
          (h : Int) * ((h : Int) + 1 - 2 * r) := by rcases hev with ⟨q, hq⟩; omega
      rcases has.2.1 _ _ h2 with ⟨hr, hlo, hhi⟩ | ⟨hr, hlo, hhi⟩ | ⟨hr, hlo, hhi⟩
      · right; right; left
        have hreq : r = (h : Int) - 1 := by omega
        rw [hreq] at hmul ⊢
        refine ⟨rfl, ?_⟩
        rw [hda_hm1]; grind
      · right; left
        have hreq : r = (h : Int) := by omega
        rw [hreq] at hmul ⊢; grind
      · left
        have hreq : r = (h : Int) + 1 := by omega
        rw [hreq] at hmul ⊢; grind
    · by_cases hreq1 : r = (h : Int) - 1
      · right; right; left; rw [hreq1] at h3 ⊢; exact ⟨rfl, by unfold archWord; grind⟩
      · right; right; right; left; exact ⟨hr0, by omega, Or.inr h3⟩

private theorem v0Word_bounds (h a : Nat) (hh : 4 ≤ h) (ha : h * h ≤ a) :
    let b := 3 * a - 1
    (∀ i, i ≤ (v0Word h a).length → 0 ≤ wordHeight (v0Word h a) i ∧ wordHeight (v0Word h a) i ≤ (h : Int) + 1) ∧
    (∀ r ϕ, SLandAt (v0Word h a) r ϕ →
      (r = (h : Int) ∧ 2 * ϕ ≤ 0 ∧ 2 * ϕ ≥ 2 * dphiW (v0Word h a) (h : Int) - 2 * (b : Int)) ∨
      (r = (h : Int) - 1 ∧ 2 * ϕ = -(((h : Int) - 1) * ((h : Int) - 2)) + 4) ∨
      (r = (h : Int) - 2 ∧
        ((-(h : Int) * (h : Int) ≤ ϕ ∧ ϕ ≤ (b : Int)) ∨
         2 * ϕ = 2 * dphiW (v0Word h a) ((h : Int) - 2) + ((h : Int) - 2) * ((h : Int) - 1))) ∨
      (0 ≤ r ∧ r ≤ (h : Int) - 3 ∧ 2 * ϕ = 2 * dphiW (v0Word h a) r + r * (r + 1))) ∧
    (∀ r ϕ, KeyAt (v0Word h a) r ϕ →
      (r = (h : Int) + 1 ∧ ϕ ≤ 0) ∨
      (r = (h : Int) ∧ ϕ ≤ 0 ∧
        2 * ϕ ≥ -6 * (b : Int) - (h : Int) * (h : Int)) ∨
      (r = (h : Int) - 1 ∧
        -((b : Int) + (h : Int) * (h : Int)) ≤ ϕ ∧
        2 * ϕ ≤ -(((h : Int) - 1) * ((h : Int) - 2)) + 4) ∨
      (r = (h : Int) - 2 ∧
        (ϕ ≤ (b : Int) ∨
         2 * ϕ = 2 * dphiW (v0Word h a) ((h : Int) - 2) + ((h : Int) - 2) * ((h : Int) - 1))) ∨
      (r = (h : Int) - 3 ∧
        (ϕ ≤ 3 * (b : Int) + (h : Int) ∨
         2 * ϕ = 2 * dphiW (v0Word h a) ((h : Int) - 3) + ((h : Int) - 3) * ((h : Int) - 2))) ∨
      (0 ≤ r ∧ r ≤ (h : Int) - 4 ∧
        (ϕ ≤ 1 ∨ 2 * ϕ = 2 * dphiW (v0Word h a) r + r * (r + 1))) ∨
      (r = -1 ∧ ϕ = 0)) := by
  intro b
  have ha1 : 1 ≤ a := by have : 16 ≤ h * h := Nat.mul_le_mul hh hh; omega
  have hha : (h : Int) * (h : Int) ≤ (a : Int) := by exact_mod_cast ha
  have hh1 : ((h - 1 : Nat) : Int) = (h : Int) - 1 := by omega
  have hb_eq : (b : Int) = 3 * (a : Int) - 1 := by dsimp only [b]; omega
  refine ⟨?_, ?_, ?_⟩
  · -- Height band `[0, h + 1]`
    intro i hi
    unfold v0Word at hi ⊢
    rw [elevateWord_length] at hi
    by_cases h1 : i ≤ h - 1
    · rw [(wordHeight_elevateWord (h - 1) (v0Inner_mass a)).1 i h1]; omega
    · by_cases h2 : i ≤ (h - 1) + (saRep b ++ elevateWord 1 (asRep a)).length
      · let j := i - (h - 1)
        have hij : i = (h - 1) + j := by omega
        rw [hij, (wordHeight_elevateWord (h - 1) (v0Inner_mass a)).2.1 j (by dsimp only [b] at h2; omega)]
        have h_in : -1 ≤ wordHeight (saRep (3 * a - 1) ++ elevateWord 1 (asRep a)) j ∧
            wordHeight (saRep (3 * a - 1) ++ elevateWord 1 (asRep a)) j ≤ 2 := by
          by_cases hj1 : j ≤ (saRep (3 * a - 1)).length
          · rw [wordHeight_append_left j hj1]
            have := wordHeight_saRep_band (3 * a - 1) j hj1; omega
          · let j' := j - (saRep (3 * a - 1)).length
            have hjj : j = (saRep (3 * a - 1)).length + j' := by omega
            rw [hjj, wordHeight_append_right (mass_saRep (3 * a - 1)) j'
              (by dsimp only [b] at h2; rw [List.length_append] at h2; omega)]
            have harch := wordHeight_archWord 1 a j'
              (by rw [archWord_length]; dsimp only [b] at h2; rw [List.length_append, elevateWord_length, asRep_length] at h2; omega)
            unfold archWord at harch; omega
        omega
      · let k := i - ((h - 1) + (saRep (3 * a - 1) ++ elevateWord 1 (asRep a)).length)
        have hik : i = (h - 1) + (saRep (3 * a - 1) ++ elevateWord 1 (asRep a)).length + k := by
          dsimp only [b] at h2; omega
        rw [hik, (wordHeight_elevateWord (h - 1) (v0Inner_mass a)).2.2 k (by dsimp only [b] at h2; omega)]
        omega
  · -- SLandAt of v0Word
    intro r ϕ hS
    have hev := two_dvd_mul_sub_two (h - 1) r
    have hmul : 2 * ((((h - 1 : Nat) : Int) * (((h - 1 : Nat) : Int) + 1 - 2 * r)) / 2) =
        ((h - 1 : Nat) : Int) * (((h - 1 : Nat) : Int) + 1 - 2 * r) := by rcases hev with ⟨q, hq⟩; omega
    rcases elevateWord_sLandAt (h - 1) (v0Inner_mass a) r ϕ hS with h1 | ⟨hr0, hrh, h2⟩
    · rcases v0Inner_sLandAt a ha1 _ _ h1 with ⟨hr, hlo, hhi⟩ | ⟨hr, hphi⟩ | ⟨hr, hlo, hhi⟩
      · right; right; left
        have hreq : r = (h : Int) - 2 := by omega
        rw [hreq] at hmul hlo hhi ⊢
        rw [hh1] at hmul hlo hhi
        have h4 : ((h : Int) - 1) * (4 - (h : Int)) ≤ 0 :=
          Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
        have h4lo : -2 * ((h : Int) * (h : Int)) ≤ ((h : Int) - 1) * (4 - (h : Int)) := by
          have : ((h : Int) - 1) * ((h : Int) - 4) ≤ (h : Int) * (h : Int) := by
            have h1 := Int.mul_le_mul_of_nonneg_left (by omega : (h : Int) - 4 ≤ (h : Int)) (by omega : (0 : Int) ≤ (h : Int) - 1)
            have h2 := Int.mul_le_mul_of_nonneg_right (by omega : (h : Int) - 1 ≤ (h : Int)) (by omega : (0 : Int) ≤ (h : Int))
            omega
          grind
        refine ⟨rfl, Or.inl ?_⟩
        grind
      · right; left
        have hreq : r = (h : Int) - 1 := by omega
        rw [hreq] at hmul hphi ⊢
        rw [hh1] at hmul hphi
        refine ⟨rfl, ?_⟩
        grind
      · left
        have hreq : r = (h : Int) := by omega
        have hdv := dphiW_v0Word h a (by omega) ha1 (h : Int)
        rw [hreq] at hmul hlo hhi ⊢
        rw [hh1] at hmul hlo hhi
        have hneg : ((h : Int) - 1) * (-((h : Int))) ≤ 0 :=
          Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
        refine ⟨rfl, by grind, by grind⟩
    · by_cases hreq2 : r = (h : Int) - 2
      · right; right; left; rw [hreq2] at h2 ⊢
        exact ⟨rfl, Or.inr (by unfold v0Word; grind)⟩
      · right; right; right; exact ⟨hr0, by omega, h2⟩
  · -- KeyAt of v0Word
    intro r ϕ hK
    have hev := two_dvd_mul_sub_two (h - 1) r
    have hmul : 2 * ((((h - 1 : Nat) : Int) * (((h - 1 : Nat) : Int) + 1 - 2 * r)) / 2) =
        ((h - 1 : Nat) : Int) * (((h - 1 : Nat) : Int) + 1 - 2 * r) := by rcases hev with ⟨q, hq⟩; omega
    rcases elevateWord_keyAt (h - 1) (v0Inner_mass a) r ϕ hK with
      ⟨hr0, hrh, h1⟩ | ⟨hr0, hrh, h1⟩ | h2 | ⟨hr0, hrh, h3⟩
    · by_cases hreq1 : r = (h : Int) - 1
      · right; right; left; rw [hreq1] at h1 ⊢; refine ⟨rfl, by grind, by grind⟩
      · by_cases hreq2 : r = (h : Int) - 2
        · right; right; right; left; rw [hreq2] at h1 ⊢
          have hrr : 0 ≤ ((h : Int) - 2) * ((h : Int) - 3) := Int.mul_nonneg (by omega) (by omega)
          refine ⟨rfl, Or.inl (by dsimp only [b]; grind)⟩
        · by_cases hreq3 : r = (h : Int) - 3
          · right; right; right; right; left; rw [hreq3] at h1 ⊢
            have hrr : 0 ≤ ((h : Int) - 3) * ((h : Int) - 4) := Int.mul_nonneg (by omega) (by omega)
            refine ⟨rfl, Or.inl (by dsimp only [b]; grind)⟩
          · right; right; right; right; right; left
            have hrr : 0 ≤ r * (r - 1) := by
              by_cases hr0' : r = 0
              · rw [hr0']; simp
              · exact Int.mul_nonneg (by omega) (by omega)
            exact ⟨hr0, by omega, Or.inl (by omega)⟩
    · by_cases hrm1 : r = -1
      · right; right; right; right; right; right; rw [hrm1] at h1 ⊢; omega
      · by_cases hreq3 : r = (h : Int) - 3
        · right; right; right; right; left; rw [hreq3] at h1 ⊢
          have hrr : -2 ≤ ((h : Int) - 2) * ((h : Int) - 5) := by
            by_cases hh4 : h = 4
            · subst hh4; decide
            · exact Int.le_trans (by decide : (-2 : Int) ≤ 0) (Int.mul_nonneg (by omega) (by omega))
          refine ⟨rfl, Or.inl (by dsimp only [b]; grind)⟩
        · right; right; right; right; right; left
          have hrr : -2 ≤ (r + 1) * (r - 2) := by
            by_cases hr0' : r = 0
            · rw [hr0']; decide
            · by_cases hr1' : r = 1
              · rw [hr1']; decide
              · exact Int.le_trans (by decide : (-2 : Int) ≤ 0) (Int.mul_nonneg (by omega) (by omega))
          exact ⟨by omega, by omega, Or.inl (by omega)⟩
    · rcases v0Inner_keyAt a ha1 _ _ h2 with
        ⟨hr, hlo, hhi⟩ | ⟨hr, hlo, hhi⟩ | ⟨hr, hlo, hhi⟩ | ⟨hr, hlo, hhi⟩ | ⟨hr, hhi⟩
      · right; right; right; right; left
        have hreq : r = (h : Int) - 3 := by omega
        rw [hreq] at hmul hlo hhi ⊢; rw [hh1] at hmul hlo hhi
        have h4 : ((h : Int) - 1) * (6 - (h : Int)) ≤ 2 * (h : Int) := by
          by_cases hh4 : h = 4
          · subst hh4; decide
          · by_cases hh5 : h = 5
            · subst hh5; decide
            · have : ((h : Int) - 1) * (6 - (h : Int)) ≤ 0 :=
                Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
              omega
        refine ⟨rfl, Or.inl (by grind)⟩
      · right; right; right; left
        have hreq : r = (h : Int) - 2 := by omega
        rw [hreq] at hmul hlo hhi ⊢; rw [hh1] at hmul hlo hhi
        have h4 : ((h : Int) - 1) * (4 - (h : Int)) ≤ 0 :=
          Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
        refine ⟨rfl, Or.inl (by grind)⟩
      · right; right; left
        have hreq : r = (h : Int) - 1 := by omega
        rw [hreq] at hmul hlo hhi ⊢; rw [hh1] at hmul hlo hhi
        refine ⟨rfl, by grind, by grind⟩
      · right; left
        have hreq : r = (h : Int) := by omega
        rw [hreq] at hmul hlo hhi ⊢; rw [hh1] at hmul hlo hhi
        have hneg : ((h : Int) - 1) * (-((h : Int))) ≤ 0 :=
          Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
        refine ⟨rfl, by grind, by grind⟩
      · left
        have hreq : r = (h : Int) + 1 := by omega
        rw [hreq] at hmul hhi ⊢; rw [hh1] at hmul hhi
        have hneg : ((h : Int) - 1) * (-((h : Int)) - 2) ≤ 0 :=
          Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
        refine ⟨rfl, by grind⟩
    · by_cases hreq2 : r = (h : Int) - 2
      · right; right; right; left; rw [hreq2] at h3 ⊢
        exact ⟨rfl, Or.inr (by unfold v0Word; grind)⟩
      · by_cases hreq3 : r = (h : Int) - 3
        · right; right; right; right; left; rw [hreq3] at h3 ⊢
          exact ⟨rfl, Or.inr (by unfold v0Word; grind)⟩
        · right; right; right; right; right; left; exact ⟨hr0, by omega, Or.inr h3⟩

private theorem exists_mod3_qpa (k p_lo : Nat) (d : Int) :
    ∃ q dp : Nat, q ≤ 2 ∧ dp ≤ 2 ∧
      (k % 3 ≠ 1 → dp = 0) ∧
      (3 : Int) ∣ (1 - d + ((2 * k + 4 : Nat) : Int) * (((2 * k + 4 : Nat) : Int) - 2) +
        (q : Int) * (2 * ((2 * k + 4 : Nat) : Int) - 3) +
        ((p_lo + dp : Nat) : Int) * (2 * ((2 * k + 4 : Nat) : Int) - 1)) := by
  let h : Int := (2 * k + 4 : Nat)
  let base : Int := 1 - d + h * (h - 2) + (p_lo : Int) * (2 * h - 1)
  have hdiv : ∀ x : Int, x % 3 = 0 → (3 : Int) ∣ x := fun x hx => ⟨x / 3, by omega⟩
  have hre : ∀ q dp : Nat,
      1 - d + ((2 * k + 4 : Nat) : Int) * (((2 * k + 4 : Nat) : Int) - 2) +
        (q : Int) * (2 * ((2 * k + 4 : Nat) : Int) - 3) +
        ((p_lo + dp : Nat) : Int) * (2 * ((2 * k + 4 : Nat) : Int) - 1) =
      base + (q : Int) * (2 * h - 3) + (dp : Int) * (2 * h - 1) := by
    intro q dp; dsimp only [base, h]; push_cast; grind
  by_cases hk : k % 3 = 1
  · have hm : (base % 3 = 0) ∨ (base % 3 = 1) ∨ (base % 3 = 2) := by omega
    have hcoeff : (2 * h - 1) % 3 = 2 := by dsimp only [h]; omega
    rcases hm with h0 | h1 | h2
    · exact ⟨0, 0, by omega, by omega, fun hne => (hne hk).elim, by rw [hre]; exact hdiv _ (by omega)⟩
    · exact ⟨0, 1, by omega, by omega, fun hne => (hne hk).elim, by rw [hre]; exact hdiv _ (by omega)⟩
    · exact ⟨0, 2, by omega, by omega, fun hne => (hne hk).elim, by rw [hre]; exact hdiv _ (by omega)⟩
  · have hm : (base % 3 = 0) ∨ (base % 3 = 1) ∨ (base % 3 = 2) := by omega
    have hcoeff : (2 * h - 3) % 3 = 1 ∨ (2 * h - 3) % 3 = 2 := by dsimp only [h]; omega
    rcases hcoeff with hc1 | hc2
    · rcases hm with h0 | h1 | h2
      · exact ⟨0, 0, by omega, by omega, fun _ => rfl, by rw [hre]; exact hdiv _ (by omega)⟩
      · exact ⟨2, 0, by omega, by omega, fun _ => rfl, by rw [hre]; exact hdiv _ (by omega)⟩
      · exact ⟨1, 0, by omega, by omega, fun _ => rfl, by rw [hre]; exact hdiv _ (by omega)⟩
    · rcases hm with h0 | h1 | h2
      · exact ⟨0, 0, by omega, by omega, fun _ => rfl, by rw [hre]; exact hdiv _ (by omega)⟩
      · exact ⟨1, 0, by omega, by omega, fun _ => rfl, by rw [hre]; exact hdiv _ (by omega)⟩
      · exact ⟨2, 0, by omega, by omega, fun _ => rfl, by rw [hre]; exact hdiv _ (by omega)⟩

/-- Helper: `KeyAt (repeatWord R V) r ϕ` comes from some copy `0 ≤ m < R` of `V`. -/
private theorem keyAt_repeatWord_exists {v : List Bool} (hm : mass v = 0) (r ϕ : Int) :
    ∀ R, KeyAt (repeatWord R v) r ϕ →
      (R = 0 ∧ r = 0 ∧ ϕ = 0) ∨
      ∃ m, m < R ∧ KeyAt v r (ϕ - (m : Int) * dphiW v r)
  | 0, hK => by
    left
    rcases hK with ⟨i, hi, hH, hP⟩ | ⟨i, hi, _⟩
    · simp [repeatWord] at hi; subst hi
      simp [repeatWord, wordHeight, wordPot, mass, areaW] at hH hP
      exact ⟨rfl, hH.symm, hP.symm⟩
    · simp [repeatWord] at hi
  | R + 1, hK => by
    unfold repeatWord at hK
    rcases (keyAt_append hm r ϕ).mp hK with h1 | h2
    · right; refine ⟨0, by omega, by simpa using h1⟩
    · rcases keyAt_repeatWord_exists hm r (ϕ - dphiW v r) R h2 with ⟨hR0, hr0, hphi⟩ | ⟨m, hmR, hKm⟩
      · right
        subst hR0
        refine ⟨0, by omega, Or.inl ⟨v.length, Nat.le_refl _, ?_, ?_⟩⟩
        · unfold wordHeight; rw [List.take_length, hm]; omega
        · unfold wordPot dphiW at *; rw [List.take_length]; omega
      · right; refine ⟨m + 1, by omega, ?_⟩
        rw [show ϕ - ((m + 1 : Nat) : Int) * dphiW v r = ϕ - dphiW v r - (m : Int) * dphiW v r by push_cast; grind]
        exact hKm

/-- Helper: `SLandAt (repeatWord R V) r ϕ` comes from some copy `0 ≤ m < R` of `V`. -/
private theorem sLandAt_repeatWord {v : List Bool} (hm : mass v = 0) (r ϕ : Int) :
    ∀ R, SLandAt (repeatWord R v) r ϕ →
      ∃ m, m < R ∧ SLandAt v r (ϕ - (m : Int) * dphiW v r)
  | 0, ⟨i, hi, _⟩ => by simp [repeatWord] at hi
  | R + 1, hS => by
    unfold repeatWord at hS
    rcases (sLandAt_append hm r ϕ).mp hS with h1 | h2
    · exact ⟨0, by omega, by simpa using h1⟩
    · obtain ⟨m, hmR, hSm⟩ := sLandAt_repeatWord hm r (ϕ - dphiW v r) R h2
      refine ⟨m + 1, by omega, ?_⟩
      rw [show ϕ - ((m + 1 : Nat) : Int) * dphiW v r = ϕ - dphiW v r - (m : Int) * dphiW v r by push_cast; grind]
      exact hSm

/-- Helper: height band of `u ++ v` when `mass u = 0`. -/
private theorem wordHeight_append_band {u v : List Bool} (hm : mass u = 0) (lo hi : Int)
    (hu : ∀ i, i ≤ u.length → lo ≤ wordHeight u i ∧ wordHeight u i ≤ hi)
    (hv : ∀ i, i ≤ v.length → lo ≤ wordHeight v i ∧ wordHeight v i ≤ hi) :
    ∀ i, i ≤ (u ++ v).length → lo ≤ wordHeight (u ++ v) i ∧ wordHeight (u ++ v) i ≤ hi := by
  intro i hi_le
  by_cases h1 : i ≤ u.length
  · rw [wordHeight_append_left i h1]; exact hu i h1
  · let j := i - u.length
    have hij : i = u.length + j := by omega
    rw [hij, wordHeight_append_right hm j (by rw [List.length_append] at hi_le; omega)]
    exact hv j (by rw [List.length_append] at hi_le; omega)

private theorem wordHeight_repeatWord_band {v : List Bool} (hm : mass v = 0) (lo hi : Int)
    (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (hv : ∀ i, i ≤ v.length → lo ≤ wordHeight v i ∧ wordHeight v i ≤ hi) :
    ∀ R i, i ≤ (repeatWord R v).length → lo ≤ wordHeight (repeatWord R v) i ∧ wordHeight (repeatWord R v) i ≤ hi
  | 0, i, hi_le => by
    simp [repeatWord] at hi_le; subst hi_le
    simp [repeatWord, wordHeight, mass]; exact ⟨hlo, hhi⟩
  | R + 1, i, hi_le =>
    wordHeight_append_band hm lo hi hv (wordHeight_repeatWord_band hm lo hi hlo hhi hv R) i hi_le

/-- Helper: if `wordHeight w i ≤ hi` for all `i ≤ w.length`, then `KeyAt w r ϕ` implies `r ≤ hi`
and `SLandAt w r ϕ` implies `r < hi` (and similarly lower bound `lo ≤ wordHeight` implies
`SLandAt w r ϕ → lo ≤ r`). -/
private theorem keyAt_sLandAt_height_bounds {w : List Bool} {lo hi : Int}
    (hb : ∀ i, i ≤ w.length → lo ≤ wordHeight w i ∧ wordHeight w i ≤ hi) :
    (∀ r ϕ, KeyAt w r ϕ → lo - 1 ≤ r ∧ r ≤ hi) ∧
    (∀ r ϕ, SLandAt w r ϕ → lo ≤ r ∧ r < hi) := by
  constructor
  · rintro r ϕ (⟨i, hi_le, hH, _⟩ | ⟨i, hi_lt, _, hH, _⟩)
    · have := hb i hi_le; omega
    · have := hb i (by omega); omega
  · rintro r ϕ ⟨i, hi_lt, hS, hH, _⟩
    have h1 := hb (i + 1) (by omega)
    have h2 := hb i (by omega)
    have hstep : wordHeight w (i + 1) = wordHeight w i - 1 := by
      unfold wordHeight
      rw [List.take_succ_eq_append_getElem hi_lt, mass_append]
      have hge : w[i] = false := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi_lt] at hS
        exact hS
      rw [hge]; change mass (w.take i) + (-1 + 0) = mass (w.take i) - 1; omega
    omega

private theorem dphiW_sub_shift (w : List Bool) (r1 r2 : Int) :
    dphiW w r1 = dphiW w r2 + (w.length : Int) * (r2 - r1) := by
  unfold dphiW; grind

private structure StepData (k h h' : Nat) (B : List Bool) (bank q p a : Nat) : Prop where
  hh : h = 2 * k + 2
  hh' : h' = h + 2
  hh_ge : 4 ≤ h
  hbank_lg : 20 * ((h + 4) * (h + 4)) ≤ bank
  hq2 : q ≤ 2
  hp_lo : 3 * bank + 2 * (2 * h - 3) < 2 * (2 * h - 3) * p
  hp_hi : 2 * (2 * h - 3) * p ≤ 3 * bank + 8 * (2 * h - 3)
  hp_small : 3 * p ≤ bank + 24
  h2hp_ub : (2 * h + 3) * p ≤ 4 * bank
  ha_eq : 3 * (a : Int) = 1 - dphiW B ((h' : Int) - 1) + (h' : Int) * ((h' : Int) - 2) +
    (q : Int) * (2 * (h' : Int) - 3) + (p : Int) * (2 * (h' : Int) - 1)
  hbank'_lb : 2 * B.length - bank - 2 ≤ 3 * a - 1
  hbank'_ge_7 : 7 * bank - 2 ≤ 3 * a - 1
  hbank'_lg : 20 * ((h' + 4) * (h' + 4)) ≤ 3 * a - 1
  ha_ge_h'2 : h' * h' ≤ a
  ha_ge_bank : 2 * bank ≤ a
  hbank'_ub : 3 * a - 1 ≤ 2 * B.length + 5 * bank

private theorem exists_stepData_aux (k h h' : Nat) (hh : h = 2 * k + 2) (hh' : h' = h + 2)
    (B : List Bool) (bank : Nat) (hS : StageInv k B bank) :
    ∃ q p a : Nat, StepData k h h' B bank q p a := by
  have hh_ge : 4 ≤ h := by have := hS.hk; omega
  have hbank_lg : 20 * ((h + 4) * (h + 4)) ≤ bank := by
    have h0 := hS.hbank_large
    rw [show 2 * k + 6 = h + 4 by omega, Nat.mul_assoc] at h0; exact h0
  have hcast_h : (h : Int) = 2 * (k : Int) + 2 := by omega
  have hd_B_hm1 : -((h : Int) * (h : Int)) ≤ dphiW B ((h : Int) - 1) ∧
      dphiW B ((h : Int) - 1) ≤ (bank : Int) + 2 := by
    rw [hcast_h]; exact hS.hdphi_hm1
  have hd_B_hp1 : dphiW B ((h' : Int) - 1) = dphiW B ((h : Int) - 1) - 2 * (B.length : Int) := by
    have := dphiW_sub_shift B ((h' : Int) - 1) ((h : Int) - 1)
    have hdiff : ((h : Int) - 1) - ((h' : Int) - 1) = -2 := by omega
    rw [hdiff] at this; grind
  let p_lo : Nat := (3 * bank) / (2 * (2 * h - 3)) + 2
  obtain ⟨q, dp, hq2, hdp2, _, a_int, ha_div⟩ :=
    exists_mod3_qpa k p_lo (dphiW B ((h' : Int) - 1))
  let p : Nat := p_lo + dp
  have hp_lo_b : 3 * bank + 2 * (2 * h - 3) < 2 * (2 * h - 3) * p_lo ∧
      2 * (2 * h - 3) * p_lo ≤ 3 * bank + 4 * (2 * h - 3) := by
    have hden : 0 < 2 * (2 * h - 3) := by omega
    have hdm := Nat.div_add_mod (3 * bank) (2 * (2 * h - 3))
    have hmod := Nat.mod_lt (3 * bank) hden
    have heq : 2 * (2 * h - 3) * p_lo = 2 * (2 * h - 3) * ((3 * bank) / (2 * (2 * h - 3))) + 4 * (2 * h - 3) := by
      dsimp only [p_lo]; rw [Nat.mul_add]; omega
    omega
  have hp_b : 3 * bank + 2 * (2 * h - 3) < 2 * (2 * h - 3) * p ∧
      2 * (2 * h - 3) * p ≤ 3 * bank + 8 * (2 * h - 3) := by
    have heq : 2 * (2 * h - 3) * p = 2 * (2 * h - 3) * p_lo + 2 * (2 * h - 3) * dp := by
      dsimp only [p]; rw [Nat.mul_add]
    have h1 : 2 * (2 * h - 3) * dp ≤ 4 * (2 * h - 3) := by
      have := Nat.mul_le_mul_left (2 * (2 * h - 3)) hdp2; omega
    omega
  have h160h : 160 * (h + 4) ≤ bank := by
    have h1 : 8 * (h + 4) ≤ (h + 4) * (h + 4) := Nat.mul_le_mul_right (h + 4) (by omega)
    have h2 : 20 * (8 * (h + 4)) ≤ 20 * ((h + 4) * (h + 4)) := Nat.mul_le_mul_left 20 h1
    omega
  have hp_small : 3 * p ≤ bank + 24 := by
    have h5 : 10 * p ≤ 2 * (2 * h - 3) * p := Nat.mul_le_mul_right p (by omega)
    omega
  have h2hp_ub : (2 * h + 3) * p ≤ 4 * bank := by
    have h11 : 5 * (2 * h + 3) ≤ 11 * (2 * h - 3) := by omega
    have h1 : 10 * ((2 * h + 3) * p) ≤ 11 * (2 * (2 * h - 3) * p) := by
      have hm := Nat.mul_le_mul_right p h11
      have h2m := Nat.mul_le_mul_left 2 hm
      have hl : 2 * (5 * (2 * h + 3) * p) = 10 * ((2 * h + 3) * p) := by grind
      have hr : 2 * (11 * (2 * h - 3) * p) = 11 * (2 * (2 * h - 3) * p) := by grind
      omega
    have h2 : 11 * (2 * (2 * h - 3) * p) ≤ 11 * (3 * bank + 8 * (2 * h - 3)) :=
      Nat.mul_le_mul_left 11 hp_b.2
    omega
  have hh'_cast : ((2 * k + 4 : Nat) : Int) = (h' : Int) := by omega
  have ha_eq_int : 3 * a_int =
      1 - dphiW B ((h' : Int) - 1) + (h' : Int) * ((h' : Int) - 2) +
        (q : Int) * (2 * (h' : Int) - 3) + (p : Int) * (2 * (h' : Int) - 1) := by
    rw [hh'_cast] at ha_div; dsimp only [p]; grind
  have hlenB_ge : 30 * bank ≤ B.length := hS.hlen_ge
  have hq_nn : (0 : Int) ≤ (q : Int) * (2 * (h' : Int) - 3) := Int.mul_nonneg (by omega) (by omega)
  have hp_nn : (0 : Int) ≤ (p : Int) * (2 * (h' : Int) - 1) := Int.mul_nonneg (by omega) (by omega)
  have hh_nn : (0 : Int) ≤ (h' : Int) * ((h' : Int) - 2) := Int.mul_nonneg (by omega) (by omega)
  have ha_ge_int : 58 * (bank : Int) ≤ 3 * a_int := by omega
  let a : Nat := a_int.toNat
  have ha_cast : (a : Int) = a_int := Int.toNat_of_nonneg (by omega)
  have ha_eq : 3 * (a : Int) =
      1 - dphiW B ((h' : Int) - 1) + (h' : Int) * ((h' : Int) - 2) +
        (q : Int) * (2 * (h' : Int) - 3) + (p : Int) * (2 * (h' : Int) - 1) := by
    rw [ha_cast]; exact ha_eq_int
  have hbank'_lb : 2 * B.length - bank - 2 ≤ 3 * a - 1 := by omega
  have hbank'_lg : 20 * ((h' + 4) * (h' + 4)) ≤ 3 * a - 1 := by
    have h1 : h' + 4 ≤ 2 * (h + 4) := by omega
    have h2 : (h' + 4) * (h' + 4) ≤ 4 * ((h + 4) * (h + 4)) := by
      have hm := Nat.mul_le_mul h1 h1
      have hr : 2 * (h + 4) * (2 * (h + 4)) = 4 * ((h + 4) * (h + 4)) := by grind
      omega
    have h3 : 20 * ((h' + 4) * (h' + 4)) ≤ 4 * (20 * ((h + 4) * (h + 4))) := by
      have hm := Nat.mul_le_mul_left 20 h2; grind
    omega
  have ha_ge_h'2 : h' * h' ≤ a := by
    have h1 : h' * h' ≤ (h' + 4) * (h' + 4) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hbank'_ub : 3 * a - 1 ≤ 2 * B.length + 5 * bank := by
    have hq_ub : (q : Int) * (2 * (h' : Int) - 3) ≤ 4 * (h' : Int) := by
      have := Int.mul_le_mul_of_nonneg_right (by omega : (q : Int) ≤ 2) (by omega : (0 : Int) ≤ 2 * (h' : Int) - 3)
      omega
    have hp_ub : (p : Int) * (2 * (h' : Int) - 1) ≤ 4 * (bank : Int) := by
      have hcast : (((2 * h + 3) * p : Nat) : Int) ≤ ((4 * bank : Nat) : Int) := by exact_mod_cast h2hp_ub
      have heq : 2 * (h' : Int) - 1 = ((2 * h + 3 : Nat) : Int) := by omega
      rw [heq]; push_cast at hcast; grind
    have hh2_le : (h : Int) * (h : Int) + (h' : Int) * (h' : Int) + 4 * (h' : Int) ≤ (bank : Int) := by
      have h1 : h * h ≤ (h + 4) * (h + 4) := Nat.mul_le_mul (by omega) (by omega)
      have h2 : h' * h' ≤ (h + 4) * (h + 4) := Nat.mul_le_mul (by omega) (by omega)
      have htot : h * h + h' * h' + 4 * h' ≤ bank := by omega
      exact_mod_cast htot
    have hh'2_ub : (h' : Int) * ((h' : Int) - 2) ≤ (h' : Int) * (h' : Int) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega
  exact ⟨q, p, a, ⟨hh, hh', hh_ge, hbank_lg, hq2, hp_b.1, hp_b.2, hp_small, h2hp_ub,
    ha_eq, hbank'_lb, by omega, hbank'_lg, ha_ge_h'2, by omega, hbank'_ub⟩⟩

/-- Helper: freshness, height band, `SLandAt`, and `KeyAt` bounds on the cycle word
`V = (AS)^q ++ (SA)^p ++ B ++ archWord h' a` (`E-805`). -/
private theorem step_V_core (k h h' : Nat) (B : List Bool) (bank q p a : Nat)
    (hS : StageInv k B bank) (hD : StepData k h h' B bank q p a) :
    let pref := asRep q ++ saRep p
    let V := pref ++ B ++ archWord h' a
    mass V = 0 ∧
    dphiW V ((h' : Int) - 1) = 1 ∧
    FreshWord V ∧
    (∀ i, i ≤ V.length → -1 ≤ wordHeight V i ∧ wordHeight V i ≤ (h' : Int) + 1) ∧
    (∀ r ϕ, r ≤ (h' : Int) - 2 → SLandAt V r ϕ →
      ((0 ≤ r → 2 * ϕ > r * (r + 1)) ∧ 2 * ϕ ≥ 0) ∨
      (r = (h : Int) ∧ -((B.length : Int) + 6 * (bank : Int)) ≤ ϕ ∧ ϕ ≤ 0) ∨
      (r = (h : Int) - 1 ∧ -(6 * (bank : Int)) ≤ ϕ ∧ ϕ < 0) ∨
      (r = (h : Int) - 2 ∧ -(6 * (bank : Int)) ≤ ϕ ∧ ϕ < 0)) ∧
    (∀ r ϕ, r ≤ (h' : Int) - 2 → KeyAt V r ϕ →
      (0 ≤ r ∧ 2 * ϕ = 2 * dphiW V r + r * (r + 1)) ∨
      (r = (h : Int) ∧ ϕ ≤ 0) ∨
      (r = (h : Int) - 1 ∧ ϕ ≤ (bank : Int) + 2) ∨
      (r ≤ (h : Int) - 2 ∧ (ϕ ≤ dphiW (pref ++ B) r + (h : Int) * (h : Int) + 1 ∨ ϕ ≤ (bank : Int) + 40))) ∧
    (∀ ϕ, KeyAt (pref ++ B) (h' : Int) ϕ → False) ∧
    (∀ ϕ, KeyAt (pref ++ B) ((h' : Int) - 1) ϕ → ϕ ≤ 0) ∧
    (∀ i, i ≤ (pref ++ B).length → -1 ≤ wordHeight (pref ++ B) i ∧ wordHeight (pref ++ B) i ≤ (h : Int) + 1) := by
  intro pref V
  have hcast_h : (h : Int) = 2 * (k : Int) + 2 := by have := hD.hh; omega
  have hPB := prefix_bounds q p
  have hAr := archWord_bounds h' a (by have := hD.hh_ge; have := hD.hh'; omega) hD.ha_ge_h'2
  have hmPref : mass pref = 0 := hPB.1
  have hmPB : mass (pref ++ B) = 0 := by rw [mass_append, hmPref, hS.hmass]; rfl
  have hmV : mass V = 0 := by dsimp only [V]; rw [mass_append, hmPB, mass_archWord]; rfl
  have hdV_hm1 : dphiW V ((h' : Int) - 1) = 1 := by
    dsimp only [V]
    rw [dphiW_append hmPB, dphiW_append hmPref, hPB.2.1, dphiW_archWord]
    have := hD.ha_eq; grind
  have hdV_shift : ∀ r : Int, dphiW V r = 1 + (V.length : Int) * (((h' : Int) - 1) - r) := by
    intro r; have := dphiW_sub_shift V r ((h' : Int) - 1); rw [hdV_hm1] at this; exact this
  have hlenV : V.length = 2 * q + 2 * p + B.length + 2 * a + 2 * h' := by
    dsimp only [V, pref]; rw [List.length_append, List.length_append, List.length_append,
      asRep_length, saRep_length, archWord_length]; omega
  have hB_band : ∀ i, i ≤ B.length → -1 ≤ wordHeight B i ∧ wordHeight B i ≤ (h : Int) + 1 := by
    rw [hcast_h]; exact hS.hband
  have hPB_band : ∀ i, i ≤ (pref ++ B).length → -1 ≤ wordHeight (pref ++ B) i ∧ wordHeight (pref ++ B) i ≤ (h : Int) + 1 :=
    wordHeight_append_band hmPref (-1) ((h : Int) + 1)
      (fun i hi => by have := hPB.2.2.1 i hi; have := hD.hh_ge; dsimp only [pref]; omega) hB_band
  have hV_band : ∀ i, i ≤ V.length → -1 ≤ wordHeight V i ∧ wordHeight V i ≤ (h' : Int) + 1 :=
    wordHeight_append_band hmPB (-1) ((h' : Int) + 1)
      (fun i hi => by have := hPB_band i hi; have := hD.hh'; omega)
      (fun i hi => by have := wordHeight_archWord h' a i hi; omega)
  have hdPref_le0 : ∀ r : Int, 1 ≤ r → dphiW pref r ≤ 0 := by
    intro r hr; rw [hPB.2.1]
    have h1 : (q : Int) * (1 - 2 * r) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
    have h2 : (p : Int) * (-1 - 2 * r) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
    omega
  have h160h : 160 * (h + 4) ≤ bank := by
    have h1 : 8 * (h + 4) ≤ (h + 4) * (h + 4) := Nat.mul_le_mul_right (h + 4) (by have := hD.hh_ge; omega)
    have h2 := Nat.mul_le_mul_left 20 h1
    have := hD.hbank_lg; omega
  have hh'2_lt_bank : (h : Int) * (h : Int) + (h' : Int) * (h' : Int) + 100 * (h : Int) + 100 ≤ (bank : Int) := by
    have h1 : h * h ≤ (h + 4) * (h + 4) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : h' * h' ≤ (h + 4) * (h + 4) := Nat.mul_le_mul (by have := hD.hh'; omega) (by have := hD.hh'; omega)
    have : h * h + h' * h' + 100 * h + 100 ≤ bank := by have := hD.hbank_lg; omega
    exact_mod_cast this
  have hh2_nn : (0 : Int) ≤ (h : Int) * (h : Int) := Int.mul_nonneg (by omega) (by omega)
  have hh2_ge : (16 : Int) ≤ (h : Int) * (h : Int) := by
    have : 4 * 4 ≤ h * h := Nat.mul_le_mul hD.hh_ge hD.hh_ge
    exact_mod_cast this
  have hh'2_nn : (0 : Int) ≤ (h' : Int) * (h' : Int) := Int.mul_nonneg (by omega) (by omega)
  have hFresh_PB : FreshWord (pref ++ B) := by
    refine fresh_append hmPref (fresh_asRep_append_saRep q p) hS.hfresh ?_
    intro r ϕ hSL hK
    have hSr_ge : -1 ≤ r := ((keyAt_sLandAt_height_bounds hB_band).2 r ϕ hSL).1
    have hK_pref := hPB.2.2.2.1 r (dphiW pref r + ϕ) hK
    rw [hPB.2.1] at hK_pref
    have := hD.hq2; have := hD.hp_small; have := hD.hh_ge
    rcases hK_pref with ⟨rfl, _, _⟩ | ⟨rfl, _, hhi⟩ | ⟨rfl, _, hhi⟩ | ⟨rfl, _, hhi⟩
    · omega
    · have hlo := hS.hsland_low (-1) ϕ (by omega) hSL; omega
    · have hlo := hS.hsland_low 0 ϕ (by omega) hSL; omega
    · have hlo := hS.hsland_low 1 ϕ (by omega) hSL; omega
  have hKey_PB_top :
      (∀ ϕ, KeyAt (pref ++ B) (h' : Int) ϕ → False) ∧
      (∀ ϕ, KeyAt (pref ++ B) ((h' : Int) - 1) ϕ → ϕ ≤ 0) ∧
      (∀ ϕ, KeyAt (pref ++ B) ((h' : Int) - 2) ϕ → ϕ ≤ 0) ∧
      (∀ ϕ, KeyAt (pref ++ B) ((h' : Int) - 3) ϕ → ϕ ≤ (bank : Int) + 2) ∧
      (∀ r ϕ, r ≤ (h' : Int) - 4 → KeyAt (pref ++ B) r ϕ →
        ϕ ≤ dphiW (pref ++ B) r + (h : Int) * (h : Int) ∨ ϕ ≤ (bank : Int) + 40) := by
    have := hD.hh_ge; have := hD.hh'; have := hD.hq2; have := hD.hp_small
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro ϕ hK; have := (keyAt_sLandAt_height_bounds hPB_band).1 (h' : Int) ϕ hK; omega
    · intro ϕ hK
      rcases (keyAt_append hmPref _ ϕ).mp hK with h1 | h2
      · have := (keyAt_sLandAt_height_bounds (fun i hi => by dsimp only [pref]; exact hPB.2.2.1 i hi)).1 _ ϕ h1; omega
      · have hB := hS.hkey_hp1 _ (by rw [← hcast_h]; exact by simpa [show (h' : Int) - 1 = (h : Int) + 1 by omega] using h2)
        have hd := hdPref_le0 ((h : Int) + 1) (by omega); dsimp only [pref] at hd hB ⊢; omega
    · intro ϕ hK
      rcases (keyAt_append hmPref _ ϕ).mp hK with h1 | h2
      · have := (keyAt_sLandAt_height_bounds (fun i hi => by dsimp only [pref]; exact hPB.2.2.1 i hi)).1 _ ϕ h1; omega
      · have hB := hS.hkey_h _ (by rw [← hcast_h]; exact by simpa [show (h' : Int) - 2 = (h : Int) by omega] using h2)
        have hd := hdPref_le0 (h : Int) (by omega); dsimp only [pref] at hd hB ⊢; omega
    · intro ϕ hK
      rcases (keyAt_append hmPref _ ϕ).mp hK with h1 | h2
      · have := (keyAt_sLandAt_height_bounds (fun i hi => by dsimp only [pref]; exact hPB.2.2.1 i hi)).1 _ ϕ h1; omega
      · have hB := hS.hkey_hm1 _ (by rw [← hcast_h]; exact by simpa [show (h' : Int) - 3 = (h : Int) - 1 by omega] using h2)
        have hd := hdPref_le0 ((h : Int) - 1) (by omega); dsimp only [pref] at hd hB ⊢; omega
    · intro r ϕ hr hK
      rcases (keyAt_append hmPref r ϕ).mp hK with h1 | h2
      · right; rcases hPB.2.2.2.1 r ϕ h1 with ⟨_, _, hhi⟩ | ⟨_, _, hhi⟩ | ⟨_, _, hhi⟩ | ⟨_, _, hhi⟩ <;> omega
      · left; have hB := hS.hkey_le_dphi r _ (by rw [← hcast_h]; omega) h2
        rw [← hcast_h] at hB; rw [dphiW_append hmPref]; dsimp only [pref] at hB ⊢; omega
  have hdAr_low : ∀ r : Int, r ≤ (h' : Int) - 4 →
      9 * (a : Int) - (h' : Int) * (h' : Int) ≤ dphiW (archWord h' a) r := by
    intro r hr; rw [dphiW_archWord]
    have h1 : 9 ≤ 1 + 2 * ((h' : Int) - r) := by omega
    have h2 := Int.mul_le_mul_of_nonneg_left h1 (by omega : (0 : Int) ≤ (a : Int))
    have h3 : -((h' : Int) * (h' : Int)) ≤ (h' : Int) * ((h' : Int) - 2 * r) := by
      have h3a : (h' : Int) - 2 * r ≥ -((h' : Int)) := by omega
      have := Int.mul_le_mul_of_nonneg_left h3a (by omega : (0 : Int) ≤ (h' : Int)); grind
    omega
  have hFresh_V : FreshWord V := by
    have := hD.hh_ge; have := hD.hh'; have := hD.ha_ge_bank; have := hS.hlen_ge
    refine fresh_append hmPB hFresh_PB (fresh_archWord h' a (by omega) hD.ha_ge_h'2) ?_
    intro r ϕ hSL hK
    rcases hAr.1 r ϕ hSL with ⟨rfl, _, _⟩ | ⟨hr0, hrh', hphi⟩
    · exact hKey_PB_top.1 _ hK
    · have hphiV : 2 * (dphiW (pref ++ B) r + ϕ) = 2 * dphiW V r + r * (r + 1) := by
        have : dphiW V r = dphiW (pref ++ B) r + dphiW (archWord h' a) r := dphiW_append hmPB r; omega
      have hr2 : 0 ≤ r * (r + 1) := Int.mul_nonneg (by omega) (by omega)
      by_cases hr1 : r = (h' : Int) - 1
      · rw [hr1] at hK hphiV hr2; have hle := hKey_PB_top.2.1 _ hK; rw [hdV_hm1] at hphiV; omega
      · by_cases hr2c : r = (h' : Int) - 2
        · rw [hr2c] at hK hphiV hr2; have hle := hKey_PB_top.2.2.1 _ hK; have hdv := hdV_shift ((h' : Int) - 2); omega
        · by_cases hr3 : r = (h' : Int) - 3
          · rw [hr3] at hK hphiV hr2; have hle := hKey_PB_top.2.2.2.1 _ hK; have hdv := hdV_shift ((h' : Int) - 3); omega
          · have hle := hKey_PB_top.2.2.2.2 r _ (by omega) hK
            have hda := hdAr_low r (by omega)
            have hdv : 3 * (V.length : Int) ≤ dphiW V r := by
              rw [hdV_shift r]
              have := Int.mul_le_mul_of_nonneg_left (by omega : 3 ≤ ((h' : Int) - 1) - r) (by omega : (0 : Int) ≤ (V.length : Int))
              omega
            rcases hle with hle1 | hle2
            · have : dphiW V r = dphiW (pref ++ B) r + dphiW (archWord h' a) r := dphiW_append hmPB r; omega
            · omega
  have hPref_r_lb : ∀ r : Int, -1 ≤ r → r ≤ (h : Int) →
      -((2 * (h : Int) + 3) * (p : Int)) - 4 * (h : Int) ≤ dphiW pref r := by
    intro r hlo hhi; rw [hPB.2.1]; have := hD.hq2; have := hD.hh_ge
    have h1 : (q : Int) * (1 - 2 * r) ≥ -4 * (h : Int) := by
      have : 1 - 2 * r ≥ -2 * (h : Int) := by omega
      have h1a := Int.mul_le_mul_of_nonneg_left this (by omega : (0 : Int) ≤ (q : Int))
      have h1b := Int.mul_le_mul_of_nonneg_right (by omega : (q : Int) ≤ 2) (by omega : (0 : Int) ≤ 2 * (h : Int))
      grind
    have h2 : (p : Int) * (-1 - 2 * r) ≥ -((2 * (h : Int) + 3) * (p : Int)) := by
      have : -1 - 2 * r ≥ -(2 * (h : Int) + 3) := by omega
      have := Int.mul_le_mul_of_nonneg_left this (by omega : (0 : Int) ≤ (p : Int)); grind
    omega
  have hp_2h3_int : 3 * (bank : Int) + 2 * (2 * (h : Int) - 3) < 2 * ((2 * (h : Int) - 3) * (p : Int)) ∧
      2 * ((2 * (h : Int) - 3) * (p : Int)) ≤ 3 * (bank : Int) + 8 * (2 * (h : Int) - 3) := by
    have := hD.hh_ge
    have h1 : ((3 * bank + 2 * (2 * h - 3) : Nat) : Int) < ((2 * (2 * h - 3) * p : Nat) : Int) := by exact_mod_cast hD.hp_lo
    have h2 : ((2 * (2 * h - 3) * p : Nat) : Int) ≤ ((3 * bank + 8 * (2 * h - 3) : Nat) : Int) := by exact_mod_cast hD.hp_hi
    have hh23 : ((2 * h - 3 : Nat) : Int) = 2 * (h : Int) - 3 := by omega
    push_cast at h1 h2; rw [hh23] at h1 h2; exact ⟨by grind, by grind⟩
  have h2hp_int : (2 * (h : Int) + 3) * (p : Int) ≤ 4 * (bank : Int) := by
    have : (((2 * h + 3) * p : Nat) : Int) ≤ ((4 * bank : Nat) : Int) := by exact_mod_cast hD.h2hp_ub
    push_cast at this; exact this
  have hSL_V_low : ∀ r ϕ, r ≤ (h' : Int) - 2 → SLandAt V r ϕ →
      ((0 ≤ r → 2 * ϕ > r * (r + 1)) ∧ 2 * ϕ ≥ 0) ∨
      (r = (h : Int) ∧ -((B.length : Int) + 6 * (bank : Int)) ≤ ϕ ∧ ϕ ≤ 0) ∨
      (r = (h : Int) - 1 ∧ -(6 * (bank : Int)) ≤ ϕ ∧ ϕ < 0) ∨
      (r = (h : Int) - 2 ∧ -(6 * (bank : Int)) ≤ ϕ ∧ ϕ < 0) := by
    intro r ϕ hr hSL; have := hD.hh_ge; have := hD.hh'; have := hD.hq2
    have hr_ge : -1 ≤ r := ((keyAt_sLandAt_height_bounds hV_band).2 r ϕ hSL).1
    rcases (sLandAt_append hmPB r ϕ).mp hSL with hPB_sl | hAr_sl
    · rcases (sLandAt_append hmPref r ϕ).mp hPB_sl with hP_sl | hB_sl
      · left; rcases hPB.2.2.2.2 r ϕ hP_sl with ⟨rfl, hlo, _⟩ | ⟨rfl, hlo, _⟩
        · exact ⟨fun _ => by omega, by omega⟩
        · exact ⟨fun h0 => by omega, by omega⟩
      · have hpref_lb := hPref_r_lb r hr_ge (by omega)
        by_cases hrh : r = (h : Int)
        · right; left; rw [hrh] at hB_sl hpref_lb ⊢
          have hB := hS.hsland_h _ (by rw [← hcast_h]; exact hB_sl)
          rw [← hcast_h] at hB
          have hdBhm1 : -((h : Int) * (h : Int)) ≤ dphiW B ((h : Int) - 1) := by rw [hcast_h]; exact hS.hdphi_hm1.1
          have hdBh : dphiW B (h : Int) = dphiW B ((h : Int) - 1) - (B.length : Int) := by
            have := dphiW_sub_shift B (h : Int) ((h : Int) - 1); grind
          have hdP := hdPref_le0 (h : Int) (by omega); dsimp only [pref] at hdP hpref_lb hB ⊢; omega
        · by_cases hrh1 : r = (h : Int) - 1
          · right; right; left; rw [hrh1] at hB_sl hpref_lb ⊢
            have hB := hS.hsland_hm1 _ (by rw [← hcast_h]; exact hB_sl)
            rw [← hcast_h] at hB
            have hdP_ub : dphiW pref ((h : Int) - 1) ≤ -((2 * (h : Int) - 1) * (p : Int)) := by
              rw [hPB.2.1]; have : (q : Int) * (1 - 2 * ((h : Int) - 1)) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega); grind
            have hp_ge : (2 * (h : Int) - 3) * (p : Int) ≤ (2 * (h : Int) - 1) * (p : Int) := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
            dsimp only [pref] at hdP_ub hpref_lb hB ⊢; omega
          · by_cases hrh2 : r = (h : Int) - 2
            · rw [hrh2] at hB_sl hpref_lb ⊢
              have hB := hS.hsland_hm2 _ (by rw [← hcast_h]; exact hB_sl)
              rw [← hcast_h] at hB
              rcases hB.2 with hsmall | hbig
              · right; right; right
                have hdP_ub : dphiW pref ((h : Int) - 2) ≤ -((2 * (h : Int) - 3) * (p : Int)) := by
                  rw [hPB.2.1]; have : (q : Int) * (1 - 2 * ((h : Int) - 2)) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega); grind
                dsimp only [pref] at hdP_ub hpref_lb hsmall hB ⊢; omega
              · left
                have hdP_lb : 2 * dphiW pref ((h : Int) - 2) ≥ -(3 * (bank : Int) + 24 * (h : Int)) := by
                  rw [hPB.2.1]
                  have hq_lb : (q : Int) * (1 - 2 * ((h : Int) - 2)) ≥ -4 * (h : Int) := by
                    have h1 : 1 - 2 * ((h : Int) - 2) ≥ -2 * (h : Int) := by omega
                    have h2 := Int.mul_le_mul_of_nonneg_left h1 (by omega : (0 : Int) ≤ (q : Int))
                    have h3 := Int.mul_le_mul_of_nonneg_right (by omega : (q : Int) ≤ 2) (by omega : (0 : Int) ≤ 2 * (h : Int)); grind
                  grind
                have hrr : ((h : Int) - 2) * (((h : Int) - 2) + 1) ≤ (h : Int) * (h : Int) := by
                  have h1 := Int.mul_le_mul_of_nonneg_left (by omega : (h : Int) - 1 ≤ (h : Int)) (by omega : (0 : Int) ≤ (h : Int) - 2)
                  have h2 := Int.mul_le_mul_of_nonneg_right (by omega : (h : Int) - 2 ≤ (h : Int)) (by omega : (0 : Int) ≤ (h : Int))
                  have h3 : ((h : Int) - 2) * (((h : Int) - 2) + 1) = ((h : Int) - 2) * ((h : Int) - 1) := by grind
                  omega
                dsimp only [pref] at hdP_lb hbig ⊢
                exact ⟨fun _ => by omega, by omega⟩
            · left
              have hB := hS.hsland_low r _ (by rw [← hcast_h]; omega) hB_sl
              have hdP_lb : 2 * dphiW pref r ≥ -(3 * (bank : Int) + 24 * (h : Int)) := by
                rw [hPB.2.1]
                have hq_lb : (q : Int) * (1 - 2 * r) ≥ -4 * (h : Int) := by
                  have h1 : 1 - 2 * r ≥ -2 * (h : Int) := by omega
                  have h2 := Int.mul_le_mul_of_nonneg_left h1 (by omega : (0 : Int) ≤ (q : Int))
                  have h3 := Int.mul_le_mul_of_nonneg_right (by omega : (q : Int) ≤ 2) (by omega : (0 : Int) ≤ 2 * (h : Int)); grind
                have hp_lb : (p : Int) * (-1 - 2 * r) ≥ -((2 * (h : Int) - 3) * (p : Int)) := by
                  have : -1 - 2 * r ≥ -(2 * (h : Int) - 3) := by omega
                  have := Int.mul_le_mul_of_nonneg_left this (by omega : (0 : Int) ≤ (p : Int)); grind
                grind
              have hrr : r * (r + 1) ≤ (h : Int) * (h : Int) := by
                by_cases hrm1 : r = -1
                · rw [hrm1]; have : 0 ≤ (h : Int) * (h : Int) := Int.mul_nonneg (by omega) (by omega); omega
                · have h1 := Int.mul_le_mul_of_nonneg_left (by omega : r + 1 ≤ (h : Int)) (by omega : (0 : Int) ≤ r)
                  have h2 := Int.mul_le_mul_of_nonneg_right (by omega : r ≤ (h : Int)) (by omega : (0 : Int) ≤ (h : Int)); omega
              dsimp only [pref] at hdP_lb hB ⊢
              exact ⟨fun _ => by omega, by omega⟩
    · left
      rcases hAr.1 r _ hAr_sl with ⟨hreq, _, _⟩ | ⟨hr0, _, hphi⟩
      · omega
      · have hphiV : 2 * ϕ = 2 * dphiW V r + r * (r + 1) := by
          have : dphiW V r = dphiW (pref ++ B) r + dphiW (archWord h' a) r := dphiW_append hmPB r; omega
        have hdv : 1 ≤ dphiW V r := by
          rw [hdV_shift r]; have := Int.mul_nonneg (by omega : (0 : Int) ≤ (V.length : Int)) (by omega : (0 : Int) ≤ ((h' : Int) - 1) - r); omega
        have hr2 : 0 ≤ r * (r + 1) := Int.mul_nonneg (by omega) (by omega)
        exact ⟨fun _ => by omega, by omega⟩
  have hKey_V_low : ∀ r ϕ, r ≤ (h' : Int) - 2 → KeyAt V r ϕ →
      (0 ≤ r ∧ 2 * ϕ = 2 * dphiW V r + r * (r + 1)) ∨
      (r = (h : Int) ∧ ϕ ≤ 0) ∨
      (r = (h : Int) - 1 ∧ ϕ ≤ (bank : Int) + 2) ∨
      (r ≤ (h : Int) - 2 ∧ (ϕ ≤ dphiW (pref ++ B) r + (h : Int) * (h : Int) + 1 ∨ ϕ ≤ (bank : Int) + 40)) := by
    intro r ϕ hr hK; have := hD.hh_ge; have := hD.hh'; have := hS.hlen_ge
    rcases (keyAt_append hmPB r ϕ).mp hK with h1 | h2
    · by_cases hrh : r = (h : Int)
      · right; left; rw [hrh] at h1 ⊢; exact ⟨rfl, hKey_PB_top.2.2.1 _ (by simpa [show (h' : Int) - 2 = (h : Int) by omega] using h1)⟩
      · by_cases hrh1 : r = (h : Int) - 1
        · right; right; left; rw [hrh1] at h1 ⊢; exact ⟨rfl, hKey_PB_top.2.2.2.1 _ (by simpa [show (h' : Int) - 3 = (h : Int) - 1 by omega] using h1)⟩
        · right; right; right
          rcases hKey_PB_top.2.2.2.2 r ϕ (by omega) h1 with h | h
          · exact ⟨by omega, Or.inl (by omega)⟩
          · exact ⟨by omega, Or.inr (by omega)⟩
    · rcases hAr.2 r _ h2 with ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨hr0, hrh2, hcase⟩ | ⟨rfl, hphi0⟩
      · omega
      · omega
      · omega
      · rcases hcase with hle2 | heqS
        · by_cases hrh : r = (h : Int)
          · right; left
            have hdPB : dphiW (pref ++ B) (h : Int) ≤ -((h : Int) * (h : Int)) := by
              rw [dphiW_append hmPref]; have hdP := hdPref_le0 (h : Int) (by omega)
              have hdBhm1 : dphiW B ((h : Int) - 1) ≤ (bank : Int) + 2 := by rw [hcast_h]; exact hS.hdphi_hm1.2
              have hdBh : dphiW B (h : Int) = dphiW B ((h : Int) - 1) - (B.length : Int) := by
                have := dphiW_sub_shift B (h : Int) ((h : Int) - 1); grind
              omega
            rw [hrh] at hle2 ⊢; dsimp only [pref] at hdPB hle2 ⊢; omega
          · by_cases hrh1 : r = (h : Int) - 1
            · right; right; left
              have hdPB : dphiW (pref ++ B) ((h : Int) - 1) ≤ (bank : Int) := by
                rw [dphiW_append hmPref]
                have hdBhm1 : dphiW B ((h : Int) - 1) ≤ (bank : Int) + 2 := by rw [hcast_h]; exact hS.hdphi_hm1.2
                have hdP_ub : dphiW pref ((h : Int) - 1) ≤ -((2 * (h : Int) - 1) * (p : Int)) := by
                  rw [hPB.2.1]; have : (q : Int) * (1 - 2 * ((h : Int) - 1)) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega); grind
                have hp_ge : (2 * (h : Int) - 3) * (p : Int) ≤ (2 * (h : Int) - 1) * (p : Int) := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
                omega
              rw [hrh1] at hle2 ⊢; dsimp only [pref] at hdPB hle2 ⊢; omega
            · right; right; right
              have hnn : (0 : Int) ≤ (h : Int) * (h : Int) := Int.mul_nonneg (by omega) (by omega)
              exact ⟨by omega, Or.inl (by omega)⟩
        · left; have : dphiW V r = dphiW (pref ++ B) r + dphiW (archWord h' a) r := dphiW_append hmPB r; exact ⟨hr0, by omega⟩
      · right; right; right
        have hnn : (0 : Int) ≤ (h : Int) * (h : Int) := Int.mul_nonneg (by omega) (by omega)
        exact ⟨by omega, Or.inl (by omega)⟩
  exact ⟨hmV, hdV_hm1, hFresh_V, hV_band, hSL_V_low, hKey_V_low, hKey_PB_top.1, hKey_PB_top.2.1, hPB_band⟩

private theorem stepData_h2_lt_bank {k h h' bank q p a : Nat} {B : List Bool}
    (hD : StepData k h h' B bank q p a) :
    (h : Int) * (h : Int) + (h' : Int) * (h' : Int) + 100 * (h : Int) + 100 ≤ (bank : Int) := by
  have hh_ge := hD.hh_ge; have hh' := hD.hh'; have hlg := hD.hbank_lg
  have h1 : h * h ≤ (h + 4) * (h + 4) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : h' * h' ≤ (h + 4) * (h + 4) := Nat.mul_le_mul (by omega) (by omega)
  have h3 : 8 * (h + 4) ≤ (h + 4) * (h + 4) := Nat.mul_le_mul_right (h + 4) (by omega)
  have htot : h * h + h' * h' + 100 * h + 100 ≤ bank := by omega
  exact_mod_cast htot

/-- Helper: periodic freshness of `repeatWord R V` for ALL `R : Nat` (`E-805`). -/
private theorem step_repV_fresh (k h h' : Nat) (B : List Bool) (bank q p a R : Nat)
    (hS : StageInv k B bank) (hD : StepData k h h' B bank q p a) :
    FreshWord (repeatWord R ((asRep q ++ saRep p) ++ B ++ archWord h' a)) := by
  let pref := asRep q ++ saRep p
  let V := pref ++ B ++ archWord h' a
  change FreshWord (repeatWord R V)
  have hC :
      mass V = 0 ∧
      dphiW V ((h' : Int) - 1) = 1 ∧
      FreshWord V ∧
      (∀ i, i ≤ V.length → -1 ≤ wordHeight V i ∧ wordHeight V i ≤ (h' : Int) + 1) ∧
      (∀ r ϕ, r ≤ (h' : Int) - 2 → SLandAt V r ϕ →
        ((0 ≤ r → 2 * ϕ > r * (r + 1)) ∧ 2 * ϕ ≥ 0) ∨
        (r = (h : Int) ∧ -((B.length : Int) + 6 * (bank : Int)) ≤ ϕ ∧ ϕ ≤ 0) ∨
        (r = (h : Int) - 1 ∧ -(6 * (bank : Int)) ≤ ϕ ∧ ϕ < 0) ∨
        (r = (h : Int) - 2 ∧ -(6 * (bank : Int)) ≤ ϕ ∧ ϕ < 0)) ∧
      (∀ r ϕ, r ≤ (h' : Int) - 2 → KeyAt V r ϕ →
        (0 ≤ r ∧ 2 * ϕ = 2 * dphiW V r + r * (r + 1)) ∨
        (r = (h : Int) ∧ ϕ ≤ 0) ∨
        (r = (h : Int) - 1 ∧ ϕ ≤ (bank : Int) + 2) ∨
        (r ≤ (h : Int) - 2 ∧ (ϕ ≤ dphiW (pref ++ B) r + (h : Int) * (h : Int) + 1 ∨ ϕ ≤ (bank : Int) + 40))) ∧
      (∀ ϕ, KeyAt (pref ++ B) (h' : Int) ϕ → False) ∧
      (∀ ϕ, KeyAt (pref ++ B) ((h' : Int) - 1) ϕ → ϕ ≤ 0) ∧
      (∀ i, i ≤ (pref ++ B).length → -1 ≤ wordHeight (pref ++ B) i ∧ wordHeight (pref ++ B) i ≤ (h : Int) + 1) :=
    step_V_core k h h' B bank q p a hS hD
  rcases hC with ⟨hmV, hdV_hm1, hFresh_V, hV_band, hSL_V_low, hKey_V_low, hKey_PB_h', hKey_PB_h'm1, hPB_band⟩
  have hmPref : mass pref = 0 := (prefix_bounds q p).1
  have hmPB : mass (pref ++ B) = 0 := by rw [mass_append, hmPref, hS.hmass]; rfl
  have hAr := archWord_bounds h' a (by have := hD.hh_ge; have := hD.hh'; omega) hD.ha_ge_h'2
  have hdV_shift : ∀ r : Int, dphiW V r = 1 + (V.length : Int) * (((h' : Int) - 1) - r) := by
    intro r; have := dphiW_sub_shift V r ((h' : Int) - 1); rw [hdV_hm1] at this; exact this
  have hlenV : V.length = 2 * q + 2 * p + B.length + 2 * a + 2 * h' := by
    dsimp only [V, pref]; rw [List.length_append, List.length_append, List.length_append,
      asRep_length, saRep_length, archWord_length]; omega
  have h2a_ge : 39 * bank ≤ 2 * a := by
    have := hD.hbank'_lb; have := hS.hlen_ge; omega
  have hh'2_lt_bank := stepData_h2_lt_bank hD
  have hh2_nn : (0 : Int) ≤ (h : Int) * (h : Int) := Int.mul_nonneg (by omega) (by omega)
  have hh'2_nn : (0 : Int) ≤ (h' : Int) * (h' : Int) := Int.mul_nonneg (by omega) (by omega)
  have hdAr_low : ∀ r : Int, r ≤ (h' : Int) - 4 →
      9 * (a : Int) - (h' : Int) * (h' : Int) ≤ dphiW (archWord h' a) r := by
    intro r hr; rw [dphiW_archWord]
    have h1 : 9 ≤ 1 + 2 * ((h' : Int) - r) := by omega
    have h2 : (a : Int) * 9 ≤ (a : Int) * (1 + 2 * ((h' : Int) - r)) :=
      Int.mul_le_mul_of_nonneg_left h1 (by omega)
    have h2' : 9 * (a : Int) = (a : Int) * 9 := Int.mul_comm _ _
    have h3 : (h' : Int) * (-((h' : Int))) ≤ (h' : Int) * ((h' : Int) - 2 * r) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have h3' : (h' : Int) * (-((h' : Int))) = -((h' : Int) * (h' : Int)) := Int.mul_neg _ _
    omega
  refine fresh_repeatWord hmV hFresh_V (fun c hc r ϕ hSL hK => ?_) R
  have := hD.hh_ge; have := hD.hh'; have := hS.hlen_ge; have := hD.ha_ge_bank; have := hD.ha_ge_h'2
  have hSL_r := (keyAt_sLandAt_height_bounds hV_band).2 r ϕ hSL
  by_cases hrh' : r = (h' : Int)
  · rw [hrh'] at hSL hK
    have hdVh' : dphiW V (h' : Int) = 1 - (V.length : Int) := by
      rw [hdV_shift, show ((h' : Int) - 1) - (h' : Int) = -1 by omega, Int.mul_neg, Int.mul_one]; omega
    have hSL_Ar : SLandAt (archWord h' a) (h' : Int) (ϕ - dphiW (pref ++ B) (h' : Int)) := by
      rcases (sLandAt_append hmPB (h' : Int) ϕ).mp hSL with h1 | h2
      · exfalso; have := (keyAt_sLandAt_height_bounds hPB_band).2 (h' : Int) ϕ h1; omega
      · exact h2
    have hK_Ar : KeyAt (archWord h' a) (h' : Int) (ϕ + (c : Int) * dphiW V (h' : Int) - dphiW (pref ++ B) (h' : Int)) := by
      rcases (keyAt_append hmPB (h' : Int) _).mp hK with h1 | h2
      · exfalso; exact hKey_PB_h' _ h1
      · exact h2
    have h1 : 2 * (ϕ - dphiW (pref ++ B) (h' : Int)) ≤ 2 * (a : Int) - (h' : Int) * ((h' : Int) - 1) := by
      rcases hAr.1 _ _ hSL_Ar with ⟨_, _, hhi⟩ | ⟨_, hlt, _⟩
      · exact hhi
      · omega
    have h2 : 2 * (ϕ + (c : Int) * dphiW V (h' : Int) - dphiW (pref ++ B) (h' : Int)) ≥ -((h' : Int) * ((h' : Int) - 1)) := by
      have hneg : -(h' : Int) * ((h' : Int) - 1) = -((h' : Int) * ((h' : Int) - 1)) := Int.neg_mul _ _
      rcases hAr.2 _ _ hK_Ar with ⟨hreq, _⟩ | ⟨_, hlo, _⟩ | ⟨hreq, _⟩ | ⟨_, hle, _⟩ | ⟨hreq, _⟩ <;> omega
    have hcd : (c : Int) * dphiW V (h' : Int) ≤ 1 - (V.length : Int) := by
      rw [hdVh']
      have := Int.mul_le_mul_of_nonpos_right (by omega : (1 : Int) ≤ (c : Int)) (by omega : 1 - (V.length : Int) ≤ 0)
      omega
    omega
  · by_cases hrh'1 : r = (h' : Int) - 1
    · rw [hrh'1] at hSL hK
      have hSL_Ar : SLandAt (archWord h' a) ((h' : Int) - 1) (ϕ - dphiW (pref ++ B) ((h' : Int) - 1)) := by
        rcases (sLandAt_append hmPB ((h' : Int) - 1) ϕ).mp hSL with h1 | h2
        · exfalso; have := (keyAt_sLandAt_height_bounds hPB_band).2 ((h' : Int) - 1) ϕ h1; omega
        · exact h2
      have hphi_eq : 2 * ϕ = 2 + ((h' : Int) - 1) * (h' : Int) := by
        rcases hAr.1 _ _ hSL_Ar with ⟨hreq, _, _⟩ | ⟨_, _, hphi⟩
        · omega
        · have hsp : dphiW V ((h' : Int) - 1) = dphiW (pref ++ B) ((h' : Int) - 1) + dphiW (archWord h' a) ((h' : Int) - 1) :=
            dphiW_append hmPB ((h' : Int) - 1)
          have hsub : ((h' : Int) - 1) + 1 = (h' : Int) := by omega
          rw [hsub] at hphi; rw [hdV_hm1] at hsp; omega
      have hpsi_le : 2 * (ϕ + (c : Int) * dphiW V ((h' : Int) - 1)) ≤ 2 + ((h' : Int) - 1) * (h' : Int) := by
        rcases (keyAt_append hmPB ((h' : Int) - 1) _).mp hK with h1 | h2
        · have hle := hKey_PB_h'm1 _ h1
          have hnn : 0 ≤ ((h' : Int) - 1) * (h' : Int) := Int.mul_nonneg (by omega) (by omega)
          omega
        · rcases hAr.2 _ _ h2 with ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨_, hle⟩ | ⟨_, hlt, _⟩ | ⟨hreq, _⟩
          · omega
          · omega
          · have hsp : dphiW V ((h' : Int) - 1) = dphiW (pref ++ B) ((h' : Int) - 1) + dphiW (archWord h' a) ((h' : Int) - 1) :=
              dphiW_append hmPB ((h' : Int) - 1)
            rw [hdV_hm1] at hsp; omega
          · omega
          · omega
      rw [hdV_hm1] at hpsi_le; omega
    · -- `r ≤ h' - 2`
      have hr_le : r ≤ (h' : Int) - 2 := by omega
      have hdV_ge : (V.length : Int) + 1 ≤ dphiW V r := by
        rw [hdV_shift r]
        have := Int.mul_le_mul_of_nonneg_left (by omega : 1 ≤ ((h' : Int) - 1) - r) (by omega : (0 : Int) ≤ (V.length : Int))
        omega
      have hc_ge1 : dphiW V r ≤ (c : Int) * dphiW V r := by
        have := Int.mul_le_mul_of_nonneg_right (by omega : (1 : Int) ≤ (c : Int)) (by omega : 0 ≤ dphiW V r)
        omega
      have hSL_cases := hSL_V_low r ϕ hr_le hSL
      have hK_cases := hKey_V_low r (ϕ + (c : Int) * dphiW V r) hr_le hK
      have hrr_le_h2 : r ≤ (h : Int) → 0 ≤ r → r * (r + 1) ≤ (h' : Int) * (h' : Int) := by
        intro hrh hr0
        have h1 := Int.mul_le_mul_of_nonneg_left (by omega : r + 1 ≤ (h' : Int)) hr0
        have h2 := Int.mul_le_mul_of_nonneg_right (by omega : r ≤ (h' : Int)) (by omega : (0 : Int) ≤ (h' : Int))
        omega
      have hrr_pos : 1 ≤ r → 0 < r * (r + 1) := fun hr1 => Int.mul_pos (by omega) (by omega)
      rcases hSL_cases with ⟨hpos, hnn⟩ | ⟨rfl, hlo, hhi⟩ | ⟨rfl, hlo, hhi⟩ | ⟨rfl, hlo, hhi⟩
      · -- Case 1: `(0 ≤ r → 2*ϕ > r*(r+1)) ∧ 2*ϕ ≥ 0`
        rcases hK_cases with ⟨hr0, heq⟩ | ⟨rfl, hkle⟩ | ⟨rfl, hkle⟩ | ⟨hrle, hkle⟩
        · have := hpos hr0; omega
        · omega
        · omega
        · rcases hkle with hkle1 | hkle2
          · have hda := hdAr_low r (by omega)
            have hdv_split : dphiW V r = dphiW (pref ++ B) r + dphiW (archWord h' a) r := dphiW_append hmPB r
            omega
          · omega
      · -- Case 2: `r = h ∧ -(|B| + 6*bank) ≤ ϕ ∧ ϕ ≤ 0`
        have hdVh : dphiW V (h : Int) = 1 + (V.length : Int) := by
          rw [hdV_shift, show ((h' : Int) - 1) - (h : Int) = 1 by omega, Int.mul_one]
        rcases hK_cases with ⟨hr0, heq⟩ | ⟨_, hkle⟩ | ⟨hreq, _⟩ | ⟨hrle, _⟩
        · by_cases hc1 : c = 1
          · subst hc1; have := hrr_pos (by omega : (1 : Int) ≤ (h : Int)); omega
          · have hc2 : 2 * dphiW V (h : Int) ≤ (c : Int) * dphiW V (h : Int) :=
              Int.mul_le_mul_of_nonneg_right (by omega : (2 : Int) ≤ (c : Int)) (by omega : (0 : Int) ≤ dphiW V (h : Int))
            have := hrr_le_h2 (by omega) hr0; omega
        · omega
        · omega
        · omega
      · -- Case 3: `r = h - 1 ∧ -(6*bank) ≤ ϕ ∧ ϕ < 0`
        have hdVh1 : dphiW V ((h : Int) - 1) = 1 + 2 * (V.length : Int) := by
          rw [hdV_shift, show ((h' : Int) - 1) - ((h : Int) - 1) = 2 by omega, Int.mul_comm]
        rcases hK_cases with ⟨hr0, heq⟩ | ⟨hreq, _⟩ | ⟨_, hkle⟩ | ⟨hrle, _⟩
        · by_cases hc1 : c = 1
          · subst hc1; have := hrr_pos (by omega : (1 : Int) ≤ (h : Int) - 1); omega
          · have hc2 : 2 * dphiW V ((h : Int) - 1) ≤ (c : Int) * dphiW V ((h : Int) - 1) :=
              Int.mul_le_mul_of_nonneg_right (by omega : (2 : Int) ≤ (c : Int)) (by omega : (0 : Int) ≤ dphiW V ((h : Int) - 1))
            have := hrr_le_h2 (by omega) hr0; omega
        · omega
        · omega
        · omega
      · -- Case 4: `r = h - 2 ∧ -(6*bank) ≤ ϕ ∧ ϕ < 0`
        have hdVh2 : dphiW V ((h : Int) - 2) = 1 + 3 * (V.length : Int) := by
          rw [hdV_shift, show ((h' : Int) - 1) - ((h : Int) - 2) = 3 by omega, Int.mul_comm]
        rcases hK_cases with ⟨hr0, heq⟩ | ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨_, hkle⟩
        · by_cases hc1 : c = 1
          · subst hc1; have := hrr_pos (by omega : (1 : Int) ≤ (h : Int) - 2); omega
          · have hc2 : 2 * dphiW V ((h : Int) - 2) ≤ (c : Int) * dphiW V ((h : Int) - 2) :=
              Int.mul_le_mul_of_nonneg_right (by omega : (2 : Int) ≤ (c : Int)) (by omega : (0 : Int) ≤ dphiW V ((h : Int) - 2))
            have := hrr_le_h2 (by omega) hr0; omega
        · omega
        · omega
        · rcases hkle with hkle1 | hkle2
          · have hda := hdAr_low ((h : Int) - 2) (by omega)
            have hdv_split : dphiW V ((h : Int) - 2) = dphiW (pref ++ B) ((h : Int) - 2) + dphiW (archWord h' a) ((h : Int) - 2) :=
              dphiW_append hmPB ((h : Int) - 2)
            omega
          · omega

/-- Helper: freshness of `B' = v0Word h' a ++ repeatWord R V` (`E-805`). -/
private theorem step_B'_fresh (k h h' : Nat) (B : List Bool) (bank q p a R : Nat)
    (hS : StageInv k B bank) (hD : StepData k h h' B bank q p a) :
    FreshWord (v0Word h' a ++ repeatWord R ((asRep q ++ saRep p) ++ B ++ archWord h' a)) := by
  let pref := asRep q ++ saRep p
  let V := pref ++ B ++ archWord h' a
  let V0 := v0Word h' a
  change FreshWord (V0 ++ repeatWord R V)
  have hC :
      mass V = 0 ∧
      dphiW V ((h' : Int) - 1) = 1 ∧
      FreshWord V ∧
      (∀ i, i ≤ V.length → -1 ≤ wordHeight V i ∧ wordHeight V i ≤ (h' : Int) + 1) ∧
      (∀ r ϕ, r ≤ (h' : Int) - 2 → SLandAt V r ϕ →
        ((0 ≤ r → 2 * ϕ > r * (r + 1)) ∧ 2 * ϕ ≥ 0) ∨
        (r = (h : Int) ∧ -((B.length : Int) + 6 * (bank : Int)) ≤ ϕ ∧ ϕ ≤ 0) ∨
        (r = (h : Int) - 1 ∧ -(6 * (bank : Int)) ≤ ϕ ∧ ϕ < 0) ∨
        (r = (h : Int) - 2 ∧ -(6 * (bank : Int)) ≤ ϕ ∧ ϕ < 0)) ∧
      (∀ r ϕ, r ≤ (h' : Int) - 2 → KeyAt V r ϕ →
        (0 ≤ r ∧ 2 * ϕ = 2 * dphiW V r + r * (r + 1)) ∨
        (r = (h : Int) ∧ ϕ ≤ 0) ∨
        (r = (h : Int) - 1 ∧ ϕ ≤ (bank : Int) + 2) ∨
        (r ≤ (h : Int) - 2 ∧ (ϕ ≤ dphiW (pref ++ B) r + (h : Int) * (h : Int) + 1 ∨ ϕ ≤ (bank : Int) + 40))) ∧
      (∀ ϕ, KeyAt (pref ++ B) (h' : Int) ϕ → False) ∧
      (∀ ϕ, KeyAt (pref ++ B) ((h' : Int) - 1) ϕ → ϕ ≤ 0) ∧
      (∀ i, i ≤ (pref ++ B).length → -1 ≤ wordHeight (pref ++ B) i ∧ wordHeight (pref ++ B) i ≤ (h : Int) + 1) :=
    step_V_core k h h' B bank q p a hS hD
  rcases hC with ⟨hmV, hdV_hm1, _, hV_band, hSL_V_low, _, _, _, hPB_band⟩
  have hmPref : mass pref = 0 := (prefix_bounds q p).1
  have hmPB : mass (pref ++ B) = 0 := by rw [mass_append, hmPref, hS.hmass]; rfl
  have hh'_ge : 4 ≤ h' := by have := hD.hh_ge; have := hD.hh'; omega
  have ha1 : 1 ≤ a := by have := hD.ha_ge_h'2; have : 16 ≤ h' * h' := Nat.mul_le_mul hh'_ge hh'_ge; omega
  have hAr := archWord_bounds h' a hh'_ge hD.ha_ge_h'2
  have hV0b := v0Word_bounds h' a hh'_ge hD.ha_ge_h'2
  have hdV_shift : ∀ r : Int, dphiW V r = 1 + (V.length : Int) * (((h' : Int) - 1) - r) := by
    intro r; have := dphiW_sub_shift V r ((h' : Int) - 1); rw [hdV_hm1] at this; exact this
  have hlenV : V.length = 2 * q + 2 * p + B.length + 2 * a + 2 * h' := by
    dsimp only [V, pref]; rw [List.length_append, List.length_append, List.length_append,
      asRep_length, saRep_length, archWord_length]; omega
  have h2a_ge : 39 * bank ≤ 2 * a := by
    have := hD.hbank'_lb; have := hS.hlen_ge; omega
  have hh'2_lt_bank := stepData_h2_lt_bank hD
  have hh2_nn : (0 : Int) ≤ (h : Int) * (h : Int) := Int.mul_nonneg (by omega) (by omega)
  have hh'2_nn : (0 : Int) ≤ (h' : Int) * (h' : Int) := Int.mul_nonneg (by omega) (by omega)
  have ha_ge_h'2_int : (h' : Int) * (h' : Int) ≤ (a : Int) := by exact_mod_cast hD.ha_ge_h'2
  have hrep_fresh : FreshWord (repeatWord R V) := step_repV_fresh k h h' B bank q p a R hS hD
  refine fresh_append (mass_v0Word h' a) (fresh_v0Word h' a hh'_ge hD.ha_ge_h'2) hrep_fresh ?_
  intro r ϕ hSL_rep hK_V0
  obtain ⟨m, hmR, hSL_V⟩ := sLandAt_repeatWord hmV r ϕ R hSL_rep
  let ϕV := ϕ - (m : Int) * dphiW V r
  have hphi_eq : ϕ = (m : Int) * dphiW V r + ϕV := by dsimp only [ϕV]; omega
  have := hD.hh_ge; have := hD.hh'; have := hS.hlen_ge; have := hD.ha_ge_bank; have := hD.hbank'_lb
  have hSL_r := (keyAt_sLandAt_height_bounds hV_band).2 r ϕV hSL_V
  have hdV0 : dphiW V0 r = 2 + 8 * (a : Int) * (((h' : Int) - 1) - r) + ((h' : Int) - 1) * (((h' : Int) - 1) - 2 * r) :=
    dphiW_v0Word h' a (by omega) ha1 r
  have hb'_cast : ((3 * a - 1 : Nat) : Int) = 3 * (a : Int) - 1 := by omega
  rcases hV0b.2.2 r (dphiW V0 r + ϕ) hK_V0 with
    ⟨rfl, _⟩ | ⟨rfl, _, hKlo⟩ | ⟨rfl, _, hKhi⟩ | ⟨rfl, hKcase⟩ | ⟨rfl, hKcase⟩ | ⟨hr0, hrle, hKcase⟩ | ⟨rfl, hK0⟩
  · omega
  · -- `r = h'`
    have hdVh' : dphiW V (h' : Int) = 1 - (V.length : Int) := by
      rw [hdV_shift, show ((h' : Int) - 1) - (h' : Int) = -1 by omega, Int.mul_neg, Int.mul_one]; omega
    have hm_le0 : (m : Int) * dphiW V (h' : Int) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
    have hSL_Ar : SLandAt (archWord h' a) (h' : Int) (ϕV - dphiW (pref ++ B) (h' : Int)) := by
      rcases (sLandAt_append hmPB (h' : Int) ϕV).mp hSL_V with h1 | h2
      · exfalso; have := (keyAt_sLandAt_height_bounds hPB_band).2 (h' : Int) ϕV h1; omega
      · exact h2
    have hAr_hi : 2 * (ϕV - dphiW (pref ++ B) (h' : Int)) ≤ 2 * (a : Int) - (h' : Int) * ((h' : Int) - 1) := by
      rcases hAr.1 _ _ hSL_Ar with ⟨_, _, hhi⟩ | ⟨_, hlt, _⟩
      · exact hhi
      · omega
    have hdPB_h'm1 : dphiW (pref ++ B) ((h' : Int) - 1) = 1 - 3 * (a : Int) + (h' : Int) * ((h' : Int) - 2) := by
      have h1 : dphiW V ((h' : Int) - 1) = dphiW (pref ++ B) ((h' : Int) - 1) + dphiW (archWord h' a) ((h' : Int) - 1) :=
        dphiW_append hmPB ((h' : Int) - 1)
      rw [hdV_hm1, dphiW_archWord] at h1
      have ha3 : (a : Int) * (1 + 2 * ((h' : Int) - ((h' : Int) - 1))) = 3 * (a : Int) := by
        rw [show 1 + 2 * ((h' : Int) - ((h' : Int) - 1)) = 3 by omega, Int.mul_comm]
      have hh2 : (h' : Int) * ((h' : Int) - 2 * ((h' : Int) - 1)) = -((h' : Int) * ((h' : Int) - 2)) := by
        rw [show (h' : Int) - 2 * ((h' : Int) - 1) = -((h' : Int) - 2) by omega, Int.mul_neg]
      rw [ha3, hh2] at h1; omega
    have hdPB_h' : dphiW (pref ++ B) (h' : Int) = dphiW (pref ++ B) ((h' : Int) - 1) - ((pref ++ B).length : Int) := by
      have := dphiW_sub_shift (pref ++ B) (h' : Int) ((h' : Int) - 1)
      rw [show ((h' : Int) - 1) - (h' : Int) = -1 by omega, Int.mul_neg, Int.mul_one] at this; omega
    have hdV0_simp : dphiW V0 (h' : Int) = 3 - 8 * (a : Int) - (h' : Int) * (h' : Int) := by
      have h1 : 8 * (a : Int) * (((h' : Int) - 1) - (h' : Int)) = -(8 * (a : Int)) := by
        rw [show ((h' : Int) - 1) - (h' : Int) = -1 by omega, Int.mul_neg, Int.mul_one]
      have h2 : ((h' : Int) - 1) * (((h' : Int) - 1) - 2 * (h' : Int)) = 1 - (h' : Int) * (h' : Int) := by
        rw [show ((h' : Int) - 1) - 2 * (h' : Int) = -((h' : Int) + 1) by omega, Int.mul_neg,
          Int.sub_mul, Int.one_mul, Int.mul_add, Int.mul_one]; omega
      rw [hdV0, h1, h2]; omega
    have hq1 : (h' : Int) * ((h' : Int) - 2) = (h' : Int) * (h' : Int) - 2 * (h' : Int) := by
      rw [Int.mul_sub]; omega
    have hq2 : (h' : Int) * ((h' : Int) - 1) = (h' : Int) * (h' : Int) - (h' : Int) := by
      rw [Int.mul_sub, Int.mul_one]
    rw [hb'_cast] at hKlo
    omega
  · -- `r = h' - 1`
    have hSL_Ar : SLandAt (archWord h' a) ((h' : Int) - 1) (ϕV - dphiW (pref ++ B) ((h' : Int) - 1)) := by
      rcases (sLandAt_append hmPB ((h' : Int) - 1) ϕV).mp hSL_V with h1 | h2
      · exfalso; have := (keyAt_sLandAt_height_bounds hPB_band).2 ((h' : Int) - 1) ϕV h1; omega
      · exact h2
    have hphiV_eq : 2 * ϕV = 2 + ((h' : Int) - 1) * (h' : Int) := by
      rcases hAr.1 _ _ hSL_Ar with ⟨hreq, _, _⟩ | ⟨_, _, hphi⟩
      · omega
      · have hsp : dphiW V ((h' : Int) - 1) = dphiW (pref ++ B) ((h' : Int) - 1) + dphiW (archWord h' a) ((h' : Int) - 1) :=
          dphiW_append hmPB ((h' : Int) - 1)
        have hsub : ((h' : Int) - 1) + 1 = (h' : Int) := by omega
        rw [hsub] at hphi; rw [hdV_hm1] at hsp; omega
    have hdV0_simp : dphiW V0 ((h' : Int) - 1) = 2 - ((h' : Int) - 1) * ((h' : Int) - 1) := by
      rw [hdV0, show ((h' : Int) - 1) - ((h' : Int) - 1) = 0 by omega, Int.mul_zero,
        show ((h' : Int) - 1) - 2 * ((h' : Int) - 1) = -((h' : Int) - 1) by omega, Int.mul_neg]; omega
    have hqdiff : ((h' : Int) - 1) * (h' : Int) + ((h' : Int) - 1) * ((h' : Int) - 2) =
        2 * (((h' : Int) - 1) * ((h' : Int) - 1)) := by
      rw [← Int.mul_add, show (h' : Int) + ((h' : Int) - 2) = 2 * ((h' : Int) - 1) by omega,
        ← Int.mul_assoc, Int.mul_comm ((h' : Int) - 1) 2, Int.mul_assoc]
    rw [hdV_hm1] at hphi_eq
    omega
  · -- `r = h' - 2 = h`
    have hdVh : dphiW V ((h' : Int) - 2) = 1 + (V.length : Int) := by
      rw [hdV_shift, show ((h' : Int) - 1) - ((h' : Int) - 2) = 1 by omega, Int.mul_one]
    have hm_nn : 0 ≤ (m : Int) * dphiW V ((h' : Int) - 2) := Int.mul_nonneg (by omega) (by omega)
    have hSL_c := hSL_V_low ((h' : Int) - 2) ϕV (by omega) hSL_V
    have hphiV_lb : -((B.length : Int) + 6 * (bank : Int)) ≤ ϕV := by
      rcases hSL_c with ⟨_, hnn⟩ | ⟨_, hlo, _⟩ | ⟨hreq, _⟩ | ⟨hreq, _⟩ <;> omega
    rcases hKcase with hKle | hKeq
    · rw [hb'_cast] at hKle
      have h31 : ((h' : Int) - 1) * ((h' : Int) - 3) ≤ (h' : Int) * (h' : Int) := by
        have h1 := Int.mul_le_mul_of_nonneg_left (by omega : (h' : Int) - 3 ≤ (h' : Int)) (by omega : (0 : Int) ≤ (h' : Int) - 1)
        have h2 := Int.mul_le_mul_of_nonneg_right (by omega : (h' : Int) - 1 ≤ (h' : Int)) (by omega : (0 : Int) ≤ (h' : Int)); omega
      have hdV0_simp : dphiW V0 ((h' : Int) - 2) = 2 + 8 * (a : Int) - ((h' : Int) - 1) * ((h' : Int) - 3) := by
        rw [hdV0, show ((h' : Int) - 1) - ((h' : Int) - 2) = 1 by omega, Int.mul_one,
          show ((h' : Int) - 1) - 2 * ((h' : Int) - 2) = -((h' : Int) - 3) by omega, Int.mul_neg]; omega
      omega
    · have h2phi : 2 * ϕ = ((h' : Int) - 2) * ((h' : Int) - 1) := by change 2 * (dphiW V0 _ + ϕ) = 2 * dphiW V0 _ + _ at hKeq; omega
      by_cases hm0 : m = 0
      · subst hm0
        have hrr_eq : ((h' : Int) - 2) * (((h' : Int) - 2) + 1) = ((h' : Int) - 2) * ((h' : Int) - 1) := by
          rw [show ((h' : Int) - 2) + 1 = (h' : Int) - 1 by omega]
        have hrr_pos : 0 < ((h' : Int) - 2) * ((h' : Int) - 1) := Int.mul_pos (by omega) (by omega)
        rcases hSL_c with ⟨hpos, _⟩ | ⟨_, _, hhi⟩ | ⟨hreq, _⟩ | ⟨hreq, _⟩
        · have := hpos (by omega); omega
        · omega
        · omega
        · omega
      · have hm1 : dphiW V ((h' : Int) - 2) ≤ (m : Int) * dphiW V ((h' : Int) - 2) := by
          have := Int.mul_le_mul_of_nonneg_right (by omega : (1 : Int) ≤ (m : Int)) (by omega : (0 : Int) ≤ dphiW V ((h' : Int) - 2))
          rwa [Int.one_mul] at this
        have hrr_ub : ((h' : Int) - 2) * ((h' : Int) - 1) ≤ (h' : Int) * (h' : Int) := by
          have h1 := Int.mul_le_mul_of_nonneg_left (by omega : (h' : Int) - 1 ≤ (h' : Int)) (by omega : (0 : Int) ≤ (h' : Int) - 2)
          have h2 := Int.mul_le_mul_of_nonneg_right (by omega : (h' : Int) - 2 ≤ (h' : Int)) (by omega : (0 : Int) ≤ (h' : Int)); omega
        omega
  · -- `r = h' - 3 = h - 1`
    have hdVh1 : dphiW V ((h' : Int) - 3) = 1 + 2 * (V.length : Int) := by
      rw [hdV_shift, show ((h' : Int) - 1) - ((h' : Int) - 3) = 2 by omega, Int.mul_comm]
    have hm_nn : 0 ≤ (m : Int) * dphiW V ((h' : Int) - 3) := Int.mul_nonneg (by omega) (by omega)
    have hSL_c := hSL_V_low ((h' : Int) - 3) ϕV (by omega) hSL_V
    have hphiV_lb : -(6 * (bank : Int)) ≤ ϕV := by
      rcases hSL_c with ⟨_, hnn⟩ | ⟨hreq, _⟩ | ⟨_, hlo, _⟩ | ⟨hreq, _⟩ <;> omega
    rcases hKcase with hKle | hKeq
    · rw [hb'_cast] at hKle
      have h5 : -((h' : Int) * (h' : Int)) ≤ ((h' : Int) - 1) * (5 - (h' : Int)) := by
        have h1 : ((h' : Int) - 1) * (-((h' : Int))) ≤ ((h' : Int) - 1) * (5 - (h' : Int)) :=
          Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
        have h2 : ((h' : Int) - 1) * (h' : Int) ≤ (h' : Int) * (h' : Int) :=
          Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
        rw [Int.mul_neg] at h1; omega
      have hdV0_simp : dphiW V0 ((h' : Int) - 3) = 2 + 16 * (a : Int) + ((h' : Int) - 1) * (5 - (h' : Int)) := by
        rw [hdV0, show ((h' : Int) - 1) - ((h' : Int) - 3) = 2 by omega,
          show ((h' : Int) - 1) - 2 * ((h' : Int) - 3) = 5 - (h' : Int) by omega,
          Int.mul_assoc, Int.mul_comm (a : Int) 2, ← Int.mul_assoc]; omega
      omega
    · have h2phi : 2 * ϕ = ((h' : Int) - 3) * ((h' : Int) - 2) := by change 2 * (dphiW V0 _ + ϕ) = 2 * dphiW V0 _ + _ at hKeq; omega
      by_cases hm0 : m = 0
      · subst hm0
        have hrr_eq : ((h' : Int) - 3) * (((h' : Int) - 3) + 1) = ((h' : Int) - 3) * ((h' : Int) - 2) := by
          rw [show ((h' : Int) - 3) + 1 = (h' : Int) - 2 by omega]
        have hrr_pos : 0 < ((h' : Int) - 3) * ((h' : Int) - 2) := Int.mul_pos (by omega) (by omega)
        rcases hSL_c with ⟨hpos, _⟩ | ⟨hreq, _⟩ | ⟨_, _, hhi⟩ | ⟨hreq, _⟩
        · have := hpos (by omega); omega
        · omega
        · omega
        · omega
      · have hm1 : dphiW V ((h' : Int) - 3) ≤ (m : Int) * dphiW V ((h' : Int) - 3) := by
          have := Int.mul_le_mul_of_nonneg_right (by omega : (1 : Int) ≤ (m : Int)) (by omega : (0 : Int) ≤ dphiW V ((h' : Int) - 3))
          rwa [Int.one_mul] at this
        have hrr_ub : ((h' : Int) - 3) * ((h' : Int) - 2) ≤ (h' : Int) * (h' : Int) := by
          have h1 := Int.mul_le_mul_of_nonneg_left (by omega : (h' : Int) - 2 ≤ (h' : Int)) (by omega : (0 : Int) ≤ (h' : Int) - 3)
          have h2 := Int.mul_le_mul_of_nonneg_right (by omega : (h' : Int) - 3 ≤ (h' : Int)) (by omega : (0 : Int) ≤ (h' : Int)); omega
        omega
  · -- `0 ≤ r ≤ h' - 4 = h - 2`
    have hdVr_ge : 1 + 3 * (V.length : Int) ≤ dphiW V r := by
      rw [hdV_shift r]
      have h1 := Int.mul_le_mul_of_nonneg_left (by omega : 3 ≤ ((h' : Int) - 1) - r) (by omega : (0 : Int) ≤ (V.length : Int))
      rw [Int.mul_comm (V.length : Int) 3] at h1; omega
    have hm_nn : 0 ≤ (m : Int) * dphiW V r := Int.mul_nonneg (by omega) (by omega)
    have hSL_c := hSL_V_low r ϕV (by omega) hSL_V
    have hphiV_lb : -(6 * (bank : Int)) ≤ ϕV := by
      rcases hSL_c with ⟨_, hnn⟩ | ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨_, hlo, _⟩ <;> omega
    rcases hKcase with hKle | hKeq
    · have h8a : 24 * (a : Int) ≤ 8 * (a : Int) * (((h' : Int) - 1) - r) := by
        have h1 := Int.mul_le_mul_of_nonneg_left (by omega : 3 ≤ ((h' : Int) - 1) - r) (by omega : (0 : Int) ≤ 8 * (a : Int))
        have h2 : 8 * (a : Int) * 3 = 24 * (a : Int) := by rw [Int.mul_assoc, Int.mul_comm (a : Int) 3, ← Int.mul_assoc]; omega
        omega
      have hquad : -((h' : Int) * (h' : Int)) ≤ ((h' : Int) - 1) * (((h' : Int) - 1) - 2 * r) := by
        have h1 := Int.mul_le_mul_of_nonneg_left (by omega : -((h' : Int)) ≤ ((h' : Int) - 1) - 2 * r) (by omega : (0 : Int) ≤ (h' : Int) - 1)
        have h2 : ((h' : Int) - 1) * (h' : Int) ≤ (h' : Int) * (h' : Int) := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
        rw [Int.mul_neg] at h1; omega
      omega
    · have h2phi : 2 * ϕ = r * (r + 1) := by change 2 * (dphiW V0 r + ϕ) = 2 * dphiW V0 r + _ at hKeq; omega
      by_cases hm0 : m = 0
      · subst hm0
        have hrr_nn : 0 ≤ r * (r + 1) := Int.mul_nonneg (by omega) (by omega)
        rcases hSL_c with ⟨hpos, _⟩ | ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨_, _, hhi⟩
        · have := hpos hr0; omega
        · omega
        · omega
        · omega
      · have hm1 : dphiW V r ≤ (m : Int) * dphiW V r := by
          have := Int.mul_le_mul_of_nonneg_right (by omega : (1 : Int) ≤ (m : Int)) (by omega : (0 : Int) ≤ dphiW V r)
          rwa [Int.one_mul] at this
        have hrr_ub : r * (r + 1) ≤ (h' : Int) * (h' : Int) := by
          have h1 := Int.mul_le_mul_of_nonneg_left (by omega : r + 1 ≤ (h' : Int)) hr0
          have h2 := Int.mul_le_mul_of_nonneg_right (by omega : r ≤ (h' : Int)) (by omega : (0 : Int) ≤ (h' : Int)); omega
        omega
  · -- `r = -1`
    have hdVm1 : 1 ≤ dphiW V (-1) := by
      rw [hdV_shift (-1)]; have := Int.mul_nonneg (by omega : (0 : Int) ≤ (V.length : Int)) (by omega : (0 : Int) ≤ ((h' : Int) - 1) - (-1)); omega
    have hm_nn : 0 ≤ (m : Int) * dphiW V (-1) := Int.mul_nonneg (by omega) (by omega)
    have hSL_c := hSL_V_low (-1) ϕV (by omega) hSL_V
    have hphiV_nn : 0 ≤ ϕV := by
      rcases hSL_c with ⟨_, hnn⟩ | ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨hreq, _⟩ <;> omega
    have h8a : 48 * (a : Int) ≤ 8 * (a : Int) * (((h' : Int) - 1) - (-1)) := by
      have h1 := Int.mul_le_mul_of_nonneg_left (by omega : 6 ≤ ((h' : Int) - 1) - (-1)) (by omega : (0 : Int) ≤ 8 * (a : Int))
      have h2 : 8 * (a : Int) * 6 = 48 * (a : Int) := by rw [Int.mul_assoc, Int.mul_comm (a : Int) 6, ← Int.mul_assoc]; omega
      omega
    have hquad : 0 ≤ ((h' : Int) - 1) * (((h' : Int) - 1) - 2 * (-1)) := Int.mul_nonneg (by omega) (by omega)
    omega

/-- Helper: verifies all 15 fields of `StageInv (k + 1) B' (3 * a - 1)` for `R = 3 * a - 1` (`E-805`). -/
private theorem step_B'_stageInv (k h h' : Nat) (B : List Bool) (bank q p a : Nat)
    (hS : StageInv k B bank) (hD : StepData k h h' B bank q p a) :
    StageInv (k + 1) (v0Word h' a ++ repeatWord (3 * a - 1) ((asRep q ++ saRep p) ++ B ++ archWord h' a)) (3 * a - 1) := by
  let pref := asRep q ++ saRep p
  let V := pref ++ B ++ archWord h' a
  let V0 := v0Word h' a
  let b' := 3 * a - 1
  let B' := V0 ++ repeatWord b' V
  change StageInv (k + 1) B' b'
  have hC :
      mass V = 0 ∧
      dphiW V ((h' : Int) - 1) = 1 ∧
      FreshWord V ∧
      (∀ i, i ≤ V.length → -1 ≤ wordHeight V i ∧ wordHeight V i ≤ (h' : Int) + 1) ∧
      (∀ r ϕ, r ≤ (h' : Int) - 2 → SLandAt V r ϕ →
        ((0 ≤ r → 2 * ϕ > r * (r + 1)) ∧ 2 * ϕ ≥ 0) ∨
        (r = (h : Int) ∧ -((B.length : Int) + 6 * (bank : Int)) ≤ ϕ ∧ ϕ ≤ 0) ∨
        (r = (h : Int) - 1 ∧ -(6 * (bank : Int)) ≤ ϕ ∧ ϕ < 0) ∨
        (r = (h : Int) - 2 ∧ -(6 * (bank : Int)) ≤ ϕ ∧ ϕ < 0)) ∧
      (∀ r ϕ, r ≤ (h' : Int) - 2 → KeyAt V r ϕ →
        (0 ≤ r ∧ 2 * ϕ = 2 * dphiW V r + r * (r + 1)) ∨
        (r = (h : Int) ∧ ϕ ≤ 0) ∨
        (r = (h : Int) - 1 ∧ ϕ ≤ (bank : Int) + 2) ∨
        (r ≤ (h : Int) - 2 ∧ (ϕ ≤ dphiW (pref ++ B) r + (h : Int) * (h : Int) + 1 ∨ ϕ ≤ (bank : Int) + 40))) ∧
      (∀ ϕ, KeyAt (pref ++ B) (h' : Int) ϕ → False) ∧
      (∀ ϕ, KeyAt (pref ++ B) ((h' : Int) - 1) ϕ → ϕ ≤ 0) ∧
      (∀ i, i ≤ (pref ++ B).length → -1 ≤ wordHeight (pref ++ B) i ∧ wordHeight (pref ++ B) i ≤ (h : Int) + 1) :=
    step_V_core k h h' B bank q p a hS hD
  rcases hC with ⟨hmV, hdV_hm1, _, hV_band, hSL_V_low, hKey_V_low, hKey_PB_h', hKey_PB_h'm1, hPB_band⟩
  have hmPref : mass pref = 0 := (prefix_bounds q p).1
  have hmPB : mass (pref ++ B) = 0 := by rw [mass_append, hmPref, hS.hmass]; rfl
  have hmV0 : mass V0 = 0 := mass_v0Word h' a
  have hh'_ge : 4 ≤ h' := by have := hD.hh_ge; have := hD.hh'; omega
  have ha1 : 1 ≤ a := by have := hD.ha_ge_h'2; have : 16 ≤ h' * h' := Nat.mul_le_mul hh'_ge hh'_ge; omega
  have hAr := archWord_bounds h' a hh'_ge hD.ha_ge_h'2
  have hV0b := v0Word_bounds h' a hh'_ge hD.ha_ge_h'2
  have hdV_shift : ∀ r : Int, dphiW V r = 1 + (V.length : Int) * (((h' : Int) - 1) - r) := by
    intro r; have := dphiW_sub_shift V r ((h' : Int) - 1); rw [hdV_hm1] at this; exact this
  have hlenV : V.length = 2 * q + 2 * p + B.length + 2 * a + 2 * h' := by
    dsimp only [V, pref]; rw [List.length_append, List.length_append, List.length_append,
      asRep_length, saRep_length, archWord_length]; omega
  have hcast_h' : (2 * ((k + 1 : Nat) : Int) + 2) = (h' : Int) := by have := hD.hh; have := hD.hh'; omega
  have hb'_cast : (b' : Int) = 3 * (a : Int) - 1 := by dsimp only [b']; omega
  have hdB' : ∀ r, dphiW B' r = dphiW V0 r + (b' : Int) * dphiW V r := by
    intro r; dsimp only [B']; rw [dphiW_append hmV0, dphiW_repeatWord hmV]
  have hdV0 : ∀ r, dphiW V0 r = 2 + 8 * (a : Int) * (((h' : Int) - 1) - r) + ((h' : Int) - 1) * (((h' : Int) - 1) - 2 * r) :=
    fun r => dphiW_v0Word h' a (by omega) ha1 r
  have hdPB_h'm1 : dphiW (pref ++ B) ((h' : Int) - 1) = 1 - 3 * (a : Int) + (h' : Int) * ((h' : Int) - 2) := by
    have h1 : dphiW V ((h' : Int) - 1) = dphiW (pref ++ B) ((h' : Int) - 1) + dphiW (archWord h' a) ((h' : Int) - 1) :=
      dphiW_append hmPB ((h' : Int) - 1)
    rw [hdV_hm1, dphiW_archWord] at h1
    have ha3 : (a : Int) * (1 + 2 * ((h' : Int) - ((h' : Int) - 1))) = 3 * (a : Int) := by
      rw [show 1 + 2 * ((h' : Int) - ((h' : Int) - 1)) = 3 by omega, Int.mul_comm]
    have hh2 : (h' : Int) * ((h' : Int) - 2 * ((h' : Int) - 1)) = -((h' : Int) * ((h' : Int) - 2)) := by
      rw [show (h' : Int) - 2 * ((h' : Int) - 1) = -((h' : Int) - 2) by omega, Int.mul_neg]
    rw [ha3, hh2] at h1; omega
  have hh'2_lt_bank := stepData_h2_lt_bank hD
  have hh2_nn : (0 : Int) ≤ (h : Int) * (h : Int) := Int.mul_nonneg (by omega) (by omega)
  have hh'2_nn : (0 : Int) ≤ (h' : Int) * (h' : Int) := Int.mul_nonneg (by omega) (by omega)
  have ha_ge_h'2_int : (h' : Int) * (h' : Int) ≤ (a : Int) := by exact_mod_cast hD.ha_ge_h'2
  have := hD.hh_ge; have := hD.hh'; have := hS.hlen_ge; have := hD.ha_ge_bank; have := hD.hbank'_lb
  have hbank_pos : 1 ≤ bank := by
    have h0 := hD.hbank_lg
    have : 1 ≤ (h + 4) * (h + 4) := Nat.mul_pos (by omega) (by omega)
    omega
  have hlenV_ge30 : 30 ≤ V.length := by omega
  have hlenB'_ge : 30 * b' ≤ B'.length := by
    dsimp only [B']; rw [List.length_append, repeatWord_length]
    have := Nat.mul_le_mul_left b' hlenV_ge30; omega
  have hbank'_lg : 20 * (2 * (k + 1) + 6) * (2 * (k + 1) + 6) ≤ b' := by
    have h0 := hD.hbank'_lg
    rw [show 2 * (k + 1) + 6 = h' + 4 by have := hD.hh; omega, Nat.mul_assoc]; exact h0
  have hband' : ∀ i, i ≤ B'.length → -1 ≤ wordHeight B' i ∧ wordHeight B' i ≤ (h' : Int) + 1 :=
    wordHeight_append_band hmV0 (-1) ((h' : Int) + 1)
      (fun i hi => by have := hV0b.1 i hi; change 0 ≤ wordHeight V0 i ∧ wordHeight V0 i ≤ _ at this; omega)
      (wordHeight_repeatWord_band hmV (-1) ((h' : Int) + 1) (by omega) (by omega) hV_band b')
  have hdAr_low : ∀ r : Int, r ≤ (h' : Int) - 4 →
      9 * (a : Int) - (h' : Int) * (h' : Int) ≤ dphiW (archWord h' a) r := by
    intro r hr; rw [dphiW_archWord]
    have h1 : 9 ≤ 1 + 2 * ((h' : Int) - r) := by omega
    have h2 : (a : Int) * 9 ≤ (a : Int) * (1 + 2 * ((h' : Int) - r)) :=
      Int.mul_le_mul_of_nonneg_left h1 (by omega)
    have h2' : 9 * (a : Int) = (a : Int) * 9 := Int.mul_comm _ _
    have h3 : (h' : Int) * (-((h' : Int))) ≤ (h' : Int) * ((h' : Int) - 2 * r) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have h3' : (h' : Int) * (-((h' : Int))) = -((h' : Int) * (h' : Int)) := Int.mul_neg _ _
    omega
  have hq1 : (h' : Int) * ((h' : Int) - 2) = (h' : Int) * (h' : Int) - 2 * (h' : Int) := by
    rw [Int.mul_sub]; omega
  have hq2 : (h' : Int) * ((h' : Int) - 1) = (h' : Int) * (h' : Int) - (h' : Int) := by
    rw [Int.mul_sub, Int.mul_one]
  have hq3 : (h' : Int) * ((h' : Int) + 1) = (h' : Int) * (h' : Int) + (h' : Int) := by
    rw [Int.mul_add, Int.mul_one]
  have hdV0_hm1_eq : dphiW V0 ((h' : Int) - 1) = 2 - ((h' : Int) - 1) * ((h' : Int) - 1) := by
    rw [hdV0, show ((h' : Int) - 1) - ((h' : Int) - 1) = 0 by omega, Int.mul_zero,
      show ((h' : Int) - 1) - 2 * ((h' : Int) - 1) = -((h' : Int) - 1) by omega, Int.mul_neg]; omega
  have hdV0_h'_eq : dphiW V0 (h' : Int) = 3 - 8 * (a : Int) - (h' : Int) * (h' : Int) := by
    have h1 : 8 * (a : Int) * (((h' : Int) - 1) - (h' : Int)) = -(8 * (a : Int)) := by
      rw [show ((h' : Int) - 1) - (h' : Int) = -1 by omega, Int.mul_neg, Int.mul_one]
    have h2 : ((h' : Int) - 1) * (((h' : Int) - 1) - 2 * (h' : Int)) = 1 - (h' : Int) * (h' : Int) := by
      rw [show ((h' : Int) - 1) - 2 * (h' : Int) = -((h' : Int) + 1) by omega, Int.mul_neg,
        Int.sub_mul, Int.one_mul, Int.mul_add, Int.mul_one]; omega
    rw [hdV0, h1, h2]; omega
  have hdV0_hp1_eq : dphiW V0 ((h' : Int) + 1) = 2 - 16 * (a : Int) - ((h' : Int) - 1) * ((h' : Int) + 3) := by
    have h1 : 8 * (a : Int) * (((h' : Int) - 1) - ((h' : Int) + 1)) = -(16 * (a : Int)) := by
      rw [show ((h' : Int) - 1) - ((h' : Int) + 1) = -2 by omega, Int.mul_neg,
        Int.mul_assoc, Int.mul_comm (a : Int) 2, ← Int.mul_assoc]; omega
    have h2 : ((h' : Int) - 1) * (((h' : Int) - 1) - 2 * ((h' : Int) + 1)) = -(((h' : Int) - 1) * ((h' : Int) + 3)) := by
      rw [show ((h' : Int) - 1) - 2 * ((h' : Int) + 1) = -((h' : Int) + 3) by omega, Int.mul_neg]
    rw [hdV0, h1, h2]; omega
  have hdV0_hm2_eq : dphiW V0 ((h' : Int) - 2) = 2 + 8 * (a : Int) - ((h' : Int) - 1) * ((h' : Int) - 3) := by
    rw [hdV0, show ((h' : Int) - 1) - ((h' : Int) - 2) = 1 by omega, Int.mul_one,
      show ((h' : Int) - 1) - 2 * ((h' : Int) - 2) = -((h' : Int) - 3) by omega, Int.mul_neg]; omega
  refine
    { hk := by omega
      hbank_large := hbank'_lg
      hlen_ge := hlenB'_ge
      hmass := by rw [mass_append, hmV0, mass_repeatWord_zero hmV]; rfl
      hfresh := step_B'_fresh k h h' B bank q p a b' hS hD
      hband := by rw [hcast_h']; exact hband'
      hdphi_hm1 := ?_
      hkey_hp1 := ?_
      hkey_h := ?_
      hsland_h := ?_
      hkey_hm1 := ?_
      hsland_hm1 := ?_
      hsland_hm2 := ?_
      hsland_low := ?_
      hkey_le_dphi := ?_ }
  · -- `hdphi_hm1`
    rw [hcast_h', hdB', hdV0_hm1_eq, hdV_hm1, Int.mul_one]
    have h1 : ((h' : Int) - 1) * ((h' : Int) - 1) ≤ (h' : Int) * (h' : Int) := by
      have ha := Int.mul_le_mul_of_nonneg_left (by omega : (h' : Int) - 1 ≤ (h' : Int)) (by omega : (0 : Int) ≤ (h' : Int) - 1)
      have hb := Int.mul_le_mul_of_nonneg_right (by omega : (h' : Int) - 1 ≤ (h' : Int)) (by omega : (0 : Int) ≤ (h' : Int)); omega
    have h2 : 0 ≤ ((h' : Int) - 1) * ((h' : Int) - 1) := Int.mul_nonneg (by omega) (by omega)
    omega
  · -- `hkey_hp1`
    rw [hcast_h']; intro ϕ hK
    rcases (keyAt_append hmV0 ((h' : Int) + 1) ϕ).mp hK with h1 | h2
    · rcases hV0b.2.2 _ _ h1 with ⟨_, hle⟩ | ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨_, hle, _⟩ | ⟨hreq, _⟩ <;> omega
    · rcases keyAt_repeatWord_exists hmV ((h' : Int) + 1) _ b' h2 with ⟨hb0, _, _⟩ | ⟨m, hm, hKm⟩
      · omega
      · have hdVh'p1 : dphiW V ((h' : Int) + 1) = 1 - 2 * (V.length : Int) := by
          rw [hdV_shift, show ((h' : Int) - 1) - ((h' : Int) + 1) = -2 by omega, Int.mul_neg, Int.mul_comm (V.length : Int) 2]; omega
        have hm_le0 : (m : Int) * dphiW V ((h' : Int) + 1) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
        have hK_Ar : KeyAt (archWord h' a) ((h' : Int) + 1) (ϕ - dphiW V0 ((h' : Int) + 1) - (m : Int) * dphiW V ((h' : Int) + 1) - dphiW (pref ++ B) ((h' : Int) + 1)) := by
          rcases (keyAt_append hmPB ((h' : Int) + 1) _).mp hKm with h1 | h2
          · exfalso; have := (keyAt_sLandAt_height_bounds hPB_band).1 ((h' : Int) + 1) _ h1; omega
          · exact h2
        have hAr_le : 2 * (ϕ - dphiW V0 ((h' : Int) + 1) - (m : Int) * dphiW V ((h' : Int) + 1) - dphiW (pref ++ B) ((h' : Int) + 1)) ≤ -((h' : Int) * ((h' : Int) + 1)) := by
          have hneg : -(h' : Int) * ((h' : Int) + 1) = -((h' : Int) * ((h' : Int) + 1)) := Int.neg_mul _ _
          rcases hAr.2 _ _ hK_Ar with ⟨_, hle⟩ | ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨_, hle, _⟩ | ⟨hreq, _⟩ <;> omega
        have hdPB_p1 : dphiW (pref ++ B) ((h' : Int) + 1) = dphiW (pref ++ B) ((h' : Int) - 1) - 2 * ((pref ++ B).length : Int) := by
          have := dphiW_sub_shift (pref ++ B) ((h' : Int) + 1) ((h' : Int) - 1)
          rw [show ((h' : Int) - 1) - ((h' : Int) + 1) = -2 by omega, Int.mul_neg, Int.mul_comm _ 2] at this; omega
        have hnn3 : 0 ≤ ((h' : Int) - 1) * ((h' : Int) + 3) := Int.mul_nonneg (by omega) (by omega)
        omega
  · -- `hkey_h`
    rw [hcast_h']; intro ϕ hK
    rcases (keyAt_append hmV0 (h' : Int) ϕ).mp hK with h1 | h2
    · rcases hV0b.2.2 _ _ h1 with ⟨hreq, _⟩ | ⟨_, hle, _⟩ | ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨_, hle, _⟩ | ⟨hreq, _⟩ <;> omega
    · rcases keyAt_repeatWord_exists hmV (h' : Int) _ b' h2 with ⟨hb0, _, _⟩ | ⟨m, hm, hKm⟩
      · omega
      · have hdVh' : dphiW V (h' : Int) = 1 - (V.length : Int) := by
          rw [hdV_shift, show ((h' : Int) - 1) - (h' : Int) = -1 by omega, Int.mul_neg, Int.mul_one]; omega
        have hm_le0 : (m : Int) * dphiW V (h' : Int) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
        have hK_Ar : KeyAt (archWord h' a) (h' : Int) (ϕ - dphiW V0 (h' : Int) - (m : Int) * dphiW V (h' : Int) - dphiW (pref ++ B) (h' : Int)) := by
          rcases (keyAt_append hmPB (h' : Int) _).mp hKm with h1 | h2
          · exfalso; exact hKey_PB_h' _ h1
          · exact h2
        have hAr_le : 2 * (ϕ - dphiW V0 (h' : Int) - (m : Int) * dphiW V (h' : Int) - dphiW (pref ++ B) (h' : Int)) ≤ 2 * (a : Int) - (h' : Int) * ((h' : Int) - 1) := by
          rcases hAr.2 _ _ hK_Ar with ⟨hreq, _⟩ | ⟨_, _, hhi⟩ | ⟨hreq, _⟩ | ⟨_, hle, _⟩ | ⟨hreq, _⟩ <;> omega
        have hdPB_h' : dphiW (pref ++ B) (h' : Int) = dphiW (pref ++ B) ((h' : Int) - 1) - ((pref ++ B).length : Int) := by
          have := dphiW_sub_shift (pref ++ B) (h' : Int) ((h' : Int) - 1)
          rw [show ((h' : Int) - 1) - (h' : Int) = -1 by omega, Int.mul_neg, Int.mul_one] at this; omega
        omega
  · -- `hsland_h`
    rw [hcast_h']; intro ϕ hSL
    have hdVh' : dphiW V (h' : Int) = 1 - (V.length : Int) := by
      rw [hdV_shift, show ((h' : Int) - 1) - (h' : Int) = -1 by omega, Int.mul_neg, Int.mul_one]; omega
    have hdB'_h' := hdB' (h' : Int)
    rcases (sLandAt_append hmV0 (h' : Int) ϕ).mp hSL with h1 | h2
    · rcases hV0b.2.1 _ _ h1 with ⟨_, hhi, hlo⟩ | ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨_, hle, _⟩
      · have hbn : (b' : Int) * dphiW V (h' : Int) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
        change 2 * ϕ ≥ 2 * dphiW V0 (h' : Int) - 2 * (b' : Int) at hlo
        omega
      · omega
      · omega
      · omega
    · obtain ⟨m, hm, hSLm⟩ := sLandAt_repeatWord hmV (h' : Int) _ b' h2
      have hSL_Ar : SLandAt (archWord h' a) (h' : Int) (ϕ - dphiW V0 (h' : Int) - (m : Int) * dphiW V (h' : Int) - dphiW (pref ++ B) (h' : Int)) := by
        rcases (sLandAt_append hmPB (h' : Int) _).mp hSLm with h1 | h2
        · exfalso; have := (keyAt_sLandAt_height_bounds hPB_band).2 (h' : Int) _ h1; omega
        · exact h2
      have hAr_b : 2 - (h' : Int) * ((h' : Int) - 1) ≤ 2 * (ϕ - dphiW V0 (h' : Int) - (m : Int) * dphiW V (h' : Int) - dphiW (pref ++ B) (h' : Int)) ∧
          2 * (ϕ - dphiW V0 (h' : Int) - (m : Int) * dphiW V (h' : Int) - dphiW (pref ++ B) (h' : Int)) ≤ 2 * (a : Int) - (h' : Int) * ((h' : Int) - 1) := by
        rcases hAr.1 _ _ hSL_Ar with ⟨_, hlo, hhi⟩ | ⟨_, hlt, _⟩
        · exact ⟨hlo, hhi⟩
        · omega
      have hdPB_h' : dphiW (pref ++ B) (h' : Int) = dphiW (pref ++ B) ((h' : Int) - 1) - ((pref ++ B).length : Int) := by
        have := dphiW_sub_shift (pref ++ B) (h' : Int) ((h' : Int) - 1)
        rw [show ((h' : Int) - 1) - (h' : Int) = -1 by omega, Int.mul_neg, Int.mul_one] at this; omega
      have hlenPB : (pref ++ B).length + 2 * a + 2 * h' = V.length := by
        have hVlen : V.length = (pref ++ B).length + (archWord h' a).length := List.length_append
        rw [archWord_length] at hVlen; omega
      have hm_le0 : (m : Int) * dphiW V (h' : Int) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      have hbm : (V.length : Int) - 1 ≤ ((b' : Int) - (m : Int)) * ((V.length : Int) - 1) := by
        have := Int.mul_le_mul_of_nonneg_right (by omega : (1 : Int) ≤ (b' : Int) - (m : Int)) (by omega : (0 : Int) ≤ (V.length : Int) - 1)
        rwa [Int.one_mul] at this
      have hbm_eq : ((b' : Int) - (m : Int)) * ((V.length : Int) - 1) = (m : Int) * dphiW V (h' : Int) - (b' : Int) * dphiW V (h' : Int) := by
        rw [hdVh', Int.sub_mul, show (V.length : Int) - 1 = -(1 - (V.length : Int)) by omega, Int.mul_neg, Int.mul_neg]; omega
      constructor <;> omega
  · -- `hkey_hm1`
    rw [hcast_h']; intro ϕ hK
    rcases (keyAt_append hmV0 ((h' : Int) - 1) ϕ).mp hK with h1 | h2
    · rcases hV0b.2.2 _ _ h1 with ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨_, _, hhi⟩ | ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨_, hle, _⟩ | ⟨hreq, _⟩
      · omega
      · omega
      · have hnn : 0 ≤ ((h' : Int) - 1) * ((h' : Int) - 2) := Int.mul_nonneg (by omega) (by omega); omega
      · omega
      · omega
      · omega
      · omega
    · rcases keyAt_repeatWord_exists hmV ((h' : Int) - 1) _ b' h2 with ⟨hb0, _, _⟩ | ⟨m, hm, hKm⟩
      · omega
      · rw [hdV_hm1, Int.mul_one] at hKm
        rcases (keyAt_append hmPB ((h' : Int) - 1) _).mp hKm with h1 | h2
        · have hle := hKey_PB_h'm1 _ h1
          have hnn : 0 ≤ ((h' : Int) - 1) * ((h' : Int) - 1) := Int.mul_nonneg (by omega) (by omega)
          omega
        · rcases hAr.2 _ _ h2 with ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨_, hle⟩ | ⟨_, hlt, _⟩ | ⟨hreq, _⟩
          · omega
          · omega
          · have hsp : dphiW V ((h' : Int) - 1) = dphiW (pref ++ B) ((h' : Int) - 1) + dphiW (archWord h' a) ((h' : Int) - 1) :=
              dphiW_append hmPB ((h' : Int) - 1)
            rw [hdV_hm1] at hsp
            have hqdiff : ((h' : Int) - 1) * (h' : Int) + ((h' : Int) - 1) * ((h' : Int) - 2) =
                2 * (((h' : Int) - 1) * ((h' : Int) - 1)) := by
              rw [← Int.mul_add, show (h' : Int) + ((h' : Int) - 2) = 2 * ((h' : Int) - 1) by omega,
                ← Int.mul_assoc, Int.mul_comm ((h' : Int) - 1) 2, Int.mul_assoc]
            have hnn : 0 ≤ ((h' : Int) - 1) * ((h' : Int) - 2) := Int.mul_nonneg (by omega) (by omega)
            omega
          · omega
          · omega
  · -- `hsland_hm1`
    rw [hcast_h']; intro ϕ hSL
    rcases (sLandAt_append hmV0 ((h' : Int) - 1) ϕ).mp hSL with h1 | h2
    · rcases hV0b.2.1 _ _ h1 with ⟨hreq, _⟩ | ⟨_, heq⟩ | ⟨hreq, _⟩ | ⟨_, hle, _⟩
      · omega
      · have hnn : 0 ≤ ((h' : Int) - 1) * ((h' : Int) - 2) := Int.mul_nonneg (by omega) (by omega)
        have hub : ((h' : Int) - 1) * ((h' : Int) - 2) ≤ (h' : Int) * (h' : Int) := by
          have ha := Int.mul_le_mul_of_nonneg_left (by omega : (h' : Int) - 2 ≤ (h' : Int)) (by omega : (0 : Int) ≤ (h' : Int) - 1)
          have hb := Int.mul_le_mul_of_nonneg_right (by omega : (h' : Int) - 1 ≤ (h' : Int)) (by omega : (0 : Int) ≤ (h' : Int)); omega
        omega
      · omega
      · omega
    · obtain ⟨m, hm, hSLm⟩ := sLandAt_repeatWord hmV ((h' : Int) - 1) _ b' h2
      rw [hdV_hm1, Int.mul_one] at hSLm
      have hSL_Ar : SLandAt (archWord h' a) ((h' : Int) - 1) (ϕ - dphiW V0 ((h' : Int) - 1) - (m : Int) - dphiW (pref ++ B) ((h' : Int) - 1)) := by
        rcases (sLandAt_append hmPB ((h' : Int) - 1) _).mp hSLm with h1 | h2
        · exfalso; have := (keyAt_sLandAt_height_bounds hPB_band).2 ((h' : Int) - 1) _ h1; omega
        · exact h2
      rcases hAr.1 _ _ hSL_Ar with ⟨hreq, _⟩ | ⟨_, _, hphi⟩
      · omega
      · have hsp : dphiW V ((h' : Int) - 1) = dphiW (pref ++ B) ((h' : Int) - 1) + dphiW (archWord h' a) ((h' : Int) - 1) :=
          dphiW_append hmPB ((h' : Int) - 1)
        rw [hdV_hm1] at hsp
        have hsub : ((h' : Int) - 1) + 1 = (h' : Int) := by omega
        rw [hsub] at hphi
        have hqdiff : ((h' : Int) - 1) * (h' : Int) + ((h' : Int) - 1) * ((h' : Int) - 2) =
            2 * (((h' : Int) - 1) * ((h' : Int) - 1)) := by
          rw [← Int.mul_add, show (h' : Int) + ((h' : Int) - 2) = 2 * ((h' : Int) - 1) by omega,
            ← Int.mul_assoc, Int.mul_comm ((h' : Int) - 1) 2, Int.mul_assoc]
        have hnn : 0 ≤ ((h' : Int) - 1) * ((h' : Int) - 2) := Int.mul_nonneg (by omega) (by omega)
        have hub : ((h' : Int) - 1) * ((h' : Int) - 2) ≤ (h' : Int) * (h' : Int) := by
          have ha := Int.mul_le_mul_of_nonneg_left (by omega : (h' : Int) - 2 ≤ (h' : Int)) (by omega : (0 : Int) ≤ (h' : Int) - 1)
          have hb := Int.mul_le_mul_of_nonneg_right (by omega : (h' : Int) - 1 ≤ (h' : Int)) (by omega : (0 : Int) ≤ (h' : Int)); omega
        omega
  · -- `hsland_hm2`
    rw [hcast_h']; intro ϕ hSL
    have h31 : ((h' : Int) - 1) * ((h' : Int) - 3) ≤ (h' : Int) * (h' : Int) := by
      have ha := Int.mul_le_mul_of_nonneg_left (by omega : (h' : Int) - 3 ≤ (h' : Int)) (by omega : (0 : Int) ≤ (h' : Int) - 1)
      have hb := Int.mul_le_mul_of_nonneg_right (by omega : (h' : Int) - 1 ≤ (h' : Int)) (by omega : (0 : Int) ≤ (h' : Int)); omega
    rcases (sLandAt_append hmV0 ((h' : Int) - 2) ϕ).mp hSL with h1 | h2
    · rcases hV0b.2.1 _ _ h1 with ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨_, hcase⟩ | ⟨_, hle, _⟩
      · omega
      · omega
      · rcases hcase with ⟨hlo, hhi⟩ | heq
        · have hneg : -(h' : Int) * (h' : Int) = -((h' : Int) * (h' : Int)) := Int.neg_mul _ _
          exact ⟨by omega, Or.inl hhi⟩
        · have hnn : 0 ≤ ((h' : Int) - 2) * ((h' : Int) - 1) := Int.mul_nonneg (by omega) (by omega)
          change 2 * ϕ = 2 * dphiW V0 ((h' : Int) - 2) + _ at heq
          exact ⟨by omega, Or.inr (by omega)⟩
      · omega
    · obtain ⟨m, hm, hSLm⟩ := sLandAt_repeatWord hmV ((h' : Int) - 2) _ b' h2
      have hdVh : dphiW V ((h' : Int) - 2) = 1 + (V.length : Int) := by
        rw [hdV_shift, show ((h' : Int) - 1) - ((h' : Int) - 2) = 1 by omega, Int.mul_one]
      have hm_nn : 0 ≤ (m : Int) * dphiW V ((h' : Int) - 2) := Int.mul_nonneg (by omega) (by omega)
      have hphiV_lb : -((B.length : Int) + 6 * (bank : Int)) ≤ ϕ - dphiW V0 ((h' : Int) - 2) - (m : Int) * dphiW V ((h' : Int) - 2) := by
        rcases hSL_V_low ((h' : Int) - 2) _ (by omega) hSLm with ⟨_, hnn⟩ | ⟨_, hlo, _⟩ | ⟨hreq, _⟩ | ⟨hreq, _⟩ <;> omega
      exact ⟨by omega, Or.inr (by omega)⟩
  · -- `hsland_low`
    rw [hcast_h']; intro r ϕ hr hSL
    have hr_ge : -1 ≤ r := ((keyAt_sLandAt_height_bounds hband').2 r ϕ hSL).1
    have h16a : 16 * (a : Int) ≤ 8 * (a : Int) * (((h' : Int) - 1) - r) := by
      have h1 := Int.mul_le_mul_of_nonneg_left (by omega : 2 ≤ ((h' : Int) - 1) - r) (by omega : (0 : Int) ≤ 8 * (a : Int))
      have h2 : 8 * (a : Int) * 2 = 16 * (a : Int) := by rw [Int.mul_assoc, Int.mul_comm (a : Int) 2, ← Int.mul_assoc]; omega
      omega
    have hquad : -((h' : Int) * (h' : Int)) ≤ ((h' : Int) - 1) * (((h' : Int) - 1) - 2 * r) := by
      have h1 := Int.mul_le_mul_of_nonneg_left (by omega : -((h' : Int)) ≤ ((h' : Int) - 1) - 2 * r) (by omega : (0 : Int) ≤ (h' : Int) - 1)
      have h2 : ((h' : Int) - 1) * (h' : Int) ≤ (h' : Int) * (h' : Int) := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      rw [Int.mul_neg] at h1; omega
    have hdV0_r := hdV0 r
    rcases (sLandAt_append hmV0 r ϕ).mp hSL with h1 | h2
    · rcases hV0b.2.1 r ϕ h1 with ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨hr0, _, heq⟩
      · omega
      · omega
      · omega
      · have hnn : 0 ≤ r * (r + 1) := Int.mul_nonneg (by omega) (by omega)
        change 2 * ϕ = 2 * dphiW V0 r + r * (r + 1) at heq; omega
    · obtain ⟨m, hm, hSLm⟩ := sLandAt_repeatWord hmV r _ b' h2
      have hdVr_pos : 1 ≤ dphiW V r := by
        rw [hdV_shift r]; have := Int.mul_nonneg (by omega : (0 : Int) ≤ (V.length : Int)) (by omega : (0 : Int) ≤ ((h' : Int) - 1) - r); omega
      have hm_nn : 0 ≤ (m : Int) * dphiW V r := Int.mul_nonneg (by omega) (by omega)
      have hphiV_lb : -(6 * (bank : Int)) ≤ ϕ - dphiW V0 r - (m : Int) * dphiW V r := by
        rcases hSL_V_low r _ (by omega) hSLm with ⟨_, hnn⟩ | ⟨hreq, _⟩ | ⟨_, hlo, _⟩ | ⟨_, hlo, _⟩ <;> omega
      omega
  · -- `hkey_le_dphi`
    rw [hcast_h']; intro r ϕ hr hK
    have hdVr_ge : 1 + (V.length : Int) ≤ dphiW V r := by
      rw [hdV_shift r]; have := Int.mul_le_mul_of_nonneg_left (by omega : 1 ≤ ((h' : Int) - 1) - r) (by omega : (0 : Int) ≤ (V.length : Int)); omega
    have hbdV_nn : 0 ≤ (b' : Int) * dphiW V r := Int.mul_nonneg (by omega) (by omega)
    have hdB'_r := hdB' r
    have hdV0_r := hdV0 r
    have h8a : 8 * (a : Int) ≤ 8 * (a : Int) * (((h' : Int) - 1) - r) := by
      have h1 := Int.mul_le_mul_of_nonneg_left (by omega : 1 ≤ ((h' : Int) - 1) - r) (by omega : (0 : Int) ≤ 8 * (a : Int))
      rwa [Int.mul_one] at h1
    have hquad : -((h' : Int) * (h' : Int)) ≤ ((h' : Int) - 1) * (((h' : Int) - 1) - 2 * r) := by
      have h1 := Int.mul_le_mul_of_nonneg_left (by omega : -((h' : Int)) ≤ ((h' : Int) - 1) - 2 * r) (by omega : (0 : Int) ≤ (h' : Int) - 1)
      have h2 : ((h' : Int) - 1) * (h' : Int) ≤ (h' : Int) * (h' : Int) := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      rw [Int.mul_neg] at h1; omega
    have hrr_ub : 0 ≤ r → r * (r + 1) ≤ (h' : Int) * (h' : Int) := fun hr0 => by
      have ha := Int.mul_le_mul_of_nonneg_left (by omega : r + 1 ≤ (h' : Int)) hr0
      have hb := Int.mul_le_mul_of_nonneg_right (by omega : r ≤ (h' : Int)) (by omega : (0 : Int) ≤ (h' : Int)); omega
    rcases (keyAt_append hmV0 r ϕ).mp hK with h1 | h2
    · rcases hV0b.2.2 r ϕ h1 with ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨rfl, hcase⟩ | ⟨rfl, hcase⟩ | ⟨hr0, _, hcase⟩ | ⟨rfl, h0⟩
      · omega
      · omega
      · omega
      · rcases hcase with hle | heq
        · omega
        · have := hrr_ub (by omega); have hrr_eq : ((h' : Int) - 2) * (((h' : Int) - 2) + 1) = ((h' : Int) - 2) * ((h' : Int) - 1) := by rw [show ((h' : Int) - 2) + 1 = (h' : Int) - 1 by omega]
          change 2 * ϕ = 2 * dphiW V0 _ + _ at heq; omega
      · rcases hcase with hle | heq
        · have h16a : 16 * (a : Int) ≤ 8 * (a : Int) * (((h' : Int) - 1) - ((h' : Int) - 3)) := by
            rw [show ((h' : Int) - 1) - ((h' : Int) - 3) = 2 by omega, Int.mul_assoc, Int.mul_comm (a : Int) 2, ← Int.mul_assoc]; omega
          omega
        · have := hrr_ub (by omega); have hrr_eq : ((h' : Int) - 3) * (((h' : Int) - 3) + 1) = ((h' : Int) - 3) * ((h' : Int) - 2) := by rw [show ((h' : Int) - 3) + 1 = (h' : Int) - 2 by omega]
          change 2 * ϕ = 2 * dphiW V0 _ + _ at heq; omega
      · rcases hcase with hle | heq
        · omega
        · have := hrr_ub hr0; change 2 * ϕ = 2 * dphiW V0 r + _ at heq; omega
      · omega
    · rcases keyAt_repeatWord_exists hmV r _ b' h2 with ⟨hb0, _, _⟩ | ⟨m, hm, hKm⟩
      · omega
      · have hbm : dphiW V r ≤ ((b' : Int) - (m : Int)) * dphiW V r := by
          have := Int.mul_le_mul_of_nonneg_right (by omega : (1 : Int) ≤ (b' : Int) - (m : Int)) (by omega : (0 : Int) ≤ dphiW V r)
          rwa [Int.one_mul] at this
        have hbm_eq : ((b' : Int) - (m : Int)) * dphiW V r = (b' : Int) * dphiW V r - (m : Int) * dphiW V r := Int.sub_mul _ _ _
        have hpsi_le : ϕ - dphiW V0 r - (m : Int) * dphiW V r ≤ dphiW V r + (h' : Int) * (h' : Int) := by
          rcases hKey_V_low r _ hr hKm with ⟨hr0, heq⟩ | ⟨_, hle⟩ | ⟨_, hle⟩ | ⟨hrle, hle⟩
          · have := hrr_ub hr0; omega
          · omega
          · omega
          · rcases hle with hle1 | hle2
            · have hda := hdAr_low r (by omega)
              have hsp : dphiW V r = dphiW (pref ++ B) r + dphiW (archWord h' a) r := dphiW_append hmPB r
              omega
            · omega
        omega

/-- One-step `Δ = 2` cascade lift with uniform linear-in-`M` ratio bound (`E-805`):
for every `M ≥ 200` and stage `k ≥ 1` satisfying `StageInv k B bank` and `6*M*bank ≤ F ≤ A`,
there exists a stage-`(k+1)` word `B'` with `StageInv (k + 1) B' bank'` and `F'` such that
`2 * (21 * M - 1) * additions B * F' ≤ 3 * (6 * M + 1) * F * additions B'`! -/
private theorem stageInv_step (M k : Nat) (hM : 200 ≤ M) (B : List Bool) (bank F : Nat)
    (hS : StageInv k B bank)
    (hfree : free (wordSign B) 0 B.length ≤ F)
    (hF_ge : 6 * M * bank ≤ F)
    (hF_le : F ≤ additions (wordSign B) 0 B.length) :
    ∃ (B' : List Bool) (bank' F' : Nat),
      StageInv (k + 1) B' bank' ∧
      free (wordSign B') 0 B'.length ≤ F' ∧
      6 * M * bank' ≤ F' ∧
      F' ≤ additions (wordSign B') 0 B'.length ∧
      2 * (21 * M - 1) * additions (wordSign B) 0 B.length * F' ≤
        3 * (6 * M + 1) * F * additions (wordSign B') 0 B'.length := by
  let h := 2 * k + 2
  let h' := h + 2
  obtain ⟨q, p, a, hD⟩ := exists_stepData_aux k h h' rfl rfl B bank hS
  have hC := step_V_core k h h' B bank q p a hS hD
  let pref := asRep q ++ saRep p
  let V := pref ++ B ++ archWord h' a
  let b' := 3 * a - 1
  let B' := v0Word h' a ++ repeatWord b' V
  let F' := (h' + 4 * a - 1) + b' * (q + p + F + h' + 1)
  have hS' : StageInv (k + 1) B' b' := step_B'_stageInv k h h' B bank q p a hS hD
  have hh'_ge : 4 ≤ h' := by have := hD.hh_ge; have := hD.hh'; omega
  have ha1 : 1 ≤ a := by have := hD.ha_ge_h'2; have : 16 ≤ h' * h' := Nat.mul_le_mul hh'_ge hh'_ge; omega
  have hfree' : free (wordSign B') 0 B'.length ≤ F' := by
    have hfl := free_stage_lift_le h' q p a b' B hh'_ge ha1 hS.hmass hC.2.1
    have hmul : b' * (q + p + free (wordSign B) 0 B.length + h' + 1) ≤ b' * (q + p + F + h' + 1) :=
      Nat.mul_le_mul_left b' (by omega)
    dsimp only [B', F', V, pref] at hfl ⊢; omega
  have hbank_ge1 : 1 ≤ bank := by
    have h0 := hD.hbank_lg
    have : 1 ≤ (h + 4) * (h + 4) := Nat.mul_pos (by omega) (by omega)
    omega
  have hF_ge_6M : 6 * M ≤ F := by
    have := Nat.mul_le_mul_left (6 * M) hbank_ge1; omega
  have hF'_ge : 6 * M * b' ≤ F' := by
    have h1 : 6 * M * b' ≤ F * b' := Nat.mul_le_mul_right b' hF_ge_6M
    have h2 : b' * F ≤ b' * (q + p + F + h' + 1) := Nat.mul_le_mul_left b' (by omega)
    have h3 : F * b' = b' * F := Nat.mul_comm F b'
    dsimp only [F']; omega
  let A := additions (wordSign B) 0 B.length
  let A' := additions (wordSign B') 0 B'.length
  have h2A : 2 * A = B.length := additions_eq_half_len_of_mass_zero B hS.hmass
  have h2A' : 2 * A' = B'.length := additions_eq_half_len_of_mass_zero B' hS'.hmass
  have hlenV : V.length = 2 * q + 2 * p + B.length + 2 * a + 2 * h' := by
    dsimp only [V, pref]; rw [List.length_append, List.length_append, List.length_append,
      asRep_length, saRep_length, archWord_length]; omega
  have hlenB' : B'.length = (2 * h' - 2 + 8 * a) + b' * V.length := by
    dsimp only [B']; rw [List.length_append, v0Word_length h' a (by omega) ha1, repeatWord_length]
  have hA'_eq : A' = (h' + 4 * a - 1) + b' * (q + p + A + a + h') := by
    have hmul : b' * V.length = 2 * (b' * (q + p + A + a + h')) := by
      have : V.length = 2 * (q + p + A + a + h') := by omega
      rw [this]; grind
    omega
  have hF'_le : F' ≤ A' := by
    have h1 : b' * (q + p + F + h' + 1) ≤ b' * (q + p + A + a + h') := Nat.mul_le_mul_left b' (by omega)
    dsimp only [F']; omega
  -- Key step 1: `b' * (21 * M - 1) * A ≤ 9 * M * A'`
  have hA'_lb : b' * (A + a) ≤ A' := by
    have := Nat.mul_le_mul_left b' (by omega : A + a ≤ q + p + A + a + h'); omega
  have h3Aa : 7 * A ≤ 3 * (A + a) + (bank + 1) := by have := hD.hbank'_lb; omega
  have h3M_bank : 3 * M * (bank + 1) ≤ A := by
    have h1 : bank + 1 ≤ 2 * bank := by omega
    have h2 : 3 * M * (bank + 1) ≤ 3 * M * (2 * bank) := Nat.mul_le_mul_left (3 * M) h1
    have h3 : 3 * M * (2 * bank) = 6 * M * bank := by grind
    omega
  have h9MAa : (21 * M - 1) * A ≤ 9 * M * (A + a) := by
    have h1 := Nat.mul_le_mul_left (3 * M) h3Aa
    have hl : 3 * M * (7 * A) = 21 * M * A := by grind
    have hr : 3 * M * (3 * (A + a) + (bank + 1)) = 9 * M * (A + a) + 3 * M * (bank + 1) := by grind
    have hsub : (21 * M - 1) * A + A = 21 * M * A := by
      rw [Nat.sub_mul, Nat.one_mul, Nat.sub_add_cancel (by
        have := Nat.mul_le_mul_right A (by omega : 1 ≤ 21 * M); omega)]
    omega
  have hStep1 : b' * (21 * M - 1) * A ≤ 9 * M * A' := by
    have h1 := Nat.mul_le_mul_left b' h9MAa
    have h2 := Nat.mul_le_mul_left (9 * M) hA'_lb
    have heq1 : b' * ((21 * M - 1) * A) = b' * (21 * M - 1) * A := by grind
    have heq2 : b' * (9 * M * (A + a)) = 9 * M * (b' * (A + a)) := by grind
    omega
  -- Key step 2: `6 * M * F' ≤ b' * (6 * M + 1) * F`
  have hqph_le_bank : q + p + h' + 3 ≤ bank := by
    have := hD.hq2; have := hD.hp_small; have := hD.hh'; have := hD.hh_ge
    have h1 : 8 * (h + 4) ≤ (h + 4) * (h + 4) := Nat.mul_le_mul_right (h + 4) (by omega)
    have h2 := Nat.mul_le_mul_left 20 h1
    have := hD.hbank_lg; omega
  have hF'_ub1 : F' ≤ b' * (F + bank) := by
    have hhead : h' + 4 * a - 1 ≤ 2 * b' := by
      have : h' ≤ a := by have := hD.ha_ge_h'2; have : h' ≤ h' * h' := Nat.le_mul_self h'; omega
      dsimp only [b']; omega
    have htail : b' * (q + p + F + h' + 1) + 2 * b' = b' * (F + (q + p + h' + 3)) := by grind
    have hle := Nat.mul_le_mul_left b' (by omega : F + (q + p + h' + 3) ≤ F + bank)
    dsimp only [F']; omega
  have hStep2 : 6 * M * F' ≤ b' * (6 * M + 1) * F := by
    have h1 := Nat.mul_le_mul_left (6 * M) hF'_ub1
    have h2 : 6 * M * (F + bank) ≤ (6 * M + 1) * F := by
      have hl : 6 * M * (F + bank) = 6 * M * F + 6 * M * bank := by grind
      have hr : (6 * M + 1) * F = 6 * M * F + F := by grind
      omega
    have h3 := Nat.mul_le_mul_left b' h2
    have heq1 : 6 * M * (b' * (F + bank)) = b' * (6 * M * (F + bank)) := by grind
    have heq2 : b' * ((6 * M + 1) * F) = b' * (6 * M + 1) * F := by grind
    omega
  -- Combine `hStep1` and `hStep2` and cancel `3 * M`:
  have hRatio : 2 * (21 * M - 1) * A * F' ≤ 3 * (6 * M + 1) * F * A' := by
    have hmul1 : (21 * M - 1) * A * (6 * M * F') ≤ (21 * M - 1) * A * (b' * (6 * M + 1) * F) :=
      Nat.mul_le_mul_left ((21 * M - 1) * A) hStep2
    have hmul2 : (6 * M + 1) * F * (b' * (21 * M - 1) * A) ≤ (6 * M + 1) * F * (9 * M * A') :=
      Nat.mul_le_mul_left ((6 * M + 1) * F) hStep1
    have hcomb : (3 * M) * (2 * (21 * M - 1) * A * F') ≤ (3 * M) * (3 * (6 * M + 1) * F * A') := by
      have hl : (3 * M) * (2 * (21 * M - 1) * A * F') = (21 * M - 1) * A * (6 * M * F') := by grind
      have hm : (21 * M - 1) * A * (b' * (6 * M + 1) * F) = (6 * M + 1) * F * (b' * (21 * M - 1) * A) := by grind
      have hr : (6 * M + 1) * F * (9 * M * A') = (3 * M) * (3 * (6 * M + 1) * F * A') := by grind
      omega
    exact Nat.le_of_mul_le_mul_left hcomb (by omega)
  exact ⟨B', b', F', hS', hfree', hF'_ge, hF'_le, hRatio⟩

/-- Base stage `k = 1` (`h = 4`, `q = 0, p = 0, a = 10*M + 3`, `bank = 30*M + 8`) (`E-805`). -/
private theorem stageInv_base (M : Nat) (hM : 200 ≤ M) :
    ∃ (B : List Bool) (bank F : Nat),
      StageInv 1 B bank ∧
      free (wordSign B) 0 B.length ≤ F ∧
      6 * M * bank ≤ F ∧
      F ≤ additions (wordSign B) 0 B.length := by
  let a := 10 * M + 3
  let b1 := 3 * a - 1
  let B0 := asRep (6 * M)
  let V := B0 ++ archWord 4 a
  let V0 := v0Word 4 a
  let B1 := V0 ++ repeatWord b1 V
  have ha1 : 1 ≤ a := by dsimp only [a]; omega
  have ha16 : 4 * 4 ≤ a := by dsimp only [a]; omega
  have hmB0 : mass B0 = 0 := mass_asRep (6 * M)
  have hmV : mass V = 0 := by dsimp only [V]; rw [mass_append, hmB0, mass_archWord]; rfl
  have hmV0 : mass V0 = 0 := mass_v0Word 4 a
  have hB0s := asRep_keyAt_sLandAt_fresh (6 * M)
  have hAr := archWord_bounds 4 a (by omega) ha16
  have hV0b := v0Word_bounds 4 a (by omega) ha16
  push_cast at hAr hV0b
  have hdV3 : dphiW V 3 = 1 := by
    dsimp only [V, B0]; rw [dphiW_append (mass_asRep (6 * M)), dphiW_asRep, dphiW_archWord]
    dsimp only [a]; grind
  have hlenV : V.length = 32 * M + 14 := by
    dsimp only [V, B0]; rw [List.length_append, asRep_length, archWord_length]; dsimp only [a]; omega
  have hdV_shift : ∀ r : Int, dphiW V r = 1 + (V.length : Int) * (3 - r) := by
    intro r; have := dphiW_sub_shift V r 3; rw [hdV3] at this; exact this
  have hB0_band : ∀ i, i ≤ B0.length → 0 ≤ wordHeight B0 i ∧ wordHeight B0 i ≤ 1 :=
    fun i hi => wordHeight_asRep_band (6 * M) i hi
  have hV_band : ∀ i, i ≤ V.length → -1 ≤ wordHeight V i ∧ wordHeight V i ≤ 5 :=
    wordHeight_append_band hmB0 (-1) 5
      (fun i hi => by have := hB0_band i hi; omega)
      (fun i hi => by have := wordHeight_archWord 4 a i hi; omega)
  have hFresh_V : FreshWord V := by
    refine fresh_append hmB0 hB0s.1 (fresh_archWord 4 a (by omega) ha16) ?_
    intro r ϕ hSL hK
    rcases hAr.1 r ϕ hSL with ⟨rfl, _, _⟩ | ⟨hr0, hr4, hphi⟩
    · rcases hB0s.2.1 4 _ hK with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    · have hsp : dphiW V r = dphiW B0 r + dphiW (archWord 4 a) r := dphiW_append hmB0 r
      have hdv := hdV_shift r
      rcases hB0s.2.1 r (dphiW B0 r + ϕ) hK with ⟨rfl, _, _⟩ | ⟨rfl, _, hhi⟩ | ⟨rfl, _, hhi⟩
      · omega
      · omega
      · omega
  have hSL_V_low : ∀ r ϕ, r ≤ 2 → SLandAt V r ϕ → 0 ≤ r ∧ 2 * ϕ > r * (r + 1) := by
    intro r ϕ hr hSL
    rcases (sLandAt_append hmB0 r ϕ).mp hSL with h1 | h2
    · have := hB0s.2.2 r ϕ h1; rcases this with ⟨rfl, hlo, _⟩; exact ⟨by omega, by omega⟩
    · rcases hAr.1 r _ h2 with ⟨rfl, _, _⟩ | ⟨hr0, _, hphi⟩
      · omega
      · have hsp : dphiW V r = dphiW B0 r + dphiW (archWord 4 a) r := dphiW_append hmB0 r
        have hdv := hdV_shift r
        have hd_pos : 1 ≤ dphiW V r := by
          have := Int.mul_nonneg (by omega : (0 : Int) ≤ (V.length : Int)) (by omega : (0 : Int) ≤ 3 - r); omega
        exact ⟨hr0, by omega⟩
  have hKey_V_low : ∀ r ϕ, r ≤ 2 → KeyAt V r ϕ →
      (0 ≤ r ∧ 2 * ϕ = 2 * dphiW V r + r * (r + 1)) ∨ ϕ ≤ 18 * (M : Int) + 1 := by
    intro r ϕ hr hK
    rcases (keyAt_append hmB0 r ϕ).mp hK with h1 | h2
    · right; rcases hB0s.2.1 r ϕ h1 with ⟨rfl, _, hhi⟩ | ⟨rfl, _, hhi⟩ | ⟨rfl, _, hhi⟩ <;> omega
    · have hdB0 : dphiW B0 r = 6 * (M : Int) * (1 - 2 * r) := by dsimp only [B0]; rw [dphiW_asRep]; grind
      rcases hAr.2 r _ h2 with ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨hr0, _, hcase⟩ | ⟨rfl, h0⟩
      · omega
      · omega
      · omega
      · rcases hcase with hle | heq
        · right
          have h1 := Int.mul_le_mul_of_nonneg_left (by omega : 1 - 2 * r ≤ 1) (by omega : (0 : Int) ≤ 6 * (M : Int))
          rw [Int.mul_one] at h1; omega
        · left; have hsp : dphiW V r = dphiW B0 r + dphiW (archWord 4 a) r := dphiW_append hmB0 r; exact ⟨hr0, by omega⟩
      · right; omega
  have hFresh_rep : FreshWord (repeatWord b1 V) := by
    refine fresh_repeatWord hmV hFresh_V (fun c hc r ϕ hSL hK => ?_) b1
    have hSL_r := (keyAt_sLandAt_height_bounds hV_band).2 r ϕ hSL
    by_cases hr4 : r = 4
    · rw [hr4] at hSL hK
      have hdV4 : dphiW V 4 = 1 - (V.length : Int) := by have := hdV_shift 4; omega
      have hSL_Ar : SLandAt (archWord 4 a) 4 (ϕ - dphiW B0 4) := by
        rcases (sLandAt_append hmB0 4 ϕ).mp hSL with h1 | h2
        · exfalso; have := hB0s.2.2 4 ϕ h1; omega
        · exact h2
      have hK_Ar : KeyAt (archWord 4 a) 4 (ϕ + (c : Int) * dphiW V 4 - dphiW B0 4) := by
        rcases (keyAt_append hmB0 4 _).mp hK with h1 | h2
        · exfalso; rcases hB0s.2.1 4 _ h1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
        · exact h2
      have h1 : 2 * (ϕ - dphiW B0 4) ≤ 2 * (a : Int) - 12 := by
        rcases hAr.1 _ _ hSL_Ar with ⟨_, _, hhi⟩ | ⟨_, hlt, _⟩
        · omega
        · omega
      have h2 : 2 * (ϕ + (c : Int) * dphiW V 4 - dphiW B0 4) ≥ -12 := by
        rcases hAr.2 _ _ hK_Ar with ⟨hreq, _⟩ | ⟨_, hlo, _⟩ | ⟨hreq, _⟩ | ⟨_, hle, _⟩ | ⟨hreq, _⟩ <;> omega
      have hcd : (c : Int) * dphiW V 4 ≤ 1 - (V.length : Int) := by
        rw [hdV4]; have := Int.mul_le_mul_of_nonpos_right (by omega : (1 : Int) ≤ (c : Int)) (by omega : 1 - (V.length : Int) ≤ 0); omega
      dsimp only [a] at h1; omega
    · by_cases hr3 : r = 3
      · rw [hr3] at hSL hK
        have hSL_Ar : SLandAt (archWord 4 a) 3 (ϕ - dphiW B0 3) := by
          rcases (sLandAt_append hmB0 3 ϕ).mp hSL with h1 | h2
          · exfalso; have := hB0s.2.2 3 ϕ h1; omega
          · exact h2
        have hphi_eq : 2 * ϕ = 14 := by
          rcases hAr.1 _ _ hSL_Ar with ⟨hreq, _⟩ | ⟨_, _, hphi⟩
          · omega
          · have hsp : dphiW V 3 = dphiW B0 3 + dphiW (archWord 4 a) 3 := dphiW_append hmB0 3; rw [hdV3] at hsp; omega
        have hpsi_le : 2 * (ϕ + (c : Int) * dphiW V 3) ≤ 14 := by
          rcases (keyAt_append hmB0 3 _).mp hK with h1 | h2
          · exfalso; rcases hB0s.2.1 3 _ h1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
          · rcases hAr.2 _ _ h2 with ⟨hreq, _⟩ | ⟨hreq, _⟩ | ⟨_, hle⟩ | ⟨_, hlt, _⟩ | ⟨hreq, _⟩
            · omega
            · omega
            · have hsp : dphiW V 3 = dphiW B0 3 + dphiW (archWord 4 a) 3 := dphiW_append hmB0 3; rw [hdV3] at hsp; omega
            · omega
            · omega
        rw [hdV3] at hpsi_le; omega
      · have hr2 : r ≤ 2 := by omega
        obtain ⟨hr0, hgt⟩ := hSL_V_low r ϕ hr2 hSL
        have hrr_nn : 0 ≤ r * (r + 1) := Int.mul_nonneg hr0 (by omega)
        have hdV_ge : 1 + (V.length : Int) ≤ dphiW V r := by
          rw [hdV_shift r]; have := Int.mul_le_mul_of_nonneg_left (by omega : 1 ≤ 3 - r) (by omega : (0 : Int) ≤ (V.length : Int)); omega
        have hc_ge : dphiW V r ≤ (c : Int) * dphiW V r := by
          have := Int.mul_le_mul_of_nonneg_right (by omega : (1 : Int) ≤ (c : Int)) (by omega : (0 : Int) ≤ dphiW V r)
          rwa [Int.one_mul] at this
        rcases hKey_V_low r (ϕ + (c : Int) * dphiW V r) hr2 hK with ⟨_, heq⟩ | hle <;> omega
  have hdV0 : ∀ r, dphiW V0 r = 2 + 8 * (a : Int) * (3 - r) + 3 * (3 - 2 * r) := by
    intro r; have := dphiW_v0Word 4 a (by omega) ha1 r; push_cast at this; grind
  have hb1_cast : (b1 : Int) = 3 * (a : Int) - 1 := by dsimp only [b1]; omega
  have hFresh_B1 : FreshWord B1 := by
    refine fresh_append hmV0 (fresh_v0Word 4 a (by omega) ha16) hFresh_rep ?_
    intro r ϕ hSL_rep hK_V0
    obtain ⟨m, hm, hSL_V⟩ := sLandAt_repeatWord hmV r ϕ b1 hSL_rep
    let ϕV := ϕ - (m : Int) * dphiW V r
    have hphi_eq : ϕ = (m : Int) * dphiW V r + ϕV := by dsimp only [ϕV]; omega
    have hSL_r := (keyAt_sLandAt_height_bounds hV_band).2 r ϕV hSL_V
    have hdV0r := hdV0 r
    rcases hV0b.2.2 r (dphiW V0 r + ϕ) hK_V0 with
      ⟨rfl, _⟩ | ⟨rfl, _, hKlo⟩ | ⟨rfl, _, hKhi⟩ | ⟨rfl, hKcase⟩ | ⟨rfl, hKcase⟩ | ⟨hr0, hrle, hKcase⟩ | ⟨rfl, _⟩
    · omega
    · -- `r = 4`
      have hdV4 : dphiW V 4 = 1 - (V.length : Int) := by have := hdV_shift 4; omega
      have hm_le0 : (m : Int) * dphiW V 4 ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      have hSL_Ar : SLandAt (archWord 4 a) 4 (ϕV - dphiW B0 4) := by
        rcases (sLandAt_append hmB0 4 ϕV).mp hSL_V with h1 | h2
        · exfalso; have := hB0s.2.2 4 ϕV h1; omega
        · exact h2
      have hAr_hi : 2 * (ϕV - dphiW B0 4) ≤ 2 * (a : Int) - 12 := by
        rcases hAr.1 _ _ hSL_Ar with ⟨_, _, hhi⟩ | ⟨_, hlt, _⟩
        · omega
        · omega
      have hdB04 : dphiW B0 4 = -42 * (M : Int) := by dsimp only [B0]; rw [dphiW_asRep]; grind
      dsimp only [a, b1] at hKlo hAr_hi hdV0r ⊢; omega
    · -- `r = 3`
      have hSL_Ar : SLandAt (archWord 4 a) 3 (ϕV - dphiW B0 3) := by
        rcases (sLandAt_append hmB0 3 ϕV).mp hSL_V with h1 | h2
        · exfalso; have := hB0s.2.2 3 ϕV h1; omega
        · exact h2
      have hphiV_eq : 2 * ϕV = 14 := by
        rcases hAr.1 _ _ hSL_Ar with ⟨hreq, _⟩ | ⟨_, _, hphi⟩
        · omega
        · have hsp : dphiW V 3 = dphiW B0 3 + dphiW (archWord 4 a) 3 := dphiW_append hmB0 3; rw [hdV3] at hsp; omega
      rw [hdV3] at hphi_eq; omega
    · -- `r = 2`
      obtain ⟨_, hgt⟩ := hSL_V_low 2 ϕV (by omega) hSL_V
      have hdV2 : dphiW V 2 = 1 + (V.length : Int) := by have := hdV_shift 2; omega
      have hm_nn : 0 ≤ (m : Int) * dphiW V 2 := Int.mul_nonneg (by omega) (by omega)
      rcases hKcase with hKle | hKeq
      · dsimp only [a] at hKle hdV0r ⊢; omega
      · change 2 * (dphiW V0 2 + ϕ) = 2 * dphiW V0 2 + _ at hKeq; omega
    · -- `r = 1`
      obtain ⟨_, hgt⟩ := hSL_V_low 1 ϕV (by omega) hSL_V
      have hdV1 : dphiW V 1 = 1 + 2 * (V.length : Int) := by have := hdV_shift 1; omega
      have hm_nn : 0 ≤ (m : Int) * dphiW V 1 := Int.mul_nonneg (by omega) (by omega)
      rcases hKcase with hKle | hKeq
      · dsimp only [a] at hKle hdV0r ⊢; omega
      · change 2 * (dphiW V0 1 + ϕ) = 2 * dphiW V0 1 + _ at hKeq; omega
    · -- `r = 0`
      have hr_eq : r = 0 := by omega
      subst hr_eq
      obtain ⟨_, hgt⟩ := hSL_V_low 0 ϕV (by omega) hSL_V
      have hdV0' : dphiW V 0 = 1 + 3 * (V.length : Int) := by have := hdV_shift 0; omega
      have hm_nn : 0 ≤ (m : Int) * dphiW V 0 := Int.mul_nonneg (by omega) (by omega)
      rcases hKcase with hKle | hKeq
      · dsimp only [a] at hKle hdV0r ⊢; omega
      · change 2 * (dphiW V0 0 + ϕ) = 2 * dphiW V0 0 + _ at hKeq; omega
    · -- `r = -1`: impossible since `hSL_V_low` gives `0 ≤ r`!
      obtain ⟨hr0, _⟩ := hSL_V_low (-1) ϕV (by omega) hSL_V; omega
  have hdB1 : ∀ r, dphiW B1 r = dphiW V0 r + (b1 : Int) * dphiW V r := by
    intro r; dsimp only [B1]; rw [dphiW_append hmV0, dphiW_repeatWord hmV]
  have hband1 : ∀ i, i ≤ B1.length → -1 ≤ wordHeight B1 i ∧ wordHeight B1 i ≤ 5 :=
    wordHeight_append_band hmV0 (-1) 5
      (fun i hi => by have := hV0b.1 i hi; change 0 ≤ wordHeight V0 i ∧ wordHeight V0 i ≤ _ at this; omega)
      (wordHeight_repeatWord_band hmV (-1) 5 (by omega) (by omega) hV_band b1)
  have hS1 : StageInv 1 B1 b1 := by
    refine
      { hk := by omega
        hbank_large := by dsimp only [b1, a]; omega
        hlen_ge := by
          dsimp only [B1]; rw [List.length_append, repeatWord_length]
          have := Nat.mul_le_mul_left b1 (by omega : 30 ≤ V.length); omega
        hmass := by dsimp only [B1]; rw [mass_append, hmV0, mass_repeatWord_zero hmV]; rfl
        hfresh := hFresh_B1
        hband := by simpa using hband1
        hdphi_hm1 := ?_
        hkey_hp1 := ?_
        hkey_h := ?_
        hsland_h := ?_
        hkey_hm1 := ?_
        hsland_hm1 := ?_
        hsland_hm2 := ?_
        hsland_low := ?_
        hkey_le_dphi := ?_ }
    · -- `hdphi_hm1`
      have h1 := hdB1 3; have h2 := hdV0 3; rw [hdV3] at h1
      change -((4 : Int) * 4) ≤ dphiW B1 3 ∧ dphiW B1 3 ≤ (b1 : Int) + 2; omega
    · -- `hkey_hp1`
      change ∀ ϕ, KeyAt B1 5 ϕ → ϕ ≤ 0; intro ϕ hK
      rcases (keyAt_append hmV0 5 ϕ).mp hK with h1 | h2
      · rcases hV0b.2.2 _ _ h1 with ⟨_, hle⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨h, _⟩ <;> omega
      · rcases keyAt_repeatWord_exists hmV 5 _ b1 h2 with ⟨hb0, _, _⟩ | ⟨m, hm, hKm⟩
        · dsimp only [b1, a] at hb0; omega
        · have hdV5 : dphiW V 5 = 1 - 2 * (V.length : Int) := by have := hdV_shift 5; omega
          have hm_le0 : (m : Int) * dphiW V 5 ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
          have hK_Ar : KeyAt (archWord 4 a) 5 (ϕ - dphiW V0 5 - (m : Int) * dphiW V 5 - dphiW B0 5) := by
            rcases (keyAt_append hmB0 5 _).mp hKm with h1 | h2
            · exfalso; rcases hB0s.2.1 5 _ h1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
            · exact h2
          have hAr_le : 2 * (ϕ - dphiW V0 5 - (m : Int) * dphiW V 5 - dphiW B0 5) ≤ -20 := by
            rcases hAr.2 _ _ hK_Ar with ⟨_, hle⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨h, _⟩ <;> omega
          have hdB05 : dphiW B0 5 = -54 * (M : Int) := by dsimp only [B0]; rw [dphiW_asRep]; grind
          have hdV05 := hdV0 5; dsimp only [a] at hdV05; omega
    · -- `hkey_h`
      change ∀ ϕ, KeyAt B1 4 ϕ → ϕ ≤ 0; intro ϕ hK
      rcases (keyAt_append hmV0 4 ϕ).mp hK with h1 | h2
      · rcases hV0b.2.2 _ _ h1 with ⟨h, _⟩ | ⟨_, hle, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨h, _⟩ <;> omega
      · rcases keyAt_repeatWord_exists hmV 4 _ b1 h2 with ⟨hb0, _, _⟩ | ⟨m, hm, hKm⟩
        · dsimp only [b1, a] at hb0; omega
        · have hdV4 : dphiW V 4 = 1 - (V.length : Int) := by have := hdV_shift 4; omega
          have hm_le0 : (m : Int) * dphiW V 4 ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
          have hK_Ar : KeyAt (archWord 4 a) 4 (ϕ - dphiW V0 4 - (m : Int) * dphiW V 4 - dphiW B0 4) := by
            rcases (keyAt_append hmB0 4 _).mp hKm with h1 | h2
            · exfalso; rcases hB0s.2.1 4 _ h1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
            · exact h2
          have hAr_le : 2 * (ϕ - dphiW V0 4 - (m : Int) * dphiW V 4 - dphiW B0 4) ≤ 2 * (a : Int) - 12 := by
            rcases hAr.2 _ _ hK_Ar with ⟨h, _⟩ | ⟨_, _, hhi⟩ | ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨h, _⟩ <;> omega
          have hdB04 : dphiW B0 4 = -42 * (M : Int) := by dsimp only [B0]; rw [dphiW_asRep]; grind
          have hdV04 := hdV0 4; dsimp only [a] at hdV04 hAr_le; omega
    · -- `hsland_h`
      change ∀ ϕ, SLandAt B1 4 ϕ → dphiW B1 4 - (b1 : Int) ≤ ϕ ∧ ϕ ≤ 0; intro ϕ hSL
      have hdV4 : dphiW V 4 = 1 - (V.length : Int) := by have := hdV_shift 4; omega
      have hdB14 := hdB1 4; have hdV04 := hdV0 4
      rcases (sLandAt_append hmV0 4 ϕ).mp hSL with h1 | h2
      · rcases hV0b.2.1 _ _ h1 with ⟨_, hhi, hlo⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h, _⟩
        · have hbn : (b1 : Int) * dphiW V 4 ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
          change 2 * ϕ ≥ 2 * dphiW V0 4 - 2 * (b1 : Int) at hlo
          omega
        · omega
        · omega
        · omega
      · obtain ⟨m, hm, hSLm⟩ := sLandAt_repeatWord hmV 4 _ b1 h2
        have hSL_Ar : SLandAt (archWord 4 a) 4 (ϕ - dphiW V0 4 - (m : Int) * dphiW V 4 - dphiW B0 4) := by
          rcases (sLandAt_append hmB0 4 _).mp hSLm with h1 | h2
          · exfalso; have := hB0s.2.2 4 _ h1; omega
          · exact h2
        have hAr_b : -10 ≤ 2 * (ϕ - dphiW V0 4 - (m : Int) * dphiW V 4 - dphiW B0 4) ∧
            2 * (ϕ - dphiW V0 4 - (m : Int) * dphiW V 4 - dphiW B0 4) ≤ 2 * (a : Int) - 12 := by
          rcases hAr.1 _ _ hSL_Ar with ⟨_, hlo, hhi⟩ | ⟨_, hlt, _⟩
          · exact ⟨by omega, by omega⟩
          · omega
        have hdB04 : dphiW B0 4 = -42 * (M : Int) := by dsimp only [B0]; rw [dphiW_asRep]; grind
        have hm_le0 : (m : Int) * dphiW V 4 ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
        have hbm : (V.length : Int) - 1 ≤ ((b1 : Int) - (m : Int)) * ((V.length : Int) - 1) := by
          have := Int.mul_le_mul_of_nonneg_right (by omega : (1 : Int) ≤ (b1 : Int) - (m : Int)) (by omega : (0 : Int) ≤ (V.length : Int) - 1)
          rwa [Int.one_mul] at this
        have hbm_eq : ((b1 : Int) - (m : Int)) * ((V.length : Int) - 1) = (m : Int) * dphiW V 4 - (b1 : Int) * dphiW V 4 := by
          rw [hdV4, Int.sub_mul, show (V.length : Int) - 1 = -(1 - (V.length : Int)) by omega, Int.mul_neg, Int.mul_neg]; omega
        dsimp only [a] at hdV04 hAr_b hb1_cast ⊢
        constructor <;> omega
    · -- `hkey_hm1`
      change ∀ ϕ, KeyAt B1 3 ϕ → ϕ ≤ (b1 : Int) + 2; intro ϕ hK
      have hdV03 := hdV0 3
      rcases (keyAt_append hmV0 3 ϕ).mp hK with h1 | h2
      · rcases hV0b.2.2 _ _ h1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, hhi⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨h, _⟩ <;> omega
      · rcases keyAt_repeatWord_exists hmV 3 _ b1 h2 with ⟨hb0, _, _⟩ | ⟨m, hm, hKm⟩
        · dsimp only [b1, a] at hb0; omega
        · rw [hdV3, Int.mul_one] at hKm
          rcases (keyAt_append hmB0 3 _).mp hKm with h1 | h2
          · exfalso; rcases hB0s.2.1 3 _ h1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
          · rcases hAr.2 _ _ h2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hle⟩ | ⟨_, h, _⟩ | ⟨h, _⟩
            · omega
            · omega
            · have hsp : dphiW V 3 = dphiW B0 3 + dphiW (archWord 4 a) 3 := dphiW_append hmB0 3; rw [hdV3] at hsp; omega
            · omega
            · omega
    · -- `hsland_hm1`
      change ∀ ϕ, SLandAt B1 3 ϕ → -((4 : Int) * 4) ≤ ϕ ∧ ϕ ≤ (b1 : Int) + 2; intro ϕ hSL
      have hdV03 := hdV0 3
      rcases (sLandAt_append hmV0 3 ϕ).mp hSL with h1 | h2
      · rcases hV0b.2.1 _ _ h1 with ⟨h, _⟩ | ⟨_, heq⟩ | ⟨h, _⟩ | ⟨_, h, _⟩ <;> omega
      · obtain ⟨m, hm, hSLm⟩ := sLandAt_repeatWord hmV 3 _ b1 h2
        rw [hdV3, Int.mul_one] at hSLm
        have hSL_Ar : SLandAt (archWord 4 a) 3 (ϕ - dphiW V0 3 - (m : Int) - dphiW B0 3) := by
          rcases (sLandAt_append hmB0 3 _).mp hSLm with h1 | h2
          · exfalso; have := hB0s.2.2 3 _ h1; omega
          · exact h2
        rcases hAr.1 _ _ hSL_Ar with ⟨h, _⟩ | ⟨_, _, hphi⟩
        · omega
        · have hsp : dphiW V 3 = dphiW B0 3 + dphiW (archWord 4 a) 3 := dphiW_append hmB0 3; rw [hdV3] at hsp; omega
    · -- `hsland_hm2`
      change ∀ ϕ, SLandAt B1 2 ϕ → -((4 : Int) * 4) ≤ ϕ ∧ (ϕ ≤ (b1 : Int) ∨ 2 * (b1 : Int) ≤ ϕ); intro ϕ hSL
      have hdV02 := hdV0 2
      rcases (sLandAt_append hmV0 2 ϕ).mp hSL with h1 | h2
      · rcases hV0b.2.1 _ _ h1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hcase⟩ | ⟨_, h, _⟩
        · omega
        · omega
        · rcases hcase with ⟨hlo, hhi⟩ | heq
          · exact ⟨by omega, Or.inl hhi⟩
          · change 2 * ϕ = 2 * dphiW V0 2 + _ at heq; exact ⟨by omega, Or.inr (by omega)⟩
        · omega
      · obtain ⟨m, hm, hSLm⟩ := sLandAt_repeatWord hmV 2 _ b1 h2
        obtain ⟨_, hgt⟩ := hSL_V_low 2 _ (by omega) hSLm
        have hdV2 : dphiW V 2 = 1 + (V.length : Int) := by have := hdV_shift 2; omega
        have hm_nn : 0 ≤ (m : Int) * dphiW V 2 := Int.mul_nonneg (by omega) (by omega)
        exact ⟨by omega, Or.inr (by omega)⟩
    · -- `hsland_low`
      change ∀ r ϕ, r ≤ 1 → SLandAt B1 r ϕ → 2 * (b1 : Int) ≤ ϕ; intro r ϕ hr hSL
      have hr_ge : -1 ≤ r := ((keyAt_sLandAt_height_bounds hband1).2 r ϕ hSL).1
      have hdV0r := hdV0 r
      have h16a : 16 * (a : Int) ≤ 8 * (a : Int) * (3 - r) := by
        have h1 := Int.mul_le_mul_of_nonneg_left (by omega : 2 ≤ 3 - r) (by omega : (0 : Int) ≤ 8 * (a : Int))
        have h2 : 8 * (a : Int) * 2 = 16 * (a : Int) := by rw [Int.mul_assoc, Int.mul_comm (a : Int) 2, ← Int.mul_assoc]; omega
        omega
      rcases (sLandAt_append hmV0 r ϕ).mp hSL with h1 | h2
      · rcases hV0b.2.1 r ϕ h1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨hr0, _, heq⟩
        · omega
        · omega
        · omega
        · have hnn : 0 ≤ r * (r + 1) := Int.mul_nonneg hr0 (by omega); change 2 * ϕ = 2 * dphiW V0 r + r * (r + 1) at heq; omega
      · obtain ⟨m, hm, hSLm⟩ := sLandAt_repeatWord hmV r _ b1 h2
        obtain ⟨hr0, hgt⟩ := hSL_V_low r _ (by omega) hSLm
        have hrr_nn : 0 ≤ r * (r + 1) := Int.mul_nonneg hr0 (by omega)
        have hdVr_pos : 1 ≤ dphiW V r := by
          rw [hdV_shift r]; have := Int.mul_nonneg (by omega : (0 : Int) ≤ (V.length : Int)) (by omega : (0 : Int) ≤ 3 - r); omega
        have hm_nn : 0 ≤ (m : Int) * dphiW V r := Int.mul_nonneg (by omega) (by omega)
        omega
    · -- `hkey_le_dphi`
      change ∀ r ϕ, r ≤ 2 → KeyAt B1 r ϕ → ϕ ≤ dphiW B1 r + 4 * 4; intro r ϕ hr hK
      have hdVr_ge : 1 + (V.length : Int) ≤ dphiW V r := by
        rw [hdV_shift r]; have := Int.mul_le_mul_of_nonneg_left (by omega : 1 ≤ 3 - r) (by omega : (0 : Int) ≤ (V.length : Int)); omega
      have hbdV_nn : 0 ≤ (b1 : Int) * dphiW V r := Int.mul_nonneg (by omega) (by omega)
      have hdB1r := hdB1 r; have hdV0r := hdV0 r
      have h8a : 8 * (a : Int) ≤ 8 * (a : Int) * (3 - r) := by
        have h1 := Int.mul_le_mul_of_nonneg_left (by omega : 1 ≤ 3 - r) (by omega : (0 : Int) ≤ 8 * (a : Int))
        rwa [Int.mul_one] at h1
      have hrr_ub : 0 ≤ r → r * (r + 1) ≤ 16 := fun hr0 => by
        have h1 := Int.mul_le_mul_of_nonneg_left (by omega : r + 1 ≤ 4) hr0
        have h2 := Int.mul_le_mul_of_nonneg_right (by omega : r ≤ 4) (by omega : (0 : Int) ≤ 4); omega
      rcases (keyAt_append hmV0 r ϕ).mp hK with h1 | h2
      · rcases hV0b.2.2 r ϕ h1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨rfl, hcase⟩ | ⟨rfl, hcase⟩ | ⟨hr0, _, hcase⟩ | ⟨rfl, h0⟩
        · omega
        · omega
        · omega
        · rcases hcase with hle | heq
          · omega
          · change 2 * ϕ = 2 * dphiW V0 _ + _ at heq; omega
        · rcases hcase with hle | heq
          · omega
          · change 2 * ϕ = 2 * dphiW V0 _ + _ at heq; omega
        · rcases hcase with hle | heq
          · omega
          · have := hrr_ub hr0; change 2 * ϕ = 2 * dphiW V0 r + _ at heq; omega
        · omega
      · rcases keyAt_repeatWord_exists hmV r _ b1 h2 with ⟨hb0, _, _⟩ | ⟨m, hm, hKm⟩
        · dsimp only [b1, a] at hb0; omega
        · have hbm : dphiW V r ≤ ((b1 : Int) - (m : Int)) * dphiW V r := by
            have := Int.mul_le_mul_of_nonneg_right (by omega : (1 : Int) ≤ (b1 : Int) - (m : Int)) (by omega : (0 : Int) ≤ dphiW V r)
            rwa [Int.one_mul] at this
          have hbm_eq : ((b1 : Int) - (m : Int)) * dphiW V r = (b1 : Int) * dphiW V r - (m : Int) * dphiW V r := Int.sub_mul _ _ _
          have hpsi : ϕ - dphiW V0 r - (m : Int) * dphiW V r ≤ dphiW V r + 16 := by
            rcases hKey_V_low r _ hr hKm with ⟨hr0, heq⟩ | hle
            · have := hrr_ub hr0; omega
            · omega
          omega
  -- `F1` bounds via `free_stage_lift_le` with `q = 0, p = 0`:
  let F1 := (4 + 4 * a - 1) + b1 * (6 * M + 5)
  have hfree1 : free (wordSign B1) 0 B1.length ≤ F1 := by
    have hfl := free_stage_lift_le 4 0 0 a b1 B0 (by omega) ha1 hmB0 (by simpa [asRep, saRep] using hdV3)
    have hB0_free : free (wordSign B0) 0 B0.length ≤ 6 * M := by
      have h1 := free_le_additions (wordSign B0) 0 B0.length
      have h2 := additions_eq_half_len_of_mass_zero B0 hmB0
      have h3 : B0.length = 12 * M := by dsimp only [B0]; rw [asRep_length]; omega
      omega
    have hmul : b1 * (0 + 0 + free (wordSign B0) 0 B0.length + 4 + 1) ≤ b1 * (6 * M + 5) :=
      Nat.mul_le_mul_left b1 (by omega)
    dsimp only [B1, F1, V, V0] at hfl ⊢
    simp only [asRep, saRep, List.nil_append] at hfl
    omega
  have hF1_ge : 6 * M * b1 ≤ F1 := by
    have h1 : b1 * (6 * M) ≤ b1 * (6 * M + 5) := Nat.mul_le_mul_left b1 (by omega)
    have h2 : 6 * M * b1 = b1 * (6 * M) := Nat.mul_comm _ _
    dsimp only [F1]; omega
  have hF1_le : F1 ≤ additions (wordSign B1) 0 B1.length := by
    have h2A1 := additions_eq_half_len_of_mass_zero B1 hS1.hmass
    have hlenB1 : B1.length = (6 + 8 * a) + b1 * (32 * M + 14) := by
      dsimp only [B1, V0]; rw [List.length_append, v0Word_length 4 a (by omega) ha1, repeatWord_length, hlenV]
    have hA1 : additions (wordSign B1) 0 B1.length = (3 + 4 * a) + b1 * (16 * M + 7) := by
      have : b1 * (32 * M + 14) = 2 * (b1 * (16 * M + 7)) := by grind
      omega
    have h1 : b1 * (6 * M + 5) ≤ b1 * (16 * M + 7) := Nat.mul_le_mul_left b1 (by omega)
    dsimp only [F1]; omega
  exact ⟨B1, b1, F1, hS1, hfree1, hF1_ge, hF1_le⟩

/-! ## Public Theorems (`E-805 PROVED-LEAN`): Arbitrary-Depth `ρ_greedy ≥ √(7/3)` -/

/-- Exact word-level `Δ = 2` coherent cascade theorem (`E-805`): for every scale parameter
`M ≥ 200` and every stage `k ≥ 1`, there exists a balanced `FreshWord` `B` confined to
relative height band `[-1, 2k + 3]` satisfying
`(2 * (21 * M - 1)) ^ (k - 1) * free (wordSign B) 0 B.length ≤ (3 * (6 * M + 1)) ^ (k - 1) * additions (wordSign B) 0 B.length`. -/
theorem delta2_coherent_cascade_word_ratio (M k : Nat) (hM : 200 ≤ M) (hk : 1 ≤ k) :
    ∃ B : List Bool,
      mass B = 0 ∧
      1 ≤ B.length ∧
      FreshWord B ∧
      (∀ i, i ≤ B.length → -1 ≤ wordHeight B i ∧ wordHeight B i ≤ (2 * k + 2 : Int) + 1) ∧
      (2 * (21 * M - 1)) ^ (k - 1) * free (wordSign B) 0 B.length ≤
        (3 * (6 * M + 1)) ^ (k - 1) * additions (wordSign B) 0 B.length := by
  have hind : ∀ n : Nat,
      ∃ (B : List Bool) (bank F : Nat),
        StageInv (n + 1) B bank ∧
        free (wordSign B) 0 B.length ≤ F ∧
        6 * M * bank ≤ F ∧
        F ≤ additions (wordSign B) 0 B.length ∧
        (2 * (21 * M - 1)) ^ n * F ≤ (3 * (6 * M + 1)) ^ n * additions (wordSign B) 0 B.length := by
    intro n
    induction n with
    | zero =>
      obtain ⟨B, bank, F, hS, hfree, hge, hle⟩ := stageInv_base M hM
      exact ⟨B, bank, F, hS, hfree, hge, hle, by simpa using hle⟩
    | succ n ih =>
      obtain ⟨B, bank, F, hS, hfree, hge, hle, hpow⟩ := ih
      obtain ⟨B', bank', F', hS', hfree', hge', hle', hstep⟩ := stageInv_step M (n + 1) hM B bank F hS hfree hge hle
      have hA_pos : 0 < additions (wordSign B) 0 B.length := by
        have h1 : 1 ≤ bank := by
          have h0 := hS.hbank_large
          have : 1 ≤ 20 * (2 * (n + 1) + 6) * (2 * (n + 1) + 6) :=
            Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
          omega
        have h2 : 1 ≤ 6 * M * bank := by
          have := Nat.mul_le_mul_left (6 * M) h1; omega
        omega
      have hpow' : (2 * (21 * M - 1)) ^ (n + 1) * F' ≤ (3 * (6 * M + 1)) ^ (n + 1) * additions (wordSign B') 0 B'.length := by
        have hmul1 := Nat.mul_le_mul_left ((2 * (21 * M - 1)) ^ n) hstep
        have hmul2 := Nat.mul_le_mul_right (3 * (6 * M + 1) * additions (wordSign B') 0 B'.length) hpow
        have h1 : (2 * (21 * M - 1)) ^ n * (2 * (21 * M - 1) * additions (wordSign B) 0 B.length * F') =
            additions (wordSign B) 0 B.length * ((2 * (21 * M - 1)) ^ (n + 1) * F') := by
          rw [Nat.pow_succ]; grind
        have h2 : (2 * (21 * M - 1)) ^ n * (3 * (6 * M + 1) * F * additions (wordSign B') 0 B'.length) =
            ((2 * (21 * M - 1)) ^ n * F) * (3 * (6 * M + 1) * additions (wordSign B') 0 B'.length) := by grind
        have h3 : ((3 * (6 * M + 1)) ^ n * additions (wordSign B) 0 B.length) * (3 * (6 * M + 1) * additions (wordSign B') 0 B'.length) =
            additions (wordSign B) 0 B.length * ((3 * (6 * M + 1)) ^ (n + 1) * additions (wordSign B') 0 B'.length) := by
          rw [Nat.pow_succ]; grind
        exact Nat.le_of_mul_le_mul_left (by omega) hA_pos
      exact ⟨B', bank', F', hS', hfree', hge', hle', hpow'⟩
  obtain ⟨B, bank, F, hS, hfree, _, _, hpow⟩ := hind (k - 1)
  have hk_eq : k - 1 + 1 = k := by omega
  rw [hk_eq] at hS
  have hlen_pos : 1 ≤ B.length := by
    have h1 := hS.hlen_ge; have h0 := hS.hbank_large
    have : 1 ≤ 20 * (2 * k + 6) * (2 * k + 6) :=
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    omega
  have hmul_free : (2 * (21 * M - 1)) ^ (k - 1) * free (wordSign B) 0 B.length ≤ (2 * (21 * M - 1)) ^ (k - 1) * F :=
    Nat.mul_le_mul_left _ hfree
  exact ⟨B, hS.hmass, hlen_pos, hS.hfresh, hS.hband, Nat.le_trans hmul_free hpow⟩

/-- Direct coherent `SeededReplay.run` realization of every stage `(M, k)` of the `Δ = 2`
cascade (`E-805`): realizes the balanced height-`[-1, 2k + 3]` corridor directly on an actual
coherent greedy continuation (`st.value ∈ st.seen`) with the exact `(42M - 2) / (18M + 3)`
per-stage amplification ratio. -/
theorem delta2_coherent_cascade_replay_stage (M k : Nat) (hM : 200 ≤ M) (hk : 1 ≤ k) :
    ∃ (b : Nat) (st : State) (L : Nat),
      st.value ∈ st.seen ∧
      1 ≤ L ∧
      Fw (replaySign b st) L = 0 ∧
      (∀ i, i ≤ L → -1 ≤ Fw (replaySign b st) i ∧ Fw (replaySign b st) i ≤ (2 * k + 2 : Int) + 1) ∧
      (2 * (21 * M - 1)) ^ (k - 1) * free (replaySign b st) 0 L ≤
        (3 * (6 * M + 1)) ^ (k - 1) * additions (replaySign b st) 0 L := by
  obtain ⟨B, hmB, hlenB, hfreshB, hbandB, hratioB⟩ := delta2_coherent_cascade_word_ratio M k hM hk
  obtain ⟨b, st, hcoh, hmatch⟩ := seeded_replay_realizes_of_fresh B hfreshB.1 hfreshB.2
  have hpref : ∀ i, i < B.length → replaySign b st i = wordSign B i := by
    intro i hi; simpa [MatchesAt, wordSign] using hmatch i hi
  have hFw_eq : ∀ i, i ≤ B.length → Fw (replaySign b st) i = wordHeight B i := by
    intro i hi
    induction i with
    | zero => simp [Fw, wordHeight, mass]
    | succ i ih =>
      rw [Fw_succ, ih (by omega), hpref i (by omega),
        wordHeight_eq_Fw_wordSign B (i + 1) hi, Fw_succ, ← wordHeight_eq_Fw_wordSign B i (by omega)]
  have hFw_L : Fw (replaySign b st) B.length = 0 := by
    rw [hFw_eq B.length (Nat.le_refl _)]; unfold wordHeight; rw [List.take_length]; exact hmB
  have hadd_eq := additions_congr_prefix (replaySign b st) (wordSign B) B.length hpref
  have hfree_eq := free_congr_prefix (replaySign b st) (wordSign B) B.length hpref
  refine ⟨b, st, B.length, hcoh, hlenB, hFw_L, ?_, ?_⟩
  · intro i hi; rw [hFw_eq i hi]; exact hbandB i hi
  · rw [hadd_eq, hfree_eq]; exact hratioB

private theorem exists_pow_beat (a b D : Nat) (ha : 1 ≤ a) (hab : a < b) :
    ∃ n : Nat, D * a ^ n < b ^ n := by
  have hbern : ∀ k : Nat, a ^ k + k * a ^ (k - 1) ≤ (a + 1) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ihk =>
      cases k with
      | zero => simp
      | succ k =>
        simp only [Nat.add_sub_cancel] at ihk ⊢
        have h1 : (a + 1) ^ (k + 2) = (a + 1) ^ (k + 1) * a + (a + 1) ^ (k + 1) := by
          rw [Nat.pow_succ, Nat.mul_add, Nat.mul_one]
        have h2 : a ^ (k + 1) ≤ (a + 1) ^ (k + 1) := Nat.pow_le_pow_left (by omega) (k + 1)
        have h3 : (a ^ (k + 1) + (k + 1) * a ^ k) * a ≤ (a + 1) ^ (k + 1) * a :=
          Nat.mul_le_mul_right a ihk
        have h4 : (a ^ (k + 1) + (k + 1) * a ^ k) * a = a ^ (k + 2) + (k + 1) * a ^ (k + 1) := by
          rw [Nat.add_mul, ← Nat.pow_succ, Nat.mul_assoc, ← Nat.pow_succ]
        have h5 : (k + 2) * a ^ (k + 1) = (k + 1) * a ^ (k + 1) + a ^ (k + 1) := by
          rw [show k + 2 = (k + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
        change a ^ (k + 2) + (k + 2) * a ^ (k + 1) ≤ (a + 1) ^ (k + 2)
        omega
  let m := a * D + 1
  refine ⟨m, ?_⟩
  have hm1 : m - 1 = a * D := by dsimp only [m]; omega
  have h_a_pow : a ^ m = a ^ (m - 1) * a := by
    calc a ^ m = a ^ (a * D + 1) := rfl
      _ = a ^ (a * D) * a := Nat.pow_succ _ _
      _ = a ^ (m - 1) * a := by rw [hm1]
  have h_lhs : D * a ^ m = (a * D) * a ^ (m - 1) := by rw [h_a_pow]; grind
  have h_pos : 0 < a ^ (m - 1) := Nat.pow_pos (by omega)
  have h_lt : (a * D) * a ^ (m - 1) < m * a ^ (m - 1) := by
    have : m * a ^ (m - 1) = (a * D) * a ^ (m - 1) + a ^ (m - 1) := by
      dsimp only [m]; rw [Nat.add_mul, Nat.one_mul]
    omega
  have h_le1 : m * a ^ (m - 1) ≤ (a + 1) ^ m := by have := hbern m; omega
  have h_le2 : (a + 1) ^ m ≤ b ^ m := Nat.pow_le_pow_left (by omega) m
  omega

/-- Unconditional arbitrary-depth `ρ_greedy ≥ √(7/3)` theorem on coherent finite-state greedy
replays `SeededReplay.run` (`E-805 PROVED-LEAN`, upgrading `E-799 PROVED-PAPER`):
for EVERY rational base `P / Q < √(7/3)` (i.e., `1 ≤ Q` and `3 * P * P < 7 * Q * Q`) and EVERY
multiplicative constant `C : Nat`, there exist a cascade stage `k ≥ 1`, a base clock `b`, a
coherent finite-state greedy configuration `st` (`st.value ∈ st.seen`), and a balanced prefix
of length `L ≥ 1` confined to relative height band `[-1, 2k + 3]` (total band span `2k + 4`)
whose actual greedy additions-to-free ratio exceeds `C * (P / Q) ^ (2 * k + 4)`. -/
theorem seeded_replay_delta2_exponential_lower_bound (P Q C : Nat)
    (hQ : 1 ≤ Q) (hPQ : 3 * P * P < 7 * Q * Q) :
    ∃ (k b : Nat) (st : State) (L : Nat),
      1 ≤ k ∧
      1 ≤ L ∧
      st.value ∈ st.seen ∧
      Fw (replaySign b st) L = 0 ∧
      (∀ i, i ≤ L → -1 ≤ Fw (replaySign b st) i ∧ Fw (replaySign b st) i ≤ (2 * k + 2 : Int) + 1) ∧
      C * P ^ (2 * k + 4) * free (replaySign b st) 0 L <
        Q ^ (2 * k + 4) * additions (replaySign b st) 0 L := by
  let M : Nat := 10 * (P * P + Q * Q) + 200
  have hM : 200 ≤ M := by dsimp only [M]; omega
  let A0 : Nat := 3 * (6 * M + 1) * (P * P)
  let B0 : Nat := 2 * (21 * M - 1) * (Q * Q)
  have hA0_lt_B0 : A0 < B0 := by
    have hgap : 7 * Q * Q ≥ 3 * P * P + 1 := by omega
    have hM_big : 3 * (P * P) + 2 * (Q * Q) < 6 * M := by dsimp only [M]; omega
    dsimp only [A0, B0]
    have h1 : 2 * (21 * M - 1) = 42 * M - 2 := by omega
    have h2 : 3 * (6 * M + 1) = 18 * M + 3 := by omega
    rw [h1, h2, Nat.sub_mul]
    have hsub_ok : 2 * (Q * Q) ≤ 42 * M * (Q * Q) := by
      have := Nat.mul_le_mul_right (Q * Q) (by omega : 2 ≤ 42 * M); omega
    have hmain : (18 * M + 3) * (P * P) + 2 * (Q * Q) < 42 * M * (Q * Q) := by
      have hm1 : 6 * M * (3 * P * P + 1) ≤ 6 * M * (7 * Q * Q) := Nat.mul_le_mul_left (6 * M) hgap
      have hl : 6 * M * (3 * P * P + 1) = 18 * M * (P * P) + 6 * M := by grind
      have hr : 6 * M * (7 * Q * Q) = 42 * M * (Q * Q) := by grind
      have hexp : (18 * M + 3) * (P * P) = 18 * M * (P * P) + 3 * (P * P) := by grind
      omega
    omega
  by_cases hP0 : P = 0
  · subst hP0
    obtain ⟨b, st, L, hcoh, hL1, hFwL, hband, _⟩ := delta2_coherent_cascade_replay_stage M 1 hM (by omega)
    have hadd_pos : 0 < additions (replaySign b st) 0 L := by
      have hbal : 2 * additions (replaySign b st) 0 L = L := by
        have hfw_add : ∀ n : Nat, Fw (replaySign b st) n + (n : Int) = 2 * (additions (replaySign b st) 0 n : Int) := by
          intro n; induction n with
          | zero => simp [Fw, additions, cN]
          | succ n ihn =>
            rw [Fw_succ]; unfold additions at ihn ⊢
            cases hst : replaySign b st n
            · rw [cN_succ_neg _ 0 n (by simp [hst])]; simp [sign]; omega
            · rw [cN_succ_pos _ 0 n (by simp [hst])]; simp [sign]; omega
        have := hfw_add L; rw [hFwL] at this; omega
      omega
    have hQ_pos : 0 < Q ^ 6 := Nat.pow_pos (by omega)
    refine ⟨1, b, st, L, by omega, hL1, hcoh, hFwL, hband, ?_⟩
    simp only [Nat.zero_pow (by omega : 0 < 2 * 1 + 4), Nat.mul_zero, Nat.zero_mul]
    exact Nat.mul_pos hQ_pos hadd_pos
  · have hP1 : 1 ≤ P := by omega
    have hA0_pos : 1 ≤ A0 := by
      dsimp only [A0]
      have h1 : 1 ≤ P * P := Nat.mul_le_mul hP1 hP1
      have h2 : 1 ≤ 3 * (6 * M + 1) := by omega
      exact Nat.mul_le_mul h2 h1
    let D : Nat := C * P ^ 6 + 1
    obtain ⟨n, hn⟩ := exists_pow_beat A0 B0 D hA0_pos hA0_lt_B0
    let k := n + 1
    obtain ⟨b, st, L, hcoh, hL1, hFwL, hband, hratio⟩ := delta2_coherent_cascade_replay_stage M k hM (by omega)
    have hadd_pos : 0 < additions (replaySign b st) 0 L := by
      have hfw_add : ∀ m : Nat, Fw (replaySign b st) m + (m : Int) = 2 * (additions (replaySign b st) 0 m : Int) := by
        intro m; induction m with
        | zero => simp [Fw, additions, cN]
        | succ m ihm =>
          rw [Fw_succ]; unfold additions at ihm ⊢
          cases hst : replaySign b st m
          · rw [cN_succ_neg _ 0 m (by simp [hst])]; simp [sign]; omega
          · rw [cN_succ_pos _ 0 m (by simp [hst])]; simp [sign]; omega
      have := hfw_add L; rw [hFwL] at this; omega
    have hQ_pos : 0 < Q ^ (2 * k + 4) := Nat.pow_pos (by omega)
    refine ⟨k, b, st, L, by omega, hL1, hcoh, hFwL, hband, ?_⟩
    by_cases hfree0 : free (replaySign b st) 0 L = 0
    · rw [hfree0, Nat.mul_zero]; exact Nat.mul_pos hQ_pos hadd_pos
    · have hfree_pos : 0 < free (replaySign b st) 0 L := by omega
      have hratio_n : (2 * (21 * M - 1)) ^ n * free (replaySign b st) 0 L ≤
          (3 * (6 * M + 1)) ^ n * additions (replaySign b st) 0 L := by
        simpa [k] using hratio
      have hP_exp : P ^ (2 * k + 4) = P ^ 6 * (P * P) ^ n := by
        dsimp only [k]
        rw [show 2 * (n + 1) + 4 = 6 + 2 * n by omega, Nat.pow_add, Nat.pow_mul, Nat.pow_two]
      have hQ_exp : Q ^ (2 * k + 4) = Q ^ 6 * (Q * Q) ^ n := by
        dsimp only [k]
        rw [show 2 * (n + 1) + 4 = 6 + 2 * n by omega, Nat.pow_add, Nat.pow_mul, Nat.pow_two]
      have hQ6 : 1 ≤ Q ^ 6 := Nat.pow_pos (by omega)
      have hA0_pow : A0 ^ n = (3 * (6 * M + 1)) ^ n * (P * P) ^ n := Nat.mul_pow _ _ n
      have hB0_pow : B0 ^ n = (2 * (21 * M - 1)) ^ n * (Q * Q) ^ n := Nat.mul_pow _ _ n
      have hstep1 : C * P ^ 6 * A0 ^ n < B0 ^ n := by
        have h1 : C * P ^ 6 * A0 ^ n < D * A0 ^ n := by
          dsimp only [D]; rw [Nat.add_mul, Nat.one_mul]; have : 0 < A0 ^ n := Nat.pow_pos hA0_pos; omega
        omega
      have hstep2 : (C * P ^ 6 * A0 ^ n) * free (replaySign b st) 0 L < B0 ^ n * free (replaySign b st) 0 L :=
        Nat.mul_lt_mul_of_pos_right hstep1 hfree_pos
      have hstep3 : B0 ^ n * free (replaySign b st) 0 L ≤ (3 * (6 * M + 1)) ^ n * ((Q * Q) ^ n * additions (replaySign b st) 0 L) := by
        rw [hB0_pow]
        have h1 := Nat.mul_le_mul_left ((Q * Q) ^ n) hratio_n
        have hl : (Q * Q) ^ n * ((2 * (21 * M - 1)) ^ n * free (replaySign b st) 0 L) =
            (2 * (21 * M - 1)) ^ n * (Q * Q) ^ n * free (replaySign b st) 0 L := by grind
        have hr : (Q * Q) ^ n * ((3 * (6 * M + 1)) ^ n * additions (replaySign b st) 0 L) =
            (3 * (6 * M + 1)) ^ n * ((Q * Q) ^ n * additions (replaySign b st) 0 L) := by grind
        omega
      have hstep4 : (3 * (6 * M + 1)) ^ n * (C * P ^ (2 * k + 4) * free (replaySign b st) 0 L) <
          (3 * (6 * M + 1)) ^ n * (Q ^ (2 * k + 4) * additions (replaySign b st) 0 L) := by
        have hl : (3 * (6 * M + 1)) ^ n * (C * P ^ (2 * k + 4) * free (replaySign b st) 0 L) =
            (C * P ^ 6 * A0 ^ n) * free (replaySign b st) 0 L := by rw [hP_exp, hA0_pow]; grind
        have hleQ : (Q * Q) ^ n * additions (replaySign b st) 0 L ≤ Q ^ (2 * k + 4) * additions (replaySign b st) 0 L := by
          rw [hQ_exp]
          have : 1 * (Q * Q) ^ n ≤ Q ^ 6 * (Q * Q) ^ n := Nat.mul_le_mul_right _ hQ6
          have := Nat.mul_le_mul_right (additions (replaySign b st) 0 L) this
          simpa using this
        have hhr := Nat.mul_le_mul_left ((3 * (6 * M + 1)) ^ n) hleQ
        omega
      exact Nat.lt_of_mul_lt_mul_left hstep4

end Recaman.DeltaTwoCoherentCascade
