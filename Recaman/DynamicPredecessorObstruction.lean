import Recaman.CoherentGreedyFreshness

namespace Recaman.DynamicPredecessorObstruction

open Recaman Recaman.SeededReplay Recaman.CoherentGreedyFreshness
open Recaman.FloorSupplyPotential Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction
open Recaman.CrossBlockReuseUnbounded Recaman.LineCapacityPeriodic
open Recaman.LeadingRunSupply
open Recaman.ShortPeriodicSupply (sign)

/-! # Exact bi-directional `E-759` characterization and arbitrary-depth dynamic predecessor separation (`E-801`)

Establishes two arbitrary-depth dynamic theorems directly on `SeededReplay.run` and the real
clock-0 Recamán orbit `Recaman.Basic.a`:

1. **Exact bi-directional `E-759` characterization (`seeded_replay_realizes_iff_fresh`)**:
   A finite sign word `w : List Bool` is realized at clock `0` by some coherent finite-state
   greedy replay `SeededReplay.run b st` (`st.value ∈ st.seen`) **if and only if** `wordSign w`
   satisfies both `TypeIFresh (wordSign w) w.length` and `TypeIIFresh (wordSign w) w.length`.
   The reverse direction constructs an explicit large-base replay `(b, st)` whose initial `seen`
   set contains only `st.value` and the strictly free `A`-step subtraction candidates.
2. **Exact 1-step predecessor obstruction (`blocksSPredecessor_forbids_S_before`,
   `blocksAPredecessor_forbids_A_before`, `no_predecessor_forbids_nonzero_clock_replay`,
   `no_predecessor_forbids_all_canonical_clocks`)**:
   Any word `w` with a `(1, 0)` `S`-landing (`areaW = q + 2`) blocks `S ++ w`, and any word `w`
   with a `(-1, 0)` or `(-2, 0)` `S`-landing (`areaW = -(q + 2)` or `-2*(q + 2)`) blocks `A ++ w`.
   Therefore no such word can occur at ANY nonzero clock `s ≥ 1` of ANY coherent `SeededReplay.run`,
   and if `w` starts with `S` or `AAS` it cannot occur at ANY clock `s : Nat` of `Recaman.Basic.a`.
3. **Arbitrary-depth dynamic separation (`e779Word_arbitrary_depth_dynamic_separation`)**:
   For every `k : Nat`, the `E-779` family `e779Word k = AAS ++ S^(3k+6) ++ A^(3k+6) ++ (SA)^(3k^2+8k+1) ++ SS`
   reaches relative excursion depth `-(3k + 5)`, is unconditionally `TypeIFresh ∧ TypeIIFresh`
   (hence realized by a coherent finite-state greedy replay), yet has NO coherent 1-step
   predecessor and NEVER occurs at ANY clock `s : Nat` of `Recaman.Basic.a`.
4. **Initial-`S` and initial-`S^2` Type-I/Type-II witnesses (`initial_S_dynamic_separation_witnesses`)**:
   Proves the same dynamic separation for explicit initial-`S` (`len = 35`, Type-I `A`-obstruction)
   and initial-`SS` (`len = 36`, Type-II `A`-obstruction) words, answering `E-779`'s question on
   whether initial-`S` coherent words also fail 1-step predecessor closure.
-/

/-! ## Word sign stream and agreement lemmas -/

/-- Sign stream extending a finite word `w : List Bool` (default `false` past `w.length`). -/
def wordSign (w : List Bool) (t : Nat) : Bool :=
  w[t]!

private theorem fw_eq_of_agree (f g : Nat → Bool) (N : Nat)
    (hag : ∀ i, i < N → f i = g i) :
    ∀ t, t ≤ N → Fw f t = Fw g t
  | 0, _ => rfl
  | t + 1, ht => by
    rw [Fw_succ, Fw_succ, fw_eq_of_agree f g N hag t (by omega), hag t (by omega)]

private theorem ar_eq_of_agree (f g : Nat → Bool) (N : Nat)
    (hag : ∀ i, i < N → f i = g i) :
    ∀ t, t ≤ N → Ar f 0 t = Ar g 0 t
  | 0, _ => rfl
  | t + 1, ht => by
    have ih := ar_eq_of_agree f g N hag t (by omega)
    have hfw := fw_eq_of_agree f g N hag (t + 1) ht
    have h1 := Ar_succ f 0 t
    have h2 := Ar_succ g 0 t
    have h0f : Fw f 0 = 0 := rfl
    have h0g : Fw g 0 = 0 := rfl
    simp only [Nat.zero_add, h0f, h0g, Int.sub_zero] at h1 h2
    omega

private theorem pot_eq_of_agree (f g : Nat → Bool) (N : Nat)
    (hag : ∀ i, i < N → f i = g i) (t : Nat) (ht : t ≤ N) (m : Int) :
    floorPotential f 0 m t = floorPotential g 0 m t := by
  unfold floorPotential
  have har := ar_eq_of_agree f g N hag t ht
  have h0f : Fw f 0 = 0 := rfl
  have h0g : Fw g 0 = 0 := rfl
  simp only [Nat.sub_zero, h0f, h0g, har]

private theorem fw_abs_le (f : Nat → Bool) :
    ∀ t : Nat, -(t : Int) ≤ Fw f t ∧ Fw f t ≤ (t : Int)
  | 0 => by simp [Fw]
  | t + 1 => by
    have ih := fw_abs_le f t
    rw [Fw_succ]
    cases f t <;> simp [sign] <;> omega

private theorem ar_abs_le (f : Nat → Bool) :
    ∀ t : Nat, -((t * t : Nat) : Int) ≤ Ar f 0 t ∧ Ar f 0 t ≤ ((t * t : Nat) : Int)
  | 0 => by simp [Ar]
  | t + 1 => by
    have ih := ar_abs_le f t
    have hfw := fw_abs_le f (t + 1)
    have hs := Ar_succ f 0 t
    have h0 : Fw f 0 = 0 := rfl
    simp only [Nat.zero_add, h0, Int.sub_zero] at hs
    have hsq : ((t + 1) * (t + 1) : Nat) = t * t + 2 * t + 1 := by grind
    rw [hsq]
    push_cast
    omega

private theorem floorPotential_abs_lt (f : Nat → Bool) (N t : Nat) (r : Int)
    (ht : t ≤ N) (hr1 : -((N + 1 : Nat) : Int) ≤ r) (hr2 : r ≤ ((N + 1 : Nat) : Int)) :
    -(((2 * (N + 1) * (N + 1) + 2 : Nat) : Int)) < floorPotential f 0 (r - 1) t ∧
      floorPotential f 0 (r - 1) t < ((2 * (N + 1) * (N + 1) + 2 : Nat) : Int) := by
  let M : Int := ((2 * (N + 1) * (N + 1) + 2 : Nat) : Int)
  change -M < floorPotential f 0 (r - 1) t ∧ floorPotential f 0 (r - 1) t < M
  have har := ar_abs_le f t
  have ht2 : t * t ≤ N * N := Nat.mul_le_mul ht ht
  have htr1 : -((N * (N + 1) : Nat) : Int) ≤ (t : Int) * r := by
    have h1 : (t : Int) * (-((N + 1 : Nat) : Int)) ≤ (t : Int) * r :=
      Int.mul_le_mul_of_nonneg_left hr1 (Int.natCast_nonneg t)
    have h2 : (t : Int) * ((N + 1 : Nat) : Int) ≤ (N : Int) * ((N + 1 : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_right (by omega) (Int.natCast_nonneg _)
    push_cast at h1 h2 ⊢
    grind
  have htr2 : (t : Int) * r ≤ ((N * (N + 1) : Nat) : Int) := by
    have h1 : (t : Int) * r ≤ (t : Int) * ((N + 1 : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left hr2 (Int.natCast_nonneg t)
    have h2 : (t : Int) * ((N + 1 : Nat) : Int) ≤ (N : Int) * ((N + 1 : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_right (by omega) (Int.natCast_nonneg _)
    push_cast at h1 h2 ⊢
    grind
  have hN1 : (N * N : Int) + (N * (N + 1) : Int) < (M : Int) := by
    dsimp only [M]
    push_cast
    have hnn : (0 : Int) ≤ (N : Int) * (N : Int) := Int.mul_nonneg (by omega) (by omega)
    grind
  unfold floorPotential
  have h0 : Fw f 0 = 0 := rfl
  simp only [Nat.sub_zero, h0]
  have hcast : ((t * t : Nat) : Int) ≤ ((N * N : Nat) : Int) := by exact_mod_cast ht2
  push_cast at hcast htr1 htr2 hN1 har ⊢
  grind

/-! ## Part 1: Exact bi-directional `E-759` characterization on `SeededReplay.run` -/

private theorem affine_key_inj (v₀ b M r₁ r₂ p₁ p₂ : Int)
    (hb : 2 * M ≤ b + 1) (hp₁ : -M < p₁ ∧ p₁ < M) (hp₂ : -M < p₂ ∧ p₂ < M)
    (heq : v₀ + (b + 1) * r₁ - p₁ = v₀ + (b + 1) * r₂ - p₂) :
    r₁ = r₂ ∧ p₁ = p₂ := by
  have hdiff : (b + 1) * (r₁ - r₂) = p₁ - p₂ := by grind
  have hr : r₁ = r₂ := by
    by_cases hgt : r₂ < r₁
    · have h1 : (1 : Int) ≤ r₁ - r₂ := by omega
      have h2 : (b + 1) * 1 ≤ (b + 1) * (r₁ - r₂) :=
        Int.mul_le_mul_of_nonneg_left h1 (by omega)
      omega
    · by_cases hlt : r₁ < r₂
      · have h1 : (1 : Int) ≤ r₂ - r₁ := by omega
        have h2 : (b + 1) * 1 ≤ (b + 1) * (r₂ - r₁) :=
          Int.mul_le_mul_of_nonneg_left h1 (by omega)
        have hd2 : (b + 1) * (r₂ - r₁) = p₂ - p₁ := by grind
        omega
      · omega
  exact ⟨hr, by rw [hr] at heq; omega⟩

/-- Sufficiency direction of `E-759` in Lean 4: EVERY finite sign word `w : List Bool`
satisfying `TypeIFresh (wordSign w) w.length` and `TypeIIFresh (wordSign w) w.length`
is realized at clock `0` by an explicit coherent finite-state greedy replay `(b, st)`. -/
theorem seeded_replay_realizes_of_fresh (w : List Bool)
    (hI : TypeIFresh (wordSign w) w.length) (hII : TypeIIFresh (wordSign w) w.length) :
    ∃ b st, st.value ∈ st.seen ∧ MatchesAt (replaySign b st) 0 w := by
  let f := wordSign w
  let N := w.length
  let M : Nat := 2 * (N + 1) * (N + 1) + 2
  let b : Nat := 2 * M + N + 2
  let v₀ : Nat := (N + 2) * (b + 1) + M
  let target : Nat → Int := fun t =>
    (v₀ : Int) + ((b + 1 : Nat) : Int) * Fw f t - floorPotential f 0 (Fw f t - 1) t
  let cand : Nat → Int := fun u =>
    (v₀ : Int) + ((b + 1 : Nat) : Int) * (Fw f u - 1) - floorPotential f 0 (Fw f u - 2) u
  have hcand_eq : ∀ u, cand u = target u - ((b + u + 1 : Nat) : Int) := by
    intro u
    dsimp only [cand, target]
    unfold floorPotential
    have h0 : Fw f 0 = 0 := rfl
    simp only [Nat.sub_zero, h0]
    push_cast
    grind
  have htarget_step : ∀ t, target (t + 1) = target t + sign (f t) * ((b + t + 1 : Nat) : Int) := by
    intro t
    dsimp only [target]
    have hFw : Fw f (t + 1) = Fw f t + sign (f t) := Fw_succ f t
    have hAr : Ar f 0 (t + 1) = Ar f 0 t + Fw f (t + 1) := by
      have := Ar_succ f 0 t
      have h0 : Fw f 0 = 0 := rfl
      simpa [h0] using this
    unfold floorPotential
    have h0 : Fw f 0 = 0 := rfl
    simp only [Nat.sub_zero, h0]
    rw [hAr, hFw]
    push_cast
    grind
  have htarget_pos : ∀ t, t ≤ N → ((b + t + 1 : Nat) : Int) < target t := by
    intro t ht
    have hfw := fw_abs_le f t
    have hpot := floorPotential_abs_lt f N t (Fw f t) ht (by omega) (by omega)
    dsimp only [target, v₀, b]
    have hmul : -((N : Int) * ((2 * M + N + 2 + 1 : Nat) : Int)) ≤
        ((2 * M + N + 2 + 1 : Nat) : Int) * Fw f t := by
      have h1 : ((2 * M + N + 2 + 1 : Nat) : Int) * (-(N : Int)) ≤
          ((2 * M + N + 2 + 1 : Nat) : Int) * Fw f t :=
        Int.mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg _)
      grind
    push_cast at hmul hpot ⊢
    dsimp only [M] at hmul hpot ⊢
    grind
  have hcand_pos : ∀ u, u ≤ N → 0 < cand u := by
    intro u hu
    rw [hcand_eq u]
    have := htarget_pos u hu
    omega
  let freeBlockers : List Nat :=
    ((List.range N).filter (fun u =>
      f u && (List.range (u + 1)).all (fun v => decide (target v ≠ cand u)))).map
      (fun u => (cand u).toNat)
  let st : State := ⟨v₀, v₀ :: freeBlockers⟩
  have hmem_block : ∀ z : Nat, z ∈ freeBlockers ↔
      ∃ u, u < N ∧ f u = true ∧ (∀ v, v ≤ u → target v ≠ cand u) ∧ (z : Int) = cand u := by
    intro z
    dsimp only [freeBlockers]
    rw [List.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [List.mem_filter, List.mem_range] at hu
      obtain ⟨huN, hcond⟩ := hu
      rw [Bool.and_eq_true, List.all_eq_true] at hcond
      refine ⟨u, huN, hcond.1, ?_, ?_⟩
      · intro v hvu
        have hv := hcond.2 v (List.mem_range.mpr (by omega))
        simpa [decide_eq_true_eq] using hv
      · exact Int.toNat_of_nonneg (Int.le_of_lt (hcand_pos u (by omega)))
    · rintro ⟨u, huN, hfu, hall, hz⟩
      refine ⟨u, ?_, ?_⟩
      · rw [List.mem_filter, List.mem_range]
        refine ⟨huN, ?_⟩
        rw [Bool.and_eq_true, List.all_eq_true]
        refine ⟨hfu, ?_⟩
        intro v hv
        rw [List.mem_range] at hv
        simp [hall v (by omega)]
      · omega
  have hrun : ∀ t, t ≤ N →
      value b st t = target t ∧
      (∀ z : Nat, z ∈ (run b st t).seen ↔
        z ∈ freeBlockers ∨ ∃ v, v ≤ t ∧ (z : Int) = target v) ∧
      (∀ i, i < t → replaySign b st i = f i) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨by simp [value, run, st, target, Fw, floorPotential, Ar], ?_, fun _ hi => by omega⟩
      intro z
      simp only [run, st, List.mem_cons]
      constructor
      · rintro (rfl | hfb)
        · right; exact ⟨0, Nat.le_refl 0, by simp [target, Fw, floorPotential, Ar]⟩
        · left; exact hfb
      · rintro (hfb | ⟨v, hv, hz⟩)
        · right; exact hfb
        · have hv0 : v = 0 := by omega
          subst hv0
          left
          simp [target, Fw, floorPotential, Ar] at hz
          omega
    | succ t ih =>
      intro htN
      obtain ⟨hval_t, hseen_t, hsign_t⟩ := ih (by omega)
      have hpos_t : b + t + 1 < (run b st t).value := by
        have hp := htarget_pos t (by omega)
        change ((run b st t).value : Int) = target t at hval_t
        omega
      have hsub_int : (((run b st t).value - (b + t + 1) : Nat) : Int) = cand t := by
        have hc := hcand_eq t
        change ((run b st t).value : Int) = target t at hval_t
        omega
      have hstep_sign : replaySign b st t = f t := by
        unfold replaySign
        cases hft : f t with
        | true =>
          have hmem_cand : (run b st t).value - (b + t + 1) ∈ (run b st t).seen := by
            rw [hseen_t]
            by_cases hex : ∃ v, v ≤ t ∧ target v = cand t
            · obtain ⟨v, hvt, hv⟩ := hex
              right
              exact ⟨v, hvt, by omega⟩
            · left
              rw [hmem_block]
              exact ⟨t, by omega, hft, fun v hvt hEq => hex ⟨v, hvt, hEq⟩, hsub_int⟩
          have hnc : ¬ CanSubtract (b + t + 1) (run b st t) := fun hc => hc.2 hmem_cand
          simp [hnc]
        | false =>
          have hnot_mem : (run b st t).value - (b + t + 1) ∉ (run b st t).seen := by
            rw [hseen_t]
            rintro (hfb | ⟨v, hvt, hv_eq⟩)
            · rw [hmem_block] at hfb
              obtain ⟨u, huN, hfu, hall, hu_eq⟩ := hfb
              have ht1_eq : target (t + 1) = cand t := by
                rw [htarget_step t, hft, hcand_eq t]
                simp [sign]; omega
              have hEq : target (t + 1) = cand u := by omega
              by_cases hlt : u < t
              · have hfw_t1 := fw_abs_le f (t + 1)
                have hfw_u := fw_abs_le f u
                have hp1 := floorPotential_abs_lt f N (t + 1) (Fw f (t + 1)) htN (by omega) (by omega)
                have hp2 := floorPotential_abs_lt f N u (Fw f u - 1) (by omega) (by omega) (by omega)
                have hinj := affine_key_inj (v₀ : Int) (b : Int) (M : Int)
                  (Fw f (t + 1)) (Fw f u - 1)
                  (floorPotential f 0 (Fw f (t + 1) - 1) (t + 1))
                  (floorPotential f 0 (Fw f u - 2) u)
                  (by dsimp only [b]; push_cast; omega)
                  (by dsimp only [M]; exact hp1)
                  (by dsimp only [M]; rw [show Fw f u - 2 = (Fw f u - 1) - 1 by omega]; exact hp2)
                  (by dsimp only [target, cand] at hEq; exact hEq)
                have hFu : Fw f u = Fw f (t + 1) + 1 := by omega
                have hpeq : floorPotential f 0 (Fw f (t + 1) - 1) (t + 1) =
                    floorPotential f 0 (Fw f (t + 1) - 1) u := by
                  have h2 := hinj.2
                  rwa [show Fw f u - 2 = Fw f (t + 1) - 1 by omega] at h2
                exact hII t (by omega) hft u hlt hfu hFu hpeq
              · by_cases heq_ut : u = t
                · rw [heq_ut, hft] at hfu; cases hfu
                · exact hall (t + 1) (by omega) hEq
            · have ht1_eq : target (t + 1) = cand t := by
                rw [htarget_step t, hft, hcand_eq t]
                simp [sign]; omega
              have hEq : target (t + 1) = target v := by omega
              have hfw_t1 := fw_abs_le f (t + 1)
              have hfw_v := fw_abs_le f v
              have hp1 := floorPotential_abs_lt f N (t + 1) (Fw f (t + 1)) htN (by omega) (by omega)
              have hp2 := floorPotential_abs_lt f N v (Fw f v) (by omega) (by omega) (by omega)
              have hinj := affine_key_inj (v₀ : Int) (b : Int) (M : Int)
                (Fw f (t + 1)) (Fw f v)
                (floorPotential f 0 (Fw f (t + 1) - 1) (t + 1))
                (floorPotential f 0 (Fw f v - 1) v)
                (by dsimp only [b]; push_cast; omega)
                (by dsimp only [M]; exact hp1)
                (by dsimp only [M]; exact hp2)
                (by dsimp only [target] at hEq; exact hEq)
              have hpeq : floorPotential f 0 (Fw f (t + 1) - 1) (t + 1) =
                  floorPotential f 0 (Fw f (t + 1) - 1) v := by
                have h2 := hinj.2
                rwa [← hinj.1] at h2
              exact hI t (by omega) hft v hvt hinj.1.symm hpeq
          have hc : CanSubtract (b + t + 1) (run b st t) := ⟨hpos_t, hnot_mem⟩
          simp [hc]
      have hval_succ : value b st (t + 1) = target (t + 1) := by
        have hstep_v : value b st (t + 1) =
            value b st t + sign (replaySign b st t) * ((b + t + 1 : Nat) : Int) := by
          have hab1 := replay_value_eq_abel_potential b st (t + 1)
          have hab0 := replay_value_eq_abel_potential b st t
          have hFw := Fw_succ (replaySign b st) t
          have hAr := Ar_succ (replaySign b st) 0 t
          have h0 : Fw (replaySign b st) 0 = 0 := rfl
          unfold floorPotential at hab1 hab0
          simp only [Nat.sub_zero, h0, Nat.zero_add, Int.sub_zero] at hab1 hab0 hAr
          rw [hAr, hFw] at hab1
          push_cast at hab1 hab0 ⊢
          grind
        rw [hstep_v, hval_t, hstep_sign, htarget_step t]
      refine ⟨hval_succ, ?_, ?_⟩
      · intro z
        change z ∈ nextValue (b + t + 1) (run b st t) :: (run b st t).seen ↔ _
        rw [List.mem_cons, hseen_t]
        have hnv : (nextValue (b + t + 1) (run b st t) : Int) = target (t + 1) := hval_succ
        constructor
        · rintro (rfl | hfb | ⟨v, hvt, hv⟩)
          · right; exact ⟨t + 1, Nat.le_refl _, hnv⟩
          · left; exact hfb
          · right; exact ⟨v, by omega, hv⟩
        · rintro (hfb | ⟨v, hvt, hv⟩)
          · right; left; exact hfb
          · by_cases hlt : v ≤ t
            · right; right; exact ⟨v, hlt, hv⟩
            · have hv_eq : v = t + 1 := by omega
              subst hv_eq
              left; omega
      · intro i hi
        by_cases hilt : i < t
        · exact hsign_t i hilt
        · have hi_eq : i = t := by omega
          subst hi_eq
          exact hstep_sign
  refine ⟨b, st, by simp [st], ?_⟩
  intro i hi
  simpa [Nat.zero_add, f, wordSign] using (hrun N (Nat.le_refl N)).2.2 i hi

/-- Complete bi-directional `E-759` characterization in Lean 4: a finite sign word `w`
is realized at clock `0` by some coherent finite-state greedy replay `(b, st)`
(`st.value ∈ st.seen`) if and only if `wordSign w` satisfies both `TypeIFresh` and `TypeIIFresh`. -/
theorem seeded_replay_realizes_iff_fresh (w : List Bool) :
    (∃ b st, st.value ∈ st.seen ∧ MatchesAt (replaySign b st) 0 w) ↔
      (TypeIFresh (wordSign w) w.length ∧ TypeIIFresh (wordSign w) w.length) := by
  constructor
  · rintro ⟨b, st, hs, hm⟩
    have hag : ∀ i, i < w.length → replaySign b st i = wordSign w i := by
      intro i hi
      have h1 := hm i hi
      simpa [Nat.zero_add, wordSign] using h1
    have hI := seeded_replay_typeIFresh b st hs w.length
    have hII := seeded_replay_typeIIFresh b st w.length
    refine ⟨?_, ?_⟩
    · intro t ht hft u hut hFu hpeq
      have hft' : replaySign b st t = false := by rw [hag t ht]; exact hft
      have hFw1 := fw_eq_of_agree (replaySign b st) (wordSign w) w.length hag (t + 1) (by omega)
      have hFwu := fw_eq_of_agree (replaySign b st) (wordSign w) w.length hag u (by omega)
      have hp1 := pot_eq_of_agree (replaySign b st) (wordSign w) w.length hag (t + 1) (by omega)
        (Fw (wordSign w) (t + 1) - 1)
      have hpu := pot_eq_of_agree (replaySign b st) (wordSign w) w.length hag u (by omega)
        (Fw (wordSign w) (t + 1) - 1)
      exact hI t ht hft' u hut (by omega) (by rw [hFw1, hp1, hpu]; exact hpeq)
    · intro t ht hft u hut hfu hFu hpeq
      have hft' : replaySign b st t = false := by rw [hag t ht]; exact hft
      have hfu' : replaySign b st u = true := by rw [hag u (by omega)]; exact hfu
      have hFw1 := fw_eq_of_agree (replaySign b st) (wordSign w) w.length hag (t + 1) (by omega)
      have hFwu := fw_eq_of_agree (replaySign b st) (wordSign w) w.length hag u (by omega)
      have hp1 := pot_eq_of_agree (replaySign b st) (wordSign w) w.length hag (t + 1) (by omega)
        (Fw (wordSign w) (t + 1) - 1)
      have hpu := pot_eq_of_agree (replaySign b st) (wordSign w) w.length hag u (by omega)
        (Fw (wordSign w) (t + 1) - 1)
      exact hII t ht hft' u hut hfu' (by omega) (by rw [hFw1, hp1, hpu]; exact hpeq)
  · rintro ⟨hI, hII⟩
    exact seeded_replay_realizes_of_fresh w hI hII

/-! ## Part 2: Exact 1-step predecessor obstruction on `TypeIFresh`/`TypeIIFresh`, `SeededReplay`, and `Recaman.Basic.a` -/

/-- `w` has a `(1, 0)` `S`-landing (`areaW = q + 2`), obstructing `S ++ w` via Type-I collision. -/
def BlocksSPredecessor (w : List Bool) : Prop :=
  ∃ q, q < w.length ∧ w[q]! = false ∧ wordHeight w (q + 1) = 1 ∧
    areaW (w.take (q + 1)) = ((q + 2 : Nat) : Int)

/-- `w` has a `(-1, 0)` `S`-landing (`areaW = -(q + 2)`), obstructing `A ++ w` via Type-I collision. -/
def BlocksAPredecessorI (w : List Bool) : Prop :=
  ∃ q, q < w.length ∧ w[q]! = false ∧ wordHeight w (q + 1) = -1 ∧
    areaW (w.take (q + 1)) = -((q + 2 : Nat) : Int)

/-- `w` has a `(-2, 0)` `S`-landing (`areaW = -2*(q + 2)`), obstructing `A ++ w` via Type-II collision. -/
def BlocksAPredecessorII (w : List Bool) : Prop :=
  ∃ q, q < w.length ∧ w[q]! = false ∧ wordHeight w (q + 1) = -2 ∧
    areaW (w.take (q + 1)) = -2 * ((q + 2 : Nat) : Int)

private theorem seg_eq_take_of_matches (f : Nat → Bool) (s : Nat) (w : List Bool)
    (hm : MatchesAt f s w) :
    ∀ k, k ≤ w.length → seg f s k = w.take k
  | 0, _ => by simp [seg]
  | k + 1, hk => by
    rw [seg_succ, seg_eq_take_of_matches f s w hm k (by omega), hm k (by omega)]
    have hlt : k < w.length := by omega
    rw [List.take_succ_eq_append_getElem hlt]
    simp [hlt]

private theorem shift_fw_and_pot (f : Nat → Bool) (s : Nat) (w : List Bool)
    (hm : MatchesAt f s w) (hs : 1 ≤ s) (k : Nat) (hk : k ≤ w.length) (r : Int) :
    Fw f (s + k) = Fw f s + wordHeight w k ∧
    floorPotential f 0 (r - 1) (s + k) - floorPotential f 0 (r - 1) (s - 1) =
      sign (f (s - 1)) + areaW (w.take k) +
        (k : Int) * (Fw f s - Fw f (s - 1)) +
        ((k + 1 : Nat) : Int) * (Fw f (s - 1) - r) := by
  have hseg := seg_eq_take_of_matches f s w hm k hk
  have hFw_k : Fw f (s + k) = Fw f s + wordHeight w k := by
    have h1 := seg_mass f s k
    rw [hseg] at h1
    unfold wordHeight
    omega
  have hAr_k : Ar f s k = areaW (w.take k) := by
    rw [Ar_areaW, hseg]
  have hAr_1 : Ar f (s - 1) 1 = sign (f (s - 1)) := by
    have h1 := Ar_succ f (s - 1) 0
    have h2 := Fw_succ f (s - 1)
    have h0' : Ar f (s - 1) 0 = 0 := rfl
    rw [h0', Int.zero_add, Nat.add_zero] at h1
    change Ar f (s - 1) 1 = Fw f (s - 1 + 1) - Fw f (s - 1) at h1
    omega
  have hsp1 := area_split_at f 0 (s - 1) (s + k) (Nat.zero_le _) (by omega)
  have hsp2 := area_split_at f (s - 1) s (s + k) (by omega) (Nat.le_add_right s k)
  have hlen1 : s + k - (s - 1) = k + 1 := by omega
  have hlen2 : s - (s - 1) = 1 := by omega
  have hlen3 : s + k - s = k := by omega
  rw [Nat.sub_zero, Nat.sub_zero, hlen1] at hsp1
  rw [hlen1, hlen2, hlen3, hAr_1, hAr_k] at hsp2
  have h0 : Fw f 0 = 0 := rfl
  rw [h0] at hsp1
  refine ⟨hFw_k, ?_⟩
  unfold floorPotential
  simp only [Nat.sub_zero, h0]
  rw [hsp1, hsp2]
  have hs_eq : ((s + k : Nat) : Int) - ((s - 1 : Nat) : Int) = ((k + 1 : Nat) : Int) := by omega
  push_cast at hs_eq ⊢
  grind

/-- Any word with `BlocksSPredecessor w` cannot be preceded by `S` in any `TypeIFresh` sequence. -/
theorem blocksSPredecessor_forbids_S_before (f : Nat → Bool) (s : Nat) (w : List Bool)
    (hb : BlocksSPredecessor w) (hs : 1 ≤ s) (hprev : f (s - 1) = false)
    (hm : MatchesAt f s w) :
    ¬ TypeIFresh f (s + w.length) := by
  intro hfresh
  obtain ⟨q, hqL, hqS, hqH, hqA⟩ := hb
  have hsh := shift_fw_and_pot f s w hm hs (q + 1) (by omega) (Fw f (s - 1))
  have hFws : Fw f s = Fw f (s - 1) - 1 := by
    have h1 := Fw_succ f (s - 1)
    rw [show s - 1 + 1 = s by omega, hprev] at h1
    simp [sign] at h1
    omega
  have hFw_land : Fw f (s + q + 1) = Fw f (s - 1) := by
    rw [show s + q + 1 = s + (q + 1) by omega, hsh.1, hqH, hFws]
    omega
  have hpeq : floorPotential f 0 (Fw f (s + q + 1) - 1) (s + q + 1) =
      floorPotential f 0 (Fw f (s + q + 1) - 1) (s - 1) := by
    rw [hFw_land, show s + q + 1 = s + (q + 1) by omega]
    have hp := hsh.2
    rw [hprev, hqA, hFws] at hp
    simp [sign] at hp
    push_cast at hp
    omega
  have hft : f (s + q) = false := by
    rw [hm q hqL, hqS]
  exact hfresh (s + q) (by omega) hft (s - 1) (by omega) hFw_land.symm hpeq

/-- Any word with `BlocksAPredecessorI w ∨ BlocksAPredecessorII w` cannot be preceded by `A`
in any sequence satisfying `TypeIFresh ∧ TypeIIFresh`. -/
theorem blocksAPredecessor_forbids_A_before (f : Nat → Bool) (s : Nat) (w : List Bool)
    (hb : BlocksAPredecessorI w ∨ BlocksAPredecessorII w) (hs : 1 ≤ s) (hprev : f (s - 1) = true)
    (hm : MatchesAt f s w) :
    ¬ (TypeIFresh f (s + w.length) ∧ TypeIIFresh f (s + w.length)) := by
  rintro ⟨hI, hII⟩
  have hFws : Fw f s = Fw f (s - 1) + 1 := by
    have h1 := Fw_succ f (s - 1)
    rw [show s - 1 + 1 = s by omega, hprev] at h1
    simp [sign] at h1
    omega
  rcases hb with ⟨q, hqL, hqS, hqH, hqA⟩ | ⟨q, hqL, hqS, hqH, hqA⟩
  · have hsh := shift_fw_and_pot f s w hm hs (q + 1) (by omega) (Fw f (s - 1))
    have hFw_land : Fw f (s + q + 1) = Fw f (s - 1) := by
      rw [show s + q + 1 = s + (q + 1) by omega, hsh.1, hqH, hFws]; omega
    have hpeq : floorPotential f 0 (Fw f (s + q + 1) - 1) (s + q + 1) =
        floorPotential f 0 (Fw f (s + q + 1) - 1) (s - 1) := by
      rw [hFw_land, show s + q + 1 = s + (q + 1) by omega]
      have hp := hsh.2
      rw [hprev, hqA, hFws] at hp
      simp [sign] at hp
      push_cast at hp
      omega
    have hft : f (s + q) = false := by rw [hm q hqL, hqS]
    exact hI (s + q) (by omega) hft (s - 1) (by omega) hFw_land.symm hpeq
  · have hsh := shift_fw_and_pot f s w hm hs (q + 1) (by omega) (Fw f (s - 1) - 1)
    have hFw_land : Fw f (s + q + 1) = Fw f (s - 1) - 1 := by
      rw [show s + q + 1 = s + (q + 1) by omega, hsh.1, hqH, hFws]; omega
    have hpeq : floorPotential f 0 (Fw f (s + q + 1) - 1) (s + q + 1) =
        floorPotential f 0 (Fw f (s + q + 1) - 1) (s - 1) := by
      rw [hFw_land, show s + q + 1 = s + (q + 1) by omega]
      have hp := hsh.2
      rw [hprev, hqA, hFws] at hp
      simp [sign] at hp
      push_cast at hp
      omega
    have hft : f (s + q) = false := by rw [hm q hqL, hqS]
    exact hII (s + q) (by omega) hft (s - 1) (by omega) hprev (by omega) hpeq

/-- No word blocking both `S`- and `A`-predecessors can appear starting at ANY nonzero clock `s ≥ 1`
in ANY coherent finite-state greedy replay `(b, st)` (`st.value ∈ st.seen`). -/
theorem no_predecessor_forbids_nonzero_clock_replay (w : List Bool)
    (hbS : BlocksSPredecessor w) (hbA : BlocksAPredecessorI w ∨ BlocksAPredecessorII w)
    (b s : Nat) (st : State) (hs : st.value ∈ st.seen) (hs1 : 1 ≤ s) :
    ¬ MatchesAt (replaySign b st) s w := by
  intro hm
  have hI := seeded_replay_typeIFresh b st hs (s + w.length)
  have hII := seeded_replay_typeIIFresh b st (s + w.length)
  cases hprev : replaySign b st (s - 1) with
  | false => exact blocksSPredecessor_forbids_S_before (replaySign b st) s w hbS hs1 hprev hm hI
  | true => exact blocksAPredecessor_forbids_A_before (replaySign b st) s w hbA hs1 hprev hm ⟨hI, hII⟩

private theorem canonical_first_three_true :
    canonicalOrbitSign 0 = true ∧ canonicalOrbitSign 1 = true ∧ canonicalOrbitSign 2 = true := by
  decide

/-- Any word blocking both `S`- and `A`-predecessors and starting with either `S` or `AAS`
NEVER appears at ANY clock `s : Nat` (including `s = 0`) in the real Recamán orbit `Recaman.Basic.a`. -/
theorem no_predecessor_forbids_all_canonical_clocks (w : List Bool)
    (hbS : BlocksSPredecessor w) (hbA : BlocksAPredecessorI w ∨ BlocksAPredecessorII w)
    (hhead : (1 ≤ w.length ∧ w[0]! = false) ∨ (3 ≤ w.length ∧ w[2]! = false)) :
    ∀ s : Nat, ¬ MatchesAt canonicalOrbitSign s w := by
  intro s hm
  by_cases hs0 : s = 0
  · subst hs0
    obtain ⟨hc0, _, hc2⟩ := canonical_first_three_true
    rcases hhead with ⟨h1, hw0⟩ | ⟨h3, hw2⟩
    · have h0 := hm 0 (by omega)
      simp only [Nat.zero_add, hc0, hw0] at h0
      cases h0
    · have h2 := hm 2 (by omega)
      simp only [Nat.zero_add, hc2, hw2] at h2
      cases h2
  · have hs_init : initial.value ∈ initial.seen := by simp [initial]
    exact no_predecessor_forbids_nonzero_clock_replay w hbS hbA 0 s initial hs_init (by omega) hm

/-! ## Part 3: Arbitrary-depth `E-779` infinite family `e779Word k` (`∀ k : Nat`) -/

/-- `E-779` arbitrary-depth family parameterized by `k : Nat` (`r = 3k + 6`, `t = 3k^2 + 8k + 1`):
`AAS ++ S^r ++ A^r ++ (SA)^t ++ SS`. -/
def e779Word (k : Nat) : List Bool :=
  let r := 3 * k + 6
  let t := 3 * k * k + 8 * k + 1
  [true, true, false] ++ List.replicate r false ++ List.replicate r true ++
    repeatWord t [false, true] ++ [false, false]

private theorem repeatWord_length_d (R : Nat) (V : List Bool) :
    (repeatWord R V).length = R * V.length := by
  induction R with
  | zero => simp [repeatWord]
  | succ R ih =>
    simp only [repeatWord, List.length_append, ih]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

private theorem e779Word_length (k : Nat) :
    (e779Word k).length = 2 * (3 * k + 6) + 2 * (3 * k * k + 8 * k + 1) + 5 := by
  unfold e779Word
  simp only [List.length_append, List.length_replicate, repeatWord_length_d, List.length_cons,
    List.length_nil]
  omega

private theorem getElem_repeatWord_sa (t i : Nat) (hi : i < 2 * t) :
    (repeatWord t [false, true])[i]! = (if i % 2 = 0 then false else true) := by
  induction t generalizing i with
  | zero => omega
  | succ t ih =>
    simp only [repeatWord]
    by_cases h0 : i = 0
    · subst h0; simp
    · by_cases h1 : i = 1
      · subst h1; simp
      · have hge2 : 2 ≤ i := by omega
        have hl : ([false, true] : List Bool).length = 2 := rfl
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        rw [hl]
        have := ih (i - 2) (by omega)
        rw [List.getElem!_eq_getElem?_getD] at this
        rw [this]
        have hmod : (i - 2) % 2 = i % 2 := by omega
        rw [hmod]

private theorem e779Word_get (k i : Nat) :
    let r := 3 * k + 6
    let t := 3 * k * k + 8 * k + 1
    let w := e779Word k
    (i = 0 → w[i]! = true) ∧
    (i = 1 → w[i]! = true) ∧
    (i = 2 → w[i]! = false) ∧
    (3 ≤ i → i < 3 + r → w[i]! = false) ∧
    (3 + r ≤ i → i < 3 + 2 * r → w[i]! = true) ∧
    (3 + 2 * r ≤ i → i < 3 + 2 * r + 2 * t →
      w[i]! = if (i - (3 + 2 * r)) % 2 = 0 then false else true) ∧
    (i = 3 + 2 * r + 2 * t → w[i]! = false) ∧
    (i = 4 + 2 * r + 2 * t → w[i]! = false) := by
  intro r t w
  have hl_aas : ([true, true, false] : List Bool).length = 3 := rfl
  have hl_Sr : (List.replicate r false).length = r := List.length_replicate
  have hl_Ar : (List.replicate r true).length = r := List.length_replicate
  have hl_sa : (repeatWord t [false, true]).length = 2 * t := by
    rw [repeatWord_length_d]; simp [Nat.mul_comm]
  have hw_eq : w = ([true, true, false] ++ List.replicate r false ++ List.replicate r true ++
      repeatWord t [false, true]) ++ [false, false] := rfl
  have hget_left : ∀ (u v : List Bool) (j : Nat), j < u.length → (u ++ v)[j]! = u[j]! := by
    intro u v j hj
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hj]
  have hget_right : ∀ (u v : List Bool) (j : Nat), u.length ≤ j →
      (u ++ v)[j]! = v[j - u.length]! := by
    intro u v j hj
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_right hj]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hi; subst hi
    rw [hw_eq, hget_left _ _ 0 (by simp), hget_left _ _ 0 (by simp),
      hget_left _ _ 0 (by simp), hget_left _ _ 0 (by simp)]; rfl
  · intro hi; subst hi
    rw [hw_eq, hget_left _ _ 1 (by simp), hget_left _ _ 1 (by simp),
      hget_left _ _ 1 (by simp), hget_left _ _ 1 (by simp)]; rfl
  · intro hi; subst hi
    rw [hw_eq, hget_left _ _ 2 (by simp), hget_left _ _ 2 (by simp),
      hget_left _ _ 2 (by simp), hget_left _ _ 2 (by simp)]; rfl
  · intro h1 h2
    rw [hw_eq, hget_left _ _ i (by simp [hl_Sr, hl_Ar, hl_sa]; omega),
      hget_left _ _ i (by simp [hl_Sr, hl_Ar]; omega),
      hget_left _ _ i (by simp [hl_Sr]; omega),
      hget_right _ _ i (by simp; omega)]
    rw [hl_aas]
    simp [show i - 3 < r by omega]
  · intro h1 h2
    rw [hw_eq, hget_left _ _ i (by simp [hl_Sr, hl_Ar, hl_sa]; omega),
      hget_left _ _ i (by simp [hl_Sr, hl_Ar]; omega),
      hget_right _ _ i (by simp [hl_Sr]; omega)]
    have hlen : ([true, true, false] ++ List.replicate r false).length = 3 + r := by
      simp [hl_Sr]; omega
    rw [hlen]
    simp [show i - (3 + r) < r by omega]
  · intro h1 h2
    rw [hw_eq, hget_left _ _ i (by simp [hl_Sr, hl_Ar, hl_sa]; omega),
      hget_right _ _ i (by simp [hl_Sr, hl_Ar]; omega)]
    have hlen : ([true, true, false] ++ List.replicate r false ++ List.replicate r true).length =
        3 + 2 * r := by simp [hl_Sr, hl_Ar]; omega
    rw [hlen]
    exact getElem_repeatWord_sa t (i - (3 + 2 * r)) (by omega)
  · intro hi; subst hi
    rw [hw_eq, hget_right _ _ (3 + 2 * r + 2 * t) (by simp [hl_Sr, hl_Ar, hl_sa]; omega)]
    have hlen : ([true, true, false] ++ List.replicate r false ++ List.replicate r true ++
        repeatWord t [false, true]).length = 3 + 2 * r + 2 * t := by
      simp [hl_Sr, hl_Ar, hl_sa]; omega
    rw [hlen, Nat.sub_self]; rfl
  · intro hi; subst hi
    rw [hw_eq, hget_right _ _ (4 + 2 * r + 2 * t) (by simp [hl_Sr, hl_Ar, hl_sa]; omega)]
    have hlen : ([true, true, false] ++ List.replicate r false ++ List.replicate r true ++
        repeatWord t [false, true]).length = 3 + 2 * r + 2 * t := by
      simp [hl_Sr, hl_Ar, hl_sa]; omega
    rw [hlen, show 4 + 2 * r + 2 * t - (3 + 2 * r + 2 * t) = 1 by omega]; rfl

private theorem e779_fw_ar (k : Nat) :
    let r := 3 * k + 6
    let t := 3 * k * k + 8 * k + 1
    let f := wordSign (e779Word k)
    let T0 : Int := 4 + 2 * (r : Int) - (r : Int) * (r : Int)
    (Fw f 0 = 0 ∧ Ar f 0 0 = 0) ∧
    (Fw f 1 = 1 ∧ Ar f 0 1 = 1) ∧
    (Fw f 2 = 2 ∧ Ar f 0 2 = 3) ∧
    (Fw f 3 = 1 ∧ Ar f 0 3 = 4) ∧
    (∀ i, i ≤ r → Fw f (3 + i) = 1 - (i : Int) ∧
      2 * Ar f 0 (3 + i) = 8 + (i : Int) - (i : Int) * (i : Int)) ∧
    (∀ i, i ≤ r → Fw f (3 + r + i) = 1 - (r : Int) + (i : Int) ∧
      2 * Ar f 0 (3 + r + i) =
        8 + (r : Int) - (r : Int) * (r : Int) +
          2 * (i : Int) * (1 - (r : Int)) + (i : Int) * ((i : Int) + 1)) ∧
    (∀ m, m ≤ t → Fw f (3 + 2 * r + 2 * m) = 1 ∧ Ar f 0 (3 + 2 * r + 2 * m) = T0 + (m : Int)) ∧
    (∀ m, m < t → Fw f (4 + 2 * r + 2 * m) = 0 ∧ Ar f 0 (4 + 2 * r + 2 * m) = T0 + (m : Int)) ∧
    (Fw f (4 + 2 * r + 2 * t) = 0 ∧ Ar f 0 (4 + 2 * r + 2 * t) = T0 + (t : Int)) ∧
    (Fw f (5 + 2 * r + 2 * t) = -1 ∧ Ar f 0 (5 + 2 * r + 2 * t) = T0 + (t : Int) - 1) := by
  intro r t f T0
  have hstep : ∀ j, Fw f (j + 1) = Fw f j + sign (f j) ∧
      Ar f 0 (j + 1) = Ar f 0 j + Fw f (j + 1) := by
    intro j
    refine ⟨Fw_succ f j, ?_⟩
    have := Ar_succ f 0 j
    have h0 : Fw f 0 = 0 := rfl
    simpa [h0] using this
  have h0 : Fw f 0 = 0 ∧ Ar f 0 0 = 0 := ⟨rfl, rfl⟩
  have h1 : Fw f 1 = 1 ∧ Ar f 0 1 = 1 := by
    have hg := (e779Word_get k 0).1 rfl
    have hs := hstep 0
    change f 0 = true at hg
    rw [hg, h0.1, h0.2] at hs; simp [sign] at hs; omega
  have h2 : Fw f 2 = 2 ∧ Ar f 0 2 = 3 := by
    have hg := (e779Word_get k 1).2.1 rfl
    have hs := hstep 1
    change f 1 = true at hg
    rw [hg, h1.1, h1.2] at hs; simp [sign] at hs; omega
  have h3 : Fw f 3 = 1 ∧ Ar f 0 3 = 4 := by
    have hg := (e779Word_get k 2).2.2.1 rfl
    have hs := hstep 2
    change f 2 = false at hg
    rw [hg, h2.1, h2.2] at hs; simp [sign] at hs; omega
  have hSr : ∀ i, i ≤ r → Fw f (3 + i) = 1 - (i : Int) ∧
      2 * Ar f 0 (3 + i) = 8 + (i : Int) - (i : Int) * (i : Int) := by
    intro i
    induction i with
    | zero => intro _; rw [Nat.add_zero, h3.1, h3.2]; omega
    | succ i ih =>
      intro hi
      have ih' := ih (by omega)
      have hg := (e779Word_get k (3 + i)).2.2.2.1 (by omega) (by omega)
      have hs := hstep (3 + i)
      change f (3 + i) = false at hg
      rw [show 3 + i + 1 = 3 + (i + 1) by omega, hg] at hs
      simp [sign] at hs
      push_cast
      grind
  have hAr : ∀ i, i ≤ r → Fw f (3 + r + i) = 1 - (r : Int) + (i : Int) ∧
      2 * Ar f 0 (3 + r + i) =
        8 + (r : Int) - (r : Int) * (r : Int) +
          2 * (i : Int) * (1 - (r : Int)) + (i : Int) * ((i : Int) + 1) := by
    intro i
    induction i with
    | zero =>
      intro _
      have hr0 := hSr r (Nat.le_refl r)
      rw [Nat.add_zero, hr0.1]; push_cast; grind
    | succ i ih =>
      intro hi
      have ih' := ih (by omega)
      have hg := (e779Word_get k (3 + r + i)).2.2.2.2.1 (by omega) (by omega)
      have hs := hstep (3 + r + i)
      change f (3 + r + i) = true at hg
      rw [show 3 + r + i + 1 = 3 + r + (i + 1) by omega, hg] at hs
      simp [sign] at hs
      push_cast
      grind
  have hT0 : Fw f (3 + 2 * r) = 1 ∧ Ar f 0 (3 + 2 * r) = T0 := by
    have hr := hAr r (Nat.le_refl r)
    rw [show 3 + r + r = 3 + 2 * r by omega] at hr
    dsimp only [T0]
    grind
  have hSA_even : ∀ m, m ≤ t →
      Fw f (3 + 2 * r + 2 * m) = 1 ∧ Ar f 0 (3 + 2 * r + 2 * m) = T0 + (m : Int) := by
    intro m
    induction m with
    | zero => intro _; simpa using hT0
    | succ m ih =>
      intro hm
      have ih' := ih (by omega)
      have hgS := (e779Word_get k (3 + 2 * r + 2 * m)).2.2.2.2.2.1 (by omega) (by omega)
      have hmod0 : (3 + 2 * r + 2 * m - (3 + 2 * r)) % 2 = 0 := by omega
      rw [if_pos hmod0] at hgS
      have hs1 := hstep (3 + 2 * r + 2 * m)
      change f (3 + 2 * r + 2 * m) = false at hgS
      rw [hgS, ih'.1, ih'.2] at hs1; simp [sign] at hs1
      have hgA := (e779Word_get k (3 + 2 * r + 2 * m + 1)).2.2.2.2.2.1 (by omega) (by omega)
      have hmod1 : ¬ (3 + 2 * r + 2 * m + 1 - (3 + 2 * r)) % 2 = 0 := by omega
      rw [if_neg hmod1] at hgA
      have hs2 := hstep (3 + 2 * r + 2 * m + 1)
      change f (3 + 2 * r + 2 * m + 1) = true at hgA
      rw [hgA, hs1.1, hs1.2, show 3 + 2 * r + 2 * m + 1 + 1 = 3 + 2 * r + 2 * (m + 1) by omega] at hs2
      simp [sign] at hs2
      push_cast; grind
  have hSA_odd : ∀ m, m < t →
      Fw f (4 + 2 * r + 2 * m) = 0 ∧ Ar f 0 (4 + 2 * r + 2 * m) = T0 + (m : Int) := by
    intro m hm
    have he := hSA_even m (by omega)
    have hgS := (e779Word_get k (3 + 2 * r + 2 * m)).2.2.2.2.2.1 (by omega) (by omega)
    have hmod0 : (3 + 2 * r + 2 * m - (3 + 2 * r)) % 2 = 0 := by omega
    rw [if_pos hmod0] at hgS
    have hs1 := hstep (3 + 2 * r + 2 * m)
    change f (3 + 2 * r + 2 * m) = false at hgS
    rw [hgS, he.1, he.2, show 3 + 2 * r + 2 * m + 1 = 4 + 2 * r + 2 * m by omega] at hs1
    simp [sign] at hs1
    omega
  have hS1 : Fw f (4 + 2 * r + 2 * t) = 0 ∧ Ar f 0 (4 + 2 * r + 2 * t) = T0 + (t : Int) := by
    have he := hSA_even t (Nat.le_refl t)
    have hg := (e779Word_get k (3 + 2 * r + 2 * t)).2.2.2.2.2.2.1 rfl
    have hs := hstep (3 + 2 * r + 2 * t)
    change f (3 + 2 * r + 2 * t) = false at hg
    rw [hg, he.1, he.2, show 3 + 2 * r + 2 * t + 1 = 4 + 2 * r + 2 * t by omega] at hs
    simp [sign] at hs; omega
  have hS2 : Fw f (5 + 2 * r + 2 * t) = -1 ∧ Ar f 0 (5 + 2 * r + 2 * t) = T0 + (t : Int) - 1 := by
    have hg := (e779Word_get k (4 + 2 * r + 2 * t)).2.2.2.2.2.2.2 rfl
    have hs := hstep (4 + 2 * r + 2 * t)
    change f (4 + 2 * r + 2 * t) = false at hg
    rw [hg, hS1.1, hS1.2, show 4 + 2 * r + 2 * t + 1 = 5 + 2 * r + 2 * t by omega] at hs
    simp [sign] at hs; omega
  exact ⟨h0, h1, h2, h3, hSr, hAr, hSA_even, hSA_odd, hS1, hS2⟩

private theorem fw_eq_wordHeight (w : List Bool) (j : Nat) (hj : j ≤ w.length) :
    Fw (wordSign w) j = wordHeight w j ∧ Ar (wordSign w) 0 j = areaW (w.take j) := by
  have hm : MatchesAt (wordSign w) 0 w := fun i _ => by simp [wordSign]
  have hseg := seg_eq_take_of_matches (wordSign w) 0 w hm j hj
  have hF := seg_mass (wordSign w) 0 j
  have hA := Ar_areaW (wordSign w) 0 j
  have h0 : Fw (wordSign w) 0 = 0 := rfl
  rw [hseg, Nat.zero_add, h0] at hF
  rw [hseg] at hA
  unfold wordHeight
  omega

private theorem e779_pot_eq (f : Nat → Bool) (r : Int) (j : Nat) :
    floorPotential f 0 (r - 1) j = Ar f 0 j - (j : Int) * r := by
  unfold floorPotential
  have h0 : Fw f 0 = 0 := rfl
  simp only [Nat.sub_zero, h0]
  grind

/-- Every member of the arbitrary-depth `E-779` family `e779Word k` (`∀ k : Nat`)
unconditionally satisfies both `TypeIFresh` and `TypeIIFresh` (`E-759 (I)/(II) = (0, 0)`). -/
theorem e779Word_fresh (k : Nat) :
    TypeIFresh (wordSign (e779Word k)) (e779Word k).length ∧
    TypeIIFresh (wordSign (e779Word k)) (e779Word k).length := by
  let r := 3 * k + 6
  let t := 3 * k * k + 8 * k + 1
  let f := wordSign (e779Word k)
  let T0 : Int := 4 + 2 * (r : Int) - (r : Int) * (r : Int)
  change TypeIFresh f (e779Word k).length ∧ TypeIIFresh f (e779Word k).length
  have hlen : (e779Word k).length = 5 + 2 * r + 2 * t := by
    rw [e779Word_length k]; dsimp only [r, t]; omega
  have h3t : 3 * (t : Int) = (r : Int) * (r : Int) - 4 * (r : Int) - 9 := by
    dsimp only [r, t]; push_cast; grind
  have hr6 : 6 ≤ r := by dsimp only [r]; omega
  have ht1 : 1 ≤ t := by dsimp only [t]; omega
  have hT0_lt : T0 + (t : Int) < 0 := by
    have hr2 : (36 : Int) ≤ (r : Int) * (r : Int) := by
      have : (6 : Int) * 6 ≤ (r : Int) * (r : Int) :=
        Int.mul_le_mul (by omega) (by omega) (by decide) (by omega)
      omega
    have hr6m : 6 * (r : Int) ≤ (r : Int) * (r : Int) :=
      Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    dsimp only [T0]; omega
  obtain ⟨h0, h1, h2, h3, hSr, hAr, hSA_even, hSA_odd, hS1, hS2⟩ := e779_fw_ar k
  change Fw f 0 = 0 ∧ Ar f 0 0 = 0 at h0
  change Fw f 1 = 1 ∧ Ar f 0 1 = 1 at h1
  change Fw f 2 = 2 ∧ Ar f 0 2 = 3 at h2
  change Fw f 3 = 1 ∧ Ar f 0 3 = 4 at h3
  change ∀ i, i ≤ r → Fw f (3 + i) = 1 - (i : Int) ∧
    2 * Ar f 0 (3 + i) = 8 + (i : Int) - (i : Int) * (i : Int) at hSr
  change ∀ i, i ≤ r → Fw f (3 + r + i) = 1 - (r : Int) + (i : Int) ∧
    2 * Ar f 0 (3 + r + i) = 8 + (r : Int) - (r : Int) * (r : Int) +
      2 * (i : Int) * (1 - (r : Int)) + (i : Int) * ((i : Int) + 1) at hAr
  change ∀ m, m ≤ t → Fw f (3 + 2 * r + 2 * m) = 1 ∧ Ar f 0 (3 + 2 * r + 2 * m) = T0 + (m : Int) at hSA_even
  change ∀ m, m < t → Fw f (4 + 2 * r + 2 * m) = 0 ∧ Ar f 0 (4 + 2 * r + 2 * m) = T0 + (m : Int) at hSA_odd
  change Fw f (4 + 2 * r + 2 * t) = 0 ∧ Ar f 0 (4 + 2 * r + 2 * t) = T0 + (t : Int) at hS1
  change Fw f (5 + 2 * r + 2 * t) = -1 ∧ Ar f 0 (5 + 2 * r + 2 * t) = T0 + (t : Int) - 1 at hS2
  have hAr_m1 : Fw f (1 + 2 * r) = -1 ∧ Ar f 0 (1 + 2 * r) = T0 - 1 := by
    have h := hAr (r - 2) (by omega)
    rw [show 3 + r + (r - 2) = 1 + 2 * r by omega] at h
    have hr_sub : ((r - 2 : Nat) : Int) = (r : Int) - 2 := by omega
    rw [hr_sub] at h
    dsimp only [T0]; grind
  have hAr_0 : Fw f (2 + 2 * r) = 0 ∧ Ar f 0 (2 + 2 * r) = T0 - 1 := by
    have h := hAr (r - 1) (by omega)
    rw [show 3 + r + (r - 1) = 2 + 2 * r by omega] at h
    have hr_sub : ((r - 1 : Nat) : Int) = (r : Int) - 1 := by omega
    rw [hr_sub] at h
    dsimp only [T0]; grind
  have hSr_1 : Fw f 4 = 0 ∧ Ar f 0 4 = 4 := by
    have h := hSr 1 (by omega)
    rw [show (3 : Nat) + 1 = 4 by rfl] at h
    omega
  have hSr_2 : Fw f 5 = -1 ∧ Ar f 0 5 = 3 := by
    have h := hSr 2 (by omega)
    rw [show (3 : Nat) + 2 = 5 by rfl] at h
    omega
  have hZero_class : ∀ u, u ≤ 5 + 2 * r + 2 * t → Fw f u = 0 →
      u = 0 ∨ u = 4 ∨ u = 2 + 2 * r ∨ (∃ m, m ≤ t ∧ u = 4 + 2 * r + 2 * m) := by
    intro u hu hFu
    by_cases hu3 : u ≤ 3
    · rcases (show u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 by omega) with rfl | rfl | rfl | rfl <;> omega
    · by_cases huSr : u ≤ 3 + r
      · have h := (hSr (u - 3) (by omega)).1
        rw [show 3 + (u - 3) = u by omega] at h; omega
      · by_cases huAr : u ≤ 3 + 2 * r
        · have h := (hAr (u - (3 + r)) (by omega)).1
          rw [show 3 + r + (u - (3 + r)) = u by omega] at h; omega
        · by_cases huEnd : u = 5 + 2 * r + 2 * t
          · rw [huEnd] at hFu; omega
          · by_cases hev : (u - (3 + 2 * r)) % 2 = 0
            · let m := (u - (3 + 2 * r)) / 2
              have hm : m ≤ t := by dsimp only [m]; omega
              have h := (hSA_even m hm).1
              rw [show 3 + 2 * r + 2 * m = u by dsimp only [m]; omega] at h; omega
            · let m := (u - (4 + 2 * r)) / 2
              have hm : m ≤ t := by dsimp only [m]; omega
              right; right; right
              exact ⟨m, hm, by dsimp only [m]; omega⟩
  have hNeg1_class : ∀ u, u ≤ 5 + 2 * r + 2 * t → Fw f u = -1 →
      u = 5 ∨ u = 1 + 2 * r ∨ u = 5 + 2 * r + 2 * t := by
    intro u hu hFu
    by_cases hu3 : u ≤ 3
    · rcases (show u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 by omega) with rfl | rfl | rfl | rfl <;> omega
    · by_cases huSr : u ≤ 3 + r
      · have h := (hSr (u - 3) (by omega)).1
        rw [show 3 + (u - 3) = u by omega] at h; omega
      · by_cases huAr : u ≤ 3 + 2 * r
        · have h := (hAr (u - (3 + r)) (by omega)).1
          rw [show 3 + r + (u - (3 + r)) = u by omega] at h; omega
        · by_cases huEnd : u = 5 + 2 * r + 2 * t
          · right; right; exact huEnd
          · by_cases hev : (u - (3 + 2 * r)) % 2 = 0
            · let m := (u - (3 + 2 * r)) / 2
              have h := (hSA_even m (by dsimp only [m]; omega)).1
              rw [show 3 + 2 * r + 2 * m = u by dsimp only [m]; omega] at h; omega
            · let m := (u - (4 + 2 * r)) / 2
              by_cases hmt : m < t
              · have h := (hSA_odd m hmt).1
                rw [show 4 + 2 * r + 2 * m = u by dsimp only [m]; omega] at h; omega
              · have hu4 : u = 4 + 2 * r + 2 * t := by omega
                rw [hu4] at hFu; omega
  have hOneTrue : ∀ u, u < 5 + 2 * r + 2 * t → f u = true → Fw f u = 1 → u = 1 := by
    intro u hu hfu hFu
    by_cases hu3 : u ≤ 3
    · rcases (show u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 by omega) with rfl | rfl | rfl | rfl
      · omega
      · rfl
      · omega
      · have hg := (e779Word_get k 3).2.2.2.1 (by omega) (by omega)
        change f 3 = false at hg; rw [hg] at hfu; cases hfu
    · by_cases huSr : u < 3 + r
      · have hg := (e779Word_get k u).2.2.2.1 (by omega) huSr
        change f u = false at hg; rw [hg] at hfu; cases hfu
      · by_cases huAr : u < 3 + 2 * r
        · have h := (hAr (u - (3 + r)) (by omega)).1
          rw [show 3 + r + (u - (3 + r)) = u by omega] at h; omega
        · by_cases huSA : u < 3 + 2 * r + 2 * t
          · have hg := (e779Word_get k u).2.2.2.2.2.1 (by omega) huSA
            change f u = _ at hg
            by_cases hev : (u - (3 + 2 * r)) % 2 = 0
            · rw [if_pos hev] at hg; rw [hg] at hfu; cases hfu
            · let m := (u - (4 + 2 * r)) / 2
              have h := (hSA_odd m (by dsimp only [m]; omega)).1
              rw [show 4 + 2 * r + 2 * m = u by dsimp only [m]; omega] at h; omega
          · by_cases hu1 : u = 3 + 2 * r + 2 * t
            · subst hu1
              have hg := (e779Word_get k (3 + 2 * r + 2 * t)).2.2.2.2.2.2.1 rfl
              change f (3 + 2 * r + 2 * t) = false at hg; rw [hg] at hfu; cases hfu
            · have hu2 : u = 4 + 2 * r + 2 * t := by omega
              subst hu2
              have hg := (e779Word_get k (4 + 2 * r + 2 * t)).2.2.2.2.2.2.2 rfl
              change f (4 + 2 * r + 2 * t) = false at hg; rw [hg] at hfu; cases hfu
  -- Classify all `S`-steps `s < 5 + 2*r + 2*t`
  have hS_step_class : ∀ s, s < 5 + 2 * r + 2 * t → f s = false →
      s = 2 ∨ (3 ≤ s ∧ s < 3 + r) ∨
        (∃ m, m ≤ t ∧ s = 3 + 2 * r + 2 * m) ∨ s = 4 + 2 * r + 2 * t := by
    intro s hs hfs
    by_cases hs2 : s ≤ 2
    · rcases (show s = 0 ∨ s = 1 ∨ s = 2 by omega) with rfl | rfl | rfl
      · have hg := (e779Word_get k 0).1 rfl; change f 0 = true at hg; rw [hg] at hfs; cases hfs
      · have hg := (e779Word_get k 1).2.1 rfl; change f 1 = true at hg; rw [hg] at hfs; cases hfs
      · left; rfl
    · by_cases hsSr : s < 3 + r
      · right; left; exact ⟨by omega, hsSr⟩
      · by_cases hsAr : s < 3 + 2 * r
        · have hg := (e779Word_get k s).2.2.2.2.1 (by omega) hsAr
          change f s = true at hg; rw [hg] at hfs; cases hfs
        · by_cases hsSA : s < 3 + 2 * r + 2 * t
          · have hg := (e779Word_get k s).2.2.2.2.2.1 (by omega) hsSA
            change f s = _ at hg
            by_cases hev : (s - (3 + 2 * r)) % 2 = 0
            · right; right; left
              exact ⟨(s - (3 + 2 * r)) / 2, by omega, by omega⟩
            · rw [if_neg hev] at hg; rw [hg] at hfs; cases hfs
          · by_cases hs1 : s = 3 + 2 * r + 2 * t
            · right; right; left; exact ⟨t, Nat.le_refl t, hs1⟩
            · right; right; right; omega
  have hSA_odd_le : ∀ m, m ≤ t →
      Fw f (4 + 2 * r + 2 * m) = 0 ∧ Ar f 0 (4 + 2 * r + 2 * m) = T0 + (m : Int) := by
    intro m hm
    by_cases hlt : m < t
    · exact hSA_odd m hlt
    · have hm_eq : m = t := by omega
      subst hm_eq; exact hS1
  refine ⟨?_, ?_⟩
  · -- TypeIFresh
    intro s hs hfs u hus hFu hpeq
    rw [hlen] at hs
    rcases hS_step_class s hs hfs with rfl | ⟨hs3, hsSr⟩ | ⟨m, hm, rfl⟩ | rfl
    · -- s = 2 -> s + 1 = 3, height 1
      rw [show (2 : Nat) + 1 = 3 by rfl] at hFu hpeq
      rw [h3.1] at hFu hpeq
      rw [e779_pot_eq, e779_pot_eq, h3.2] at hpeq
      rcases (show u = 0 ∨ u = 1 ∨ u = 2 by omega) with rfl | rfl | rfl <;> omega
    · -- 3 ≤ s < 3 + r -> s + 1 = 3 + (s - 2), height 1 - (s - 2) ≤ 0
      by_cases hs_eq3 : s = 3
      · subst hs_eq3
        rw [show (3 : Nat) + 1 = 4 by rfl] at hFu hpeq
        rw [hSr_1.1] at hFu hpeq
        rw [e779_pot_eq, e779_pot_eq, hSr_1.2] at hpeq
        rcases (show u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 by omega) with rfl | rfl | rfl | rfl <;> omega
      · -- 4 ≤ s < 3 + r -> Fw f (s + 1) = 3 - s ≤ -1, while ∀ u ≤ s, Fw f u ≥ 4 - s!
        have hFs1 := (hSr (s - 2) (by omega)).1
        rw [show 3 + (s - 2) = s + 1 by omega] at hFs1
        by_cases hu3 : u ≤ 3
        · rcases (show u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 by omega) with rfl | rfl | rfl | rfl <;> omega
        · have hFuu := (hSr (u - 3) (by omega)).1
          rw [show 3 + (u - 3) = u by omega] at hFuu
          omega
    · -- s = 3 + 2*r + 2*m -> s + 1 = 4 + 2*r + 2*m, height 0
      have hland := hSA_odd_le m hm
      rw [show 3 + 2 * r + 2 * m + 1 = 4 + 2 * r + 2 * m by omega] at hFu hpeq
      rw [hland.1] at hFu hpeq
      rw [e779_pot_eq, e779_pot_eq, hland.2] at hpeq
      rcases hZero_class u (by omega) hFu with rfl | rfl | rfl | ⟨m', hm', rfl⟩
      · omega
      · omega
      · rw [hAr_0.2] at hpeq; omega
      · have hl' := hSA_odd_le m' hm'
        rw [hl'.2] at hpeq
        omega
    · -- s = 4 + 2*r + 2*t -> s + 1 = 5 + 2*r + 2*t, height -1
      rw [show 4 + 2 * r + 2 * t + 1 = 5 + 2 * r + 2 * t by omega] at hFu hpeq
      rw [hS2.1] at hFu hpeq
      rw [e779_pot_eq, e779_pot_eq, hS2.2] at hpeq
      rcases hNeg1_class u (by omega) hFu with rfl | rfl | huEnd
      · rw [hSr_2.2] at hpeq
        dsimp only [T0] at hpeq; push_cast at hpeq; omega
      · rw [hAr_m1.2] at hpeq
        dsimp only [T0] at hpeq; push_cast at hpeq; omega
      · omega
  · -- TypeIIFresh
    intro s hs hfs u hus hfu hFu hpeq
    rw [hlen] at hs
    rcases hS_step_class s hs hfs with rfl | ⟨hs3, hsSr⟩ | ⟨m, hm, rfl⟩ | rfl
    · -- s = 2 -> height 1, need Fw u = 2 and u < 2
      rw [h3.1] at hFu
      rcases (show u = 0 ∨ u = 1 by omega) with rfl | rfl <;> omega
    · -- 3 ≤ s < 3 + r: Fw(s + 1) = 3 - s; u < s with f u = true => u ∈ {0, 1}!
      have hu01 : u = 0 ∨ u = 1 := by
        by_cases h2u : u < 2
        · omega
        · by_cases h2eq : u = 2
          · subst h2eq
            have hg := (e779Word_get k 2).2.2.1 rfl; change f 2 = false at hg; rw [hg] at hfu; cases hfu
          · have hg := (e779Word_get k u).2.2.2.1 (by omega) (by omega)
            change f u = false at hg; rw [hg] at hfu; cases hfu
      have hFs1 := (hSr (s - 2) (by omega)).1
      rw [show 3 + (s - 2) = s + 1 by omega] at hFs1
      rcases hu01 with rfl | rfl
      · -- u = 0 (Fw = 0, Ar = 0) => Fw(s+1) = -1 => s = 4, s+1 = 5
        have hs4 : s = 4 := by omega
        subst hs4
        rw [hSr_2.1] at hpeq
        rw [e779_pot_eq, e779_pot_eq, hSr_2.2, h0.2] at hpeq
        omega
      · -- u = 1 (Fw = 1, Ar = 1) => Fw(s+1) = 0 => s = 3, s+1 = 4
        have hs3' : s = 3 := by omega
        subst hs3'
        rw [hSr_1.1] at hpeq
        rw [e779_pot_eq, e779_pot_eq, hSr_1.2, h1.2] at hpeq
        omega
    · -- s = 3 + 2*r + 2*m -> height 0, need Fw u = 1 and f u = true => u = 1!
      have hland := hSA_odd_le m hm
      rw [show 3 + 2 * r + 2 * m + 1 = 4 + 2 * r + 2 * m by omega] at hFu hpeq
      rw [hland.1] at hFu hpeq
      have hu1 : u = 1 := hOneTrue u (by omega) hfu (by omega)
      subst hu1
      rw [e779_pot_eq, e779_pot_eq, hland.2, h1.2] at hpeq
      omega
    · -- s = 4 + 2*r + 2*t -> height -1, need Fw u = 0 and f u = true
      rw [show 4 + 2 * r + 2 * t + 1 = 5 + 2 * r + 2 * t by omega] at hFu hpeq
      rw [hS2.1] at hFu hpeq
      rw [e779_pot_eq, e779_pot_eq, hS2.2] at hpeq
      rcases hZero_class u (by omega) (by omega) with rfl | rfl | rfl | ⟨m', hm', rfl⟩
      · rw [h0.2] at hpeq
        dsimp only [T0] at hpeq; push_cast at hpeq; omega
      · have hg := (e779Word_get k 4).2.2.2.1 (by omega) (by omega)
        change f 4 = false at hg; rw [hg] at hfu; cases hfu
      · rw [hAr_0.2] at hpeq
        dsimp only [T0] at hpeq; push_cast at hpeq; omega
      · have hl' := hSA_odd_le m' hm'
        rw [hl'.2] at hpeq
        dsimp only [T0] at hpeq; push_cast at hpeq; omega

/-- Arbitrary-depth dynamic separation theorem (`E-779` formalized unconditionally on
`SeededReplay.run` and `Recaman.Basic.a`): for EVERY `k : Nat`, `e779Word k` reaches negative
relative excursion depth `-(3k + 5)`, is realized at clock `0` by an explicit coherent
finite-state greedy replay, yet has NO coherent 1-step predecessor (`s ≥ 1`) and NEVER appears
at ANY clock `s : Nat` of the real Recamán sequence `Recaman.Basic.a`. -/
theorem e779Word_arbitrary_depth_dynamic_separation (k : Nat) :
    (∃ b st, st.value ∈ st.seen ∧ MatchesAt (replaySign b st) 0 (e779Word k)) ∧
    (∀ b st, st.value ∈ st.seen → ∀ s, 1 ≤ s → ¬ MatchesAt (replaySign b st) s (e779Word k)) ∧
    (∀ s : Nat, ¬ MatchesAt canonicalOrbitSign s (e779Word k)) ∧
    wordHeight (e779Word k) (3 * k + 9) = -((3 * k + 5 : Nat) : Int) := by
  let r := 3 * k + 6
  let t := 3 * k * k + 8 * k + 1
  have hlen : (e779Word k).length = 5 + 2 * r + 2 * t := by
    rw [e779Word_length k]; dsimp only [r, t]; omega
  have h3t : 3 * (t : Int) = (r : Int) * (r : Int) - 4 * (r : Int) - 9 := by
    dsimp only [r, t]; push_cast; grind
  have hfr := e779Word_fresh k
  have hreal := seeded_replay_realizes_of_fresh (e779Word k) hfr.1 hfr.2
  obtain ⟨_, _, _, h3, hSr, _, _, _, _, hS2⟩ := e779_fw_ar k
  have hbS : BlocksSPredecessor (e779Word k) := by
    refine ⟨2, by omega, (e779Word_get k 2).2.2.1 rfl, ?_, ?_⟩
    · have h := fw_eq_wordHeight (e779Word k) 3 (by omega)
      rw [show (2 : Nat) + 1 = 3 by rfl]; omega
    · have h := fw_eq_wordHeight (e779Word k) 3 (by omega)
      rw [show (2 : Nat) + 1 = 3 by rfl]; omega
  have hbA : BlocksAPredecessorI (e779Word k) := by
    refine ⟨4 + 2 * r + 2 * t, by omega, (e779Word_get k (4 + 2 * r + 2 * t)).2.2.2.2.2.2.2 rfl, ?_, ?_⟩
    · have h := fw_eq_wordHeight (e779Word k) (5 + 2 * r + 2 * t) (by omega)
      rw [show 4 + 2 * r + 2 * t + 1 = 5 + 2 * r + 2 * t by omega]
      have hFwEnd : Fw (wordSign (e779Word k)) (5 + 2 * r + 2 * t) = -1 := hS2.1
      omega
    · have h := fw_eq_wordHeight (e779Word k) (5 + 2 * r + 2 * t) (by omega)
      rw [show 4 + 2 * r + 2 * t + 1 = 5 + 2 * r + 2 * t by omega]
      have hArEnd : Ar (wordSign (e779Word k)) 0 (5 + 2 * r + 2 * t) =
          4 + 2 * (r : Int) - (r : Int) * (r : Int) + (t : Int) - 1 := hS2.2
      push_cast
      omega
  have hdepth : wordHeight (e779Word k) (3 * k + 9) = -((3 * k + 5 : Nat) : Int) := by
    have h := fw_eq_wordHeight (e779Word k) (3 + r) (by omega)
    have hmin := (hSr r (Nat.le_refl r)).1
    rw [show 3 + r = 3 * k + 9 by dsimp only [r]; omega] at h hmin
    push_cast at hmin ⊢
    dsimp only [r] at hmin
    omega
  refine ⟨hreal, ?_, ?_, hdepth⟩
  · intro b st hs s hs1
    exact no_predecessor_forbids_nonzero_clock_replay (e779Word k) hbS (Or.inl hbA) b s st hs hs1
  · exact no_predecessor_forbids_all_canonical_clocks (e779Word k) hbS (Or.inl hbA)
      (Or.inr ⟨by omega, (e779Word_get k 2).2.2.1 rfl⟩)

/-! ## Part 4: Initial-`S` and initial-`SS` Type-I / Type-II dynamic separation witnesses -/

/-- Decidable `O(N^2)` chronological freshness checker using single-pass prefix states. -/
private def wordStatesAux : List Bool → Nat → Int → Int → List (Nat × Int × Int)
  | [], t, h, ar => [(t, h, ar)]
  | b :: rest, t, h, ar =>
    let h' := h + sign b
    let ar' := ar + h'
    (t, h, ar) :: wordStatesAux rest (t + 1) h' ar'

private theorem wordStatesAux_mem (w : List Bool) (t₀ : Nat) (h₀ ar₀ : Int) (f : Nat → Bool)
    (hFw₀ : Fw f t₀ = h₀) (hAr₀ : Ar f 0 t₀ = ar₀)
    (hm : MatchesAt f t₀ w) :
    ∀ x, x ∈ wordStatesAux w t₀ h₀ ar₀ ↔
      ∃ j, j ≤ w.length ∧ x = (t₀ + j, Fw f (t₀ + j), Ar f 0 (t₀ + j)) := by
  induction w generalizing t₀ h₀ ar₀ with
  | nil =>
    intro x
    simp only [wordStatesAux, List.mem_singleton, List.length_nil]
    constructor
    · rintro rfl; exact ⟨0, Nat.le_refl 0, by simp [hFw₀, hAr₀]⟩
    · rintro ⟨j, hj, rfl⟩
      have : j = 0 := by omega
      subst this; simp [hFw₀, hAr₀]
  | cons b rest ih =>
    intro x
    have hfb : f t₀ = b := by
      have := hm 0 (by simp)
      simpa using this
    have hFw1 : Fw f (t₀ + 1) = h₀ + sign b := by
      rw [Fw_succ, hFw₀, hfb]
    have hAr1 : Ar f 0 (t₀ + 1) = ar₀ + (h₀ + sign b) := by
      have hs := Ar_succ f 0 t₀
      have h0 : Fw f 0 = 0 := rfl
      simp only [Nat.zero_add, h0, Int.sub_zero] at hs
      rw [hs, hAr₀, hFw1]
    have hm' : MatchesAt f (t₀ + 1) rest := by
      intro i hi
      have := hm (i + 1) (by simp; omega)
      rw [show t₀ + (i + 1) = t₀ + 1 + i by omega] at this
      simpa using this
    have ih' := ih (t₀ + 1) (h₀ + sign b) (ar₀ + (h₀ + sign b)) hFw1 hAr1 hm' x
    simp only [wordStatesAux, List.mem_cons, List.length_cons, ih']
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact ⟨0, Nat.zero_le _, by simp [hFw₀, hAr₀]⟩
      · exact ⟨j + 1, by omega, by rw [show t₀ + 1 + j = t₀ + (j + 1) by omega]⟩
    · rintro ⟨j, hj, rfl⟩
      cases j with
      | zero => left; simp [hFw₀, hAr₀]
      | succ j =>
        right
        exact ⟨j, by omega, by rw [show t₀ + (j + 1) = t₀ + 1 + j by omega]⟩

private def checkFresh (w : List Bool) : Bool :=
  let st := wordStatesAux w 0 0 0
  st.all (fun x =>
    let t := x.1
    if t = 0 then true
    else if w[t - 1]! = true then true
    else
      let h := x.2.1
      let ar := x.2.2
      let p := ar - (t : Int) * h
      st.all (fun y =>
        let u := y.1
        let hu := y.2.1
        let aru := y.2.2
        let okI := !(decide (u < t && hu == h && aru - (u : Int) * h == p))
        let okII := !(decide (u + 1 < t && w[u]! == true && hu == h + 1 && aru - (u : Int) * h == p))
        okI && okII))

private theorem checkFresh_sound (w : List Bool) (hc : checkFresh w = true) :
    TypeIFresh (wordSign w) w.length ∧ TypeIIFresh (wordSign w) w.length := by
  unfold checkFresh at hc
  rw [List.all_eq_true] at hc
  have hm0 : MatchesAt (wordSign w) 0 w := fun i _ => by simp [wordSign]
  have hmem := wordStatesAux_mem w 0 0 0 (wordSign w) rfl rfl hm0
  refine ⟨?_, ?_⟩
  · intro t ht hft u hut hFu hpeq
    have hx_mem : (t + 1, Fw (wordSign w) (t + 1), Ar (wordSign w) 0 (t + 1)) ∈
        wordStatesAux w 0 0 0 := (hmem _).mpr ⟨t + 1, by omega, by simp⟩
    have hy_mem : (u, Fw (wordSign w) u, Ar (wordSign w) 0 u) ∈
        wordStatesAux w 0 0 0 := (hmem _).mpr ⟨u, by omega, by simp⟩
    have h1 := hc _ hx_mem
    have hne0 : ¬ (t + 1 = 0) := by omega
    have hw_f : w[t + 1 - 1]! = false := by
      rw [show t + 1 - 1 = t by omega]; exact hft
    simp only [hne0, hw_f, Bool.false_eq_true, ↓reduceIte, List.all_eq_true] at h1
    have h2 := h1 _ hy_mem
    rw [e779_pot_eq, e779_pot_eq] at hpeq
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h2
    exact h2.1 (by simp [show u < t + 1 by omega, hFu, hpeq.symm])
  · intro t ht hft u hut hfu hFu hpeq
    have hx_mem : (t + 1, Fw (wordSign w) (t + 1), Ar (wordSign w) 0 (t + 1)) ∈
        wordStatesAux w 0 0 0 := (hmem _).mpr ⟨t + 1, by omega, by simp⟩
    have hy_mem : (u, Fw (wordSign w) u, Ar (wordSign w) 0 u) ∈
        wordStatesAux w 0 0 0 := (hmem _).mpr ⟨u, by omega, by simp⟩
    have h1 := hc _ hx_mem
    have hne0 : ¬ (t + 1 = 0) := by omega
    have hw_f : w[t + 1 - 1]! = false := by
      rw [show t + 1 - 1 = t by omega]; exact hft
    simp only [hne0, hw_f, Bool.false_eq_true, ↓reduceIte, List.all_eq_true] at h1
    have h2 := h1 _ hy_mem
    rw [e779_pot_eq, e779_pot_eq] at hpeq
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h2
    exact h2.2 (by simp [show u + 1 < t + 1 by omega, show w[u]! = true from hfu, hFu, hpeq.symm])

/-- Explicit initial-`S` witness (`len = 35`): `S A^3 (AS) S ++ S^8 A^8 (SA)^5 SS`
(blocks `S`-predecessor via `(1, 0)` and `A`-predecessor via Type-I `(-1, 0)`). -/
def initialSWitnessI : List Bool :=
  [false, true, true, true, true, false, false] ++
    List.replicate 8 false ++ List.replicate 8 true ++ repeatWord 5 [false, true] ++ [false, false]

/-- Explicit initial-`SS` witness (`len = 36`): `S^2 A^6 S^3 ++ S^{10} A^9 (SA)^2 SS`
(blocks `S`-predecessor via `(1, 0)` and `A`-predecessor via Type-II `(-2, 0)`). -/
def initialSWitnessII : List Bool :=
  [false, false] ++ List.replicate 6 true ++ [false, false, false] ++
    List.replicate 10 false ++ List.replicate 9 true ++ repeatWord 2 [false, true] ++ [false, false]

/-- Dynamic separation for initial-`S` (Type-I `A`-obstruction, `len = 35`) and initial-`SS`
(Type-II `A`-obstruction, `len = 36`) words: both are realized at clock `0` by coherent
finite-state greedy replays, yet neither has any coherent 1-step predecessor and neither ever
occurs at ANY clock `s : Nat` of `Recaman.Basic.a`. -/
theorem initial_S_dynamic_separation_witnesses :
    ((∃ b st, st.value ∈ st.seen ∧ MatchesAt (replaySign b st) 0 initialSWitnessI) ∧
      (∀ b st, st.value ∈ st.seen → ∀ s, 1 ≤ s → ¬ MatchesAt (replaySign b st) s initialSWitnessI) ∧
      (∀ s : Nat, ¬ MatchesAt canonicalOrbitSign s initialSWitnessI)) ∧
    ((∃ b st, st.value ∈ st.seen ∧ MatchesAt (replaySign b st) 0 initialSWitnessII) ∧
      (∀ b st, st.value ∈ st.seen → ∀ s, 1 ≤ s → ¬ MatchesAt (replaySign b st) s initialSWitnessII) ∧
      (∀ s : Nat, ¬ MatchesAt canonicalOrbitSign s initialSWitnessII)) := by
  have hfr1 := checkFresh_sound initialSWitnessI (by decide)
  have hfr2 := checkFresh_sound initialSWitnessII (by decide)
  have hbS1 : BlocksSPredecessor initialSWitnessI := ⟨6, by decide, by decide, by decide, by decide⟩
  have hbA1 : BlocksAPredecessorI initialSWitnessI := ⟨34, by decide, by decide, by decide, by decide⟩
  have hbS2 : BlocksSPredecessor initialSWitnessII := ⟨10, by decide, by decide, by decide, by decide⟩
  have hbA2 : BlocksAPredecessorII initialSWitnessII := ⟨35, by decide, by decide, by decide, by decide⟩
  refine ⟨⟨seeded_replay_realizes_of_fresh _ hfr1.1 hfr1.2, ?_, ?_⟩,
    ⟨seeded_replay_realizes_of_fresh _ hfr2.1 hfr2.2, ?_, ?_⟩⟩
  · intro b st hs s hs1
    exact no_predecessor_forbids_nonzero_clock_replay initialSWitnessI hbS1 (Or.inl hbA1) b s st hs hs1
  · exact no_predecessor_forbids_all_canonical_clocks initialSWitnessI hbS1 (Or.inl hbA1)
      (Or.inl ⟨by decide, by decide⟩)
  · intro b st hs s hs1
    exact no_predecessor_forbids_nonzero_clock_replay initialSWitnessII hbS2 (Or.inr hbA2) b s st hs hs1
  · exact no_predecessor_forbids_all_canonical_clocks initialSWitnessII hbS2 (Or.inr hbA2)
      (Or.inl ⟨by decide, by decide⟩)

end Recaman.DynamicPredecessorObstruction
