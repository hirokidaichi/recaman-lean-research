import Recaman.CoherentGreedyFreshness

namespace Recaman.NumericStockStripPotential

open Recaman Recaman.SeededReplay Recaman.CoherentGreedyFreshness
open Recaman.FloorSupplyPotential Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction
open Recaman.LineCapacityPeriodic Recaman.LeadingRunSupply
open Recaman.ShortPeriodicSupply (sign)

/-! # Purely numeric departure `A` stock strip & `34/15` floor potential (`E-803`)

Formalizes the arbitrary-depth purely numeric stock-floor discount and departure-`A`
upcrossing strip (`E-772`) directly on arbitrary coherent finite-state greedy replays
`SeededReplay.run b s` and on the canonical clock-0 Recamán orbit `Recaman.Basic.a`:

1. `primitive_excursion_area_lower_bound`: every nonempty primitive nonnegative balanced
   walk of length `t` (`u < w`, `Fw w = Fw u`, strictly above on `(u, w)`) has `2 ∣ (w - u)`
   and relative area `3 * ((w - u) / 2) - 2 ≤ Ar f u (w - u)`.
2. `floor_cut_stock_discount`: at any coherent last floor visit `IsLastFloorVisit b s c v Q`,
   letting `c' = v + 1`, `t = v - c`, `x = (run b s c).value`, `z = (run b s v).value`,
   `K = stockBelow b s c`, `N = seenCountIn b s c z (x - 1)`:
     - `3 * t + 6 * z + 4 * N ≤ 6 * x`,
     - `floorP b s c' + 4 * K + 1 ≤ 3 * floorP b s c`,
     - `3 * t + 2 * z + 4 * K + 4 ≤ 6 * x`.
3. `departure_strip_stock_transport`: every consecutive pair of floor-departure `A` outputs
   rises by at most `+1`, so every integer in `[X(c + 1), X(c') - 1]` belongs to
   `(run b s c').seen` and is disjoint from `[1, x]`, yielding the exact clipped + upcrossing
   stock transport inequality for `stockBelow b s c'`.
4. `floor_potential_W_recurrence`: `floorW b s t = 12*(b+t) + 15*X(t) - 10*K(t)` obeys
   `15 * floorW b s (v + 1) ≤ 34 * floorW b s c - 30` at arbitrary depth (multiplier `34/15 < 3`).
5. `floor_potential_T_recurrence` & `floor_potential_T_sharp`:
   `floorT b s t = 13*(b+t) + 20*X(t) - 15*K(t)` obeys
   `13 * floorT b s (v + 1) ≤ 33 * floorT b s c - 166`, with exact equality at
   `x = 1, seen = [0, 1]` for EVERY base `a : Nat`.
6. `iterated_floorW_strictly_beats_three_pow`: for EVERY `j ≥ 7` and EVERY `P_0 ≥ 2`,
   the `(34/15)^j` floor-`W` uniform clock envelope strictly beats the `3^j` floor-`P` envelope.
7. `canonical_orbit_floor_potentials`: unconditional specialization of the stock discount,
   `15 * W' ≤ 34 * W - 30`, and `13 * T' ≤ 33 * T - 166` to `Recaman.Basic.a`.
-/

/-- Number of distinct natural numbers in `[lo, hi]` present in `(run b s t).seen`. -/
def seenCountIn (b : Nat) (s : State) (t lo hi : Nat) : Nat :=
  ((List.range (hi + 1 - lo)).filter (fun d => decide (lo + d ∈ (run b s t).seen))).length

/-- Number of distinct natural numbers in `[lo, hi]` absent from `(run b s t).seen`. -/
def missingCountIn (b : Nat) (s : State) (t lo hi : Nat) : Nat :=
  ((List.range (hi + 1 - lo)).filter (fun d => !decide (lo + d ∈ (run b s t).seen))).length

/-- Distinct seen stock strictly below current positive value: `K_t = |V_t ∩ [1, X(t) - 1]|`. -/
def stockBelow (b : Nat) (s : State) (t : Nat) : Nat :=
  seenCountIn b s t 1 ((run b s t).value - 1)

/-- Classical last-floor potential `P(t) = (b + t) + 2 * X(t)`. -/
def floorP (b : Nat) (s : State) (t : Nat) : Nat :=
  (b + t) + 2 * (run b s t).value

/-- Main paid stock-strip potential `W(t) = 12*(b + t) + 15*X(t) - 10*K(t)` (as `Int`). -/
def floorW (b : Nat) (s : State) (t : Nat) : Int :=
  12 * ((b + t : Nat) : Int) + 15 * ((run b s t).value : Int) - 10 * (stockBelow b s t : Int)

/-- Supporting sharp potential `T(t) = 13*(b + t) + 20*X(t) - 15*K(t)` (as `Int`). -/
def floorT (b : Nat) (s : State) (t : Nat) : Int :=
  13 * ((b + t : Nat) : Int) + 20 * ((run b s t).value : Int) - 15 * (stockBelow b s t : Int)

/-- Floor-cut validity predicate at cut `c` with last floor visit `v` and horizon `Q`:
coherent positive current at `c`, `Fw ≥ Fw c` on `[c, Q]`, `v` is the last visit to `Fw c`
in `[c, Q]`, and `v < Q` (so `Fw > Fw c` on `(v, Q]`). -/
def IsLastFloorVisit (b : Nat) (s : State) (c v Q : Nat) : Prop :=
  1 ≤ (run b s c).value ∧
  (run b s c).value ∈ (run b s c).seen ∧
  c ≤ v ∧ v < Q ∧
  Fw (replaySign b s) v = Fw (replaySign b s) c ∧
  (∀ q, c ≤ q → q ≤ Q → Fw (replaySign b s) c ≤ Fw (replaySign b s) q) ∧
  (∀ q, v < q → q ≤ Q → Fw (replaySign b s) c < Fw (replaySign b s) q)

/-! ## Basic list-counting & seen-set helpers -/

private theorem filter_length_add_not {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    cases hpa : p a <;> simp [List.filter, hpa] <;> omega

private theorem filter_length_le_of_imp {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    have hrest := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    cases hpa : p a
    · cases hqa : q a <;> simp [List.filter, hpa, hqa] <;> omega
    · have hqa : q a = true := h a (List.mem_cons_self ..) hpa
      simp [List.filter, hpa, hqa]
      omega

private theorem filter_length_disjoint_add {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).length + (l.filter (fun x => !p x && q x)).length = (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    have hrest := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    cases hpa : p a
    · cases hqa : q a <;> simp [List.filter, hpa, hqa] <;> omega
    · have hqa : q a = true := h a (List.mem_cons_self ..) hpa
      simp [List.filter, hpa, hqa]
      omega

private theorem nodup_length_le_of_subset {xs ys : List Nat}
    (hnd : xs.Nodup) (hsub : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a rest ih =>
    have ha_mem : a ∈ ys := hsub a (List.mem_cons_self ..)
    have hnd_cons := List.nodup_cons.mp hnd
    have hsub_rest : ∀ x ∈ rest, x ∈ ys.erase a := by
      intro x hx
      have hne : x ≠ a := fun h => hnd_cons.1 (h ▸ hx)
      exact (List.mem_erase_of_ne hne).mpr (hsub x (List.mem_cons_of_mem a hx))
    have hlen_erase : (ys.erase a).length + 1 = ys.length := by
      have h := List.length_erase_of_mem ha_mem
      have hpos : 0 < ys.length := List.length_pos_of_mem ha_mem
      omega
    have hih := ih hnd_cons.2 hsub_rest
    simp only [List.length_cons]
    omega

private theorem mem_seen_mono {b : Nat} {s : State} {t1 t2 z : Nat}
    (h12 : t1 ≤ t2) (hz : z ∈ (run b s t1).seen) : z ∈ (run b s t2).seen := by
  have hs : Seen b s t1 (z : Int) := ⟨z, hz, rfl⟩
  obtain ⟨w, hw, heq⟩ := seen_mono h12 hs
  have : w = z := by omega
  exact this ▸ hw

private theorem seenCountIn_add_missingCountIn (b : Nat) (s : State) (t lo hi : Nat) :
    seenCountIn b s t lo hi + missingCountIn b s t lo hi = hi + 1 - lo := by
  unfold seenCountIn missingCountIn
  rw [filter_length_add_not, List.length_range]

private theorem seenCountIn_split (b : Nat) (s : State) (t lo mid hi : Nat)
    (h1 : lo ≤ mid) (hmid1 : 1 ≤ mid) (h2 : mid ≤ hi + 1) :
    seenCountIn b s t lo hi = seenCountIn b s t lo (mid - 1) + seenCountIn b s t mid hi := by
  unfold seenCountIn
  have hlen : hi + 1 - lo = (mid - lo) + (hi + 1 - mid) := by omega
  have h1' : mid - 1 + 1 - lo = mid - lo := by omega
  rw [hlen, h1', List.range_add, List.filter_append, List.length_append, List.filter_map,
    List.length_map]
  congr 1
  have hfun : (fun x => decide (lo + x ∈ (run b s t).seen)) ∘ (fun x => mid - lo + x) =
      (fun d => decide (mid + d ∈ (run b s t).seen)) := by
    funext d
    have : lo + (mid - lo + d) = mid + d := by omega
    simp only [Function.comp, this]
  rw [hfun]

private theorem missingCountIn_mono_hi (b : Nat) (s : State) (t lo hi1 hi2 : Nat)
    (h1 : lo ≤ hi1 + 1) (h2 : hi1 ≤ hi2) :
    missingCountIn b s t lo hi1 ≤ missingCountIn b s t lo hi2 := by
  unfold missingCountIn
  have hlen : hi2 + 1 - lo = (hi1 + 1 - lo) + (hi2 - hi1) := by omega
  rw [hlen, List.range_add, List.filter_append, List.length_append]
  omega

private theorem seenCountIn_eq_width_of_all_mem (b : Nat) (s : State) (t lo hi : Nat)
    (hall : ∀ w, lo ≤ w → w ≤ hi → w ∈ (run b s t).seen) :
    seenCountIn b s t lo hi = hi + 1 - lo := by
  unfold seenCountIn
  have hfilt : (List.range (hi + 1 - lo)).filter (fun d => decide (lo + d ∈ (run b s t).seen)) =
      List.range (hi + 1 - lo) := by
    rw [List.filter_eq_self]
    intro d hd
    rw [List.mem_range] at hd
    simp [hall (lo + d) (by omega) (by omega)]
  rw [hfilt, List.length_range]

private theorem seenCountIn_ge_of_fresh_list (b : Nat) (s : State) (t1 t2 lo hi : Nat)
    (h12 : t1 ≤ t2) (R : List Nat) (hnd : R.Nodup)
    (hR : ∀ r ∈ R, lo ≤ r ∧ r ≤ hi ∧ r ∉ (run b s t1).seen ∧ r ∈ (run b s t2).seen) :
    seenCountIn b s t1 lo hi + R.length ≤ seenCountIn b s t2 lo hi := by
  unfold seenCountIn
  let l := List.range (hi + 1 - lo)
  let p := fun d => decide (lo + d ∈ (run b s t1).seen)
  let q := fun d => decide (lo + d ∈ (run b s t2).seen)
  have himp : ∀ d ∈ l, p d = true → q d = true := by
    intro d _ hp
    simp only [p, decide_eq_true_eq] at hp
    simp only [q, decide_eq_true_eq]
    exact mem_seen_mono h12 hp
  have hsplit := filter_length_disjoint_add l p q himp
  have hnd_map : (R.map (fun r => r - lo)).Nodup := by
    have hpw : R.Pairwise (fun x y => x - lo ≠ y - lo) := by
      clear hsplit himp p q l
      induction R with
      | nil => exact List.Pairwise.nil
      | cons a rest ih =>
        have hcons := List.nodup_cons.mp hnd
        rw [List.pairwise_cons]
        refine ⟨fun y hy heq => ?_, ih hcons.2 (fun r hr => hR r (List.mem_cons_of_mem a hr))⟩
        have ha := hR a (List.mem_cons_self ..)
        have hy' := hR y (List.mem_cons_of_mem a hy)
        have : a = y := by omega
        exact hcons.1 (this ▸ hy)
    exact List.pairwise_map.mpr hpw
  have hsub : ∀ d ∈ R.map (fun r => r - lo), d ∈ l.filter (fun x => !p x && q x) := by
    intro d hd
    rw [List.mem_map] at hd
    obtain ⟨r, hr, rfl⟩ := hd
    have hrr := hR r hr
    rw [List.mem_filter]
    refine ⟨List.mem_range.mpr (by omega), ?_⟩
    simp only [p, q, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    have heq : lo + (r - lo) = r := by omega
    rw [heq]
    exact ⟨hrr.2.2.1, hrr.2.2.2⟩
  have hle := nodup_length_le_of_subset hnd_map hsub
  rw [List.length_map] at hle
  change (l.filter p).length + R.length ≤ (l.filter q).length
  omega

private theorem seenCountIn_le_width (b : Nat) (s : State) (t lo hi : Nat) :
    seenCountIn b s t lo hi ≤ hi + 1 - lo := by
  have := seenCountIn_add_missingCountIn b s t lo hi
  omega

private theorem seenCountIn_mono_time (b : Nat) (s : State) (t1 t2 lo hi : Nat)
    (h12 : t1 ≤ t2) : seenCountIn b s t1 lo hi ≤ seenCountIn b s t2 lo hi := by
  unfold seenCountIn
  refine filter_length_le_of_imp _ _ _ fun d _ hd => ?_
  simp only [decide_eq_true_eq] at hd ⊢
  exact mem_seen_mono h12 hd

/-! ## Part 1: Primitive nonnegative balanced excursion area lower bound -/

private theorem fw_parity (f : Nat → Bool) (u : Nat) :
    ∀ k : Nat, (Fw f (u + k) - Fw f u) % 2 = ((k : Int) % 2) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show u + (k + 1) = (u + k) + 1 by omega, Fw_succ]
    cases f (u + k) <;> simp [sign] <;> omega

/-- Every nonempty primitive nonnegative balanced walk of length `w - u` (`u < w`,
`Fw f w = Fw f u`, and `Fw f i > Fw f u` for all `u < i < w`) has even length `2 * l`
and relative post-step area `Ar f u (w - u) ≥ 3 * l - 2`. -/
theorem primitive_excursion_area_lower_bound (f : Nat → Bool) (u w : Nat)
    (huw : u < w) (hEq : Fw f w = Fw f u)
    (hpos : ∀ i, u < i → i < w → Fw f u < Fw f i) :
    (w - u) % 2 = 0 ∧ 3 * (((w - u) / 2 : Nat) : Int) - 2 ≤ Ar f u (w - u) := by
  have hpar := fw_parity f u (w - u)
  rw [Nat.add_sub_cancel' (Nat.le_of_lt huw), hEq] at hpar
  have heven : (w - u) % 2 = 0 := by omega
  refine ⟨heven, ?_⟩
  have haux : ∀ k : Nat, k < w - u →
      ((k : Int) + ((k / 2 : Nat) : Int)) ≤ Ar f u k := by
    intro k
    induction k with
    | zero => intro _; simp [Ar]
    | succ k ih =>
      intro hk
      have hih := ih (by omega)
      have hAr := Ar_succ f u k
      have hgt : Fw f u < Fw f (u + (k + 1)) := hpos (u + (k + 1)) (by omega) (by omega)
      have hpk := fw_parity f u (k + 1)
      have hdiff_ge :
          (if (k + 1) % 2 = 0 then (2 : Int) else 1) ≤ Fw f (u + (k + 1)) - Fw f u := by
        split <;> omega
      rw [show u + k + 1 = u + (k + 1) by omega] at hAr
      split at hdiff_ge <;> omega
  have hlen_ge2 : 2 ≤ w - u := by omega
  have h1 := haux (w - u - 1) (by omega)
  have hlast := Ar_succ f u (w - u - 1)
  rw [show u + (w - u - 1) + 1 = w by omega, show (w - u - 1) + 1 = w - u by omega, hEq] at hlast
  omega

private theorem replay_value_diff_equal_height (b : Nat) (s : State) (u w : Nat)
    (huw : u ≤ w) (hEq : Fw (replaySign b s) w = Fw (replaySign b s) u) :
    value b s w = value b s u - Ar (replaySign b s) u (w - u) := by
  let f := replaySign b s
  have hu := replay_value_eq_abel_potential b s u
  have hw := replay_value_eq_abel_potential b s w
  have hsp := area_split_at f 0 u w (Nat.zero_le u) huw
  rw [Nat.sub_zero, Nat.sub_zero] at hsp
  have h0 : Fw f 0 = 0 := rfl
  rw [h0] at hsp
  unfold floorPotential at hu hw
  simp only [Nat.sub_zero] at hu hw
  change value b s u =
    (s.value : Int) + ((b + 1 : Nat) : Int) * Fw f u -
      (Ar f 0 u + (u : Int) * (Fw f 0 - (Fw f u - 1 + 1))) at hu
  change value b s w =
    (s.value : Int) + ((b + 1 : Nat) : Int) * Fw f w -
      (Ar f 0 w + (w : Int) * (Fw f 0 - (Fw f w - 1 + 1))) at hw
  rw [h0] at hu hw
  change Fw f w = Fw f u at hEq
  rw [hEq] at hw
  have hcast : ((w - u : Nat) : Int) = (w : Int) - (u : Int) := by omega
  rw [hcast] at hsp
  push_cast at hu hw hsp ⊢
  grind

private theorem replay_step_add_of_fw_gt (b : Nat) (s : State) (t : Nat)
    (hgt : Fw (replaySign b s) t < Fw (replaySign b s) (t + 1)) :
    replaySign b s t = true ∧ (run b s (t + 1)).value = (run b s t).value + (b + t + 1) := by
  have hsign : replaySign b s t = true := by
    have hF := Fw_succ (replaySign b s) t
    cases h : replaySign b s t
    · rw [h] at hF; simp [sign] at hF; omega
    · rfl
  refine ⟨hsign, ?_⟩
  have hnc : ¬ CanSubtract (b + t + 1) (run b s t) := by
    unfold replaySign at hsign
    by_cases hc : CanSubtract (b + t + 1) (run b s t)
    · simp [hc] at hsign
    · exact hc
  change (step (b + t + 1) (run b s t)).value = _
  simp only [step, nextValue, if_neg hnc]

private theorem least_floor_return (P : Nat → Prop) :
    ∀ n k, k ≤ n → P k → ∃ m, m ≤ k ∧ P m ∧ ∀ j, j < m → ¬ P j := by
  intro n
  induction n with
  | zero =>
    intro k hk hPk
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨0, Nat.le_refl 0, hPk, fun j hj => by omega⟩
  | succ n ih =>
    intro k hk hPk
    by_cases hkn : k ≤ n
    · exact ih k hkn hPk
    · have hkeq : k = n + 1 := by omega
      subst hkeq
      by_cases hex : ∃ j, j ≤ n ∧ P j
      · obtain ⟨j, hjn, hPj⟩ := hex
        obtain ⟨m, hmj, hPm, hmin⟩ := ih j hjn hPj
        exact ⟨m, by omega, hPm, hmin⟩
      · refine ⟨n + 1, Nat.le_refl _, hPk, ?_⟩
        intro j hjl hPj
        exact hex ⟨j, by omega, hPj⟩

/-! ## Part 2: Unified inductive excursion chain & departure `A` upcrossing strip -/

private theorem floor_visit_chain_induction (b : Nat) (s : State) :
    ∀ n c v Q, v - c ≤ n → IsLastFloorVisit b s c v Q →
      ∃ (m : Nat) (R : List Nat),
        (v - c) % 2 = 0 ∧
        R.length = m ∧
        R.Nodup ∧
        (run b s v).value ≤ (run b s c).value ∧
        1 ≤ (run b s v).value ∧
        3 * (v - c) ≤ 2 * ((run b s c).value - (run b s v).value) + 4 * m ∧
        (∀ r ∈ R, (run b s v).value ≤ r ∧ r < (run b s c).value ∧
          r ∉ (run b s c).seen ∧ r ∈ (run b s v).seen) ∧
        (run b s (c + 1)).value = (run b s c).value + (b + c + 1) ∧
        (run b s (v + 1)).value = (run b s v).value + (b + v + 1) ∧
        (∀ w : Nat, (run b s (c + 1)).value ≤ w → w < (run b s (v + 1)).value →
          w ∈ (run b s (v + 1)).seen) := by
  intro n
  induction n with
  | zero =>
    intro c v Q hle hL
    obtain ⟨hx1, hx_seen, hcv, hvQ, hFv, hge, hgt⟩ := hL
    have heq : v = c := by omega
    subst heq
    have hA := replay_step_add_of_fw_gt b s v (hgt (v + 1) (by omega) (by omega))
    refine ⟨0, [], by simp, rfl, List.Pairwise.nil, Nat.le_refl _, hx1, by simp, ?_,
      hA.2, hA.2, fun _ h1 h2 => by omega⟩
    intro _ h; cases h
  | succ n ih =>
    intro c v Q hle hL
    by_cases hcv_eq : c = v
    · subst hcv_eq
      obtain ⟨hx1, _, _, hvQ, _, _, hgt⟩ := hL
      have hA := replay_step_add_of_fw_gt b s c (hgt (c + 1) (by omega) (by omega))
      refine ⟨0, [], by simp, rfl, List.Pairwise.nil, Nat.le_refl _, hx1, by simp, ?_,
        hA.2, hA.2, fun _ h1 h2 => by omega⟩
      intro _ h; cases h
    · obtain ⟨hx1, hx_seen, hcv, hvQ, hFv, hge, hgt⟩ := hL
      let f := replaySign b s
      have hd0 : 0 < v - c ∧ Fw f (c + (v - c)) = Fw f c :=
        ⟨by omega, by rw [Nat.add_sub_cancel' hcv]; exact hFv⟩
      obtain ⟨d, hd_le, ⟨hd_pos, hd_fw⟩, hd_min⟩ :=
        least_floor_return (fun j => 0 < j ∧ Fw f (c + j) = Fw f c) (v - c) (v - c) (Nat.le_refl _) hd0
      let u := c + d
      have hcu : c < u := by omega
      have huv : u ≤ v := by omega
      have hFwu : Fw f u = Fw f c := hd_fw
      have hstrict : ∀ i, c < i → i < u → Fw f c < Fw f i := by
        intro i hi1 hi2
        have hge_i : Fw f c ≤ Fw f i := hge i (by omega) (by omega)
        have hnot := hd_min (i - c) (by omega)
        rw [Nat.add_sub_cancel' (by omega)] at hnot
        by_cases heqi : Fw f i = Fw f c
        · exact (hnot ⟨by omega, heqi⟩).elim
        · omega
      -- Primitive excursion from `c` to `u`
      have hprim := primitive_excursion_area_lower_bound f c u hcu hFwu hstrict
      have hdiff_val := replay_value_diff_equal_height b s c u (Nat.le_of_lt hcu) hFwu
      have hu_ge2 : 2 ≤ u - c := by omega
      have hAc := replay_step_add_of_fw_gt b s c (hstrict (c + 1) (by omega) (by omega))
      -- Step `u - 1` is `S` (strictly positive fresh landing at `u`)
      have hSu : replaySign b s (u - 1) = false := by
        have hFprev := hstrict (u - 1) (by omega) (by omega)
        have hstep := Fw_succ f (u - 1)
        rw [show u - 1 + 1 = u by omega] at hstep
        cases hs_eq : replaySign b s (u - 1)
        · rfl
        · change Fw f u = Fw f (u - 1) + sign (replaySign b s (u - 1)) at hstep
          rw [hs_eq] at hstep
          simp [sign] at hstep
          omega
      have hc_sub : CanSubtract (b + (u - 1) + 1) (run b s (u - 1)) := by
        unfold replaySign at hSu
        by_cases hc : CanSubtract (b + (u - 1) + 1) (run b s (u - 1))
        · exact hc
        · simp [hc] at hSu
      have hu_pos : 1 ≤ (run b s u).value := by
        have hv : (run b s ((u - 1) + 1)).value = (run b s (u - 1)).value - (b + (u - 1) + 1) := by
          change (step (b + (u - 1) + 1) (run b s (u - 1))).value = _
          simp only [step, nextValue, if_pos hc_sub]
        rw [show (u - 1) + 1 = u by omega] at hv
        have hlt := hc_sub.1
        omega
      have hu_mem_u : (run b s u).value ∈ (run b s u).seen := by
        have hv_eq : u = (u - 1) + 1 := by omega
        rw [hv_eq]
        exact step_value_mem_seen _ _
      have hu_not_seen_c : (run b s u).value ∉ (run b s c).seen := by
        intro hmem_c
        have hmem_prev := mem_seen_mono (show c ≤ u - 1 by omega) hmem_c
        have hv : (run b s ((u - 1) + 1)).value = (run b s (u - 1)).value - (b + (u - 1) + 1) := by
          change (step (b + (u - 1) + 1) (run b s (u - 1))).value = _
          simp only [step, nextValue, if_pos hc_sub]
        rw [show (u - 1) + 1 = u by omega] at hv
        exact hc_sub.2 (hv ▸ hmem_prev)
      have hL_u : IsLastFloorVisit b s u v Q :=
        ⟨hu_pos, hu_mem_u, huv, hvQ,
          by change Fw f v = Fw f u; change Fw f v = Fw f c at hFv; omega,
          fun q hq1 hq2 => by
            change Fw f u ≤ Fw f q
            have h1 : Fw f c ≤ Fw f q := hge q (by omega) hq2
            omega,
          fun q hq1 hq2 => by
            change Fw f u < Fw f q
            have h1 : Fw f c < Fw f q := hgt q hq1 hq2
            omega⟩
      obtain ⟨m', R', hev', hRlen', hRnd', hvu_val, hv_pos, harea', hRprop', hAu, hAv, hstrip'⟩ :=
        ih u v Q (by omega) hL_u
      have hu_lt_c : (run b s u).value < (run b s c).value := by
        change ((run b s u).value : Int) = ((run b s c).value : Int) - Ar f c (u - c) at hdiff_val
        omega
      have hZ_step : (run b s (u + 1)).value ≤ (run b s (c + 1)).value + 1 := by
        change ((run b s u).value : Int) = ((run b s c).value : Int) - Ar f c (u - c) at hdiff_val
        omega
      refine ⟨m' + 1, (run b s u).value :: R', by omega, by simp [hRlen'], ?_, by omega, hv_pos,
        ?_, ?_, hAc.2, hAv, ?_⟩
      · rw [List.nodup_cons]
        refine ⟨fun hmem => ?_, hRnd'⟩
        have := (hRprop' _ hmem).2.1
        omega
      · change ((run b s u).value : Int) = ((run b s c).value : Int) - Ar f c (u - c) at hdiff_val
        omega
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact ⟨hvu_val, hu_lt_c, hu_not_seen_c, mem_seen_mono huv hu_mem_u⟩
        · have hp := hRprop' r hr'
          refine ⟨hp.1, by omega, fun hc_mem => hp.2.2.1 (mem_seen_mono (Nat.le_of_lt hcu) hc_mem),
            hp.2.2.2⟩
      · intro w hw1 hw2
        by_cases hw_eq : w = (run b s (c + 1)).value
        · rw [hw_eq]
          have hmem_c1 : (run b s (c + 1)).value ∈ (run b s (c + 1)).seen := step_value_mem_seen _ _
          exact mem_seen_mono (by omega) hmem_c1
        · exact hstrip' w (by omega) hw2

/-! ## Part 3: Main stock-floor discount, departure strip transport, and `W`/`T` recurrences -/

/-- Single-cut old-stock discount (`E-772` / `H03`): at any coherent last floor visit
`IsLastFloorVisit b s c v Q`, with `t = v - c`, `x = X(c)`, `z = X(v)`,
`K = stockBelow b s c`, and `N = seenCountIn b s c z (x - 1)`:
1. `3 * t + 6 * z + 4 * N ≤ 6 * x`,
2. `floorP b s (v + 1) + 4 * K + 1 ≤ 3 * floorP b s c`,
3. `3 * t + 2 * z + 4 * K + 4 ≤ 6 * x`. -/
theorem floor_cut_stock_discount (b : Nat) (s : State) (c v Q : Nat)
    (hL : IsLastFloorVisit b s c v Q) :
    3 * (v - c) + 6 * (run b s v).value +
        4 * seenCountIn b s c (run b s v).value ((run b s c).value - 1) ≤
      6 * (run b s c).value ∧
      floorP b s (v + 1) + 4 * stockBelow b s c + 1 ≤ 3 * floorP b s c ∧
      3 * (v - c) + 2 * (run b s v).value + 4 * stockBelow b s c + 4 ≤
        6 * (run b s c).value := by
  obtain ⟨m, R, _, hRlen, hRnd, hzx, hz1, harea, hRprop, _, hAv, _⟩ :=
    floor_visit_chain_induction b s (v - c) c v Q (Nat.le_refl _) hL
  have hcv : c ≤ v := hL.2.2.1
  have hseen_m : seenCountIn b s c (run b s v).value ((run b s c).value - 1) + m ≤
      (run b s c).value - (run b s v).value := by
    have hge := seenCountIn_ge_of_fresh_list b s c v (run b s v).value ((run b s c).value - 1)
      hcv R hRnd (fun r hr => by
        have hp := hRprop r hr
        exact ⟨hp.1, by omega, hp.2.2.1, hp.2.2.2⟩)
    have hle := seenCountIn_le_width b s v (run b s v).value ((run b s c).value - 1)
    rw [hRlen] at hge
    omega
  have hK_split : stockBelow b s c ≤
      seenCountIn b s c (run b s v).value ((run b s c).value - 1) + ((run b s v).value - 1) := by
    unfold stockBelow
    by_cases hzv : (run b s v).value ≤ (run b s c).value
    · have hsp := seenCountIn_split b s c 1 (run b s v).value ((run b s c).value - 1)
        hz1 hz1 (by omega)
      have hlo := seenCountIn_le_width b s c 1 ((run b s v).value - 1)
      omega
    · omega
  refine ⟨by omega, ?_, by omega⟩
  unfold floorP
  rw [hAv]
  omega

/-- Clipped + departure-`A` upcrossing stock transport (`E-772` Eq. (2)):
at any coherent last floor visit `IsLastFloorVisit b s c v Q`, letting `x = X(c)`,
`y = X(v + 1)`, `K = stockBelow b s c`, and `Z_0 = x + (b + c) + 1`, there exists `m : Nat`
(the primitive return count) with `m + K + 1 ≤ x`, `3 * (v - c) ≤ 2 * (x - X(v)) + 4 * m`,
`(v - c) % 2 = 0`, `1 ≤ X(v) ≤ x`, `y = X(v) + (b + v + 1)`, and:
`(min x (y - 1) - (x - 1 - m - K)) + (y - Z_0) ≤ stockBelow b s (v + 1)`. -/
theorem departure_strip_stock_transport (b : Nat) (s : State) (c v Q : Nat)
    (hL : IsLastFloorVisit b s c v Q) :
    ∃ m : Nat,
      (v - c) % 2 = 0 ∧
      1 ≤ (run b s v).value ∧ (run b s v).value ≤ (run b s c).value ∧
      m + stockBelow b s c + 1 ≤ (run b s c).value ∧
      3 * (v - c) ≤ 2 * ((run b s c).value - (run b s v).value) + 4 * m ∧
      (run b s (v + 1)).value = (run b s v).value + (b + v + 1) ∧
      (min (run b s c).value ((run b s (v + 1)).value - 1) -
          ((run b s c).value - 1 - m - stockBelow b s c)) +
        ((run b s (v + 1)).value - ((run b s c).value + (b + c) + 1)) ≤
        stockBelow b s (v + 1) := by
  obtain ⟨m, R, heven, hRlen, hRnd, hzx, hz1, harea, hRprop, hAc, hAv, hstrip⟩ :=
    floor_visit_chain_induction b s (v - c) c v Q (Nat.le_refl _) hL
  have hcv : c ≤ v := hL.2.2.1
  have hx1 : 1 ≤ (run b s c).value := hL.1
  have hx_seen : (run b s c).value ∈ (run b s c).seen := hL.2.1
  -- Fresh return values + old stock below x all fit inside `[1, x - 1]`
  have hseen_below : stockBelow b s c + m ≤ seenCountIn b s (v + 1) 1 ((run b s c).value - 1) := by
    have h1 := seenCountIn_ge_of_fresh_list b s c v 1 ((run b s c).value - 1) hcv R hRnd
      (fun r hr => by
        have hp := hRprop r hr
        exact ⟨by omega, by omega, hp.2.2.1, hp.2.2.2⟩)
    have h2 := seenCountIn_mono_time b s v (v + 1) 1 ((run b s c).value - 1) (Nat.le_succ v)
    rw [hRlen] at h1
    unfold stockBelow
    omega
  have hmK : m + stockBelow b s c + 1 ≤ (run b s c).value := by
    have hle := seenCountIn_le_width b s (v + 1) 1 ((run b s c).value - 1)
    omega
  -- `x` itself is in `(run b s (v + 1)).seen`, so missing count in `[1, x]` is `≤ M := x - 1 - m - K`
  let x := (run b s c).value
  let y := (run b s (v + 1)).value
  let L := min x (y - 1)
  let Z0 := x + (b + c) + 1
  have hmiss_x : missingCountIn b s (v + 1) 1 x ≤ x - 1 - m - stockBelow b s c := by
    have hsp := seenCountIn_split b s (v + 1) 1 x x hx1 hx1 (by omega)
    have hx_pt : seenCountIn b s (v + 1) x x = 1 := by
      have h := seenCountIn_eq_width_of_all_mem b s (v + 1) x x (fun w hw1 hw2 => by
        have hw : w = x := by omega
        rw [hw]; exact mem_seen_mono (by omega) hx_seen)
      omega
    have hcomp := seenCountIn_add_missingCountIn b s (v + 1) 1 x
    change stockBelow b s c + m ≤ seenCountIn b s (v + 1) 1 (x - 1) at hseen_below
    omega
  have hclip : L - (x - 1 - m - stockBelow b s c) ≤ seenCountIn b s (v + 1) 1 L := by
    have hmono := missingCountIn_mono_hi b s (v + 1) 1 L x (by omega) (Nat.min_le_left _ _)
    have hcomp := seenCountIn_add_missingCountIn b s (v + 1) 1 L
    omega
  refine ⟨m, heven, hz1, hzx, hmK, harea, hAv, ?_⟩
  change (L - (x - 1 - m - stockBelow b s c)) + (y - Z0) ≤ seenCountIn b s (v + 1) 1 (y - 1)
  by_cases hRpos : Z0 < y
  · have hL_eq : L = x := by omega
    have hsp1 := seenCountIn_split b s (v + 1) 1 Z0 (y - 1) (by omega) (by omega) (by omega)
    have hsp2 := seenCountIn_split b s (v + 1) 1 (x + 1) (Z0 - 1) (by omega) (by omega) (by omega)
    have hx1' : x + 1 - 1 = x := by omega
    rw [hx1'] at hsp2
    have hstrip_cnt : seenCountIn b s (v + 1) Z0 (y - 1) = y - Z0 := by
      have h := seenCountIn_eq_width_of_all_mem b s (v + 1) Z0 (y - 1) (fun w hw1 hw2 => by
        exact hstrip w (by omega) (by omega))
      omega
    rw [hL_eq] at hclip ⊢
    omega
  · have hR0 : y - Z0 = 0 := by omega
    rw [hR0, Nat.add_zero]
    have hsp := seenCountIn_split b s (v + 1) 1 (L + 1) (y - 1) (by omega) (by omega) (by omega)
    have hL1 : L + 1 - 1 = L := by omega
    rw [hL1] at hsp
    omega

/-- Main paid potential recurrence (`E-772` Eq. (3)): for EVERY coherent last floor visit
`IsLastFloorVisit b s c v Q`, `W = 12*(b + t) + 15*X(t) - 10*K(t)` obeys
`15 * floorW b s (v + 1) ≤ 34 * floorW b s c - 30` (arbitrary-depth multiplier `34/15 < 3`). -/
theorem floor_potential_W_recurrence (b : Nat) (s : State) (c v Q : Nat)
    (hL : IsLastFloorVisit b s c v Q) :
    15 * floorW b s (v + 1) ≤ 34 * floorW b s c - 30 := by
  obtain ⟨m, heven, hz1, hzx, hmK, harea, hAv, htrans⟩ :=
    departure_strip_stock_transport b s c v Q hL
  unfold floorW
  have hs_def : v - c = 2 * ((v - c) / 2) := by omega
  -- Exact two-case proof via `L0 = min x (z + 2*s) ≤ min x (y - 1)`:
  -- Let `M = x - 1 - m - K ≥ 0`, `r = x - z - 3*s + 2*m ≥ 0`, `R = y - (x + a + 1)`.
  have hcv : c ≤ v := hL.2.2.1
  have hL_ge : min (run b s c).value ((run b s v).value + (v - c)) ≤
      min (run b s c).value ((run b s (v + 1)).value - 1) := by omega
  omega

/-- Supporting sharper potential recurrence (`E-772` Eq. (7)): for EVERY coherent last floor
visit `IsLastFloorVisit b s c v Q`, `T = 13*(b + t) + 20*X(t) - 15*K(t)` obeys
`13 * floorT b s (v + 1) ≤ 33 * floorT b s c - 166`. -/
theorem floor_potential_T_recurrence (b : Nat) (s : State) (c v Q : Nat)
    (hL : IsLastFloorVisit b s c v Q) :
    13 * floorT b s (v + 1) ≤ 33 * floorT b s c - 166 := by
  obtain ⟨m, heven, hz1, hzx, hmK, harea, hAv, htrans⟩ :=
    departure_strip_stock_transport b s c v Q hL
  unfold floorT
  have hcv : c ≤ v := hL.2.2.1
  omega

/-- Sharp `T`-recurrence witness state `{ value := 1, seen := [0, 1] }`. -/
def sharpTState : State :=
  { value := 1, seen := [0, 1] }

/-- Exact sharpness of `13 * floorT' ≤ 33 * floorT - 166` (`E-772`): for EVERY base `a : Nat`,
starting at `sharpTState` executes a single `A` at clock `0` attaining
`13 * floorT a sharpTState 1 = 33 * floorT a sharpTState 0 - 166` identically. -/
theorem floor_potential_T_sharp (a : Nat) :
    IsLastFloorVisit a sharpTState 0 0 1 ∧
      13 * floorT a sharpTState 1 = 33 * floorT a sharpTState 0 - 166 := by
  let s : State := sharpTState
  change IsLastFloorVisit a s 0 0 1 ∧ 13 * floorT a s 1 = 33 * floorT a s 0 - 166
  have hnc : ¬ CanSubtract (a + 0 + 1) (run a s 0) := by
    intro h
    have hlt := h.1
    change a + 0 + 1 < 1 at hlt
    omega
  have hs0 : replaySign a s 0 = true := by simp [replaySign, hnc]
  have hr1 : run a s 1 = { value := a + 2, seen := [a + 2, 0, 1] } := by
    change step (a + 0 + 1) (run a s 0) = _
    simp only [step, nextValue, if_neg hnc]
    dsimp only [run, s, sharpTState]
    have hv : 1 + (a + 0 + 1) = a + 2 := by omega
    rw [hv]
  have hFw1 : Fw (replaySign a s) 1 = 1 := by
    have h := Fw_succ (replaySign a s) 0
    have h0 : Fw (replaySign a s) 0 = 0 := rfl
    rw [h0, hs0] at h
    simp [sign] at h
    omega
  have hK0 : stockBelow a s 0 = 0 := by
    unfold stockBelow seenCountIn
    simp [run, s, sharpTState]
  have hK1 : stockBelow a s 1 = 1 := by
    unfold stockBelow seenCountIn
    rw [hr1]
    dsimp only
    have hlen : a + 2 - 1 + 1 - 1 = 1 + a := by omega
    rw [hlen, List.range_add, List.filter_append, List.length_append]
    have hfirst : ((List.range 1).filter (fun d => decide (1 + d ∈ [a + 2, 0, 1]))).length = 1 := by
      simp
    have hrest : ((List.map (fun x => 1 + x) (List.range a)).filter
        (fun d => decide (1 + d ∈ [a + 2, 0, 1]))).length = 0 := by
      rw [List.filter_map, List.length_map]
      have hemp : (List.range a).filter
          ((fun d => decide (1 + d ∈ [a + 2, 0, 1])) ∘ (fun x => 1 + x)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro d hd
        rw [List.mem_range] at hd
        simp only [Function.comp, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false]
        omega
      rw [hemp]; rfl
    omega
  refine ⟨⟨by simp [run, s, sharpTState], by simp [run, s, sharpTState], Nat.le_refl 0,
    Nat.zero_lt_one, rfl, ?_, ?_⟩, ?_⟩
  · intro q _ hq
    have h0 : Fw (replaySign a s) 0 = 0 := rfl
    by_cases hq0 : q = 0
    · subst hq0; exact Int.le_refl _
    · have : q = 1 := by omega
      subst this; omega
  · intro q hq1 hq2
    have : q = 1 := by omega
    subst this
    have h0 : Fw (replaySign a s) 0 = 0 := rfl
    omega
  · unfold floorT
    rw [hK0, hK1, hr1]
    simp only [run, s, sharpTState]
    omega

/-! ## Part 4: Iterated arbitrary-depth `W`-envelope strictly beating `3^j` from `j ≥ 7` -/

private theorem six_mul_34_pow_lt_45_pow : ∀ j : Nat, 7 ≤ j → 6 * 34 ^ j < 45 ^ j := by
  intro j hj
  have hbase : 6 * 34 ^ 7 < 45 ^ 7 := by decide
  have hstep : ∀ k : Nat, 6 * 34 ^ (7 + k) < 45 ^ (7 + k) := by
    intro k
    induction k with
    | zero => exact hbase
    | succ k ih =>
      rw [show 7 + (k + 1) = (7 + k) + 1 by omega, Nat.pow_succ, Nat.pow_succ]
      have h1 : 6 * (34 ^ (7 + k) * 34) = (6 * 34 ^ (7 + k)) * 34 := by omega
      have h2 : (6 * 34 ^ (7 + k)) * 34 < 45 ^ (7 + k) * 34 :=
        Nat.mul_lt_mul_of_pos_right ih (by omega)
      have h3 : 45 ^ (7 + k) * 34 ≤ 45 ^ (7 + k) * 45 :=
        Nat.mul_le_mul_left _ (by omega)
      omega
  simpa [Nat.add_sub_cancel' hj] using hstep (j - 7)

/-- Iterated arbitrary-depth `W`-envelope & strict `j ≥ 7` horizon improvement (`E-772`):
for any chain of `j` successive coherent floor cuts `cut 0, cut 1, ..., cut j`
(`IsLastFloorVisit b s (cut i) (vis i) Q` and `cut (i + 1) = vis i + 1`):
1. `19 * 15^j * floorW b s (cut j) ≤ 34^j * (19 * floorW b s (cut 0) - 30) + 30 * 15^j`,
2. `1 ≤ (run b s (cut j)).value → 5 * floorP b s (cut j) + 20 ≤ 2 * floorW b s (cut j)`,
3. Whenever `7 ≤ j` and `floorW b s (cut 0) ≤ 12 * P0` (`2 ≤ P0`), the resulting
   `(34/15)^j` floor-`P` bound strictly beats the classical `3^j` horizon
   `B_j = 3^j * (P0 - 1/2) + 1/2` (cleared of denominator `190 * 15^j`). -/
theorem iterated_floorW_envelope_beats_three_pow (b : Nat) (s : State) (Q : Nat)
    (cut vis : Nat → Nat) (j : Nat)
    (hchain : ∀ i, i < j → IsLastFloorVisit b s (cut i) (vis i) Q ∧ cut (i + 1) = vis i + 1) :
    19 * ((15 ^ j : Nat) : Int) * floorW b s (cut j) ≤
      ((34 ^ j : Nat) : Int) * (19 * floorW b s (cut 0) - 30) + 30 * ((15 ^ j : Nat) : Int) ∧
    (1 ≤ (run b s (cut j)).value →
      5 * (floorP b s (cut j) : Int) + 20 ≤ 2 * floorW b s (cut j)) ∧
    (∀ P0 : Nat, 7 ≤ j → 2 ≤ P0 → floorW b s (cut 0) ≤ 12 * (P0 : Int) →
      190 * ((15 ^ j : Nat) : Int) * (floorP b s (cut j) : Int) <
        95 * ((45 ^ j : Nat) : Int) * (2 * (P0 : Int) - 1) + 95 * ((15 ^ j : Nat) : Int)) := by
  have hiter : ∀ k, k ≤ j →
      19 * ((15 ^ k : Nat) : Int) * floorW b s (cut k) ≤
        ((34 ^ k : Nat) : Int) * (19 * floorW b s (cut 0) - 30) + 30 * ((15 ^ k : Nat) : Int) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp
    | succ k ih =>
      intro hkj
      have hih := ih (by omega)
      obtain ⟨hLk, hcutk⟩ := hchain k (by omega)
      have hstep := floor_potential_W_recurrence b s (cut k) (vis k) Q hLk
      rw [← hcutk] at hstep
      have h15k_pos : (0 : Int) ≤ ((15 ^ k : Nat) : Int) := Int.natCast_nonneg _
      have hmul1 : 19 * ((15 ^ k : Nat) : Int) * (15 * floorW b s (cut (k + 1))) ≤
          19 * ((15 ^ k : Nat) : Int) * (34 * floorW b s (cut k) - 30) :=
        Int.mul_le_mul_of_nonneg_left hstep (by omega)
      have hmul2 : (34 : Int) * (19 * ((15 ^ k : Nat) : Int) * floorW b s (cut k)) ≤
          (34 : Int) * (((34 ^ k : Nat) : Int) * (19 * floorW b s (cut 0) - 30) +
            30 * ((15 ^ k : Nat) : Int)) :=
        Int.mul_le_mul_of_nonneg_left hih (by omega)
      have hp15 : ((15 ^ (k + 1) : Nat) : Int) = ((15 ^ k : Nat) : Int) * 15 := by
        rw [Nat.pow_succ]; push_cast; rfl
      have hp34 : ((34 ^ (k + 1) : Nat) : Int) = ((34 ^ k : Nat) : Int) * 34 := by
        rw [Nat.pow_succ]; push_cast; rfl
      rw [hp15, hp34]
      grind
  have hP_le_W : 1 ≤ (run b s (cut j)).value →
      5 * (floorP b s (cut j) : Int) + 20 ≤ 2 * floorW b s (cut j) := by
    intro hx1
    unfold floorP floorW stockBelow
    have hK_le : seenCountIn b s (cut j) 1 ((run b s (cut j)).value - 1) ≤
        (run b s (cut j)).value - 1 := by
      have h := seenCountIn_le_width b s (cut j) 1 ((run b s (cut j)).value - 1)
      omega
    omega
  have hW_j := hiter j (Nat.le_refl j)
  refine ⟨hW_j, hP_le_W, ?_⟩
  intro P0 hj7 hP0 hW0
  -- Since `7 ≤ j`, `cut j = vis (j - 1) + 1`, so `1 ≤ (run b s (cut j)).value` unconditionally!
  obtain ⟨hLlast, hcutlast⟩ := hchain (j - 1) (by omega)
  have hpos_j : 1 ≤ (run b s (cut j)).value := by
    rw [show j = (j - 1) + 1 by omega, hcutlast]
    have hstep := floor_visit_chain_induction b s (vis (j - 1) - cut (j - 1))
      (cut (j - 1)) (vis (j - 1)) Q (Nat.le_refl _) hLlast
    obtain ⟨_, _, _, _, _, _, hz1, _, _, _, hAv, _⟩ := hstep
    omega
  have hPW := hP_le_W hpos_j
  have h15_pos : (0 : Int) < ((15 ^ j : Nat) : Int) := by
    have : 0 < 15 ^ j := Nat.pow_pos (by omega)
    omega
  have hmul_PW : 38 * ((15 ^ j : Nat) : Int) * (5 * (floorP b s (cut j) : Int) + 20) ≤
      38 * ((15 ^ j : Nat) : Int) * (2 * floorW b s (cut j)) :=
    Int.mul_le_mul_of_nonneg_left hPW (by omega)
  have hmul_W0 : ((34 ^ j : Nat) : Int) * (19 * floorW b s (cut 0) - 30) ≤
      ((34 ^ j : Nat) : Int) * (19 * (12 * (P0 : Int)) - 30) :=
    Int.mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg _)
  -- Now `190 * 15^j * floorP + 760 * 15^j ≤ 4 * 34^j * (228 * P0 - 30) + 120 * 15^j`.
  have hpow6_nat : 6 * 34 ^ j < 45 ^ j := six_mul_34_pow_lt_45_pow j hj7
  have hpow6 : 6 * ((34 ^ j : Nat) : Int) < ((45 ^ j : Nat) : Int) := by exact_mod_cast hpow6_nat
  have hcoeff_pos : (0 : Int) < 228 * (P0 : Int) - 30 := by omega
  have hstrict : (912 * (P0 : Int) - 120) * (6 * ((34 ^ j : Nat) : Int)) <
      (912 * (P0 : Int) - 120) * ((45 ^ j : Nat) : Int) :=
    Int.mul_lt_mul_of_pos_left hpow6 (by omega)
  have hlin : (912 * (P0 : Int) - 120) * ((45 ^ j : Nat) : Int) ≤
      (1140 * (P0 : Int) - 570) * ((45 ^ j : Nat) : Int) :=
    Int.mul_le_mul_of_nonneg_right (by omega) (Int.natCast_nonneg _)
  -- Therefore `6 * (4 * 34^j * (228 * P0 - 30)) < 6 * (95 * 45^j * (2 * P0 - 1))`!
  have hcore : 4 * ((34 ^ j : Nat) : Int) * (228 * (P0 : Int) - 30) <
      95 * ((45 ^ j : Nat) : Int) * (2 * (P0 : Int) - 1) := by
    have h6 : 6 * (4 * ((34 ^ j : Nat) : Int) * (228 * (P0 : Int) - 30)) <
        6 * (95 * ((45 ^ j : Nat) : Int) * (2 * (P0 : Int) - 1)) := by
      grind
    omega
  grind

/-- Unconditional specialization of the stock-floor discount, `15 * W' ≤ 34 * W - 30`,
and `13 * T' ≤ 33 * T - 166` to the canonical clock-0 Recamán orbit `Recaman.Basic.a`. -/
theorem canonical_orbit_floor_potentials (c v Q : Nat)
    (hL : IsLastFloorVisit 0 initial c v Q) :
    3 * (v - c) + 6 * a v + 4 * seenCountIn 0 initial c (a v) (a c - 1) ≤ 6 * a c ∧
      floorP 0 initial (v + 1) + 4 * stockBelow 0 initial c + 1 ≤ 3 * floorP 0 initial c ∧
      15 * floorW 0 initial (v + 1) ≤ 34 * floorW 0 initial c - 30 ∧
      13 * floorT 0 initial (v + 1) ≤ 33 * floorT 0 initial c - 166 := by
  have hrun_eq : ∀ t, run 0 initial t = stateAt t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      change step (0 + t + 1) (run 0 initial t) = step (t + 1) (stateAt t)
      rw [Nat.zero_add, ih]
  have ha_eq : ∀ t, (run 0 initial t).value = a t := fun t => by unfold a; rw [hrun_eq t]
  have hdisc := floor_cut_stock_discount 0 initial c v Q hL
  have hW := floor_potential_W_recurrence 0 initial c v Q hL
  have hT := floor_potential_T_recurrence 0 initial c v Q hL
  rw [ha_eq c, ha_eq v] at hdisc
  exact ⟨hdisc.1, hdisc.2.1, hW, hT⟩

end Recaman.NumericStockStripPotential
