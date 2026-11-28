import Recaman.CoherentGreedyFreshness

namespace Recaman.NumericCandidateRankPotential

open Recaman Recaman.SeededReplay Recaman.CoherentGreedyFreshness
open Recaman.FloorSupplyPotential Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction
open Recaman.LineCapacityPeriodic Recaman.LeadingRunSupply
open Recaman.ShortPeriodicSupply (sign)

/-! # Purely numeric candidate-band rank potential & all-time fresh wallet (`E-802`)

Formalizes the purely numeric arbitrary-depth candidate-band rank potential (`E-761`)
directly on arbitrary finite-state greedy continuations `SeededReplay.run b s` and on
the canonical clock-0 Recamán orbit `Recaman.Basic.a`:

1. `candidate_area_bridge_identity`: exact Abel bridge identity connecting `replayCand`
   at arbitrary clocks `p, q` to `floorPotential` at level `Fw p - 2`.
2. `small_candidate_permanent_floor`: at any actual `A`-step `p` with
   `replayCand b s p ≤ (b + p + 1) + 6`, every future `t ≥ p` satisfies
   `Fw (replaySign b s) p - 1 ≤ Fw (replaySign b s) t` (no coherence assumed).
3. `small_candidate_floor_sharp`: exact sharpness of constant `+6` for every `n ≥ 2`
   via `ASSS` reaching `Fw = -2`.
4. `candidate_band_rank_strict_mono`: for every `Y : Nat`, `K = Y / 3 + 1`, and any
   `p < q` with `replaySign b s p = true`, `Y ≤ b + p + 1`, and both candidates in `[0, Y]`:
   `Fw p ≤ Fw q`, equality forces `replayCand q + 3 ≤ replayCand p`, and
   `bandRank Y b s p + 1 ≤ bandRank Y b s q`.
5. `candidate_band_fixed_height_sharp`: exact sharpness of the fixed-height bound
   `Y / 3 + 1` for every `Y : Nat` via `(AS)^(Y/3) A`.
6. `same_candidate_same_height_fresh_wallet`: independent all-time fresh-value wallet
   (with NO late-clock restriction and NO `s.value ∈ s.seen`): any strictly sorted list `ps`
   of actual `A`-clocks sharing fixed `(y : Nat, k : Int)` has `ps.length ≤ max 1 (y - 2)`.
7. `same_candidate_late_strict_ascent` & `original_win_source_finite_capacity`:
   for fixed `y : Nat`, after `y ≤ (b + p + 1) + 6`, every later event `q > p` with
   `replayCand b s q = y` has strictly higher `Fw q ≥ Fw p + 1`. Consequently any fixed
   original `Win` source `u` supplies at most `1` late hit and at most
   `max 1 ((run b s u).value - 2)` hits in all time.
8. `candidate_band_finite_horizon_count_le` & `canonical_orbit_candidate_band_bounds`:
   running-minimum positivity bound `-(s.value / (b + 1)) ≤ Fw t` yields the finite-horizon
   selected-event cardinality bound `≤ (Y / 3 + 1) * (Fw Q + s.value / (b + 1) + 2)`,
   specializing directly to `Recaman.Basic.a` (`≤ (Y / 3 + 1) * (Fw Q + 2)`).
-/

/-- Integer subtraction candidate `X_t - (b + t + 1)` at step `t` of `SeededReplay.run b s`. -/
def replayCand (b : Nat) (s : State) (t : Nat) : Int :=
  value b s t - ((b + t + 1 : Nat) : Int)

/-- Bounded candidate-band monotone rank `Φ_Y(p) = (Y / 3 + 1) * H_p - ⌊c_p / 3⌋`. -/
def bandRank (Y b : Nat) (s : State) (p : Nat) : Int :=
  ((Y / 3 + 1 : Nat) : Int) * Fw (replaySign b s) p - replayCand b s p / 3

/-- Sharp `+6` floor-threshold witness state for `n ≥ 2`. -/
def sharpFloorState (n : Nat) : State :=
  { value := 2 * n + 7, seen := [0, n + 7, 2 * n + 7] }

/-- Sharp fixed-height witness state for band `Y : Nat`. -/
def sharpBandState (Y : Nat) : State :=
  { value := 2 * Y + 2
    seen := 0 :: (2 * Y + 2) :: (List.range (Y / 3 + 1)).map (fun j => Y - 3 * j) }

/-- Selected `A`-clocks in `[0, Q)` with clock `≥ Y` and candidate in `[0, Y]`. -/
def bandSelectedClocks (Y b : Nat) (s : State) (Q : Nat) : List Nat :=
  (List.range Q).filter (fun p =>
    replaySign b s p && decide (Y ≤ b + p + 1) &&
      decide (0 ≤ replayCand b s p) && decide (replayCand b s p ≤ (Y : Int)))

/-! ## Basic positivity, step, and discrete IVT helpers -/

private theorem replay_value_pos_of_pos (b : Nat) (s : State) {t : Nat} (ht : 1 ≤ t) :
    1 ≤ value b s t := by
  cases t with
  | zero => omega
  | succ t =>
    change (1 : Int) ≤ ((step (b + t + 1) (run b s t)).value : Int)
    simp only [step, nextValue]
    by_cases hc : CanSubtract (b + t + 1) (run b s t)
    · rw [if_pos hc]
      have hlt : b + t + 1 < (run b s t).value := hc.1
      omega
    · rw [if_neg hc]
      omega

private theorem floorPotential_step_zero (f : Nat → Bool) (m : Int) (i : Nat) :
    floorPotential f 0 m (i + 1) - floorPotential f 0 m i = Fw f (i + 1) - (m + 1) := by
  unfold floorPotential
  simp only [Nat.sub_zero]
  have hAr := Ar_succ f 0 i
  have h0 : Fw f 0 = 0 := rfl
  simp only [Nat.zero_add, h0, Int.sub_zero] at hAr ⊢
  rw [hAr]
  push_cast
  grind

private theorem floorPotential_diff_nonneg_of_ge (f : Nat → Bool) (m : Int) :
    ∀ {p q : Nat}, p ≤ q → (∀ i, p < i → i ≤ q → m + 1 ≤ Fw f i) →
      0 ≤ floorPotential f 0 m q - floorPotential f 0 m p := by
  intro p q hpq
  induction q with
  | zero =>
    have hp : p = 0 := by omega
    subst hp
    intro _
    omega
  | succ q ih =>
    intro hge
    by_cases heq : p = q + 1
    · subst heq; omega
    · have hpq' : p ≤ q := by omega
      have hih := ih hpq' (fun i hi1 hi2 => hge i hi1 (by omega))
      have hst := floorPotential_step_zero f m q
      have hq1 := hge (q + 1) (by omega) (Nat.le_refl _)
      omega

private theorem floorPotential_diff_ge_of_witness (f : Nat → Bool) (m : Int)
    {p q u : Nat} (hpu : p < u) (huq : u ≤ q)
    (hge : ∀ i, p < i → i ≤ q → m + 1 ≤ Fw f i) :
    Fw f u - (m + 1) ≤ floorPotential f 0 m q - floorPotential f 0 m p := by
  have h1 := floorPotential_diff_nonneg_of_ge f m (p := p) (q := u - 1) (by omega)
    (fun i hi1 hi2 => hge i hi1 (by omega))
  have h2 := floorPotential_diff_nonneg_of_ge f m (p := u) (q := q) huq
    (fun i hi1 hi2 => hge i (by omega) hi2)
  have hst := floorPotential_step_zero f m (u - 1)
  rw [show u - 1 + 1 = u by omega] at hst
  omega

private theorem floorPotential_diff_ge_of_two_witnesses (f : Nat → Bool) (m : Int)
    {p q u v : Nat} (hpu : p < u) (huv : u < v) (hvq : v ≤ q)
    (hge : ∀ i, p < i → i ≤ q → m + 1 ≤ Fw f i) :
    (Fw f u - (m + 1)) + (Fw f v - (m + 1)) ≤
      floorPotential f 0 m q - floorPotential f 0 m p := by
  have h1 := floorPotential_diff_nonneg_of_ge f m (p := p) (q := u - 1) (by omega)
    (fun i hi1 hi2 => hge i hi1 (by omega))
  have h2 := floorPotential_diff_nonneg_of_ge f m (p := u) (q := v - 1) (by omega)
    (fun i hi1 hi2 => hge i (by omega) (by omega))
  have h3 := floorPotential_diff_nonneg_of_ge f m (p := v) (q := q) hvq
    (fun i hi1 hi2 => hge i (by omega) hi2)
  have hsu := floorPotential_step_zero f m (u - 1)
  rw [show u - 1 + 1 = u by omega] at hsu
  have hsv := floorPotential_step_zero f m (v - 1)
  rw [show v - 1 + 1 = v by omega] at hsv
  omega

private theorem fw_step_diff (f : Nat → Bool) (i : Nat) :
    Fw f (i + 1) = Fw f i + 1 ∨ Fw f (i + 1) = Fw f i - 1 := by
  have h := Fw_succ f i
  cases hfi : f i <;> simp [hfi, sign] at h <;> omega

private theorem fw_ivt_down (f : Nat → Bool) (target : Int) :
    ∀ {a b : Nat}, a ≤ b → target ≤ Fw f a → Fw f b ≤ target →
      ∃ u, a ≤ u ∧ u ≤ b ∧ Fw f u = target := by
  intro a b hab
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha
    intro h1 h2
    exact ⟨0, Nat.le_refl 0, Nat.le_refl 0, by omega⟩
  | succ b ih =>
    intro ha hb
    by_cases heq : a = b + 1
    · subst heq; exact ⟨b + 1, Nat.le_refl _, Nat.le_refl _, by omega⟩
    · by_cases hbt : Fw f b ≤ target
      · obtain ⟨u, hu1, hu2, hfu⟩ := ih (by omega) ha hbt
        exact ⟨u, hu1, by omega, hfu⟩
      · have hst := fw_step_diff f b
        exact ⟨b + 1, by omega, Nat.le_refl _, by omega⟩

private theorem least_violation (P : Nat → Prop) :
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

/-! ## Part 1: Exact candidate/area bridge identity and sharp permanent future sign floor -/

/-- Exact Abel-summation bridge identity connecting `replayCand` at arbitrary clocks `p, q`
to `floorPotential` at level `Fw p - 2`. -/
theorem candidate_area_bridge_identity (b : Nat) (s : State) (p q : Nat) :
    floorPotential (replaySign b s) 0 (Fw (replaySign b s) p - 2) q -
      floorPotential (replaySign b s) 0 (Fw (replaySign b s) p - 2) p =
    ((b + q + 1 : Nat) : Int) * (Fw (replaySign b s) q - Fw (replaySign b s) p) +
      replayCand b s p - replayCand b s q := by
  have hp := replay_value_eq_abel_potential b s p
  have hq := replay_value_eq_abel_potential b s q
  unfold replayCand floorPotential at hp hq ⊢
  simp only [Nat.sub_zero] at hp hq ⊢
  have h0 : Fw (replaySign b s) 0 = 0 := rfl
  rw [h0] at hp hq ⊢
  push_cast at hp hq ⊢
  grind

/-- Permanent future sign floor (`E-761` proposer lemma): at any actual `A`-step `p`
with `replayCand b s p ≤ (b + p + 1) + 6`, every future clock `t ≥ p` satisfies
`Fw (replaySign b s) p - 1 ≤ Fw (replaySign b s) t`. -/
theorem small_candidate_permanent_floor (b : Nat) (s : State) (p : Nat)
    (hA : replaySign b s p = true)
    (hc : replayCand b s p ≤ ((b + p + 1 : Nat) : Int) + 6) :
    ∀ t, p ≤ t → Fw (replaySign b s) p - 1 ≤ Fw (replaySign b s) t := by
  let f := replaySign b s
  intro t hpt
  apply Classical.byContradiction
  intro hlt
  change ¬ Fw f p - 1 ≤ Fw f t at hlt
  have hd0 : Fw f (p + (t - p)) < Fw f p - 1 := by
    rw [Nat.add_sub_cancel' hpt]; omega
  obtain ⟨d, _, hd_lt, hd_min⟩ :=
    least_violation (fun k => Fw f (p + k) < Fw f p - 1) (t - p) (t - p) (Nat.le_refl _) hd0
  have hFw_p1 : Fw f (p + 1) = Fw f p + 1 := by
    have h := Fw_succ f p
    change Fw f (p + 1) = Fw f p + sign (replaySign b s p) at h
    rw [hA] at h
    simp [sign] at h
    omega
  have hd_ge4 : 4 ≤ d := by
    by_cases hd0' : d = 0
    · subst hd0'; simp only [Nat.add_zero] at hd_lt; omega
    by_cases hd1 : d = 1
    · subst hd1; omega
    by_cases hd2 : d = 2
    · subst hd2
      have h1 := fw_step_diff f (p + 1)
      rw [show p + 1 + 1 = p + 2 by omega] at h1
      omega
    by_cases hd3 : d = 3
    · subst hd3
      have h1 := fw_step_diff f (p + 1)
      have h2 := fw_step_diff f (p + 2)
      rw [show p + 1 + 1 = p + 2 by omega] at h1
      rw [show p + 2 + 1 = p + 3 by omega] at h2
      omega
    omega
  have hprev_ge : ∀ i, p < i → i < p + d → Fw f p - 1 ≤ Fw f i := by
    intro i hi1 hi2
    have hnot := hd_min (i - p) (by omega)
    rw [Nat.add_sub_cancel' (by omega)] at hnot
    omega
  have hFw_prev : Fw f (p + d - 1) = Fw f p - 1 := by
    have hge := hprev_ge (p + d - 1) (by omega) (by omega)
    have hst := fw_step_diff f (p + d - 1)
    rw [show p + d - 1 + 1 = p + d by omega] at hst
    omega
  have hFw_d : Fw f (p + d) = Fw f p - 2 := by
    have hst := fw_step_diff f (p + d - 1)
    rw [show p + d - 1 + 1 = p + d by omega] at hst
    omega
  obtain ⟨u, hu1, hu2, hFwu⟩ := fw_ivt_down f (Fw f p) (a := p + 1) (b := p + d - 1)
    (by omega) (by omega) (by omega)
  have hup1 : p + 1 < u := by
    by_cases h : u = p + 1
    · subst h; omega
    · omega
  have hu_lt : u < p + d - 1 := by
    by_cases h : u = p + d - 1
    · subst h; omega
    · omega
  have hpot_before :
      3 ≤ floorPotential f 0 (Fw f p - 2) (p + d - 1) - floorPotential f 0 (Fw f p - 2) p := by
    have htwo := floorPotential_diff_ge_of_two_witnesses f (Fw f p - 2)
      (p := p) (q := p + d - 1) (u := p + 1) (v := u)
      (by omega) hup1 (by omega)
      (fun i hi1 hi2 => by
        have h := hprev_ge i hi1 (by omega)
        omega)
    rw [hFw_p1, hFwu] at htwo
    omega
  have hpot_last := floorPotential_step_zero f (Fw f p - 2) (p + d - 1)
  rw [show p + d - 1 + 1 = p + d by omega, hFw_d] at hpot_last
  have hpot_total :
      2 ≤ floorPotential f 0 (Fw f p - 2) (p + d) - floorPotential f 0 (Fw f p - 2) p := by
    omega
  have hbr := candidate_area_bridge_identity b s p (p + d)
  change floorPotential f 0 (Fw f p - 2) (p + d) - floorPotential f 0 (Fw f p - 2) p =
    ((b + (p + d) + 1 : Nat) : Int) * (Fw f (p + d) - Fw f p) +
      replayCand b s p - replayCand b s (p + d) at hbr
  rw [hFw_d] at hbr
  have hv_pos : 1 ≤ value b s (p + d) := replay_value_pos_of_pos b s (by omega)
  unfold replayCand at hbr hc
  push_cast at hbr hc
  omega

/-- Exact sharpness of constant `+6` in `small_candidate_permanent_floor`:
for every `n ≥ 2`, `b = n - 1`, `s = sharpFloorState n` has `replayCand b s 0 = n + 7`
and executes `ASSS`, reaching `Fw = -2` at step `4`. -/
theorem small_candidate_floor_sharp (n : Nat) (hn : 2 ≤ n) :
    replaySign (n - 1) (sharpFloorState n) 0 = true ∧
      replayCand (n - 1) (sharpFloorState n) 0 = ((n + 7 : Nat) : Int) ∧
      Fw (replaySign (n - 1) (sharpFloorState n)) 4 = -2 := by
  let b := n - 1
  let s : State := sharpFloorState n
  change replaySign b s 0 = true ∧ replayCand b s 0 = ((n + 7 : Nat) : Int) ∧
    Fw (replaySign b s) 4 = -2
  have hnc0 : ¬ CanSubtract (b + 0 + 1) (run b s 0) := by
    intro h
    have hmem : (2 * n + 7) - (b + 0 + 1) ∈ ([0, n + 7, 2 * n + 7] : List Nat) := by
      have : (2 * n + 7) - (b + 0 + 1) = n + 7 := by omega
      rw [this]; simp
    exact h.2 hmem
  have hs0 : replaySign b s 0 = true := by simp [replaySign, hnc0]
  have hr1 : run b s 1 = { value := 3 * n + 7, seen := [3 * n + 7, 0, n + 7, 2 * n + 7] } := by
    change step (b + 0 + 1) (run b s 0) = _
    simp only [step, nextValue, if_neg hnc0]
    dsimp only [run, s, sharpFloorState]
    have hv : 2 * n + 7 + (b + 0 + 1) = 3 * n + 7 := by omega
    rw [hv]
  have hc1 : CanSubtract (b + 1 + 1) (run b s 1) := by
    rw [hr1]
    refine ⟨by dsimp; omega, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hs1 : replaySign b s 1 = false := by simp [replaySign, hc1]
  have hr2 : run b s 2 = { value := 2 * n + 6, seen := [2 * n + 6, 3 * n + 7, 0, n + 7, 2 * n + 7] } := by
    change step (b + 1 + 1) (run b s 1) = _
    simp only [step, nextValue, if_pos hc1]
    rw [hr1]
    dsimp
    have hv : 3 * n + 7 - (b + 1 + 1) = 2 * n + 6 := by omega
    rw [hv]
  have hc2 : CanSubtract (b + 2 + 1) (run b s 2) := by
    rw [hr2]
    refine ⟨by dsimp; omega, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hs2 : replaySign b s 2 = false := by simp [replaySign, hc2]
  have hr3 : run b s 3 = { value := n + 4, seen := [n + 4, 2 * n + 6, 3 * n + 7, 0, n + 7, 2 * n + 7] } := by
    change step (b + 2 + 1) (run b s 2) = _
    simp only [step, nextValue, if_pos hc2]
    rw [hr2]
    dsimp
    have hv : 2 * n + 6 - (b + 2 + 1) = n + 4 := by omega
    rw [hv]
  have hc3 : CanSubtract (b + 3 + 1) (run b s 3) := by
    rw [hr3]
    refine ⟨by dsimp; omega, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hs3 : replaySign b s 3 = false := by simp [replaySign, hc3]
  refine ⟨hs0, ?_, ?_⟩
  · unfold replayCand value
    simp only [run, s, sharpFloorState]
    omega
  · have h1 := Fw_succ (replaySign b s) 0
    have h2 := Fw_succ (replaySign b s) 1
    have h3 := Fw_succ (replaySign b s) 2
    have h4 := Fw_succ (replaySign b s) 3
    have h0 : Fw (replaySign b s) 0 = 0 := rfl
    rw [hs0, h0] at h1
    rw [hs1] at h2
    rw [hs2] at h3
    rw [hs3] at h4
    simp [sign] at h1 h2 h3 h4
    omega

/-! ## Part 2: Monotone candidate-band rank `Φ_Y` and sharp fixed-height count -/

/-- Bounded candidate-band monotone rank (`E-761` principal theorem):
for any `Y : Nat` and any `p < q` with `replaySign b s p = true`, `Y ≤ b + p + 1`,
and `replayCand b s p, replayCand b s q ∈ [0, Y]`:
1. `Fw p ≤ Fw q` (heights are nondecreasing across all candidates in `[0, Y]`),
2. `Fw q = Fw p → replayCand q + 3 ≤ replayCand p` (strict drop by `≥ 3` at equal height),
3. `bandRank Y b s p + 1 ≤ bandRank Y b s q`. -/
theorem candidate_band_rank_strict_mono (Y b : Nat) (s : State) (p q : Nat)
    (hpq : p < q)
    (hAp : replaySign b s p = true)
    (hclk : Y ≤ b + p + 1)
    (hcp0 : 0 ≤ replayCand b s p) (hcpY : replayCand b s p ≤ (Y : Int))
    (hcq0 : 0 ≤ replayCand b s q) (hcqY : replayCand b s q ≤ (Y : Int)) :
    Fw (replaySign b s) p ≤ Fw (replaySign b s) q ∧
      (Fw (replaySign b s) q = Fw (replaySign b s) p →
        replayCand b s q + 3 ≤ replayCand b s p) ∧
      bandRank Y b s p + 1 ≤ bandRank Y b s q := by
  let f := replaySign b s
  have hfloor : ∀ t, p ≤ t → Fw f p - 1 ≤ Fw f t :=
    small_candidate_permanent_floor b s p hAp (by omega)
  have hFw_p1 : Fw f (p + 1) = Fw f p + 1 := by
    have h := Fw_succ f p
    change Fw f (p + 1) = Fw f p + sign (replaySign b s p) at h
    rw [hAp] at h
    simp [sign] at h
    omega
  have hpot_ge2 :
      2 ≤ floorPotential f 0 (Fw f p - 2) q - floorPotential f 0 (Fw f p - 2) p := by
    have hw := floorPotential_diff_ge_of_witness f (Fw f p - 2)
      (p := p) (q := q) (u := p + 1) (by omega) (by omega)
      (fun i hi1 _ => by have := hfloor i (by omega); omega)
    rw [hFw_p1] at hw
    omega
  have hbr := candidate_area_bridge_identity b s p q
  change floorPotential f 0 (Fw f p - 2) q - floorPotential f 0 (Fw f p - 2) p =
    ((b + q + 1 : Nat) : Int) * (Fw f q - Fw f p) +
      replayCand b s p - replayCand b s q at hbr
  have hd_ge : Fw f p ≤ Fw f q := by
    apply Classical.byContradiction
    intro hlt
    have hle : Fw f q - Fw f p ≤ -1 := by omega
    have hmul : ((b + q + 1 : Nat) : Int) * (Fw f q - Fw f p) ≤
        ((b + q + 1 : Nat) : Int) * (-1) :=
      Int.mul_le_mul_of_nonneg_left hle (by omega)
    omega
  have heq_drop : Fw f q = Fw f p → replayCand b s q + 3 ≤ replayCand b s p := by
    intro hEq
    have hq_ge : p + 2 ≤ q := by
      by_cases h : q = p + 1
      · subst h; omega
      · omega
    have hpot_ge3 :
        3 ≤ floorPotential f 0 (Fw f p - 2) q - floorPotential f 0 (Fw f p - 2) p := by
      have htwo := floorPotential_diff_ge_of_two_witnesses f (Fw f p - 2)
        (p := p) (q := q) (u := p + 1) (v := q)
        (by omega) (by omega) (Nat.le_refl q)
        (fun i hi1 _ => by have := hfloor i (by omega); omega)
      rw [hFw_p1, hEq] at htwo
      omega
    rw [hEq] at hbr
    omega
  refine ⟨hd_ge, heq_drop, ?_⟩
  unfold bandRank
  change ((Y / 3 + 1 : Nat) : Int) * Fw f p - replayCand b s p / 3 + 1 ≤
    ((Y / 3 + 1 : Nat) : Int) * Fw f q - replayCand b s q / 3
  by_cases hEq : Fw f q = Fw f p
  · have hdrop := heq_drop hEq
    rw [hEq]
    omega
  · have hgt : Fw f p + 1 ≤ Fw f q := by omega
    have hmul : ((Y / 3 + 1 : Nat) : Int) * (Fw f p + 1) ≤
        ((Y / 3 + 1 : Nat) : Int) * Fw f q :=
      Int.mul_le_mul_of_nonneg_left hgt (by omega)
    rw [Int.mul_add, Int.mul_one] at hmul
    omega

/-- Exact sharpness of the fixed-height bound `Y / 3 + 1` for every `Y : Nat`:
with `b = Y + 1` and `s = sharpBandState Y`, the actual greedy replay executes `(AS)^(Y/3) A`,
producing `Y / 3 + 1` selected events at height `0` with candidates `Y, Y - 3, ..., Y - 3*(Y/3)`. -/
theorem candidate_band_fixed_height_sharp (Y : Nat) :
    ∀ j, j ≤ Y / 3 →
      replaySign (Y + 1) (sharpBandState Y) (2 * j) = true ∧
        Fw (replaySign (Y + 1) (sharpBandState Y)) (2 * j) = 0 ∧
        replayCand (Y + 1) (sharpBandState Y) (2 * j) = ((Y - 3 * j : Nat) : Int) := by
  let m := Y / 3
  let b := Y + 1
  let val := 2 * Y + 2
  let s : State := sharpBandState Y
  have hinv : ∀ j, j ≤ m →
      (run b s (2 * j)).value = val - j ∧
      Fw (replaySign b s) (2 * j) = 0 ∧
      (∀ z : Nat, z ∈ (run b s (2 * j)).seen ↔
        z ∈ s.seen ∨
        (∃ i, i < j ∧ z = 3 * Y + 4 + i) ∨
        (∃ i, i < j ∧ z = val - (i + 1))) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨rfl, rfl, fun z => ?_⟩
      simp [run]
    | succ j ih =>
      intro hjm
      obtain ⟨hval_j, hFw_j, hseen_j⟩ := ih (by omega)
      have hcand_j : (run b s (2 * j)).value - (b + 2 * j + 1) = Y - 3 * j := by omega
      have hmem_j : Y - 3 * j ∈ s.seen := by
        simp only [s, sharpBandState, List.mem_cons, List.mem_map, List.mem_range]
        right; right
        exact ⟨j, by omega, rfl⟩
      have hnc_j : ¬ CanSubtract (b + 2 * j + 1) (run b s (2 * j)) := by
        intro hc
        exact hc.2 (by rw [hcand_j]; exact (hseen_j (Y - 3 * j)).mpr (Or.inl hmem_j))
      have hsign_2j : replaySign b s (2 * j) = true := by simp [replaySign, hnc_j]
      have hval_2j1 : (run b s (2 * j + 1)).value = 3 * Y + 4 + j := by
        change (step (b + 2 * j + 1) (run b s (2 * j))).value = _
        simp only [step, nextValue, if_neg hnc_j]
        omega
      have hseen_2j1 : ∀ z : Nat, z ∈ (run b s (2 * j + 1)).seen ↔
          z = 3 * Y + 4 + j ∨ z ∈ (run b s (2 * j)).seen := by
        intro z
        change z ∈ nextValue (b + 2 * j + 1) (run b s (2 * j)) :: (run b s (2 * j)).seen ↔ _
        rw [List.mem_cons]
        have hnv : nextValue (b + 2 * j + 1) (run b s (2 * j)) = 3 * Y + 4 + j := hval_2j1
        rw [hnv]
      have hsub_val : (run b s (2 * j + 1)).value - (b + (2 * j + 1) + 1) = val - (j + 1) := by
        omega
      have hnot_mem : val - (j + 1) ∉ (run b s (2 * j + 1)).seen := by
        rw [hseen_2j1, hseen_j]
        rintro (h1 | (h2 | (⟨i, hi, h3⟩ | ⟨i, hi, h4⟩)))
        · omega
        · simp only [s, sharpBandState, List.mem_cons, List.mem_map, List.mem_range] at h2
          rcases h2 with h2 | h2 | ⟨k, hk, h2⟩ <;> omega
        · omega
        · omega
      have hc_2j1 : CanSubtract (b + (2 * j + 1) + 1) (run b s (2 * j + 1)) := by
        refine ⟨by omega, ?_⟩
        rw [hsub_val]
        exact hnot_mem
      have hsign_2j1 : replaySign b s (2 * j + 1) = false := by simp [replaySign, hc_2j1]
      have hval_next : (run b s (2 * (j + 1))).value = val - (j + 1) := by
        rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega]
        change (step (b + (2 * j + 1) + 1) (run b s (2 * j + 1))).value = _
        simp only [step, nextValue, if_pos hc_2j1]
        exact hsub_val
      have hFw_next : Fw (replaySign b s) (2 * (j + 1)) = 0 := by
        rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega]
        have h1 := Fw_succ (replaySign b s) (2 * j)
        have h2 := Fw_succ (replaySign b s) (2 * j + 1)
        rw [hsign_2j, hFw_j] at h1
        rw [hsign_2j1] at h2
        simp [sign] at h1 h2
        omega
      refine ⟨hval_next, hFw_next, ?_⟩
      intro z
      rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega]
      change z ∈ nextValue (b + (2 * j + 1) + 1) (run b s (2 * j + 1)) :: (run b s (2 * j + 1)).seen ↔ _
      rw [List.mem_cons]
      have hnv2 : nextValue (b + (2 * j + 1) + 1) (run b s (2 * j + 1)) = val - (j + 1) := by
        simp only [nextValue, if_pos hc_2j1]
        exact hsub_val
      rw [hnv2, hseen_2j1, hseen_j]
      constructor
      · rintro (rfl | rfl | hs_mem | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
        · right; right; exact ⟨j, Nat.lt_succ_self j, rfl⟩
        · right; left; exact ⟨j, Nat.lt_succ_self j, rfl⟩
        · left; exact hs_mem
        · right; left; exact ⟨i, by omega, rfl⟩
        · right; right; exact ⟨i, by omega, rfl⟩
      · rintro (hs_mem | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
        · right; right; left; exact hs_mem
        · by_cases hij : i = j
          · subst hij; right; left; rfl
          · right; right; right; left; exact ⟨i, by omega, rfl⟩
        · by_cases hij : i = j
          · subst hij; left; rfl
          · right; right; right; right; exact ⟨i, by omega, rfl⟩
  intro j hjm
  obtain ⟨hval_j, hFw_j, hseen_j⟩ := hinv j hjm
  have hcand_j : (run b s (2 * j)).value - (b + 2 * j + 1) = Y - 3 * j := by omega
  have hmem_j : Y - 3 * j ∈ s.seen := by
    simp only [s, sharpBandState, List.mem_cons, List.mem_map, List.mem_range]
    right; right
    exact ⟨j, by omega, rfl⟩
  have hnc_j : ¬ CanSubtract (b + 2 * j + 1) (run b s (2 * j)) := by
    intro hc
    exact hc.2 (by rw [hcand_j]; exact (hseen_j (Y - 3 * j)).mpr (Or.inl hmem_j))
  refine ⟨by change replaySign b s (2 * j) = true; simp [replaySign, hnc_j], hFw_j, ?_⟩
  unfold replayCand value
  rw [hval_j]
  omega

/-! ## Part 3: Independent all-time fresh-value wallet & late-clock strict height ascent -/

/-- Between two `A`-events `p < q` sharing the same candidate `y : Nat` and height `k`,
there is an actual fresh `S`-landing `v ∈ (p, q]` with `1 ≤ value b s v ≤ y - 3`. -/
private theorem bridge_fresh_s_landing (b : Nat) (s : State) (y : Nat) (k : Int)
    (p q : Nat) (hpq : p < q)
    (hAp : replaySign b s p = true)
    (hcp : replayCand b s p = (y : Int)) (hcq : replayCand b s q = (y : Int))
    (hFp : Fw (replaySign b s) p = k) (hFq : Fw (replaySign b s) q = k) :
    ∃ v, p < v ∧ v ≤ q ∧
      replaySign b s (v - 1) = false ∧
      1 ≤ (run b s v).value ∧ (run b s v).value + 3 ≤ y := by
  let f := replaySign b s
  have hFw_p1 : Fw f (p + 1) = k + 1 := by
    have h := Fw_succ f p
    change Fw f (p + 1) = Fw f p + sign (replaySign b s p) at h
    rw [hAp, hFp] at h
    simp [sign] at h
    omega
  have hbr := candidate_area_bridge_identity b s p q
  change floorPotential f 0 (Fw f p - 2) q - floorPotential f 0 (Fw f p - 2) p =
    ((b + q + 1 : Nat) : Int) * (Fw f q - Fw f p) +
      replayCand b s p - replayCand b s q at hbr
  rw [hFp, hFq, hcp, hcq] at hbr
  have hpot_zero : floorPotential f 0 (k - 2) q - floorPotential f 0 (k - 2) p = 0 := by omega
  have hex_dip : ∃ d, p + d ≤ q ∧ 0 < d ∧ Fw f (p + d) ≤ k - 1 := by
    apply Classical.byContradiction
    intro hno
    have hall : ∀ i, p < i → i ≤ q → k ≤ Fw f i := by
      intro i hi1 hi2
      apply Classical.byContradiction
      intro hlt
      exact hno ⟨i - p, by omega, by omega, by rw [Nat.add_sub_cancel' (by omega)]; omega⟩
    have hw := floorPotential_diff_ge_of_witness f (k - 2)
      (p := p) (q := q) (u := p + 1) (by omega) (by omega)
      (fun i hi1 hi2 => by have := hall i hi1 hi2; omega)
    rw [hFw_p1] at hw
    omega
  obtain ⟨d0, hd0_le, hd0_pos, hd0_fw⟩ := hex_dip
  obtain ⟨d, hd_le, ⟨hd_pos, hd_fw⟩, hd_min⟩ :=
    least_violation (fun j => 0 < j ∧ Fw f (p + j) ≤ k - 1) d0 d0 (Nat.le_refl _) ⟨hd0_pos, hd0_fw⟩
  have hv_ge : 3 ≤ d := by
    by_cases h1 : d = 1
    · subst h1; omega
    by_cases h2 : d = 2
    · subst h2
      have hst := fw_step_diff f (p + 1)
      rw [show p + 1 + 1 = p + 2 by omega] at hst
      omega
    omega
  have hprev_ge : ∀ i, p < i → i < p + d → k ≤ Fw f i := by
    intro i hi1 hi2
    have hnot := hd_min (i - p) (by omega)
    rw [Nat.add_sub_cancel' (by omega)] at hnot
    apply Classical.byContradiction
    intro hlt
    exact hnot ⟨by omega, by omega⟩
  have hFw_prev : Fw f (p + d - 1) = k := by
    have h1 := hprev_ge (p + d - 1) (by omega) (by omega)
    have hst := fw_step_diff f (p + d - 1)
    rw [show p + d - 1 + 1 = p + d by omega] at hst
    omega
  have hFw_v : Fw f (p + d) = k - 1 := by
    have hst := fw_step_diff f (p + d - 1)
    rw [show p + d - 1 + 1 = p + d by omega] at hst
    omega
  have hS_step : replaySign b s (p + d - 1) = false := by
    have h := Fw_succ f (p + d - 1)
    rw [show p + d - 1 + 1 = p + d by omega] at h
    cases hs_eq : replaySign b s (p + d - 1)
    · rfl
    · change Fw f (p + d) = Fw f (p + d - 1) + sign (replaySign b s (p + d - 1)) at h
      rw [hs_eq] at h
      simp [sign] at h
      omega
  have hpot_v : 3 ≤ floorPotential f 0 (k - 2) (p + d) - floorPotential f 0 (k - 2) p := by
    have htwo := floorPotential_diff_ge_of_two_witnesses f (k - 2)
      (p := p) (q := p + d - 1) (u := p + 1) (v := p + d - 1)
      (by omega) (by omega) (Nat.le_refl _)
      (fun i hi1 hi2 => by have := hprev_ge i hi1 (by omega); omega)
    rw [hFw_p1, hFw_prev] at htwo
    have hlast := floorPotential_step_zero f (k - 2) (p + d - 1)
    rw [show p + d - 1 + 1 = p + d by omega, hFw_v] at hlast
    omega
  have hv_abel := replay_value_eq_abel_potential b s (p + d)
  have hp_abel := replay_value_eq_abel_potential b s p
  have hval_diff : value b s (p + d) =
      replayCand b s p - (floorPotential f 0 (k - 2) (p + d) - floorPotential f 0 (k - 2) p) := by
    unfold replayCand floorPotential at hv_abel hp_abel ⊢
    simp only [Nat.sub_zero] at hv_abel hp_abel ⊢
    have h0 : Fw f 0 = 0 := rfl
    change value b s (p + d) =
      (s.value : Int) + ((b + 1 : Nat) : Int) * Fw f (p + d) -
        (Ar f 0 (p + d) + ((p + d : Nat) : Int) * (Fw f 0 - (Fw f (p + d) - 1 + 1))) at hv_abel
    change value b s p =
      (s.value : Int) + ((b + 1 : Nat) : Int) * Fw f p -
        (Ar f 0 p + (p : Int) * (Fw f 0 - (Fw f p - 1 + 1))) at hp_abel
    rw [h0, hFw_v] at hv_abel
    rw [h0, hFp] at hp_abel
    rw [h0]
    push_cast at hv_abel hp_abel ⊢
    grind
  have hv_pos : 1 ≤ value b s (p + d) := replay_value_pos_of_pos b s (by omega)
  refine ⟨p + d, by omega, by omega, hS_step, ?_, ?_⟩
  · change (1 : Int) ≤ ((run b s (p + d)).value : Int) at hv_pos
    omega
  · change ((run b s (p + d)).value : Int) = _ at hval_diff
    rw [hcp] at hval_diff
    omega

private theorem fresh_s_values_distinct (b : Nat) (s : State) :
    ∀ {u v : Nat}, 1 ≤ u → u < v → replaySign b s (v - 1) = false →
      (run b s u).value ≠ (run b s v).value := by
  intro u v hu huv hS hEq
  have hc : CanSubtract (b + (v - 1) + 1) (run b s (v - 1)) := by
    unfold replaySign at hS
    by_cases h : CanSubtract (b + (v - 1) + 1) (run b s (v - 1))
    · exact h
    · simp [h] at hS
  have hval_v : (run b s v).value = (run b s (v - 1)).value - (b + (v - 1) + 1) := by
    have hstep : (run b s ((v - 1) + 1)).value = (run b s (v - 1)).value - (b + (v - 1) + 1) := by
      change (step (b + (v - 1) + 1) (run b s (v - 1))).value = _
      simp only [step, nextValue, if_pos hc]
    rwa [show (v - 1) + 1 = v by omega] at hstep
  have hmem_u : (run b s u).value ∈ (run b s u).seen := by
    cases u with
    | zero => omega
    | succ u => exact step_value_mem_seen _ _
  have hseen_u : Seen b s u ((run b s u).value : Int) := ⟨(run b s u).value, hmem_u, rfl⟩
  have hseen_v1 : Seen b s (v - 1) ((run b s u).value : Int) := seen_mono (by omega) hseen_u
  obtain ⟨z, hz_mem, hz_eq⟩ := hseen_v1
  have hz : z = (run b s (v - 1)).value - (b + (v - 1) + 1) := by omega
  exact hc.2 (hz ▸ hz_mem)

private theorem nodup_length_le_of_subset_nat {xs ys : List Nat}
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

private theorem pairwise_fresh_s_ne (b : Nat) (s : State) :
    ∀ (vs : List Nat), vs.Pairwise (· < ·) →
      (∀ v ∈ vs, 1 ≤ v ∧ replaySign b s (v - 1) = false) →
      vs.Pairwise (fun u v => (run b s u).value ≠ (run b s v).value) := by
  intro vs
  induction vs with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons u rest ih =>
    intro hsort hprop
    have hu := List.pairwise_cons.mp hsort
    rw [List.pairwise_cons]
    refine ⟨fun v hv => ?_, ih hu.2 (fun w hw => hprop w (List.mem_cons_of_mem u hw))⟩
    have hu_prop := hprop u (List.mem_cons_self ..)
    have hv_prop := hprop v (List.mem_cons_of_mem u hv)
    exact fresh_s_values_distinct b s hu_prop.1 (hu.1 v hv) hv_prop.2

/-- Independent all-time fresh-value wallet (`E-761`): for ANY `b, s, y : Nat, k : Int`
(with NO late-clock restriction and NO `s.value ∈ s.seen`), any strictly sorted list `ps`
of actual `A`-clocks sharing candidate `y` and height `k` satisfies `ps.length ≤ max 1 (y - 2)`. -/
theorem same_candidate_same_height_fresh_wallet (b : Nat) (s : State) (y : Nat) (k : Int)
    (ps : List Nat) (hsort : ps.Pairwise (· < ·))
    (hmem : ∀ p ∈ ps, replaySign b s p = true ∧ replayCand b s p = (y : Int) ∧
      Fw (replaySign b s) p = k) :
    ps.length ≤ max 1 (y - 2) := by
  have hex_vs : ∀ (l : List Nat), l.Pairwise (· < ·) →
      (∀ p ∈ l, replaySign b s p = true ∧ replayCand b s p = (y : Int) ∧
        Fw (replaySign b s) p = k) →
      ∃ vs : List Nat, l.length ≤ vs.length + 1 ∧
        vs.Pairwise (· < ·) ∧
        (∀ v ∈ vs, 1 ≤ v ∧ replaySign b s (v - 1) = false ∧
          1 ≤ (run b s v).value ∧ (run b s v).value + 3 ≤ y) ∧
        (∀ p : Nat, l.head? = some p → ∀ v ∈ vs, p < v) := by
    intro l
    induction l with
    | nil =>
      intro _ _
      refine ⟨[], by simp, List.Pairwise.nil, fun _ h => ?_, fun _ h => ?_⟩
      · cases h
      · cases h
    | cons p rest ih =>
      intro hs hm
      cases rest with
      | nil =>
        refine ⟨[], by simp, List.Pairwise.nil, fun _ h => ?_, fun _ _ _ h => ?_⟩
        · cases h
        · cases h
      | cons q tail =>
        have hpw := List.pairwise_cons.mp hs
        have hpq : p < q := hpw.1 q (List.mem_cons_self ..)
        obtain ⟨vs', hlen', hsort', hprop', hhead'⟩ :=
          ih hpw.2 (fun x hx => hm x (List.mem_cons_of_mem p hx))
        have hmp := hm p (List.mem_cons_self ..)
        have hmq := hm q (List.mem_cons_of_mem p (List.mem_cons_self ..))
        obtain ⟨v, hpv, hvq, hSv, hv1, hvy⟩ :=
          bridge_fresh_s_landing b s y k p q hpq hmp.1 hmp.2.1 hmq.2.1 hmp.2.2 hmq.2.2
        refine ⟨v :: vs', ?_, ?_, ?_, ?_⟩
        · simp only [List.length_cons] at hlen' ⊢; omega
        · rw [List.pairwise_cons]
          refine ⟨fun w hw => ?_, hsort'⟩
          have hqw := hhead' q rfl w hw
          omega
        · intro w hw
          rcases List.mem_cons.mp hw with rfl | hw'
          · exact ⟨by omega, hSv, hv1, hvy⟩
          · exact hprop' w hw'
        · intro x hhd w hw
          simp only [List.head?, Option.some.injEq] at hhd
          subst hhd
          rcases List.mem_cons.mp hw with rfl | hw'
          · exact hpv
          · have hqw := hhead' q rfl w hw'
            omega
  obtain ⟨vs, hlen, hvs_sort, hvs_prop, _⟩ := hex_vs ps hsort hmem
  by_cases hps1 : ps.length ≤ 1
  · omega
  · have hpw_ne := pairwise_fresh_s_ne b s vs hvs_sort
      (fun v hv => ⟨(hvs_prop v hv).1, (hvs_prop v hv).2.1⟩)
    have hnd : (vs.map (fun v => (run b s v).value)).Nodup :=
      List.pairwise_map.mpr hpw_ne
    have hsub : ∀ x ∈ vs.map (fun v => (run b s v).value),
        x ∈ (List.range (y - 3)).map (· + 1) := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨v, hv_mem, rfl⟩ := hx
      have hp := hvs_prop v hv_mem
      rw [List.mem_map]
      refine ⟨(run b s v).value - 1, ?_, by omega⟩
      rw [List.mem_range]
      omega
    have hcard := nodup_length_le_of_subset_nat hnd hsub
    simp only [List.length_map, List.length_range] at hcard
    omega

/-- Late-clock strict height ascent for a fixed candidate `y : Nat` (`E-761`):
if `p < q`, `replaySign b s p = true`, `replayCand b s p = replayCand b s q = y`,
and `y ≤ (b + p + 1) + 6`, then `Fw p + 1 ≤ Fw q`. -/
theorem same_candidate_late_strict_ascent (b : Nat) (s : State) (y : Nat) (p q : Nat)
    (hpq : p < q)
    (hAp : replaySign b s p = true)
    (hcp : replayCand b s p = (y : Int)) (hcq : replayCand b s q = (y : Int))
    (hclk : (y : Int) ≤ ((b + p + 1 : Nat) : Int) + 6) :
    Fw (replaySign b s) p + 1 ≤ Fw (replaySign b s) q := by
  let f := replaySign b s
  have hfloor : ∀ t, p ≤ t → Fw f p - 1 ≤ Fw f t :=
    small_candidate_permanent_floor b s p hAp (by rw [hcp]; exact hclk)
  have hFw_p1 : Fw f (p + 1) = Fw f p + 1 := by
    have h := Fw_succ f p
    change Fw f (p + 1) = Fw f p + sign (replaySign b s p) at h
    rw [hAp] at h
    simp [sign] at h
    omega
  have hpot_ge2 :
      2 ≤ floorPotential f 0 (Fw f p - 2) q - floorPotential f 0 (Fw f p - 2) p := by
    have hw := floorPotential_diff_ge_of_witness f (Fw f p - 2)
      (p := p) (q := q) (u := p + 1) (by omega) (by omega)
      (fun i hi1 _ => by have := hfloor i (by omega); omega)
    rw [hFw_p1] at hw
    omega
  have hbr := candidate_area_bridge_identity b s p q
  change floorPotential f 0 (Fw f p - 2) q - floorPotential f 0 (Fw f p - 2) p =
    ((b + q + 1 : Nat) : Int) * (Fw f q - Fw f p) +
      replayCand b s p - replayCand b s q at hbr
  rw [hcp, hcq] at hbr
  apply Classical.byContradiction
  intro hle
  change ¬ Fw f p + 1 ≤ Fw f q at hle
  have hdiff : Fw f q - Fw f p ≤ 0 := by omega
  have hmul : ((b + q + 1 : Nat) : Int) * (Fw f q - Fw f p) ≤ ((b + q + 1 : Nat) : Int) * 0 :=
    Int.mul_le_mul_of_nonneg_left hdiff (by omega)
  omega

/-- Fixed original `Win` source finite-use capacity (`E-761` consumer):
for any `u : Nat`, every `Win (replaySign b s) u (p - u)` hit has
`replayCand b s p = value b s u` and `Fw p = Fw u + 1`. Consequently:
1. Any strictly sorted list `ps` of hits from source `u` satisfies
   `ps.length ≤ max 1 ((run b s u).value - 2)`.
2. At most ONE hit from source `u` can occur after `value b s u ≤ (b + p + 1) + 6`. -/
theorem original_win_source_finite_capacity (b : Nat) (s : State) (u : Nat) :
    (∀ ps : List Nat, ps.Pairwise (· < ·) →
      (∀ p ∈ ps, u ≤ p ∧ replaySign b s p = true ∧ Win (replaySign b s) u (p - u)) →
      ps.length ≤ max 1 ((run b s u).value - 2)) ∧
    (∀ p q : Nat, u ≤ p → p < q →
      replaySign b s p = true →
      Win (replaySign b s) u (p - u) → Win (replaySign b s) u (q - u) →
      value b s u ≤ ((b + p + 1 : Nat) : Int) + 6 → False) := by
  let f := replaySign b s
  have hwin_eq : ∀ p, u ≤ p → Win f u (p - u) →
      Fw f p = Fw f u + 1 ∧ replayCand b s p = value b s u := by
    intro p hup hw
    have hFp : Fw f p = Fw f u + 1 := by
      have h := hw.2.1
      rw [Nat.add_sub_cancel' hup] at h
      omega
    have hAr : Ar f u (p - u) = 0 := hw.2.2
    have hsp := area_split_at f 0 u p (Nat.zero_le u) hup
    rw [Nat.sub_zero, Nat.sub_zero] at hsp
    have h0 : Fw f 0 = 0 := rfl
    rw [h0, hAr] at hsp
    have hp_ab := replay_value_eq_abel_potential b s p
    have hu_ab := replay_value_eq_abel_potential b s u
    unfold floorPotential at hp_ab hu_ab
    simp only [Nat.sub_zero] at hp_ab hu_ab
    change value b s p = _ at hp_ab
    change value b s u = _ at hu_ab
    rw [h0, hFp] at hp_ab
    rw [h0] at hu_ab
    have hpu_cast : ((p - u : Nat) : Int) = (p : Int) - (u : Int) := by omega
    rw [hpu_cast] at hsp
    unfold replayCand
    push_cast at hp_ab hu_ab hsp ⊢
    refine ⟨hFp, ?_⟩
    grind
  constructor
  · intro ps hsort hmem
    refine same_candidate_same_height_fresh_wallet b s (run b s u).value (Fw f u + 1) ps hsort ?_
    intro p hp
    obtain ⟨hup, hAp, hw⟩ := hmem p hp
    obtain ⟨hFp, hcp⟩ := hwin_eq p hup hw
    exact ⟨hAp, hcp, hFp⟩
  · intro p q hup hpq hAp hwp hwq hclk
    obtain ⟨hFp, hcp⟩ := hwin_eq p hup hwp
    obtain ⟨hFq, hcq⟩ := hwin_eq q (by omega) hwq
    have hasc := same_candidate_late_strict_ascent b s (run b s u).value p q hpq hAp hcp hcq hclk
    change Fw f p + 1 ≤ Fw f q at hasc
    omega

/-! ## Part 4: Running-minimum positivity lower bound & finite-horizon band cardinality -/

/-- Running-minimum positivity bound (`E-761`): for EVERY `b, s, t`,
`-((s.value / (b + 1) : Nat) : Int) ≤ Fw (replaySign b s) t`. -/
theorem replay_fw_lower_bound (b : Nat) (s : State) (t : Nat) :
    -((s.value / (b + 1) : Nat) : Int) ≤ Fw (replaySign b s) t := by
  let f := replaySign b s
  have hex_min : ∀ n : Nat, ∃ r, r ≤ n ∧ ∀ i, i ≤ n → Fw f r ≤ Fw f i := by
    intro n
    induction n with
    | zero =>
      refine ⟨0, Nat.le_refl 0, fun i hi => ?_⟩
      have hi0 : i = 0 := by omega
      rw [hi0]
      exact Int.le_refl _
    | succ n ih =>
      obtain ⟨r, hrn, hrmin⟩ := ih
      by_cases hcmp : Fw f (n + 1) ≤ Fw f r
      · refine ⟨n + 1, Nat.le_refl _, fun i hi => ?_⟩
        by_cases hi' : i ≤ n
        · have := hrmin i hi'; omega
        · have heq : i = n + 1 := by omega
          rw [heq]; exact Int.le_refl _
      · refine ⟨r, by omega, fun i hi => ?_⟩
        by_cases hi' : i ≤ n
        · exact hrmin i hi'
        · have heq : i = n + 1 := by omega
          rw [heq]; omega
  obtain ⟨r, hrt, hrmin⟩ := hex_min t
  have hpot_nonneg : 0 ≤ floorPotential f 0 (Fw f r - 1) r := by
    have h0 : floorPotential f 0 (Fw f r - 1) 0 = 0 := by simp [floorPotential, Ar]
    have hdiff := floorPotential_diff_nonneg_of_ge f (Fw f r - 1) (p := 0) (q := r)
      (Nat.zero_le r) (fun i _ hi2 => by have := hrmin i (by omega); omega)
    omega
  have hab := replay_value_eq_abel_potential b s r
  have hv_nonneg : 0 ≤ value b s r := by
    change (0 : Int) ≤ ((run b s r).value : Int)
    omega
  have hlin : (0 : Int) ≤ (s.value : Int) + ((b + 1 : Nat) : Int) * Fw f r := by
    change value b s r =
      (s.value : Int) + ((b + 1 : Nat) : Int) * Fw f r - floorPotential f 0 (Fw f r - 1) r at hab
    omega
  have hle_t : Fw f r ≤ Fw f t := hrmin t (Nat.le_refl t)
  change -((s.value / (b + 1) : Nat) : Int) ≤ Fw f t
  by_cases hneg : Fw f r < 0
  · let d : Nat := (-Fw f r).toNat
    have hd_eq : (d : Int) = -Fw f r := Int.toNat_of_nonneg (by omega)
    have hmul_int : ((b + 1 : Nat) : Int) * (d : Int) ≤ (s.value : Int) := by
      rw [hd_eq, Int.mul_neg]
      omega
    have hmul_nat : (b + 1) * d ≤ s.value := by
      have hcast : (((b + 1) * d : Nat) : Int) ≤ (s.value : Int) := by
        simpa [Int.natCast_mul] using hmul_int
      exact Int.ofNat_le.mp hcast
    have hd_le_div : d ≤ s.value / (b + 1) := by
      rw [Nat.le_div_iff_mul_le (Nat.succ_pos b)]
      simpa [Nat.mul_comm] using hmul_nat
    omega
  · have hnonneg_div : (0 : Int) ≤ ((s.value / (b + 1) : Nat) : Int) := Int.natCast_nonneg _
    omega

/-- Finite-horizon candidate-band cardinality bound (`E-761` endpoint consumer):
for any horizon `Q` and band `Y : Nat`, the number of selected `A`-events `p < Q`
with `Y ≤ b + p + 1` and `0 ≤ replayCand b s p ≤ Y` is at most
`(Y / 3 + 1) * (Fw (replaySign b s) Q + s.value / (b + 1) + 2)`. -/
theorem candidate_band_finite_horizon_count_le (Y b : Nat) (s : State) (Q : Nat) :
    ((bandSelectedClocks Y b s Q).length : Int) ≤
      ((Y / 3 + 1 : Nat) : Int) *
        (Fw (replaySign b s) Q + ((s.value / (b + 1) : Nat) : Int) + 2) := by
  let sel := bandSelectedClocks Y b s Q
  change (sel.length : Int) ≤ _
  let K : Nat := Y / 3 + 1
  let f := replaySign b s
  have hsort : sel.Pairwise (· < ·) := List.Pairwise.filter _ List.pairwise_lt_range
  have hmem_sel : ∀ p ∈ sel,
      p < Q ∧ replaySign b s p = true ∧ Y ≤ b + p + 1 ∧
        0 ≤ replayCand b s p ∧ replayCand b s p ≤ (Y : Int) := by
    intro p hp
    simp only [sel, bandSelectedClocks, List.mem_filter, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq] at hp
    exact ⟨hp.1, hp.2.1.1.1, hp.2.1.1.2, hp.2.1.2, hp.2.2⟩
  let lo : Int := -(K : Int) * ((s.value / (b + 1) : Nat) : Int) - ((Y / 3 : Nat) : Int)
  let hi : Int := (K : Int) * (Fw f Q + 1)
  have hbounds : ∀ p ∈ sel, lo ≤ bandRank Y b s p ∧ bandRank Y b s p ≤ hi := by
    intro p hp
    obtain ⟨hpQ, hAp, hclk, hcp0, hcpY⟩ := hmem_sel p hp
    have hfl_Q : Fw f p - 1 ≤ Fw f Q :=
      small_candidate_permanent_floor b s p hAp (by omega) Q (by omega)
    have hlb_p : -((s.value / (b + 1) : Nat) : Int) ≤ Fw f p :=
      replay_fw_lower_bound b s p
    unfold bandRank
    have hmul_lo : (K : Int) * (-((s.value / (b + 1) : Nat) : Int)) ≤ (K : Int) * Fw f p :=
      Int.mul_le_mul_of_nonneg_left hlb_p (by omega)
    rw [Int.mul_neg] at hmul_lo
    have hmul_hi : (K : Int) * Fw f p ≤ (K : Int) * (Fw f Q + 1) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    constructor
    · change -(K : Int) * ((s.value / (b + 1) : Nat) : Int) - ((Y / 3 : Nat) : Int) ≤
        (K : Int) * Fw f p - replayCand b s p / 3
      rw [Int.neg_mul]
      omega
    · change (K : Int) * Fw f p - replayCand b s p / 3 ≤ (K : Int) * (Fw f Q + 1)
      omega
  by_cases hnil : sel = []
  · rw [hnil]
    have hlb_Q : -((s.value / (b + 1) : Nat) : Int) ≤ Fw f Q := replay_fw_lower_bound b s Q
    have hnonneg : (0 : Int) ≤ (K : Int) * (Fw f Q + ((s.value / (b + 1) : Nat) : Int) + 2) :=
      Int.mul_nonneg (by omega) (by omega)
    simpa [K, f] using hnonneg
  · have hstep_chain : ∀ (p : Nat) (rest : List Nat),
        (p :: rest).Pairwise (· < ·) →
        (∀ x ∈ p :: rest, x ∈ sel) →
        bandRank Y b s p + (rest.length : Int) ≤ hi := by
      intro p rest
      induction rest generalizing p with
      | nil =>
        intro _ hsub
        have hb := (hbounds p (hsub p (List.mem_cons_self ..))).2
        simp; omega
      | cons q tail ih =>
        intro hpw hsub
        have hpw_cons := List.pairwise_cons.mp hpw
        have hpq : p < q := hpw_cons.1 q (List.mem_cons_self ..)
        have hmp := hmem_sel p (hsub p (List.mem_cons_self ..))
        have hmq := hmem_sel q (hsub q (List.mem_cons_of_mem p (List.mem_cons_self ..)))
        have hmono := (candidate_band_rank_strict_mono Y b s p q hpq hmp.2.1 hmp.2.2.1
          hmp.2.2.2.1 hmp.2.2.2.2 hmq.2.2.2.1 hmq.2.2.2.2).2.2
        have hih := ih q hpw_cons.2 (fun x hx => hsub x (List.mem_cons_of_mem p hx))
        simp only [List.length_cons]
        omega
    cases hsel : sel with
    | nil => exact (hnil hsel).elim
    | cons p rest =>
      have hpw' : (p :: rest).Pairwise (· < ·) := hsel ▸ hsort
      have hsub' : ∀ x ∈ p :: rest, x ∈ sel := fun x hx => hsel ▸ hx
      have hch := hstep_chain p rest hpw' hsub'
      have hlo_p := (hbounds p (hsel ▸ List.mem_cons_self ..)).1
      simp only [List.length_cons]
      have hwidth : hi - lo + 1 =
          (K : Int) * (Fw f Q + ((s.value / (b + 1) : Nat) : Int) + 2) := by
        dsimp only [lo, hi, K]
        push_cast
        grind
      change ((rest.length + 1 : Nat) : Int) ≤
        (K : Int) * (Fw f Q + ((s.value / (b + 1) : Nat) : Int) + 2)
      omega

/-- Unconditional specialization of the candidate-band monotone rank, all-time fresh-value
wallet, and finite-horizon cardinality bound to the canonical clock-0 Recamán orbit
`Recaman.Basic.a` (`b = 0, s = initial`, where `initial.value = 0`). -/
theorem canonical_orbit_candidate_band_bounds (Y Q : Nat) :
    (∀ p q : Nat, p < q → canonicalOrbitSign p = true → Y ≤ p + 1 →
      0 ≤ (a p : Int) - ((p + 1 : Nat) : Int) →
      (a p : Int) - ((p + 1 : Nat) : Int) ≤ (Y : Int) →
      0 ≤ (a q : Int) - ((q + 1 : Nat) : Int) →
      (a q : Int) - ((q + 1 : Nat) : Int) ≤ (Y : Int) →
      Fw canonicalOrbitSign p ≤ Fw canonicalOrbitSign q ∧
        bandRank Y 0 initial p + 1 ≤ bandRank Y 0 initial q) ∧
    (∀ y : Nat, ∀ k : Int, ∀ ps : List Nat, ps.Pairwise (· < ·) →
      (∀ p ∈ ps, canonicalOrbitSign p = true ∧
        (a p : Int) - ((p + 1 : Nat) : Int) = (y : Int) ∧ Fw canonicalOrbitSign p = k) →
      ps.length ≤ max 1 (y - 2)) ∧
    (((List.range Q).filter (fun p =>
        canonicalOrbitSign p && decide (Y ≤ p + 1) &&
          decide (0 ≤ (a p : Int) - ((p + 1 : Nat) : Int)) &&
          decide ((a p : Int) - ((p + 1 : Nat) : Int) ≤ (Y : Int)))).length : Int) ≤
      ((Y / 3 + 1 : Nat) : Int) * (Fw canonicalOrbitSign Q + 2) := by
  have hrun_eq : ∀ t, run 0 initial t = stateAt t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      change step (0 + t + 1) (run 0 initial t) = step (t + 1) (stateAt t)
      rw [Nat.zero_add, ih]
  have hcand_eq : ∀ t, replayCand 0 initial t = (a t : Int) - ((t + 1 : Nat) : Int) := by
    intro t
    unfold replayCand value a
    rw [hrun_eq t, Nat.zero_add]
  refine ⟨?_, ?_, ?_⟩
  · intro p q hpq hAp hclk hcp0 hcpY hcq0 hcqY
    have h := candidate_band_rank_strict_mono Y 0 initial p q hpq hAp (by omega)
      (by rw [hcand_eq]; exact hcp0) (by rw [hcand_eq]; exact hcpY)
      (by rw [hcand_eq]; exact hcq0) (by rw [hcand_eq]; exact hcqY)
    exact ⟨h.1, h.2.2⟩
  · intro y k ps hsort hmem
    refine same_candidate_same_height_fresh_wallet 0 initial y k ps hsort ?_
    intro p hp
    obtain ⟨hAp, hcp, hFp⟩ := hmem p hp
    exact ⟨hAp, by rw [hcand_eq]; exact hcp, hFp⟩
  · have h := candidate_band_finite_horizon_count_le Y 0 initial Q
    unfold bandSelectedClocks at h
    have hinit : initial.value / (0 + 1) = 0 := rfl
    simp only [Nat.zero_add, hcand_eq, hinit, Int.ofNat_zero, Int.add_zero] at h
    exact h

end Recaman.NumericCandidateRankPotential
