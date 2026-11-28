import Recaman.SeededReplay
import Recaman.FloorSupplyPotential
import Recaman.CrossBlockReuseUnbounded

namespace Recaman.CoherentGreedyFreshness

open Recaman Recaman.SeededReplay Recaman.FloorSupplyPotential
open Recaman.BlockSuffixPositivity Recaman.SingleWindowEquality
open Recaman.CapacityEqualityInduction Recaman.CrossBlockReuseUnbounded
open Recaman.LineCapacityPeriodic Recaman.LeadingRunSupply
open Recaman.ShortPeriodicSupply (sign)

/-! # Chronological `S`-freshness (`E-759`) on greedy replays and periodic obstruction (`E-798`)

Connects arbitrary coherent finite-state greedy continuations `SeededReplay.run b s`
(and in particular the canonical clock-0 Recamán orbit `Recaman.Basic.a` at `b = 0, s = initial`)
to the sign-word potential `floorPotential f 0 (r - 1)` via the exact Abel-summation identity:

  `value b s t = s.value + (b + 1) * Fw f t - floorPotential f 0 (Fw f t - 1) t`.

From this identity we prove unconditionally (with zero unproven `Prop` hypotheses):
1. Every coherent finite-state greedy replay (`s.value ∈ s.seen`), and in particular the
   canonical Recamán orbit `Recaman.Basic.a`, satisfies both `TypeIFresh` (no `S`-landing
   repeats a prior output key `(r, Φ_r)`) and `TypeIIFresh` (no `S`-landing repeats a prior
   rejected `A`-candidate key `(r, Φ_r)`).
2. **Periodic `S`-freshness pigeonhole law**: for every balanced word `V` (`mass V = 0`)
   repeated `R ≥ 1` times inside any `TypeIFresh` sign sequence (hence inside every coherent
   greedy replay and inside `Recaman.Basic.a`) at any offset `s` and relative height `r : Int`,
     `R * wordSLandings V r ≤ wordPotSpan V r + (R - 1) * (wordPotDrift V r).natAbs + 1`.
3. **Zero-drift repeat obstruction**: any balanced cycle `V` with `wordPotDrift V r = 0` and
   `1 ≤ wordSLandings V r` (including every `E-786` cascade cycle at height `H - 1`) cannot
   repeat more than `wordPotSpan V r + 1` consecutive times anywhere in any coherent greedy
   replay or in `Recaman.Basic.a`.
4. **Unit-drift `Δ ≥ 2` necessity**: any balanced cycle `V` with `|wordPotDrift V r| = 1`
   repeated at least `wordPotSpan V r + 2` consecutive times in any coherent greedy replay
   (or in `Recaman.Basic.a`) must satisfy `wordSLandings V r ≤ 1`, forcing unit-drift coherent
   recursive towers to skip height `h_k - 1` (`Δ ≥ 2`, making the `Δ = 2` cascade of base
   `√(7/3) ≈ 1.527525` optimal among unit-drift coherent towers).
-/

/-! ## Sign sequence of a greedy replay and chronological freshness predicates -/

/-- Sign sequence of a seeded greedy replay from `(b, s)`: `true` for addition (`A`),
`false` for subtraction (`S`). -/
def replaySign (b : Nat) (s : State) (t : Nat) : Bool :=
  decide (¬ CanSubtract (b + t + 1) (run b s t))

/-- Sign sequence of the canonical clock-0 Recamán orbit `Recaman.Basic.a`. -/
def canonicalOrbitSign (t : Nat) : Bool :=
  replaySign 0 initial t

/-- Type-I chronological `S`-freshness (`E-759 (I)`): no `S`-step landing at `(r, Φ_r)`
in `[0, N)` collides with any earlier visit to height `r`. -/
def TypeIFresh (f : Nat → Bool) (N : Nat) : Prop :=
  ∀ t, t < N → f t = false →
    ∀ u, u ≤ t → Fw f u = Fw f (t + 1) →
      floorPotential f 0 (Fw f (t + 1) - 1) (t + 1) ≠
        floorPotential f 0 (Fw f (t + 1) - 1) u

/-- Type-II chronological `S`-freshness (`E-759 (II)`): no `S`-step landing at `(r, Φ_r)`
in `[0, N)` collides with any earlier `A`-step subtraction candidate at height `r`. -/
def TypeIIFresh (f : Nat → Bool) (N : Nat) : Prop :=
  ∀ t, t < N → f t = false →
    ∀ u, u < t → f u = true → Fw f u = Fw f (t + 1) + 1 →
      floorPotential f 0 (Fw f (t + 1) - 1) (t + 1) ≠
        floorPotential f 0 (Fw f (t + 1) - 1) u

/-! ## Exact Abel-summation bridge from `SeededReplay.value` to `floorPotential` -/

private theorem replay_step_value (b : Nat) (s : State) (t : Nat) :
    value b s (t + 1) =
      value b s t + sign (replaySign b s t) * ((b + t + 1 : Nat) : Int) := by
  unfold value replaySign
  change ((step (b + t + 1) (run b s t)).value : Int) = _
  simp only [step, nextValue]
  by_cases hc : CanSubtract (b + t + 1) (run b s t)
  · have hlt : b + t + 1 < (run b s t).value := hc.1
    rw [if_pos hc]
    have hdec : decide (¬ CanSubtract (b + t + 1) (run b s t)) = false := by simp [hc]
    rw [hdec]
    simp [sign]
    omega
  · rw [if_neg hc]
    have hdec : decide (¬ CanSubtract (b + t + 1) (run b s t)) = true := by simp [hc]
    rw [hdec]
    simp [sign]

/-- Exact Abel-summation identity connecting arbitrary seeded greedy replay values `value b s t`
to `Fw` and `floorPotential` at origin `0`. -/
theorem replay_value_eq_abel_potential (b : Nat) (s : State) :
    ∀ t, value b s t =
      (s.value : Int) + ((b + 1 : Nat) : Int) * Fw (replaySign b s) t -
        floorPotential (replaySign b s) 0 (Fw (replaySign b s) t - 1) t
  | 0 => by
    simp [value, run, Fw, floorPotential, Ar]
  | t + 1 => by
    have ih := replay_value_eq_abel_potential b s t
    have hstep := replay_step_value b s t
    have hFw : Fw (replaySign b s) (t + 1) = Fw (replaySign b s) t + sign (replaySign b s t) := by
      rw [Fw_succ]
    have hAr : Ar (replaySign b s) 0 (t + 1) = Ar (replaySign b s) 0 t + Fw (replaySign b s) (t + 1) := by
      have := Ar_succ (replaySign b s) 0 t
      have h0 : Fw (replaySign b s) 0 = 0 := rfl
      simpa [h0] using this
    unfold floorPotential at ih ⊢
    simp only [Nat.sub_zero] at ih ⊢
    have h0 : Fw (replaySign b s) 0 = 0 := rfl
    rw [h0] at ih ⊢
    rw [hstep, ih, hAr, hFw]
    push_cast
    grind

private theorem replay_value_at_height (b : Nat) (s : State) (t : Nat) (r : Int)
    (hF : Fw (replaySign b s) t = r) :
    value b s t =
      (s.value : Int) + ((b + 1 : Nat) : Int) * r - floorPotential (replaySign b s) 0 (r - 1) t := by
  have h := replay_value_eq_abel_potential b s t
  rwa [hF] at h

private theorem replay_cand_at_height (b : Nat) (s : State) (u : Nat) (r : Int)
    (hF : Fw (replaySign b s) u = r + 1) :
    value b s u - ((b + u + 1 : Nat) : Int) =
      (s.value : Int) + ((b + 1 : Nat) : Int) * r - floorPotential (replaySign b s) 0 (r - 1) u := by
  have h := replay_value_at_height b s u (r + 1) hF
  rw [h]
  unfold floorPotential
  simp only [Nat.sub_zero, Fw]
  push_cast
  grind

/-- Every coherent finite-state greedy replay (`s.value ∈ s.seen`) satisfies Type-I
chronological `S`-freshness (`E-759 (I)`) for every horizon `N : Nat`. -/
theorem seeded_replay_typeIFresh (b : Nat) (s : State) (hs : s.value ∈ s.seen) (N : Nat) :
    TypeIFresh (replaySign b s) N := by
  intro t _ hft u hut hFu hpeq
  have hc : CanSubtract (b + t + 1) (run b s t) := by
    unfold replaySign at hft
    by_cases h : CanSubtract (b + t + 1) (run b s t)
    · exact h
    · simp [h] at hft
  have hv1 := replay_value_at_height b s (t + 1) (Fw (replaySign b s) (t + 1)) rfl
  have hvu := replay_value_at_height b s u (Fw (replaySign b s) (t + 1)) hFu
  have hveq : value b s (t + 1) = value b s u := by omega
  have hseen_u : Seen b s t (value b s u) := seen_mono hut (seen_value hs u)
  have hstep : value b s (t + 1) = value b s t - ((b + t + 1 : Nat) : Int) := by
    have hst := replay_step_value b s t
    rw [hft] at hst
    simp [sign] at hst
    omega
  have hseen_sub : Seen b s t (value b s t - ((b + t + 1 : Nat) : Int)) := by
    rw [← hstep, hveq]
    exact hseen_u
  obtain ⟨z, hz_mem, hz_eq⟩ := hseen_sub
  have hlt : b + t + 1 < (run b s t).value := hc.1
  have hz_nat : (run b s t).value - (b + t + 1) = z := by
    change (z : Int) = ((run b s t).value : Int) - ((b + t + 1 : Nat) : Int) at hz_eq
    omega
  exact hc.2 (hz_nat ▸ hz_mem)

/-- Every finite-state greedy replay `(b, s)` satisfies Type-II chronological `S`-freshness
(`E-759 (II)`) for every horizon `N : Nat` (even without assuming `s.value ∈ s.seen`). -/
theorem seeded_replay_typeIIFresh (b : Nat) (s : State) (N : Nat) :
    TypeIIFresh (replaySign b s) N := by
  intro t _ hft u hut hfu hFu hpeq
  have hct : CanSubtract (b + t + 1) (run b s t) := by
    unfold replaySign at hft
    by_cases h : CanSubtract (b + t + 1) (run b s t)
    · exact h
    · simp [h] at hft
  have hncu : ¬ CanSubtract (b + u + 1) (run b s u) := by
    unfold replaySign at hfu
    by_cases h : CanSubtract (b + u + 1) (run b s u)
    · simp [h] at hfu
    · exact h
  have hv1 := replay_value_at_height b s (t + 1) (Fw (replaySign b s) (t + 1)) rfl
  have hcu := replay_cand_at_height b s u (Fw (replaySign b s) (t + 1)) hFu
  have hveq : value b s (t + 1) = value b s u - ((b + u + 1 : Nat) : Int) := by omega
  have hstep : value b s (t + 1) = value b s t - ((b + t + 1 : Nat) : Int) := by
    have hst := replay_step_value b s t
    rw [hft] at hst
    simp [sign] at hst
    omega
  have hpos_t : 0 < value b s (t + 1) := by
    have hlt : b + t + 1 < (run b s t).value := hct.1
    change value b s (t + 1) = ((run b s t).value : Int) - ((b + t + 1 : Nat) : Int) at hstep
    omega
  have hlt_u : b + u + 1 < (run b s u).value := by
    change value b s (t + 1) = ((run b s u).value : Int) - ((b + u + 1 : Nat) : Int) at hveq
    omega
  have hmem_u : (run b s u).value - (b + u + 1) ∈ (run b s u).seen := by
    by_cases hm : (run b s u).value - (b + u + 1) ∈ (run b s u).seen
    · exact hm
    · exact (hncu ⟨hlt_u, hm⟩).elim
  have hseen_u : Seen b s u (value b s u - ((b + u + 1 : Nat) : Int)) := by
    refine ⟨(run b s u).value - (b + u + 1), hmem_u, ?_⟩
    change (((run b s u).value - (b + u + 1) : Nat) : Int) =
      ((run b s u).value : Int) - ((b + u + 1 : Nat) : Int)
    omega
  have hseen_t : Seen b s t (value b s t - ((b + t + 1 : Nat) : Int)) := by
    rw [← hstep, hveq]
    exact seen_mono (Nat.le_of_lt hut) hseen_u
  obtain ⟨z, hz_mem, hz_eq⟩ := hseen_t
  have hlt : b + t + 1 < (run b s t).value := hct.1
  have hz_nat : (run b s t).value - (b + t + 1) = z := by
    change (z : Int) = ((run b s t).value : Int) - ((b + t + 1 : Nat) : Int) at hz_eq
    omega
  exact hct.2 (hz_nat ▸ hz_mem)

private theorem run_zero_initial_eq_stateAt : ∀ t, run 0 initial t = stateAt t
  | 0 => rfl
  | t + 1 => by
    simp only [run, stateAt, Nat.zero_add, run_zero_initial_eq_stateAt t]

/-- The canonical clock-0 Recamán orbit `Recaman.Basic.a` unconditionally satisfies both
`TypeIFresh` and `TypeIIFresh` (`E-759 (I)/(II)`) at every horizon `N : Nat`, together with
the exact Abel potential relation `a t = Fw t - floorPotential 0 (Fw t - 1) t`. -/
theorem canonical_orbit_greedyFresh (N : Nat) :
    TypeIFresh canonicalOrbitSign N ∧ TypeIIFresh canonicalOrbitSign N ∧
      ∀ t, (a t : Int) = Fw canonicalOrbitSign t -
        floorPotential canonicalOrbitSign 0 (Fw canonicalOrbitSign t - 1) t := by
  have hs0 : initial.value ∈ initial.seen := by simp [initial]
  refine ⟨seeded_replay_typeIFresh 0 initial hs0 N,
    seeded_replay_typeIIFresh 0 initial N, ?_⟩
  intro t
  have hab := replay_value_eq_abel_potential 0 initial t
  have hrun : value 0 initial t = (a t : Int) := by
    unfold value a
    rw [run_zero_initial_eq_stateAt t]
  rw [hrun] at hab
  simp only [initial_value, Nat.zero_add] at hab
  change (a t : Int) = Fw (replaySign 0 initial) t -
    floorPotential (replaySign 0 initial) 0 (Fw (replaySign 0 initial) t - 1) t
  omega

/-! ## Word-level relative height, potential drift, span, and `S`-landing counts -/

/-- Relative walk height after `j` steps of word `V`. -/
def wordHeight (V : List Bool) (j : Nat) : Int :=
  mass (V.take j)

/-- Relative potential `Φ_r` after `j` steps of word `V`. -/
def wordRelPot (V : List Bool) (r : Int) (j : Nat) : Int :=
  areaW (V.take j) - (j : Int) * r

/-- Net drift `ΔΦ_r(V)` of one full copy of `V` at relative height `r`. -/
def wordPotDrift (V : List Bool) (r : Int) : Int :=
  wordRelPot V r V.length

/-- Minimum relative potential of `V` along `j ∈ {0, ..., k}` at relative height `r`. -/
def wordPotMinUpTo (V : List Bool) (r : Int) : Nat → Int
  | 0 => 0
  | k + 1 => min (wordPotMinUpTo V r k) (wordRelPot V r (k + 1))

/-- Maximum relative potential of `V` along `j ∈ {0, ..., k}` at relative height `r`. -/
def wordPotMaxUpTo (V : List Bool) (r : Int) : Nat → Int
  | 0 => 0
  | k + 1 => max (wordPotMaxUpTo V r k) (wordRelPot V r (k + 1))

/-- Total relative potential span `max_{0 ≤ j ≤ |V|} Φ_r(j) - min_{0 ≤ j ≤ |V|} Φ_r(j)`. -/
def wordPotSpan (V : List Bool) (r : Int) : Nat :=
  (wordPotMaxUpTo V r V.length - wordPotMinUpTo V r V.length).toNat

/-- Indices `j < |V|` where `V[j] = false` (`S`-step) lands at relative height `r`. -/
def wordSLandingIndices (V : List Bool) (r : Int) : List Nat :=
  (List.range V.length).filter (fun j => decide (V[j]! = false ∧ wordHeight V (j + 1) = r))

/-- Number of `S`-landings of word `V` at relative height `r`. -/
def wordSLandings (V : List Bool) (r : Int) : Nat :=
  (wordSLandingIndices V r).length

private theorem wordPotMinUpTo_le (V : List Bool) (r : Int) :
    ∀ k j, j ≤ k → wordPotMinUpTo V r k ≤ wordRelPot V r j
  | 0, j, hj => by
    have : j = 0 := by omega
    subst this
    simp [wordPotMinUpTo, wordRelPot, areaW]
  | k + 1, j, hj => by
    simp only [wordPotMinUpTo]
    by_cases hjk : j ≤ k
    · exact Int.le_trans (Int.min_le_left _ _) (wordPotMinUpTo_le V r k j hjk)
    · have : j = k + 1 := by omega
      subst this
      exact Int.min_le_right _ _

private theorem wordPotMaxUpTo_ge (V : List Bool) (r : Int) :
    ∀ k j, j ≤ k → wordRelPot V r j ≤ wordPotMaxUpTo V r k
  | 0, j, hj => by
    have : j = 0 := by omega
    subst this
    simp [wordPotMaxUpTo, wordRelPot, areaW]
  | k + 1, j, hj => by
    simp only [wordPotMaxUpTo]
    by_cases hjk : j ≤ k
    · exact Int.le_trans (wordPotMaxUpTo_ge V r k j hjk) (Int.le_max_left _ _)
    · have : j = k + 1 := by omega
      subst this
      exact Int.le_max_right _ _

private theorem wordPotMin_le_max (V : List Bool) (r : Int) :
    wordPotMinUpTo V r V.length ≤ wordPotMaxUpTo V r V.length :=
  Int.le_trans (wordPotMinUpTo_le V r V.length 0 (Nat.zero_le _))
    (wordPotMaxUpTo_ge V r V.length 0 (Nat.zero_le _))

private theorem repeatWord_length (R : Nat) (V : List Bool) :
    (repeatWord R V).length = R * V.length := by
  induction R with
  | zero => simp [repeatWord]
  | succ R ih =>
    simp only [repeatWord, List.length_append, ih]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

private theorem seg_eq_of_matchesAt (f : Nat → Bool) (s : Nat) (w : List Bool)
    (hm : MatchesAt f s w) :
    ∀ k, k ≤ w.length → seg f s k = w.take k
  | 0, _ => by simp [seg]
  | k + 1, hk => by
    have ih := seg_eq_of_matchesAt f s w hm k (by omega)
    rw [seg_succ, ih, hm k (by omega)]
    have htake : w.take (k + 1) = w.take k ++ [w[k]!] := by
      have hlt : k < w.length := by omega
      rw [List.take_succ_eq_append_getElem hlt]
      simp [hlt]
    exact htake.symm

private theorem matchesAt_repeat_copy (f : Nat → Bool) (s : Nat) (V : List Bool) :
    ∀ R c, c < R → MatchesAt f s (repeatWord R V) → MatchesAt f (s + c * V.length) V
  | 0, _, hc, _ => by omega
  | R + 1, 0, _, hm => by
    intro i hi
    have h1 := hm i (by rw [repeatWord_length]; have : 1 * V.length ≤ (R + 1) * V.length := Nat.mul_le_mul_right _ (by omega); omega)
    simp only [Nat.zero_mul, Nat.add_zero]
    rw [h1]
    simp [repeatWord, List.getElem!_eq_getElem?_getD, List.getElem?_append_left hi]
  | R + 1, c + 1, hc, hm => by
    have htail : MatchesAt f (s + V.length) (repeatWord R V) := by
      intro i hi
      have h1 := hm (V.length + i) (by rw [repeatWord_length] at hi ⊢; rw [Nat.add_mul, Nat.one_mul]; omega)
      rw [← Nat.add_assoc] at h1
      rw [h1]
      simp [repeatWord, List.getElem!_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right V.length i)]
    have ih := matchesAt_repeat_copy f (s + V.length) V R c (by omega) htail
    intro i hi
    have h1 := ih i hi
    have hidx : s + V.length + c * V.length + i = s + (c + 1) * V.length + i := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    rwa [hidx] at h1

private theorem fw_and_ar_copy (f : Nat → Bool) (s : Nat) (V : List Bool) (hbal : mass V = 0)
    (R : Nat) (hm : MatchesAt f s (repeatWord R V)) :
    ∀ c, c ≤ R →
      Fw f (s + c * V.length) = Fw f s ∧
      Ar f s (c * V.length) = (c : Int) * areaW V
  | 0, _ => by simp [Ar]
  | c + 1, hc => by
    have ih := fw_and_ar_copy f s V hbal R hm c (by omega)
    have hm_c := matchesAt_repeat_copy f s V R c (by omega) hm
    have hseg := seg_eq_of_matchesAt f (s + c * V.length) V hm_c V.length (Nat.le_refl _)
    rw [List.take_length] at hseg
    have hFw_step : Fw f (s + (c + 1) * V.length) = Fw f (s + c * V.length) + mass V := by
      have h1 := seg_mass f (s + c * V.length) V.length
      rw [hseg] at h1
      rw [show s + (c + 1) * V.length = s + c * V.length + V.length by rw [Nat.add_mul, Nat.one_mul]; omega]
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
    grind

private theorem periodic_height_and_pot (f : Nat → Bool) (s : Nat) (V : List Bool)
    (hbal : mass V = 0) (R : Nat) (hm : MatchesAt f s (repeatWord R V))
    (c j : Nat) (hc : c < R) (hj : j ≤ V.length) (r : Int) :
    Fw f (s + c * V.length + j) = Fw f s + wordHeight V j ∧
    floorPotential f 0 (Fw f s + r - 1) (s + c * V.length + j) =
      floorPotential f 0 (Fw f s + r - 1) s +
        (c : Int) * wordPotDrift V r + wordRelPot V r j := by
  have hcopy := fw_and_ar_copy f s V hbal R hm c (Nat.le_of_lt hc)
  have hm_c := matchesAt_repeat_copy f s V R c hc hm
  have hseg := seg_eq_of_matchesAt f (s + c * V.length) V hm_c j hj
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
  push_cast
  grind

/-! ## List helper lemmas for the periodic `S`-freshness pigeonhole bound -/

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

private theorem prod_flatMap_length {α β : Type} (L₁ : List α) (L₂ : List β) :
    (L₁.flatMap (fun a => L₂.map (fun b => (a, b)))).length = L₁.length * L₂.length := by
  induction L₁ with
  | nil => simp
  | cons a t ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, ih, List.length_cons]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

private theorem prod_flatMap_nodup {α β : Type} (L₁ : List α) (L₂ : List β)
    (h₁ : L₁.Nodup) (h₂ : L₂.Nodup) :
    (L₁.flatMap (fun a => L₂.map (fun b => (a, b)))).Nodup := by
  induction L₁ with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at h₁
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨nodup_map_of_inj L₂ (fun b => (a, b)) h₂ (fun _ _ _ _ h => by cases h; rfl),
      ih h₁.2, ?_⟩
    intro x hx y hy hxy
    rw [List.mem_map] at hx
    rw [List.mem_flatMap] at hy
    obtain ⟨b₁, _, rfl⟩ := hx
    obtain ⟨a₂, ha₂, hy'⟩ := hy
    rw [List.mem_map] at hy'
    obtain ⟨b₂, _, rfl⟩ := hy'
    have h1 := congrArg Prod.fst hxy
    dsimp at h1
    exact h₁.1 (h1 ▸ ha₂)

/-! ## Core arbitrary-depth periodic `S`-freshness pigeonhole theorem and obstructions -/

/-- Arbitrary-depth periodic `S`-freshness pigeonhole law (`E-759 (I)`):
for every balanced word `V` (`mass V = 0`) repeated `R ≥ 1` times starting at `s` inside
any `TypeIFresh` sign sequence `f`, and every relative height `r : Int`,
  `R * wordSLandings V r ≤ wordPotSpan V r + (R - 1) * (wordPotDrift V r).natAbs + 1`. -/
theorem typeIFresh_periodic_s_count_le_drift (f : Nat → Bool) (s R : Nat) (V : List Bool) (r : Int)
    (hbal : mass V = 0) (hR : 1 ≤ R)
    (hm : MatchesAt f s (repeatWord R V))
    (hfresh : TypeIFresh f (s + R * V.length)) :
    R * wordSLandings V r ≤ wordPotSpan V r + (R - 1) * (wordPotDrift V r).natAbs + 1 := by
  let L := V.length
  let rAbs := Fw f s + r
  let p0 := floorPotential f 0 (rAbs - 1) s
  let d := wordPotDrift V r
  let lo : Int := p0 + wordPotMinUpTo V r L - (((R - 1) * d.natAbs : Nat) : Int)
  let W : Nat := wordPotSpan V r + (R - 1) * d.natAbs + 1
  let dom : List (Nat × Nat) :=
    (List.range R).flatMap (fun c => (wordSLandingIndices V r).map (fun j => (c, j)))
  let phi : Nat × Nat → Int :=
    fun cj => floorPotential f 0 (rAbs - 1) (s + cj.1 * L + cj.2 + 1)
  let target : List Int :=
    if 0 ≤ d then
      (List.range W).map (fun k : Nat => p0 + wordPotMinUpTo V r L + (k : Int))
    else
      (List.range W).map (fun k : Nat => lo + (k : Int))
  have hdom_nodup : dom.Nodup :=
    prod_flatMap_nodup (List.range R) (wordSLandingIndices V r)
      (List.nodup_range (n := R)) ((List.nodup_range (n := L)).filter _)
  have hdom_mem : ∀ cj, cj ∈ dom →
      cj.1 < R ∧ cj.2 < L ∧ V[cj.2]! = false ∧ wordHeight V (cj.2 + 1) = r := by
    intro cj hmem
    rw [List.mem_flatMap] at hmem
    obtain ⟨c, hc, h2⟩ := hmem
    rw [List.mem_range] at hc
    rw [List.mem_map] at h2
    obtain ⟨j, hj, rfl⟩ := h2
    unfold wordSLandingIndices at hj
    rw [List.mem_filter, List.mem_range] at hj
    simp only [decide_eq_true_eq] at hj
    exact ⟨hc, hj.1, hj.2.1, hj.2.2⟩
  have hphi_val : ∀ cj, cj ∈ dom →
      phi cj = p0 + (cj.1 : Int) * d + wordRelPot V r (cj.2 + 1) ∧
      Fw f (s + cj.1 * L + cj.2 + 1) = rAbs ∧
      f (s + cj.1 * L + cj.2) = false := by
    intro cj hmem
    obtain ⟨hc, hjL, hVf, hwh⟩ := hdom_mem cj hmem
    have hper := periodic_height_and_pot f s V hbal R hm cj.1 (cj.2 + 1) hc (by omega) r
    have hmc := matchesAt_repeat_copy f s V R cj.1 hc hm cj.2 hjL
    have hidx : s + cj.1 * L + (cj.2 + 1) = s + cj.1 * L + cj.2 + 1 := by omega
    rw [hidx] at hper
    exact ⟨hper.2, by rw [hper.1, hwh], by rw [hmc, hVf]⟩
  have hsub : dom.map phi ⊆ target := by
    intro z hz
    rw [List.mem_map] at hz
    obtain ⟨cj, hmem, rfl⟩ := hz
    obtain ⟨hc, hjL, _, _⟩ := hdom_mem cj hmem
    have hval := (hphi_val cj hmem).1
    have hmin := wordPotMinUpTo_le V r L (cj.2 + 1) (by omega)
    have hmax := wordPotMaxUpTo_ge V r L (cj.2 + 1) (by omega)
    have hspan_le : wordPotMinUpTo V r L ≤ wordPotMaxUpTo V r L := wordPotMin_le_max V r
    have hspan_eq : (wordPotSpan V r : Int) = wordPotMaxUpTo V r L - wordPotMinUpTo V r L := by
      unfold wordPotSpan
      dsimp only [L] at hspan_le ⊢
      exact Int.toNat_of_nonneg (by omega)
    dsimp only [target]
    by_cases hd0 : 0 ≤ d
    · rw [if_pos hd0, List.mem_map]
      have hd_nat : (d.natAbs : Int) = d := Int.natAbs_of_nonneg hd0
      have hc_le : (cj.1 : Int) * d ≤ ((R - 1 : Nat) : Int) * d :=
        Int.mul_le_mul_of_nonneg_right (by omega) hd0
      have hc_nn : 0 ≤ (cj.1 : Int) * d :=
        Int.mul_nonneg (Int.natCast_nonneg _) hd0
      let k := (phi cj - (p0 + wordPotMinUpTo V r L)).toNat
      refine ⟨k, ?_, ?_⟩
      · rw [List.mem_range]
        dsimp only [k, W]
        have hmul : (((R - 1) * d.natAbs : Nat) : Int) = ((R - 1 : Nat) : Int) * d := by
          rw [Int.natCast_mul, hd_nat]
        omega
      · dsimp only [k]; omega
    · rw [if_neg hd0, List.mem_map]
      have hd_neg : (d.natAbs : Int) = -d := by omega
      have hmul : (((R - 1) * d.natAbs : Nat) : Int) = -(((R - 1 : Nat) : Int) * d) := by
        rw [Int.natCast_mul, hd_neg]; grind
      have hc_ge : ((R - 1 : Nat) : Int) * d ≤ (cj.1 : Int) * d := by
        have h1 := Int.mul_le_mul_of_nonneg_right (show (cj.1 : Int) ≤ ((R - 1 : Nat) : Int) by omega)
          (show 0 ≤ -d by omega)
        grind
      have hc_le0 : (cj.1 : Int) * d ≤ 0 := by
        have h1 := Int.mul_nonneg (Int.natCast_nonneg cj.1) (show 0 ≤ -d by omega)
        grind
      let k := (phi cj - lo).toNat
      refine ⟨k, ?_, ?_⟩
      · rw [List.mem_range]
        dsimp only [k, W, lo]
        omega
      · dsimp only [k, lo]; omega
  have hinj : ∀ x, x ∈ dom → ∀ y, y ∈ dom → phi x = phi y → x = y := by
    intro x hx y hy hxy
    obtain ⟨hcx, hjx, _, _⟩ := hdom_mem x hx
    obtain ⟨hcy, hjy, _, _⟩ := hdom_mem y hy
    obtain ⟨_, hFx, hfx⟩ := hphi_val x hx
    obtain ⟨_, hFy, hfy⟩ := hphi_val y hy
    let tx := s + x.1 * L + x.2
    let ty := s + y.1 * L + y.2
    have htx_lt : tx < s + R * L := by
      have h1 : (x.1 + 1) * L ≤ R * L := Nat.mul_le_mul_right L (by omega)
      rw [Nat.add_mul, Nat.one_mul] at h1
      dsimp only [tx]; omega
    have hty_lt : ty < s + R * L := by
      have h1 : (y.1 + 1) * L ≤ R * L := Nat.mul_le_mul_right L (by omega)
      rw [Nat.add_mul, Nat.one_mul] at h1
      dsimp only [ty]; omega
    by_cases hlt : tx < ty
    · have hne := hfresh ty hty_lt hfy (tx + 1) (by omega) (by rw [hFx, hFy])
      rw [hFy] at hne
      exact (hne hxy.symm).elim
    · by_cases hgt : ty < tx
      · have hne := hfresh tx htx_lt hfx (ty + 1) (by omega) (by rw [hFx, hFy])
        rw [hFx] at hne
        exact (hne hxy).elim
      · have heq : tx = ty := by omega
        have hcj : x.1 * L + x.2 = y.1 * L + y.2 := by dsimp only [tx, ty] at heq; omega
        have h1 : x.1 = y.1 := by
          by_cases h1lt : x.1 < y.1
          · have hmul : (x.1 + 1) * L ≤ y.1 * L := Nat.mul_le_mul_right L (by omega)
            rw [Nat.add_mul, Nat.one_mul] at hmul; omega
          · by_cases h1gt : y.1 < x.1
            · have hmul : (y.1 + 1) * L ≤ x.1 * L := Nat.mul_le_mul_right L (by omega)
              rw [Nat.add_mul, Nat.one_mul] at hmul; omega
            · omega
        have h2 : x.2 = y.2 := by rw [h1] at hcj; omega
        exact Prod.ext h1 h2
  have hnd_img := nodup_map_of_inj dom phi hdom_nodup hinj
  have hlen := hnd_img.length_le_of_subset hsub
  rw [List.length_map] at hlen
  have hdom_len : dom.length = R * wordSLandings V r := by
    simp only [dom, prod_flatMap_length, List.length_range, wordSLandings]
  have htgt_len : target.length = W := by
    dsimp only [target]
    split <;> simp [List.length_map, List.length_range]
  rw [hdom_len, htgt_len] at hlen
  exact hlen

/-- Direct periodic `S`-freshness pigeonhole bound on EVERY coherent finite-state greedy
replay `(b, s)` (`s.value ∈ s.seen`) with no external freshness hypothesis. -/
theorem seeded_replay_periodic_s_count_le_drift (b s R : Nat) (st : State)
    (hs : st.value ∈ st.seen) (V : List Bool) (r : Int)
    (hbal : mass V = 0) (hR : 1 ≤ R)
    (hm : MatchesAt (replaySign b st) s (repeatWord R V)) :
    R * wordSLandings V r ≤ wordPotSpan V r + (R - 1) * (wordPotDrift V r).natAbs + 1 :=
  typeIFresh_periodic_s_count_le_drift (replaySign b st) s R V r hbal hR hm
    (seeded_replay_typeIFresh b st hs (s + R * V.length))

/-- Zero-drift periodic repeat obstruction: ANY balanced cycle `V` with `wordPotDrift V r = 0`
and at least one `S`-landing at relative height `r` (including every `E-786` balanced cascade
cycle at source height `H - 1`) can repeat at most `wordPotSpan V r + 1` consecutive times
in any coherent finite-state greedy replay `(b, st)`. -/
theorem seeded_replay_zero_drift_repeat_bound (b s R : Nat) (st : State)
    (hs : st.value ∈ st.seen) (V : List Bool) (r : Int)
    (hbal : mass V = 0) (hdrift : wordPotDrift V r = 0) (hS : 1 ≤ wordSLandings V r)
    (hm : MatchesAt (replaySign b st) s (repeatWord R V)) :
    R ≤ wordPotSpan V r + 1 := by
  by_cases hR : R = 0
  · omega
  · have hbound := seeded_replay_periodic_s_count_le_drift b s R st hs V r hbal (by omega) hm
    rw [hdrift] at hbound
    simp only [Int.natAbs_zero, Nat.mul_zero, Nat.add_zero] at hbound
    have hmul : R * 1 ≤ R * wordSLandings V r := Nat.mul_le_mul_left R hS
    omega

/-- Unit-drift `Δ ≥ 2` necessity theorem: ANY balanced cycle `V` with `|wordPotDrift V r| = 1`
repeated at least `wordPotSpan V r + 2` consecutive times in any coherent finite-state greedy
replay `(b, st)` MUST satisfy `wordSLandings V r ≤ 1`. In particular, unit-drift coherent
recursive towers cannot populate height `h_k - 1` (`Δ ≥ 2`), showing that the `Δ = 2`
coherent cascade (base `√(7/3) ≈ 1.527525`) is optimal among unit-drift recursive towers. -/
theorem seeded_replay_unit_drift_at_most_one_s_landing (b s R : Nat) (st : State)
    (hs : st.value ∈ st.seen) (V : List Bool) (r : Int)
    (hbal : mass V = 0) (hunit : (wordPotDrift V r).natAbs = 1)
    (hR : wordPotSpan V r + 2 ≤ R)
    (hm : MatchesAt (replaySign b st) s (repeatWord R V)) :
    wordSLandings V r ≤ 1 := by
  have hbound := seeded_replay_periodic_s_count_le_drift b s R st hs V r hbal (by omega) hm
  rw [hunit, Nat.mul_one] at hbound
  by_cases hge : 2 ≤ wordSLandings V r
  · have h2 : R * 2 ≤ R * wordSLandings V r := Nat.mul_le_mul_left R hge
    omega
  · omega

/-- Canonical clock-0 orbit zero-drift obstruction: in the real Recamán sequence `Recaman.Basic.a`,
no balanced word `V` with `wordPotDrift V r = 0` and `1 ≤ wordSLandings V r` can repeat
`wordPotSpan V r + 2` consecutive times starting at ANY clock `s : Nat`. -/
theorem canonical_zero_drift_forbids_long_repeat (s : Nat) (V : List Bool) (r : Int)
    (hbal : mass V = 0) (hdrift : wordPotDrift V r = 0) (hS : 1 ≤ wordSLandings V r) :
    ¬ MatchesAt canonicalOrbitSign s (repeatWord (wordPotSpan V r + 2) V) := by
  intro hm
  have hs0 : initial.value ∈ initial.seen := by simp [initial]
  have hle := seeded_replay_zero_drift_repeat_bound 0 s (wordPotSpan V r + 2) initial hs0
    V r hbal hdrift hS hm
  omega

end Recaman.CoherentGreedyFreshness
