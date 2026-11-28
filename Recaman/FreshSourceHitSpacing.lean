import Recaman.CommonSourceHitSpacing
import Recaman.NumericCandidateRankPotential

namespace Recaman.FreshSourceHitSpacing

open Recaman Recaman.SeededReplay Recaman.CoherentGreedyFreshness
open Recaman.NumericCandidateRankPotential Recaman.CommonSourceHitSpacing
open Recaman.FloorSupplyPotential Recaman.BlockSuffixPositivity
open Recaman.SingleWindowEquality Recaman.CapacityEqualityInduction
open Recaman.LineCapacityPeriodic Recaman.LeadingRunSupply
open Recaman.CrossBlockReuseUnbounded Recaman.SameSourceLowCrossings
open Recaman.ShortPeriodicSupply (sign)

/-! # Fresh same-source hit spacing (`E-760`) & source-clock capacity (`E-804`)

Combines `E-748` (`CommonSourceHitSpacing.common_source_hit_gap`), `E-798`
(`CoherentGreedyFreshness`), and `E-802` (`NumericCandidateRankPotential`) to prove
unconditionally in Lean 4 (with NO coherence assumption `s.value ∈ s.seen` needed!):

1. `gap_eight_bridge_unique_Z`: every balanced length-8 bridge starting with `A`
   (`f p = true`, `Fw f (p + 8) = Fw f p`, `Ar f p 8 = -8`) is uniquely
   `Z = ASSSSAAA` (`[true, false, false, false, false, true, true, true]`).
2. `consecutive_gap_eight_forbidden_on_replay`: `Z ++ Z` cannot occur anywhere in
   ANY actual finite-state greedy replay `SeededReplay.run b s` (even incoherent!),
   because the `S`-landing at phase `3` equals the `S`-landing at phase `11`.
3. `common_source_two_step_gap_ge_twenty`: any three hits `p < q < r` of one
   unchanged `Win` source `u` with actual `A` at `p, q` satisfy `p + 20 ≤ r`.
4. `fresh_common_source_hit_span` (`E-760`): any strictly sorted nonempty list
   `p0 :: rest` of `M = rest.length + 1` actual `A` hits sharing one unchanged `Win`
   source `u` satisfies
     `p0 + 8 * rest.length + 4 * (rest.length / 2) ≤ (p0 :: rest).getLast _`,
   i.e. `span ≥ 10 * (M - 1) - 2 * ((M - 1) % 2)`.
5. `original_win_source_clock_capacity` (`E-760` + `E-761` unified consumer):
   if a fixed `Win` source `u` has `M ≥ 2` actual `A` hits (`k = M - 2`), then
   `(b + u) + 11 + 8 * k + 4 * (k / 2) ≤ (run b s u).value` (hence
   `(run b s u).value < b + u + 11` forces `M ≤ 1`, and otherwise
   `M ≤ 2 + ((run b s u).value - (b + u) - 9) / 10`).
6. `raw_nonfresh_counterexample_beats_fresh_span`: exact raw non-fresh witness
   `SSAA ++ Z ++ Z ++ A` (`len = 21`) with three hits at `4, 12, 20` sharing unchanged
   source `1` and all heights `≤ 1`, yet span `16 < 20` (confirming `S`-freshness is
   essential).
7. `canonical_orbit_fresh_source_spacing`: unconditional specialization of both the
   `10n - 2(n%2)` span bound and the `a_src + 11 + 10k - 2(k%2) ≤ a u` clock capacity
   directly to `Recaman.Basic.a`.
-/

/-- The unique minimum-area balanced length-8 bridge starting with `A`: `Z = ASSSSAAA`. -/
def bridgeZ : List Bool :=
  [true, false, false, false, false, true, true, true]

/-- Raw non-fresh counterexample `SSAA ++ Z ++ Z ++ A` (length 21) from `E-760`. -/
def rawNonFreshWord : List Bool :=
  [false, false, true, true] ++ bridgeZ ++ bridgeZ ++ [true]

/-- Sign stream of `rawNonFreshWord` (padded by `true` past index 20). -/
def rawNonFreshSign (i : Nat) : Bool :=
  rawNonFreshWord.getD i true

/-! ## Part 1: Uniqueness of `Z = ASSSSAAA` and `Z ++ Z` greedy obstruction -/

private theorem win_length_mod_four (f : Nat → Bool) (u k : Nat)
    (h : Win f u k) : k % 4 = 3 := by
  let e : Int → Bool := fun x => f x.toNat
  let v := past e ((u + k : Nat) : Int) k
  have hb := past_bridge e 0 u k
  simp only [Int.zero_add, e, Int.toNat_natCast] at hb
  change mass v = Fw f (u + k) - Fw f u ∧ moment v = Ar f u k at hb
  have hP : P2 v := ⟨by rw [hb.1, h.2.1]; omega, hb.2.trans h.2.2⟩
  have hp := p2_count_identities v hP
  have hl : v.length = k := by simp [v, past]
  rw [hl] at hp
  omega

private theorem win_bridge_mass_area (f : Nat → Bool) (u p q : Nat)
    (hup : u ≤ p) (hpq : p ≤ q)
    (hp : Win f u (p - u)) (hq : Win f u (q - u)) :
    Fw f q = Fw f p ∧ Ar f p (q - p) = -((q - p : Nat) : Int) := by
  have hFp := hp.2.1
  have hFq := hq.2.1
  rw [Nat.add_sub_cancel' hup] at hFp
  rw [Nat.add_sub_cancel' (by omega : u ≤ q)] at hFq
  have hsp := area_split_at f u p q hup hpq
  rw [hp.2.2, hq.2.2] at hsp
  refine ⟨by omega, ?_⟩
  have : Fw f p - Fw f u = 1 := by omega
  rw [this] at hsp
  omega

/-- Every balanced length-8 bridge starting with `A` (`f p = true`, `Fw f (p + 8) = Fw f p`)
and relative area `Ar f p 8 = -8` is uniquely `bridgeZ = ASSSSAAA`. -/
theorem gap_eight_bridge_unique_Z (f : Nat → Bool) (p : Nat)
    (hA : f p = true) (hbal : Fw f (p + 8) = Fw f p) (harea : Ar f p 8 = -8) :
    seg f p 8 = bridgeZ := by
  -- Express `Fw f (p + k) - Fw f p` and `Ar f p 8` in terms of `b_j = if f (p + j) then 1 else 0`.
  let b : Nat → Int := fun j => if f (p + j) then 1 else 0
  have hb_rng : ∀ j, 0 ≤ b j ∧ b j ≤ 1 := fun j => by
    dsimp only [b]; split <;> omega
  have hs_eq : ∀ j, sign (f (p + j)) = 2 * b j - 1 := fun j => by
    dsimp only [b]; cases f (p + j) <;> simp [sign]
  have hb0 : b 0 = 1 := by dsimp only [b]; simp [hA]
  have hF1 : Fw f (p + 1) = Fw f p + (2 * b 0 - 1) := by
    have h := Fw_succ f p; rw [← hs_eq 0]; simpa using h
  have hF2 : Fw f (p + 2) = Fw f (p + 1) + (2 * b 1 - 1) := by
    have h := Fw_succ f (p + 1); rw [← hs_eq 1]; exact h
  have hF3 : Fw f (p + 3) = Fw f (p + 2) + (2 * b 2 - 1) := by
    have h := Fw_succ f (p + 2); rw [← hs_eq 2]; exact h
  have hF4 : Fw f (p + 4) = Fw f (p + 3) + (2 * b 3 - 1) := by
    have h := Fw_succ f (p + 3); rw [← hs_eq 3]; exact h
  have hF5 : Fw f (p + 5) = Fw f (p + 4) + (2 * b 4 - 1) := by
    have h := Fw_succ f (p + 4); rw [← hs_eq 4]; exact h
  have hF6 : Fw f (p + 6) = Fw f (p + 5) + (2 * b 5 - 1) := by
    have h := Fw_succ f (p + 5); rw [← hs_eq 5]; exact h
  have hF7 : Fw f (p + 7) = Fw f (p + 6) + (2 * b 6 - 1) := by
    have h := Fw_succ f (p + 6); rw [← hs_eq 6]; exact h
  have hF8 : Fw f (p + 8) = Fw f (p + 7) + (2 * b 7 - 1) := by
    have h := Fw_succ f (p + 7); rw [← hs_eq 7]; exact h
  have hA0 : Ar f p 0 = 0 := rfl
  have hA1 : Ar f p 1 = Ar f p 0 + (Fw f (p + 1) - Fw f p) := Ar_succ f p 0
  have hA2 : Ar f p 2 = Ar f p 1 + (Fw f (p + 2) - Fw f p) := Ar_succ f p 1
  have hA3 : Ar f p 3 = Ar f p 2 + (Fw f (p + 3) - Fw f p) := Ar_succ f p 2
  have hA4 : Ar f p 4 = Ar f p 3 + (Fw f (p + 4) - Fw f p) := Ar_succ f p 3
  have hA5 : Ar f p 5 = Ar f p 4 + (Fw f (p + 5) - Fw f p) := Ar_succ f p 4
  have hA6 : Ar f p 6 = Ar f p 5 + (Fw f (p + 6) - Fw f p) := Ar_succ f p 5
  have hA7 : Ar f p 7 = Ar f p 6 + (Fw f (p + 7) - Fw f p) := Ar_succ f p 6
  have hA8 : Ar f p 8 = Ar f p 7 + (Fw f (p + 8) - Fw f p) := Ar_succ f p 7
  have hr1 := hb_rng 1; have hr2 := hb_rng 2; have hr3 := hb_rng 3
  have hr4 := hb_rng 4; have hr5 := hb_rng 5; have hr6 := hb_rng 6; have hr7 := hb_rng 7
  have hvals : b 1 = 0 ∧ b 2 = 0 ∧ b 3 = 0 ∧ b 4 = 0 ∧ b 5 = 1 ∧ b 6 = 1 ∧ b 7 = 1 := by
    omega
  have hf_bool : ∀ j, (b j = 0 → f (p + j) = false) ∧ (b j = 1 → f (p + j) = true) := by
    intro j; dsimp only [b]; cases f (p + j) <;> simp
  have hf1 : f (p + 1) = false := (hf_bool 1).1 hvals.1
  have hf2 : f (p + 2) = false := (hf_bool 2).1 hvals.2.1
  have hf3 : f (p + 3) = false := (hf_bool 3).1 hvals.2.2.1
  have hf4 : f (p + 4) = false := (hf_bool 4).1 hvals.2.2.2.1
  have hf5 : f (p + 5) = true := (hf_bool 5).2 hvals.2.2.2.2.1
  have hf6 : f (p + 6) = true := (hf_bool 6).2 hvals.2.2.2.2.2.1
  have hf7 : f (p + 7) = true := (hf_bool 7).2 hvals.2.2.2.2.2.2
  -- Expand `seg f p 8`
  have hseg : seg f p 8 =
      [f p, f (p + 1), f (p + 2), f (p + 3), f (p + 4), f (p + 5), f (p + 6), f (p + 7)] := by
    rfl
  rw [hseg, hA, hf1, hf2, hf3, hf4, hf5, hf6, hf7]
  rfl

/-- `Z ++ Z` (`ASSSSAAA ++ ASSSSAAA`) cannot occur anywhere in ANY actual finite-state
greedy replay `SeededReplay.run b s` (even without assuming `s.value ∈ s.seen`):
the `S`-landing at phase `3` (`p + 3 ≥ 1`) coincides with the `S`-landing at phase `11`
(`p + 11`), violating freshness of `S` at step `p + 10`. -/
theorem consecutive_gap_eight_forbidden_on_replay (b : Nat) (s : State) (p : Nat)
    (h1 : seg (replaySign b s) p 8 = bridgeZ)
    (h2 : seg (replaySign b s) (p + 8) 8 = bridgeZ) : False := by
  let f := replaySign b s
  have hseg_eq : ∀ q, seg f q 8 =
      [f q, f (q + 1), f (q + 2), f (q + 3), f (q + 4), f (q + 5), f (q + 6), f (q + 7)] := by
    intro q; rfl
  have h1' : [f p, f (p + 1), f (p + 2), f (p + 3), f (p + 4), f (p + 5), f (p + 6), f (p + 7)] =
      [true, false, false, false, false, true, true, true] := by
    rw [← hseg_eq p]; exact h1
  have h2' : [f (p + 8), f (p + 9), f (p + 10), f (p + 11), f (p + 12), f (p + 13), f (p + 14), f (p + 15)] =
      [true, false, false, false, false, true, true, true] := by
    have hq := hseg_eq (p + 8)
    simp only [Nat.add_assoc] at hq
    rw [← hq]; exact h2
  simp only [List.cons.injEq, and_true] at h1' h2'
  have hF4 : Fw f (p + 4) = Fw f (p + 3) - 1 := by
    rw [show p + 4 = (p + 3) + 1 by omega, Fw_succ, h1'.2.2.2.1]; simp [sign]; omega
  have hF5 : Fw f (p + 5) = Fw f (p + 3) - 2 := by
    rw [show p + 5 = (p + 4) + 1 by omega, Fw_succ, h1'.2.2.2.2.1]; simp [sign]; omega
  have hF6 : Fw f (p + 6) = Fw f (p + 3) - 1 := by
    rw [show p + 6 = (p + 5) + 1 by omega, Fw_succ, h1'.2.2.2.2.2.1]; simp [sign]; omega
  have hF7 : Fw f (p + 7) = Fw f (p + 3) := by
    rw [show p + 7 = (p + 6) + 1 by omega, Fw_succ, h1'.2.2.2.2.2.2.1]; simp [sign]; omega
  have hF8 : Fw f (p + 8) = Fw f (p + 3) + 1 := by
    rw [show p + 8 = (p + 7) + 1 by omega, Fw_succ, h1'.2.2.2.2.2.2.2]; simp [sign]; omega
  have hF9 : Fw f (p + 9) = Fw f (p + 3) + 2 := by
    rw [show p + 9 = (p + 8) + 1 by omega, Fw_succ, h2'.1]; simp [sign]; omega
  have hF10 : Fw f (p + 10) = Fw f (p + 3) + 1 := by
    rw [show p + 10 = (p + 9) + 1 by omega, Fw_succ, h2'.2.1]; simp [sign]; omega
  have hF11 : Fw f (p + 11) = Fw f (p + 3) := by
    rw [show p + 11 = (p + 10) + 1 by omega, Fw_succ, h2'.2.2.1]; simp [sign]; omega
  have hAr8 : Ar f (p + 3) 8 = 0 := by
    have hA0 : Ar f (p + 3) 0 = 0 := rfl
    have hA1 : Ar f (p + 3) 1 = Ar f (p + 3) 0 + (Fw f (p + 4) - Fw f (p + 3)) := by
      simpa [Nat.add_assoc] using Ar_succ f (p + 3) 0
    have hA2 : Ar f (p + 3) 2 = Ar f (p + 3) 1 + (Fw f (p + 5) - Fw f (p + 3)) := by
      simpa [Nat.add_assoc] using Ar_succ f (p + 3) 1
    have hA3 : Ar f (p + 3) 3 = Ar f (p + 3) 2 + (Fw f (p + 6) - Fw f (p + 3)) := by
      simpa [Nat.add_assoc] using Ar_succ f (p + 3) 2
    have hA4 : Ar f (p + 3) 4 = Ar f (p + 3) 3 + (Fw f (p + 7) - Fw f (p + 3)) := by
      simpa [Nat.add_assoc] using Ar_succ f (p + 3) 3
    have hA5 : Ar f (p + 3) 5 = Ar f (p + 3) 4 + (Fw f (p + 8) - Fw f (p + 3)) := by
      simpa [Nat.add_assoc] using Ar_succ f (p + 3) 4
    have hA6 : Ar f (p + 3) 6 = Ar f (p + 3) 5 + (Fw f (p + 9) - Fw f (p + 3)) := by
      simpa [Nat.add_assoc] using Ar_succ f (p + 3) 5
    have hA7 : Ar f (p + 3) 7 = Ar f (p + 3) 6 + (Fw f (p + 10) - Fw f (p + 3)) := by
      simpa [Nat.add_assoc] using Ar_succ f (p + 3) 6
    have hA8 : Ar f (p + 3) 8 = Ar f (p + 3) 7 + (Fw f (p + 11) - Fw f (p + 3)) := by
      simpa [Nat.add_assoc] using Ar_succ f (p + 3) 7
    omega
  -- Hence `value b s (p + 11) = value b s (p + 3)`!
  have hv3 := replay_value_eq_abel_potential b s (p + 3)
  have hv11 := replay_value_eq_abel_potential b s (p + 11)
  have hsp := area_split_at f 0 (p + 3) (p + 11) (Nat.zero_le _) (by omega)
  rw [Nat.sub_zero, Nat.sub_zero, show p + 11 - (p + 3) = 8 by omega, hAr8] at hsp
  have h0 : Fw f 0 = 0 := rfl
  rw [h0] at hsp
  unfold floorPotential at hv3 hv11
  simp only [Nat.sub_zero] at hv3 hv11
  change value b s (p + 3) =
    (s.value : Int) + ((b + 1 : Nat) : Int) * Fw f (p + 3) -
      (Ar f 0 (p + 3) + ((p + 3 : Nat) : Int) * (Fw f 0 - (Fw f (p + 3) - 1 + 1))) at hv3
  change value b s (p + 11) =
    (s.value : Int) + ((b + 1 : Nat) : Int) * Fw f (p + 11) -
      (Ar f 0 (p + 11) + ((p + 11 : Nat) : Int) * (Fw f 0 - (Fw f (p + 11) - 1 + 1))) at hv11
  rw [h0, hF11] at hv11
  rw [h0] at hv3
  have hveq : (run b s (p + 3)).value = (run b s (p + 11)).value := by
    have : value b s (p + 3) = value b s (p + 11) := by
      push_cast at hv3 hv11 hsp
      grind
    change ((run b s (p + 3)).value : Int) = ((run b s (p + 11)).value : Int) at this
    omega
  -- Contradicts freshness of the `S`-step at `p + 10` (`p + 3 ≥ 1` so `X(p + 3)` is in `seen(p + 3) ⊆ seen(p + 10)`)!
  have hc10 : CanSubtract (b + (p + 10) + 1) (run b s (p + 10)) := by
    have hS : replaySign b s (p + 10) = false := h2'.2.2.1
    unfold replaySign at hS
    by_cases hc : CanSubtract (b + (p + 10) + 1) (run b s (p + 10))
    · exact hc
    · simp [hc] at hS
  have hv11_sub : (run b s (p + 11)).value = (run b s (p + 10)).value - (b + (p + 10) + 1) := by
    rw [show p + 11 = (p + 10) + 1 by omega]
    change (step (b + (p + 10) + 1) (run b s (p + 10))).value = _
    simp only [step, nextValue, if_pos hc10]
  have hmem3 : (run b s (p + 3)).value ∈ (run b s (p + 3)).seen := by
    rw [show p + 3 = (p + 2) + 1 by omega]
    exact step_value_mem_seen _ _
  have hseen10 : Seen b s (p + 10) ((run b s (p + 3)).value : Int) :=
    seen_mono (by omega) ⟨(run b s (p + 3)).value, hmem3, rfl⟩
  obtain ⟨z, hz_mem, hz_eq⟩ := hseen10
  have hz : z = (run b s (p + 10)).value - (b + (p + 10) + 1) := by omega
  exact hc10.2 (hz ▸ hz_mem)

/-! ## Part 2: `10n - 2(n%2)` fresh hit spacing & unified source-clock capacity -/

/-- Two-step gap theorem (`E-760`): any three hits `p < q < r` of one unchanged `Win` source
`u` with actual `A` at `p, q` satisfy `p + 20 ≤ r`. -/
theorem common_source_two_step_gap_ge_twenty (b : Nat) (s : State) (u p q r : Nat)
    (hup : u ≤ p) (hpq : p < q) (hqr : q < r)
    (hAp : replaySign b s p = true) (hAq : replaySign b s q = true)
    (hp : Win (replaySign b s) u (p - u))
    (hq : Win (replaySign b s) u (q - u))
    (hr : Win (replaySign b s) u (r - u)) :
    p + 20 ≤ r := by
  let f := replaySign b s
  have hgap1 : p + 8 ≤ q := common_source_hit_gap f u p q hup hpq hAp hp hq
  have hgap2 : q + 8 ≤ r := common_source_hit_gap f u q r (by omega) hqr hAq hq hr
  have hmodp : (p - u) % 4 = 3 := win_length_mod_four f u (p - u) hp
  have hmodq : (q - u) % 4 = 3 := win_length_mod_four f u (q - u) hq
  have hmodr : (r - u) % 4 = 3 := win_length_mod_four f u (r - u) hr
  by_cases hboth : q = p + 8 ∧ r = q + 8
  · obtain ⟨hq_eq, hr_eq⟩ := hboth
    have hb1 := win_bridge_mass_area f u p q hup (Nat.le_of_lt hpq) hp hq
    have hb2 := win_bridge_mass_area f u q r (by omega) (Nat.le_of_lt hqr) hq hr
    rw [hq_eq, show p + 8 - p = 8 by omega] at hb1
    rw [hr_eq, show q + 8 - q = 8 by omega] at hb2
    have hZ1 : seg f p 8 = bridgeZ := gap_eight_bridge_unique_Z f p hAp hb1.1 hb1.2
    have hZ2 : seg f (p + 8) 8 = bridgeZ := by
      rw [← hq_eq]
      exact gap_eight_bridge_unique_Z f q hAq hb2.1 hb2.2
    exact (consecutive_gap_eight_forbidden_on_replay b s p hZ1 hZ2).elim
  · omega

/-- Principal `E-760` spacing theorem on arbitrary finite-state greedy replays:
for any nonempty strictly sorted list `p0 :: rest` of actual `A` hits sharing one unchanged
original `Win` source `u`, writing `n = rest.length`:
  `p0 + 8 * n + 4 * (n / 2) ≤ (p0 :: rest).getLast (List.cons_ne_nil p0 rest)`
(equivalently `last - first ≥ 10 * n - 2 * (n % 2)`). -/
theorem fresh_common_source_hit_span (b : Nat) (s : State) (u p0 : Nat) (rest : List Nat)
    (hsort : (p0 :: rest).Pairwise (· < ·))
    (hmem : ∀ p ∈ p0 :: rest, u ≤ p ∧ replaySign b s p = true ∧ Win (replaySign b s) u (p - u)) :
    p0 + 8 * rest.length + 4 * (rest.length / 2) ≤
      (p0 :: rest).getLast (List.cons_ne_nil p0 rest) := by
  have haux : ∀ n : Nat, ∀ p0 : Nat, ∀ rest : List Nat, rest.length ≤ n →
      (p0 :: rest).Pairwise (· < ·) →
      (∀ p ∈ p0 :: rest, u ≤ p ∧ replaySign b s p = true ∧ Win (replaySign b s) u (p - u)) →
      p0 + 8 * rest.length + 4 * (rest.length / 2) ≤
        (p0 :: rest).getLast (List.cons_ne_nil p0 rest) := by
    intro n
    induction n with
    | zero =>
      intro p0 rest hlen _ _
      cases rest with
      | nil => simp
      | cons _ _ => simp at hlen
    | succ n ih =>
      intro p0 rest hlen hpw hm
      cases rest with
      | nil => simp
      | cons q tail =>
        cases tail with
        | nil =>
          have hpq : p0 < q := (List.pairwise_cons.mp hpw).1 q (List.mem_cons_self ..)
          have hm0 := hm p0 (List.mem_cons_self ..)
          have hmq := hm q (List.mem_cons_of_mem p0 (List.mem_cons_self ..))
          have hg := common_source_hit_gap (replaySign b s) u p0 q hm0.1 hpq hm0.2.1 hm0.2.2 hmq.2.2
          simp only [List.length_cons, List.length_nil, List.getLast_cons_cons, List.getLast_singleton]
          omega
        | cons r tail' =>
          have hpw0 := List.pairwise_cons.mp hpw
          have hpw1 := List.pairwise_cons.mp hpw0.2
          have hpq : p0 < q := hpw0.1 q (List.mem_cons_self ..)
          have hqr : q < r := hpw1.1 r (List.mem_cons_self ..)
          have hm0 := hm p0 (List.mem_cons_self ..)
          have hmq := hm q (List.mem_cons_of_mem p0 (List.mem_cons_self ..))
          have hmr := hm r (List.mem_cons_of_mem p0 (List.mem_cons_of_mem q (List.mem_cons_self ..)))
          have h20 := common_source_two_step_gap_ge_twenty b s u p0 q r hm0.1 hpq hqr
            hm0.2.1 hmq.2.1 hm0.2.2 hmq.2.2 hmr.2.2
          have hih := ih r tail' (by simp only [List.length_cons] at hlen; omega) hpw1.2
            (fun x hx => hm x (List.mem_cons_of_mem p0 (List.mem_cons_of_mem q hx)))
          simp only [List.length_cons, List.getLast_cons_cons] at hih ⊢
          omega
  exact haux rest.length p0 rest (Nat.le_refl _) hsort hmem

/-- Unified `E-760` + `E-761` source-clock capacity theorem:
for any fixed `Win` source `u` with `M ≥ 2` strictly sorted actual `A` hits `ps`,
writing `k = ps.length - 2`, `a_src = b + u`, and `y_src = (run b s u).value`:
1. `a_src + 11 + 8 * k + 4 * (k / 2) ≤ y_src`,
2. Consequently `y_src < a_src + 11` forces `ps.length ≤ 1`, and in general
   `ps.length ≤ 2 + (y_src - a_src - 9) / 10`. -/
theorem original_win_source_clock_capacity (b : Nat) (s : State) (u : Nat)
    (ps : List Nat) (hsort : ps.Pairwise (· < ·)) (hM : 2 ≤ ps.length)
    (hmem : ∀ p ∈ ps, u ≤ p ∧ replaySign b s p = true ∧ Win (replaySign b s) u (p - u)) :
    (b + u) + 11 + 8 * (ps.length - 2) + 4 * ((ps.length - 2) / 2) ≤ (run b s u).value ∧
      ps.length ≤ 2 + ((run b s u).value - (b + u) - 9) / 10 := by
  -- Split `ps` into `pref ++ [p_last]` where `pref` is nonempty (`pref.length = ps.length - 1`).
  have hne : ps ≠ [] := by intro h; rw [h] at hM; simp at hM
  have hdecomp : ps = ps.dropLast ++ [ps.getLast hne] := by
    have haux : ∀ (l : List Nat) (h : l ≠ []), l = l.dropLast ++ [l.getLast h] := by
      intro l
      induction l with
      | nil => intro h; exact (h rfl).elim
      | cons a t ih =>
        intro h
        cases t with
        | nil => rfl
        | cons b t' =>
          have ih' := ih (List.cons_ne_nil b t')
          simpa [List.dropLast, List.getLast] using congrArg (a :: ·) ih'
    exact haux ps hne
  have hdl_len : ps.dropLast.length = ps.length - 1 := by simp
  cases hdl : ps.dropLast with
  | nil =>
    rw [hdl] at hdl_len
    simp at hdl_len
    omega
  | cons p0 rest =>
    have hsort_dl : (p0 :: rest).Pairwise (· < ·) := by
      have hpw_app : (ps.dropLast ++ [ps.getLast hne]).Pairwise (· < ·) := hdecomp ▸ hsort
      rw [hdl] at hpw_app
      exact (List.pairwise_append.mp hpw_app).1
    have hmem_dl : ∀ p ∈ p0 :: rest, u ≤ p ∧ replaySign b s p = true ∧ Win (replaySign b s) u (p - u) := by
      intro p hp
      apply hmem p
      rw [hdecomp, hdl]
      exact List.mem_append_left _ hp
    have hspan := fresh_common_source_hit_span b s u p0 rest hsort_dl hmem_dl
    let p_pen := (p0 :: rest).getLast (List.cons_ne_nil p0 rest)
    let p_last := ps.getLast hne
    have hpen_lt_last : p_pen < p_last := by
      have hpw_app : (ps.dropLast ++ [ps.getLast hne]).Pairwise (· < ·) := hdecomp ▸ hsort
      rw [hdl] at hpw_app
      have hrel := (List.pairwise_append.mp hpw_app).2.2
      exact hrel p_pen (List.getLast_mem _) p_last (List.mem_cons_self ..)
    have hpen_mem := hmem_dl p_pen (List.getLast_mem _)
    have hlast_mem := hmem p_last (List.getLast_mem hne)
    -- By `original_win_source_finite_capacity` (E-802), `p_pen < p_last` forces `b + p_pen + 7 < (run b s u).value`!
    have hpen_ub : b + p_pen + 8 ≤ (run b s u).value := by
      apply Classical.byContradiction
      intro hnot
      have hle : value b s u ≤ ((b + p_pen + 1 : Nat) : Int) + 6 := by
        change ((run b s u).value : Int) ≤ _; omega
      exact (original_win_source_finite_capacity b s u).2 p_pen p_last
        hpen_mem.1 hpen_lt_last hpen_mem.2.1 hpen_mem.2.2 hlast_mem.2.2 hle
    -- First hit `p0` satisfies `u + 3 ≤ p0` since `(p0 - u) % 4 = 3`!
    have hp0_mem := hmem_dl p0 (List.mem_cons_self ..)
    have hp0_mod : (p0 - u) % 4 = 3 := win_length_mod_four (replaySign b s) u (p0 - u) hp0_mem.2.2
    have hp0_lb : u + 3 ≤ p0 := by omega
    have hrest_len : rest.length = ps.length - 2 := by
      rw [hdl] at hdl_len
      simp only [List.length_cons] at hdl_len
      omega
    have hmain : (b + u) + 11 + 8 * (ps.length - 2) + 4 * ((ps.length - 2) / 2) ≤ (run b s u).value := by
      change p0 + 8 * rest.length + 4 * (rest.length / 2) ≤ p_pen at hspan
      rw [hrest_len] at hspan
      omega
    refine ⟨hmain, ?_⟩
    -- Notice `8 * k + 4 * (k / 2) ≥ 10 * k - 2`, so `10 * k ≤ y - a - 9`!
    omega

/-! ## Part 3: Raw non-fresh negative control & canonical orbit specialization -/

/-- Exact raw non-fresh negative control (`E-760`): on `rawNonFreshWord = SSAA ++ Z ++ Z ++ A`
(length 21), `rawNonFreshSign` has three `A` hits at `4, 12, 20` sharing unchanged
original `Win` source `1` with all heights `≤ 1`, yet `20 - 4 = 16 < 20 = 8 * 2 + 4 * (2 / 2)`.
Thus `S`-freshness is strictly necessary for `fresh_common_source_hit_span`. -/
theorem raw_nonfresh_counterexample_beats_fresh_span :
    rawNonFreshSign 4 = true ∧ rawNonFreshSign 12 = true ∧ rawNonFreshSign 20 = true ∧
      Win rawNonFreshSign 1 3 ∧ Win rawNonFreshSign 1 11 ∧ Win rawNonFreshSign 1 19 ∧
      (∀ i, i ≤ 21 → Fw rawNonFreshSign i ≤ 1) ∧
      20 - 4 < 8 * 2 + 4 * (2 / 2) := by
  refine ⟨rfl, rfl, rfl, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, ?_, by decide⟩
  intro i hi
  have hall : (List.range 22).all (fun k => decide (Fw rawNonFreshSign k ≤ 1)) = true := by decide
  have hm := List.all_eq_true.mp hall i (List.mem_range.mpr (by omega))
  exact decide_eq_true_eq.mp hm

/-- Unconditional specialization of `fresh_common_source_hit_span` and
`original_win_source_clock_capacity` directly to the canonical clock-0 Recamán orbit
`Recaman.Basic.a`. -/
theorem canonical_orbit_fresh_source_spacing (u : Nat) :
    (∀ (p0 : Nat) (rest : List Nat), (p0 :: rest).Pairwise (· < ·) →
      (∀ p ∈ p0 :: rest, u ≤ p ∧ canonicalOrbitSign p = true ∧ Win canonicalOrbitSign u (p - u)) →
      p0 + 8 * rest.length + 4 * (rest.length / 2) ≤
        (p0 :: rest).getLast (List.cons_ne_nil p0 rest)) ∧
    (∀ ps : List Nat, ps.Pairwise (· < ·) → 2 ≤ ps.length →
      (∀ p ∈ ps, u ≤ p ∧ canonicalOrbitSign p = true ∧ Win canonicalOrbitSign u (p - u)) →
      u + 11 + 8 * (ps.length - 2) + 4 * ((ps.length - 2) / 2) ≤ a u ∧
        ps.length ≤ 2 + (a u - u - 9) / 10) := by
  have hrun_eq : ∀ t, run 0 initial t = stateAt t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      change step (0 + t + 1) (run 0 initial t) = step (t + 1) (stateAt t)
      rw [Nat.zero_add, ih]
  have ha_eq : (run 0 initial u).value = a u := by unfold a; rw [hrun_eq u]
  constructor
  · intro p0 rest hsort hmem
    exact fresh_common_source_hit_span 0 initial u p0 rest hsort hmem
  · intro ps hsort hM hmem
    have h := original_win_source_clock_capacity 0 initial u ps hsort hM hmem
    rw [Nat.zero_add, ha_eq] at h
    exact h

end Recaman.FreshSourceHitSpacing
