import Recaman.LagSevenDonorCoverage

/-!
# PairedSubtractionCoverage: short minimal windows over the older member of an SS pair

Convention throughout: `past e u d = [e (u-1), e (u-2), ..., e (u-d)]` (newest first),
`true` = A (addition), `false` = S (subtraction); bit `k` (0-based) of `past e u d` is the sign
at clock `u - 1 - k` (`past_getD`). A clock `s` is a *paired older subtraction* when
`e s = false` and `e (s + 1) = false`, i.e. `s` is the older member of an adjacent SS pair.

This is a local, bit-level lemma on the G1 route (research plan P2). A paired older subtraction
can never lie inside a minimal lag-3 window (`AAS`), and if it lies inside a minimal lag-7 window
(`w1 = SAAAASS` or `w2 = ASAASAS`) then the window is `w1` and the subtraction is its oldest
bit, clock `u - 7`. The reason is purely positional: the newer neighbour of window bit `k ≥ 1`
is bit `k - 1`, and the newer neighbour of bit `0` is the addition `u` itself, so the paired-S
check `pairedAt` can only pass at an S bit whose next-newer window bit is also S.

## What is proved

1. `pairedAt_aas`: no bit of `[true, true, false]` passes the paired-S check `pairedAt`.
2. `pairedAt_lag7`: among the bits of `w1` and `w2`, only bit 6 of `w1` passes `pairedAt`.
3. `pairedAt_of_stream`: the stream hypotheses (`e u = true`, `PairedOlderS e s` and
   `u - 1 - k = s`) force `pairedAt (past e u d) k = true` for every `k < d`.
4. `aas_window_no_paired_older`: a paired older subtraction never lies inside a lag-3 window
   `past e u 3 = AAS` under an addition `u`.
5. `lag7_window_paired_older`: if `past e u 7 ∈ {w1, w2}`, `e u = true` and a paired older
   subtraction `s` lies inside the window, then `past e u 7 = w1` and `s = u - 7`.
6. `w2_window_no_paired_older`: the `w2` case of item 5 is impossible.
7. `minimal_lag7_window_paired_older`: item 5 with the membership hypothesis replaced by
   "`past e u 7` is a P2 word with no proper P2 prefix" via `lag7_minimal_lag7_must_be_w1_or_w2`.
8. `aas_window_no_paired_older_of_p2`: item 4 with `past e u 3 = AAS` replaced by
   `P2 (past e u 3)` via `p2_length_three_eq_aas`.

## What is not proved

Nothing here concerns tight subsets, Hall's condition or deletability, periodicity, windows of
lag ≥ 11, or Gate T6. The lemmas say only which bits of the three short minimal words can sit on
the older member of an adjacent SS pair; they do not assert that any such placement occurs in a
positive-sum periodic word, and they say nothing about the newer member of the pair.
-/

namespace Recaman.PairedSubtractionCoverage

open Recaman.LeadingRunSupply (past P2)
open Recaman.LagSevenPrefixRigidity (w1 w2 isP2Word lag7_minimal_lag7_must_be_w1_or_w2)
open Recaman.TwoSSEndpoint (hasP2Prefix)
open Recaman.TwoSSLeadingSibling (past_length)
open Recaman.LagSevenDonorCoverage (past_getD)
open Recaman.TightP2ParityRigidity (p2_length_three_eq_aas)

/-- `s` is the older subtraction of an adjacent SS pair. -/
def PairedOlderS (e : Int → Bool) (s : Int) : Prop := e s = false ∧ e (s + 1) = false

/-- Bit-level check: index `k` of word `v` holds an S whose newer neighbour (index `k - 1`, or
the addition `u` when `k = 0`) is also S. -/
def pairedAt (v : List Bool) (k : Nat) : Bool :=
  (v.getD k true == false) && decide (0 < k) && (v.getD (k - 1) true == false)

/-- No bit of the minimal lag-3 word `AAS` passes the paired-S check. -/
theorem pairedAt_aas : ∀ k ∈ List.range 3, pairedAt [true, true, false] k = false := by
  decide

set_option maxRecDepth 100000 in
/-- Among the bits of the two minimal lag-7 words, only bit 6 of `w1` passes the paired-S check. -/
theorem pairedAt_lag7 :
    ∀ v ∈ [w1, w2], ∀ k ∈ List.range 7, pairedAt v k = true → v = w1 ∧ k = 6 := by
  decide

/-- The stream hypotheses force `pairedAt` on the actual past word at the covering index. -/
theorem pairedAt_of_stream (e : Int → Bool) (u s : Int) (d k : Nat) (hk : k < d)
    (huA : e u = true) (hs : PairedOlderS e s) (hpos : u - 1 - (k : Int) = s) :
    pairedAt (past e u d) k = true := by
  obtain ⟨hs0, hs1⟩ := hs
  have hkpos : 0 < k := by
    by_cases h : k = 0
    · subst h
      have hx : s + 1 = u := by omega
      rw [hx, huA] at hs1
      exact absurd hs1 (by decide)
    · omega
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hjd : j < d := by omega
  have hx : u - 1 - (j : Int) = s + 1 := by omega
  unfold pairedAt
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨?_, hkpos⟩, ?_⟩
  · rw [past_getD e u d (j + 1) hk, hpos, hs0]
  · rw [Nat.add_sub_cancel, past_getD e u d j hjd, hx, hs1]

/-- A paired older subtraction never lies inside a lag-3 window `AAS` under an addition `u`. -/
theorem aas_window_no_paired_older (e : Int → Bool) (u s : Int)
    (hw : past e u 3 = [true, true, false]) (huA : e u = true) (hs : PairedOlderS e s)
    (hin : ∃ k : Nat, k < 3 ∧ u - 1 - (k : Int) = s) : False := by
  obtain ⟨k, hk, hpos⟩ := hin
  have h1 := pairedAt_of_stream e u s 3 k hk huA hs hpos
  have h2 := pairedAt_aas k (List.mem_range.mpr hk)
  rw [hw, h2] at h1
  exact absurd h1 (by decide)

/-- A paired older subtraction inside a minimal lag-7 window under an addition `u` forces the
window to be `w1` and the subtraction to be its oldest bit, clock `u - 7`. -/
theorem lag7_window_paired_older (e : Int → Bool) (u s : Int)
    (hw : past e u 7 = w1 ∨ past e u 7 = w2) (huA : e u = true) (hs : PairedOlderS e s)
    (hin : ∃ k : Nat, k < 7 ∧ u - 1 - (k : Int) = s) :
    past e u 7 = w1 ∧ s = u - 7 := by
  obtain ⟨k, hk, hpos⟩ := hin
  have hv : past e u 7 ∈ [w1, w2] := by
    rcases hw with h | h <;> simp [h]
  have hok := pairedAt_of_stream e u s 7 k hk huA hs hpos
  obtain ⟨hw1, hk6⟩ := pairedAt_lag7 (past e u 7) hv k (List.mem_range.mpr hk) hok
  refine ⟨hw1, ?_⟩
  subst hk6
  omega

/-- The minimal lag-7 word `w2 = ASAASAS` never contains a paired older subtraction. -/
theorem w2_window_no_paired_older (e : Int → Bool) (u s : Int)
    (hw : past e u 7 = w2) (huA : e u = true) (hs : PairedOlderS e s)
    (hin : ∃ k : Nat, k < 7 ∧ u - 1 - (k : Int) = s) : False := by
  obtain ⟨hw1, _⟩ := lag7_window_paired_older e u s (Or.inr hw) huA hs hin
  rw [hw] at hw1
  exact absurd hw1 (by decide)

/-- Item 5 with the window given semantically: `past e u 7` is P2 with no proper P2 prefix. -/
theorem minimal_lag7_window_paired_older (e : Int → Bool) (u s : Int)
    (hP : isP2Word (past e u 7) = true) (hmin : hasP2Prefix (past e u 7) = false)
    (huA : e u = true) (hs : PairedOlderS e s)
    (hin : ∃ k : Nat, k < 7 ∧ u - 1 - (k : Int) = s) :
    past e u 7 = w1 ∧ s = u - 7 :=
  lag7_window_paired_older e u s
    (lag7_minimal_lag7_must_be_w1_or_w2 (past e u 7) (past_length e u 7) hP hmin) huA hs hin

/-- Item 4 with the window given semantically: `past e u 3` is a P2 word (necessarily `AAS`). -/
theorem aas_window_no_paired_older_of_p2 (e : Int → Bool) (u s : Int)
    (hP : P2 (past e u 3)) (huA : e u = true) (hs : PairedOlderS e s)
    (hin : ∃ k : Nat, k < 3 ∧ u - 1 - (k : Int) = s) : False :=
  aas_window_no_paired_older e u s
    (p2_length_three_eq_aas (past e u 3) (past_length e u 3) hP) huA hs hin

end Recaman.PairedSubtractionCoverage
