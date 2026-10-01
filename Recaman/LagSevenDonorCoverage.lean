import Recaman.LagSevenPrefixRigidity
import Recaman.SS2LagElevenForcing

/-!
# LagSevenDonorCoverage: lag-7 coverers of the oldest subtraction of an SS=2 lag-11 donor

Convention throughout: `past e u d = [e (u-1), e (u-2), ..., e (u-d)]` (newest first),
`true` = A (addition), `false` = S (subtraction). A "donor" is a minimal P2 window of
length 11 with `ssCount = 2`; its oldest subtraction is the S bit at the largest offset
(`oldestOffset`). A "lag-7 coverer" is an addition `u` whose minimal lag-7 window
(`past e u 7 = w1` or `w2`, the two minimal lag-7 P2 words) contains the donor's oldest
subtraction position `u0 - oldestOffset`.

## What is proved

1. `minimal_ss2_eleven_words`: the length-11 words that are P2, have no proper P2 prefix and
   have `ssCount = 2` are exactly the seven words `d1, ..., d7` (checked by `decide` over
   `bitWords 11`); `minimal_ss2_eleven_mem_donors` and `minimal_ss2_lt_fifteen_mem_donors`
   restate this at the `Prop` level (the latter via `minimal_ss2_lag_lt_fifteen_eq_eleven`).
2. `oldestOffset_donors` / `oldestOffset_is_oldest_S`: the oldest subtraction of the donor sits
   at offset 10 for `d1, d2, d3, d6` and at offset 11 for `d4, d5, d7`.
3. `lag7_cover_classification` (Theorem A): if `past e u0 11` is one of the seven donors,
   `e u = true`, `past e u 7 ∈ {w1, w2}`, and some bit of the lag-7 window at `u` sits on the
   donor's oldest subtraction, then the window is `w1 = SAAAASS`, its newest bit is the covered
   subtraction (`u = u0 - oldestOffset + 1`), and the donor is `d1`, `d2` or `d4`.
   `lag7_cover_classification_explicit` spells out `u = u0 - 9` (for `d1`, `d2`) and
   `u = u0 - 10` (for `d4`); `lag7_cover_impossible_d3_d5_d6_d7` records that the other four
   donors have no lag-7 coverer at all; `lag7_cover_classification_of_minimal` replaces the
   membership hypothesis by `ShortPeriodicSupply.P2 e u0 11`, minimality and `ssCount = 2`.

The proof of Theorem A is purely combinatorial on bits: `coverOK` is a Boolean check that every
window bit lying inside the donor agrees with the donor bit and that `u` itself is an A bit of
the donor; `coverOK_of_stream` derives it once, generically, from the stream hypotheses via
`past_getD`, and `coverOK_classification` decides all 7 × 2 × 7 placements at once.

## What is not proved

This module does not prove Gate T6, says nothing about tight subsets, Hall's condition or
deletability, and says nothing about windows of lag ≥ 11 (or of lag 3) covering the donor's
oldest subtraction. No periodicity is assumed or concluded, and nothing here asserts that the
three surviving configurations actually occur in any positive-sum periodic word.
-/

namespace Recaman.LagSevenDonorCoverage

open Recaman.LeadingRunSupply (past P2 mass moment past_p2_iff)
open Recaman.LagSevenPrefixRigidity (w1 w2 isP2Word)
open Recaman.TwoSSEndpoint (bitWords hasP2Prefix mem_bitWords)
open Recaman.OneSSMultiplicity (ssCount)
open Recaman.TwoSSLeadingSibling (past_length)
open Recaman.SS2LagElevenForcing (minimal_ss2_lag_lt_fifteen_eq_eleven)

/-- Donor `AAASSSASASA` (newest first). -/
def d1 : List Bool := [true, true, true, false, false, false, true, false, true, false, true]
/-- Donor `ASAAASSSASA`. -/
def d2 : List Bool := [true, false, true, true, true, false, false, false, true, false, true]
/-- Donor `ASASAAASSSA`. -/
def d3 : List Bool := [true, false, true, false, true, true, true, false, false, false, true]
/-- Donor `ASSAAAASSAS`. -/
def d4 : List Bool := [true, false, false, true, true, true, true, false, false, true, false]
/-- Donor `ASSAAASAASS`. -/
def d5 : List Bool := [true, false, false, true, true, true, false, true, true, false, false]
/-- Donor `SAAASAASSSA`. -/
def d6 : List Bool := [false, true, true, true, false, true, true, false, false, false, true]
/-- Donor `SAAASSAAASS`. -/
def d7 : List Bool := [false, true, true, true, false, false, true, true, true, false, false]

/-- The seven SS=2 lag-11 donor words. -/
def donors : List (List Bool) := [d1, d2, d3, d4, d5, d6, d7]

/-- The two minimal lag-7 P2 words `w1 = SAAAASS` and `w2 = ASAASAS`. -/
def lag7Words : List (List Bool) := [w1, w2]

theorem mem_donors_iff (w : List Bool) :
    w ∈ donors ↔ w = d1 ∨ w = d2 ∨ w = d3 ∨ w = d4 ∨ w = d5 ∨ w = d6 ∨ w = d7 := by
  simp [donors]

/-- The largest 1-based offset (newest first) holding an S, or `0` if the word has no S. -/
def oldestOffset : List Bool → Nat
  | [] => 0
  | b :: w => if oldestOffset w = 0 then (if b then 0 else 1) else oldestOffset w + 1

/-- Oldest-subtraction offsets of the seven donors: 10 for `d1, d2, d3, d6`, 11 for `d4, d5, d7`. -/
theorem oldestOffset_donors :
    oldestOffset d1 = 10 ∧ oldestOffset d2 = 10 ∧ oldestOffset d3 = 10 ∧ oldestOffset d4 = 11 ∧
    oldestOffset d5 = 11 ∧ oldestOffset d6 = 10 ∧ oldestOffset d7 = 11 := by
  decide

/-- On every donor, `oldestOffset` points at an S bit and every older bit is A. -/
theorem oldestOffset_is_oldest_S :
    ∀ w ∈ donors, w.getD (oldestOffset w - 1) true = false ∧
      ∀ j ∈ List.range 11, oldestOffset w ≤ j → w.getD j true = true := by
  decide

/-- Explicit form of the length-11 past window (analogue of `past_seven`). -/
theorem past_eleven (e : Int → Bool) (u : Int) :
    past e u 11 = [e (u - 1), e (u - 2), e (u - 3), e (u - 4), e (u - 5), e (u - 6),
      e (u - 7), e (u - 8), e (u - 9), e (u - 10), e (u - 11)] := by
  unfold past
  rfl

/-- Bit `j` (0-based, newest first) of `past e t d` is the sign at clock `t - 1 - j`. -/
theorem past_getD (e : Int → Bool) (t : Int) (d j : Nat) (hj : j < d) (b : Bool) :
    (past e t d).getD j b = e (t - 1 - (j : Int)) := by
  unfold past
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  simp only [Option.map_some, Option.getD_some]
  congr 1
  omega

/-- Bit-level compatibility of a lag-7 word `v` placed on a donor word `w` so that window bit
`k` (0-based, newest first) sits on donor offset `off`, i.e. `u - 1 - k = u0 - off`.
Window bit `m` sits at clock `u - 1 - m` and donor bit `j` at clock `u0 - 1 - j`; they coincide
iff `j + k + 1 = m + off`, and `u` itself coincides with donor bit `j` iff `j + k + 2 = off`.
The check demands agreement on every coincidence and an A bit under `u`. -/
def coverOK (w v : List Bool) (off k : Nat) : Bool :=
  ((List.range 7).all fun m => (List.range 11).all fun j =>
      !(j + k + 1 == m + off) || (v.getD m true == w.getD j true)) &&
  ((List.range 11).all fun j => !(j + k + 2 == off) || w.getD j true)

/-- The stream hypotheses force `coverOK` on the actual past words, for any `off` and `k`. -/
theorem coverOK_of_stream (e : Int → Bool) (u0 u : Int) (off k : Nat)
    (huA : e u = true) (hpos : u - 1 - (k : Int) = u0 - (off : Int)) :
    coverOK (past e u0 11) (past e u 7) off k = true := by
  unfold coverOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨fun m hm j hj => ?_, fun j hj => ?_⟩
  · by_cases h : j + k + 1 = m + off
    · have hx : u - 1 - (m : Int) = u0 - 1 - (j : Int) := by omega
      rw [past_getD e u 7 m hm, past_getD e u0 11 j hj, hx]
      simp [h]
    · simp [h]
  · by_cases h : j + k + 2 = off
    · have hx : u0 - 1 - (j : Int) = u := by omega
      rw [past_getD e u0 11 j hj, hx, huA]
      simp
    · simp [h]

set_option maxRecDepth 100000 in
/-- Finite core: among all 7 donors × 2 lag-7 words × 7 placements of the covered subtraction,
only `k = 0`, `v = w1` and `w ∈ {d1, d2, d4}` pass the bit check. -/
theorem coverOK_classification :
    ∀ w ∈ donors, ∀ v ∈ lag7Words, ∀ k ∈ List.range 7,
      coverOK w v (oldestOffset w) k = true →
        k = 0 ∧ v = w1 ∧ (w = d1 ∨ w = d2 ∨ w = d4) := by
  decide

/-- Theorem A. A minimal lag-7 window at `u` covering the oldest subtraction of an SS=2 lag-11
donor at `u0` must be `w1`, must cover it with its newest bit (`u = u0 - oldestOffset + 1`),
and the donor must be `d1`, `d2` or `d4`. -/
theorem lag7_cover_classification (e : Int → Bool) (u0 u : Int)
    (hdon : past e u0 11 ∈ donors)
    (huA : e u = true)
    (hw : past e u 7 = w1 ∨ past e u 7 = w2)
    (hcov : ∃ k : Nat, k < 7 ∧ e (u - 1 - (k : Int)) = false ∧
      u - 1 - (k : Int) = u0 - (oldestOffset (past e u0 11) : Int)) :
    past e u 7 = w1 ∧ u = u0 - (oldestOffset (past e u0 11) : Int) + 1 ∧
      (past e u0 11 = d1 ∨ past e u0 11 = d2 ∨ past e u0 11 = d4) := by
  obtain ⟨k, hk, _hS, hpos⟩ := hcov
  have hv : past e u 7 ∈ lag7Words := by
    rcases hw with h | h <;> simp [lag7Words, h]
  have hok := coverOK_of_stream e u0 u (oldestOffset (past e u0 11)) k huA hpos
  obtain ⟨hk0, hw1, hd⟩ :=
    coverOK_classification (past e u0 11) hdon (past e u 7) hv k (List.mem_range.mpr hk) hok
  refine ⟨hw1, ?_, hd⟩
  subst hk0
  omega

/-- Theorem A with the offsets written out: `u = u0 - 9` for `d1`, `d2` and `u = u0 - 10` for `d4`. -/
theorem lag7_cover_classification_explicit (e : Int → Bool) (u0 u : Int)
    (hdon : past e u0 11 ∈ donors)
    (huA : e u = true)
    (hw : past e u 7 = w1 ∨ past e u 7 = w2)
    (hcov : ∃ k : Nat, k < 7 ∧ e (u - 1 - (k : Int)) = false ∧
      u - 1 - (k : Int) = u0 - (oldestOffset (past e u0 11) : Int)) :
    past e u 7 = w1 ∧
      ((past e u0 11 = d1 ∧ u = u0 - 9) ∨ (past e u0 11 = d2 ∧ u = u0 - 9) ∨
        (past e u0 11 = d4 ∧ u = u0 - 10)) := by
  obtain ⟨hw1, hu, hd⟩ := lag7_cover_classification e u0 u hdon huA hw hcov
  refine ⟨hw1, ?_⟩
  have hoff := oldestOffset_donors
  rcases hd with hd | hd | hd
  · left; refine ⟨hd, ?_⟩; rw [hd, hoff.1] at hu; omega
  · right; left; refine ⟨hd, ?_⟩; rw [hd, hoff.2.1] at hu; omega
  · right; right; refine ⟨hd, ?_⟩; rw [hd, hoff.2.2.2.1] at hu; omega

/-- The donors `d3`, `d5`, `d6`, `d7` have no minimal lag-7 coverer of their oldest subtraction. -/
theorem lag7_cover_impossible_d3_d5_d6_d7 (e : Int → Bool) (u0 u : Int)
    (hdon : past e u0 11 = d3 ∨ past e u0 11 = d5 ∨ past e u0 11 = d6 ∨ past e u0 11 = d7)
    (huA : e u = true)
    (hw : past e u 7 = w1 ∨ past e u 7 = w2)
    (hcov : ∃ k : Nat, k < 7 ∧ e (u - 1 - (k : Int)) = false ∧
      u - 1 - (k : Int) = u0 - (oldestOffset (past e u0 11) : Int)) : False := by
  have hmem : past e u0 11 ∈ donors := by
    rw [mem_donors_iff]
    rcases hdon with h | h | h | h <;> simp [h]
  obtain ⟨_, _, hd⟩ := lag7_cover_classification e u0 u hmem huA hw hcov
  rcases hdon with h | h | h | h <;> rcases hd with h' | h' | h' <;> rw [h] at h' <;>
    exact absurd h' (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
/-- Theorem B. The length-11 words that are P2, have no proper P2 prefix and have `ssCount = 2`
are exactly the seven donors (listed here in the enumeration order of `bitWords 11`). -/
theorem minimal_ss2_eleven_words :
    (bitWords 11).filter (fun w => isP2Word w && !hasP2Prefix w && ssCount w == 2) =
      [d5, d7, d4, d6, d3, d2, d1] := by
  decide

/-- `hasP2Prefix w = false` is the `Prop`-level "no proper P2 prefix" condition. -/
theorem hasP2Prefix_eq_false_iff (w : List Bool) :
    hasP2Prefix w = false ↔ ∀ d, d < w.length → 0 < d → ¬ P2 (w.take d) := by
  unfold hasP2Prefix
  rw [List.any_eq_false]
  constructor
  · intro h d hd hpos hP
    apply h d (List.mem_range.mpr hd)
    simp [hpos, hP.1, hP.2]
  · intro h d hd hb
    have hd' := List.mem_range.mp hd
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
    exact h d hd' hb.1.1 ⟨hb.1.2, hb.2⟩

/-- Every minimal P2 word of length 11 with `ssCount = 2` is one of the seven donors. -/
theorem minimal_ss2_eleven_mem_donors (w : List Bool) (hlen : w.length = 11) (hP : P2 w)
    (hmin : ∀ d, d < w.length → 0 < d → ¬ P2 (w.take d)) (hss : ssCount w = 2) :
    w ∈ donors := by
  have hmem : w ∈ bitWords 11 := by
    have := mem_bitWords w
    rwa [hlen] at this
  have hfilt : w ∈ (bitWords 11).filter
      (fun w => isP2Word w && !hasP2Prefix w && ssCount w == 2) := by
    rw [List.mem_filter]
    refine ⟨hmem, ?_⟩
    have h1 : isP2Word w = true := by
      unfold isP2Word
      simp [hP.1, hP.2]
    have h2 : hasP2Prefix w = false := (hasP2Prefix_eq_false_iff w).mpr hmin
    simp [h1, h2, hss]
  rw [minimal_ss2_eleven_words] at hfilt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfilt
  rw [mem_donors_iff]
  rcases hfilt with h | h | h | h | h | h | h <;> simp [h]

/-- Every minimal P2 word with `ssCount = 2` and length below 15 is one of the seven donors. -/
theorem minimal_ss2_lt_fifteen_mem_donors (w : List Bool) (hP : P2 w)
    (hmin : ∀ d, d < w.length → 0 < d → ¬ P2 (w.take d)) (hss : ssCount w = 2)
    (hlt : w.length < 15) :
    w ∈ donors :=
  minimal_ss2_eleven_mem_donors w (minimal_ss2_lag_lt_fifteen_eq_eleven w hP hmin hss hlt)
    hP hmin hss

/-- Theorem A with the donor given semantically: a P2 window of lag 11 at `u0` with no proper
P2 prefix and `ssCount = 2`, instead of explicit membership in `donors`. -/
theorem lag7_cover_classification_of_minimal (e : Int → Bool) (u0 u : Int)
    (hP : Recaman.ShortPeriodicSupply.P2 e u0 11)
    (hmin : ∀ d, d < 11 → 0 < d → ¬ P2 ((past e u0 11).take d))
    (hss : ssCount (past e u0 11) = 2)
    (huA : e u = true)
    (hw : past e u 7 = w1 ∨ past e u 7 = w2)
    (hcov : ∃ k : Nat, k < 7 ∧ e (u - 1 - (k : Int)) = false ∧
      u - 1 - (k : Int) = u0 - (oldestOffset (past e u0 11) : Int)) :
    past e u 7 = w1 ∧ u = u0 - (oldestOffset (past e u0 11) : Int) + 1 ∧
      (past e u0 11 = d1 ∨ past e u0 11 = d2 ∨ past e u0 11 = d4) := by
  have hdon : past e u0 11 ∈ donors :=
    minimal_ss2_eleven_mem_donors (past e u0 11) (past_length e u0 11)
      ((past_p2_iff e u0 11).mpr hP) (by rw [past_length]; exact hmin) hss
  exact lag7_cover_classification e u0 u hdon huA hw hcov

end Recaman.LagSevenDonorCoverage
