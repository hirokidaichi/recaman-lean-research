import Recaman.SharpResidualKernel
import Recaman.OrbitBounds
import Recaman.EventualEscape
import Recaman.DriftResetAccumulation

/-!
# Global Unboundedness and Supply Obstruction Synthesis

This module synthesizes the sharp residual kernel (`SharpResidualKernel`),
value growth laws, and Theme 4 unsupplied additions accumulation (`DriftResetAccumulation`)
to establish global value unboundedness and structural supply obstructions.

Key results:
1. Triangular monotonicity:
   `upperTri_le_upperTri`, `upperTri_lt_upperTri`, and `lt_of_upperTri_lt_upperTri`.
2. Corridor linear unboundedness:
   In any `SharpCorridor`, values grow faster than the linear ray `n + target + 1`,
   escaping every ceiling after any prescribed cutoff.
3. Reset stream blocker and entry unboundedness:
   In any `SharpResetStream`, comb entries escape every ceiling after any cutoff,
   driven by unbounded blocker growth.
4. Universal missing tail unboundedness theorem:
   For any `MissingPermanentAboveTail target tailStart` and any cutoff `C` and bound `B`,
   there exists a time `n > C` such that `a n > B`.
5. Canonical sequence unboundedness:
   `canonical_orbit_unbounded` and `canonical_orbit_unbounded_after`.
6. Structural run obstruction:
   `consecutive_additions_unsupplied_deficit`:
   Any run of `K ≥ 3` consecutive additions forces at least `K - 2` unsupplied additions.
7. Local pattern exclusion under full supply:
   `no_three_consecutive_additions_if_all_supplied`:
   If all additions in a block are short-supplied, three consecutive additions (`AAA`) cannot occur.
-/

namespace Recaman.GlobalUnboundednessSupply

open Recaman
open Recaman.ShortPeriodicSupply
open Recaman.CanonicalSSFreeSupply
open Recaman.DriftResetAccumulation

/-- Upper triangular numbers are monotonically non-decreasing. -/
theorem upperTri_le_upperTri {a b : Nat} (h : a ≤ b) : upperTri a ≤ upperTri b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this
    exact Nat.le_refl _
  | succ b ih =>
    by_cases hab : a ≤ b
    · have h1 := ih hab
      have h2 : upperTri b ≤ upperTri (b + 1) := by
        simp [upperTri]
        omega
      exact Nat.le_trans h1 h2
    · have : a = b + 1 := by omega
      subst this
      exact Nat.le_refl _

/-- Upper triangular numbers are strictly increasing. -/
theorem upperTri_lt_upperTri {a b : Nat} (h : a < b) : upperTri a < upperTri b := by
  have hsucc_le : a + 1 ≤ b := h
  have h1 : upperTri a < upperTri (a + 1) := by
    simp [upperTri]
    omega
  have h2 : upperTri (a + 1) ≤ upperTri b := upperTri_le_upperTri hsucc_le
  exact Nat.lt_of_lt_of_le h1 h2

/-- Reflection: strict inequality of upper triangular numbers reflects to indices. -/
theorem lt_of_upperTri_lt_upperTri {a b : Nat} (h : upperTri a < upperTri b) : a < b := by
  by_cases hle : b ≤ a
  · have hle_tri := upperTri_le_upperTri hle
    omega
  · omega

/-- In any sharp corridor, values exceed every ceiling after any prescribed cutoff. -/
theorem corridor_values_unbounded_after
    {target tailStart cutoff : Nat}
    (hcorridor : SharpCorridor target tailStart cutoff)
    (c B : Nat) :
    ∃ n, c < n ∧ B < a n := by
  let n := (cutoff + c + 1) + (B + 1)
  have hcutoff : cutoff < n := by dsimp [n]; omega
  have hc : c < n := by dsimp [n]; omega
  have hval := hcorridor.value_law n hcutoff
  refine ⟨n, hc, ?_⟩
  dsimp [n] at *
  omega

/-- In any sharp reset stream, comb entries exceed every ceiling after any prescribed cutoff. -/
theorem reset_stream_values_unbounded_after
    {target tailStart root rootFirstTime : Nat}
    (hstream : SharpResetStream target tailStart root rootFirstTime)
    (c B : Nat) :
    ∃ n, c < n ∧ B < a n := by
  let targetCeiling := B + upperTri c + 1
  rcases hstream.blockers_unbounded targetCeiling with
    ⟨start, length, blocker, _htail, _hlow, hcomb, hblocker⟩
  have hentry := hcomb.entry_eq_blocker_add_length
  have hval_gt_blocker : blocker < a start := by omega
  have hblocker_gt_tri : upperTri c < blocker := by
    dsimp [targetCeiling] at hblocker
    omega
  have hval_gt_B : B < a start := by
    dsimp [targetCeiling] at hblocker
    omega
  have hval_le_tri := a_le_upperTri start
  have htri_lt : upperTri c < upperTri start := by
    calc
      upperTri c < blocker := hblocker_gt_tri
      _ < a start := hval_gt_blocker
      _ ≤ upperTri start := hval_le_tri
  have hc_lt_start := lt_of_upperTri_lt_upperTri htri_lt
  exact ⟨start, hc_lt_start, hval_gt_B⟩

/-- **Universal Value Unboundedness in Missing Tails.**
In any hypothetical missing permanent tail, the sequence values strictly escape
every ceiling after any prescribed cutoff. -/
theorem missing_permanent_tail_values_unbounded_after
    {target tailStart : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (cutoff B : Nat) :
    ∃ n, cutoff < n ∧ B < a n := by
  rcases htail.sharpResidualKernel with ⟨c, hcorridor⟩ | ⟨root, rootFirstTime, hstream⟩
  · exact corridor_values_unbounded_after hcorridor cutoff B
  · exact reset_stream_values_unbounded_after hstream cutoff B

/-- In any hypothetical missing permanent tail, values are strictly unbounded past tailStart. -/
theorem missing_permanent_tail_values_unbounded
    {target tailStart : Nat}
    (htail : MissingPermanentAboveTail target tailStart)
    (B : Nat) :
    ∃ n, tailStart < n ∧ B < a n :=
  missing_permanent_tail_values_unbounded_after htail tailStart B

/-- Global Unboundedness of the Canonical Recamán Sequence:
the canonical sequence values exceed every prescribed bound. -/
theorem canonical_orbit_unbounded (B : Nat) :
    ∃ n, B < a n := by
  rcases eventually_above_every_bound B with ⟨N, hN⟩
  exact ⟨N, hN N (Nat.le_refl N)⟩

/-- The canonical sequence values exceed every bound after any cutoff. -/
theorem canonical_orbit_unbounded_after (cutoff B : Nat) :
    ∃ n, cutoff < n ∧ B < a n := by
  rcases eventually_above_every_bound B with ⟨N, hN⟩
  let n := cutoff + 1 + N
  have hn_cutoff : cutoff < n := by dsimp [n]; omega
  have hn_N : N ≤ n := by dsimp [n]; omega
  exact ⟨n, hn_cutoff, hN n hn_N⟩

/-- Any run of K consecutive additions has net signSum equal to K. -/
theorem signSum_of_all_additions (e : Int → Bool) (t : Int) (K : Nat)
    (hall : ∀ i : Nat, i < K → e (t + (i : Int)) = true) :
    signSum e t K = (K : Int) := by
  induction K with
  | zero => simp [signSum]
  | succ K ih =>
    have hprev : ∀ i : Nat, i < K → e (t + (i : Int)) = true := fun i hi =>
      hall i (by omega)
    have ih_val := ih hprev
    have hlast := hall K (Nat.lt_succ_self K)
    simp only [signSum]
    rw [ih_val]
    simp [sign, hlast]

/-- Quantitative unsupplied deficit in any addition run:
any run of K ≥ 3 consecutive additions forces at least K - 2 unsupplied additions. -/
theorem consecutive_additions_unsupplied_deficit (e : Int → Bool) (t : Int) (K : Nat)
    (_hK : 3 ≤ K)
    (hall : ∀ i : Nat, i < K → e (t + (i : Int)) = true) :
    (K - 2 : Int) ≤ (unsuppliedCount e t K : Int) := by
  have hdrift := signSum_of_all_additions e t K hall
  have hd := unsuppliedCount_ge_signSum_sub_two e t K
  rw [hdrift] at hd
  exact hd

/-- A run of 3 consecutive additions must contain at least one unsupplied addition. -/
theorem three_consecutive_additions_unsupplied (e : Int → Bool) (t : Int)
    (h0 : e t = true)
    (h1 : e (t + 1) = true)
    (h2 : e (t + 2) = true) :
    1 ≤ unsuppliedCount e t 3 := by
  have hall : ∀ i : Nat, i < 3 → e (t + (i : Int)) = true := by
    intro i hi
    cases i with
    | zero =>
      have : t + ((0 : Nat) : Int) = t := by omega
      rw [this]; exact h0
    | succ i =>
      cases i with
      | zero =>
        have : t + ((1 : Nat) : Int) = t + 1 := by omega
        rw [this]; exact h1
      | succ i =>
        cases i with
        | zero =>
          have : t + ((2 : Nat) : Int) = t + 2 := by omega
          rw [this]; exact h2
        | succ i => omega
  have hd := consecutive_additions_unsupplied_deficit e t 3 (by omega) hall
  omega

/-- Pattern exclusion:
If all additions across an interval are short-supplied, three consecutive additions (`AAA`)
cannot occur anywhere within that interval. -/
theorem no_three_consecutive_additions_if_all_supplied (e : Int → Bool) (t : Int)
    (h_all_supplied : unsuppliedCount e t 3 = 0) :
    ¬ (e t = true ∧ e (t + 1) = true ∧ e (t + 2) = true) := by
  intro ⟨h0, h1, h2⟩
  have hpos := three_consecutive_additions_unsupplied e t h0 h1 h2
  omega

end Recaman.GlobalUnboundednessSupply
