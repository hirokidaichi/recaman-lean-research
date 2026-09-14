import Recaman.ShortPeriodicSupply
import Recaman.CanonicalSSFreeSupply
import Recaman.FiniteBlockCapacity
import Recaman.CorridorDensityObstruction

/-!
# Drift Resets and Accumulation of Unsupplied Additions

This module formalizes the cumulative accumulation of short-unsupplied additions
across arbitrary intervals, multi-block partitions, and drift-reset regimes.

Key results:
1. `suppliedCount_le_additionCount`:
   The number of supplied additions is always bounded by the total number of additions.
2. `unsuppliedCount`:
   Definition of the exact unsupplied additions count:
   `unsuppliedCount e t n = additionCount e t n - suppliedCount e t n`.
3. Additivity of counts:
   `additionCount_add`, `subtractionCount_add`, `suppliedCount_add`, and `unsuppliedCount_add`.
4. Monotonicity of unsupplied additions:
   `unsuppliedCount e t n ≤ unsuppliedCount e t (n + m)`.
   The count of unsupplied additions is monotonically non-decreasing over time.
5. Drift deficit inequality:
   `(signSum e t n - 2 : Int) ≤ (unsuppliedCount e t n : Int)`.
   Whenever `3 ≤ signSum e t n`, at least `signSum - 2 ≥ 1` unsupplied additions are produced.
6. Multi-interval reset accumulation:
   Across disjoint intervals each having net drift `signSum ≥ 3`, the unsupplied additions
   accumulate additively regardless of intervening negative drift / resets.
7. Drift boundedness vs. infinite unsupplied additions dichotomy:
   If unsupplied additions are globally bounded, then net positive drift on all intervals
   is uniformly bounded; conversely, unbounded drift excursions force unbounded unsupplied additions.
8. Application to exact canonical Recamán sequence and corridor regimes.
-/

namespace Recaman.DriftResetAccumulation

open Recaman.ShortPeriodicSupply
open Recaman.CanonicalSSFreeSupply
open Recaman.FiniteBlockCapacity

/-- Supplied additions are always bounded by total additions. -/
theorem suppliedCount_le_additionCount (e : Int → Bool) (t : Int) (n : Nat) :
    suppliedCount e t n ≤ additionCount e t n := by
  induction n with
  | zero => simp [suppliedCount, additionCount]
  | succ n ih =>
    simp only [suppliedCount, additionCount]
    cases hb : e (t + (n : Int)) <;> cases hs : supplied (window e (t + (n : Int))) <;>
      dsimp <;> omega

/-- The exact number of additions in clocks t through t+n-1 that cannot be
supplied by any lag d ≤ 7. -/
def unsuppliedCount (e : Int → Bool) (t : Int) (n : Nat) : Nat :=
  additionCount e t n - suppliedCount e t n

/-- Unsupplied count is non-negative and equals the subtraction of counts. -/
theorem unsuppliedCount_eq (e : Int → Bool) (t : Int) (n : Nat) :
    (unsuppliedCount e t n : Int) = (additionCount e t n : Int) - (suppliedCount e t n : Int) := by
  have hle := suppliedCount_le_additionCount e t n
  simp [unsuppliedCount]
  omega

/-- Additivity of additionCount across adjacent intervals. -/
theorem additionCount_add (e : Int → Bool) (t : Int) (n m : Nat) :
    additionCount e t (n + m) = additionCount e t n + additionCount e (t + (n : Int)) m := by
  induction m with
  | zero => simp [additionCount]
  | succ m ih =>
    have h1 : n + (m + 1) = (n + m) + 1 := by omega
    rw [h1]
    simp only [additionCount]
    rw [ih]
    have hT : t + ((n + m : Nat) : Int) = (t + (n : Int)) + (m : Int) := by omega
    rw [hT]
    omega

/-- Additivity of subtractionCount across adjacent intervals. -/
theorem subtractionCount_add (e : Int → Bool) (t : Int) (n m : Nat) :
    subtractionCount e t (n + m) = subtractionCount e t n + subtractionCount e (t + (n : Int)) m := by
  induction m with
  | zero => simp [subtractionCount]
  | succ m ih =>
    have h1 : n + (m + 1) = (n + m) + 1 := by omega
    rw [h1]
    simp only [subtractionCount]
    rw [ih]
    have hT : t + ((n + m : Nat) : Int) = (t + (n : Int)) + (m : Int) := by omega
    rw [hT]
    omega

/-- Additivity of suppliedCount across adjacent intervals. -/
theorem suppliedCount_add (e : Int → Bool) (t : Int) (n m : Nat) :
    suppliedCount e t (n + m) = suppliedCount e t n + suppliedCount e (t + (n : Int)) m := by
  induction m with
  | zero => simp [suppliedCount]
  | succ m ih =>
    have h1 : n + (m + 1) = (n + m) + 1 := by omega
    rw [h1]
    simp only [suppliedCount]
    rw [ih]
    have hT : t + ((n + m : Nat) : Int) = (t + (n : Int)) + (m : Int) := by omega
    rw [hT]
    omega

/-- Additivity of signSum across adjacent intervals. -/
theorem signSum_add (e : Int → Bool) (t : Int) (n m : Nat) :
    signSum e t (n + m) = signSum e t n + signSum e (t + (n : Int)) m := by
  induction m with
  | zero => simp [signSum]
  | succ m ih =>
    have h1 : n + (m + 1) = (n + m) + 1 := by omega
    rw [h1]
    simp only [signSum]
    rw [ih]
    have hT : t + ((n + m : Nat) : Int) = (t + (n : Int)) + (m : Int) := by omega
    rw [hT]
    omega

/-- Additivity of unsuppliedCount across adjacent intervals:
unsupplied additions are strictly additive. -/
theorem unsuppliedCount_add (e : Int → Bool) (t : Int) (n m : Nat) :
    unsuppliedCount e t (n + m) = unsuppliedCount e t n + unsuppliedCount e (t + (n : Int)) m := by
  have hA := additionCount_add e t n m
  have hS := suppliedCount_add e t n m
  have hle1 := suppliedCount_le_additionCount e t n
  have hle2 := suppliedCount_le_additionCount e (t + (n : Int)) m
  dsimp [unsuppliedCount]
  rw [hA, hS]
  omega

/-- Monotonicity: The cumulative unsupplied addition count is non-decreasing over time. -/
theorem unsuppliedCount_mono (e : Int → Bool) (t : Int) (n m : Nat) :
    unsuppliedCount e t n ≤ unsuppliedCount e t (n + m) := by
  rw [unsuppliedCount_add]
  omega

/-- Drift deficit lower bound:
The unsupplied count on any interval [t, t+n) is at least `signSum - 2`. -/
theorem unsuppliedCount_ge_signSum_sub_two (e : Int → Bool) (t : Int) (n : Nat) :
    signSum e t n - 2 ≤ (unsuppliedCount e t n : Int) := by
  have hd := finite_block_unsupplied_deficit e t n
  rw [unsuppliedCount_eq]
  exact hd

/-- Positive drift forces at least one unsupplied addition. -/
theorem unsuppliedCount_pos_of_signSum_ge_three (e : Int → Bool) (t : Int) (n : Nat)
    (hdrift : 3 ≤ signSum e t n) :
    1 ≤ unsuppliedCount e t n := by
  have hd := unsuppliedCount_ge_signSum_sub_two e t n
  omega

/-- Strict deficit: If signSum ≥ K with K ≥ 2, unsuppliedCount ≥ K - 2. -/
theorem unsuppliedCount_ge_of_signSum (e : Int → Bool) (t : Int) (n : Nat) (K : Int)
    (_hK : 2 ≤ K) (hdrift : K ≤ signSum e t n) :
    (K - 2 : Int) ≤ (unsuppliedCount e t n : Int) := by
  have hd := unsuppliedCount_ge_signSum_sub_two e t n
  omega

/-- Two-block accumulation across intervening reset:
Given two disjoint intervals [t, t + n1) and [t + n1 + g, t + n1 + g + n2) separated
by an arbitrary gap of length g (which may have severe downward reset),
the total unsupplied count across the entire span is at least the sum of unsupplied counts
on both blocks. Downward resets cannot erase unsupplied additions! -/
theorem unsuppliedCount_two_blocks (e : Int → Bool) (t : Int) (n1 g n2 : Nat) :
    unsuppliedCount e t n1 + unsuppliedCount e (t + (n1 : Int) + (g : Int)) n2 ≤
    unsuppliedCount e t (n1 + g + n2) := by
  have h1 : n1 + g + n2 = n1 + (g + n2) := by omega
  rw [h1, unsuppliedCount_add e t n1 (g + n2)]
  have h2 : unsuppliedCount e (t + (n1 : Int)) (g + n2) =
      unsuppliedCount e (t + (n1 : Int)) g + unsuppliedCount e (t + (n1 : Int) + (g : Int)) n2 := by
    exact unsuppliedCount_add e (t + (n1 : Int)) g n2
  rw [h2]
  omega

/-- If two disjoint intervals each have net drift ≥ 3, the span contains at least 2 unsupplied additions,
even if the intervening gap has negative drift. -/
theorem unsuppliedCount_ge_two_of_two_drift_blocks (e : Int → Bool) (t : Int) (n1 g n2 : Nat)
    (hdrift1 : 3 ≤ signSum e t n1)
    (hdrift2 : 3 ≤ signSum e (t + (n1 : Int) + (g : Int)) n2) :
    2 ≤ unsuppliedCount e t (n1 + g + n2) := by
  have hu1 := unsuppliedCount_pos_of_signSum_ge_three e t n1 hdrift1
  have hu2 := unsuppliedCount_pos_of_signSum_ge_three e (t + (n1 : Int) + (g : Int)) n2 hdrift2
  have hacc := unsuppliedCount_two_blocks e t n1 g n2
  omega

/-- Drift Boundedness Theorem:
If the unsupplied addition count on all sub-intervals is bounded by K,
then the net positive drift across all sub-intervals is uniformly bounded by K + 2. -/
theorem drift_le_of_unsupplied_le (e : Int → Bool) (t : Int) (n : Nat) (K : Nat)
    (hbound : unsuppliedCount e t n ≤ K) :
    signSum e t n ≤ (K : Int) + 2 := by
  have hd := unsuppliedCount_ge_signSum_sub_two e t n
  omega

/-- Unbounded Drift Excursion forces Unbounded Unsupplied Additions:
If for every bound M there exists an interval with drift ≥ M,
then the unsupplied addition count can also exceed any prescribed threshold. -/
theorem exists_unsupplied_ge_of_exists_signSum_ge (e : Int → Bool) (t : Int) (M : Nat) :
    (∃ n : Nat, (M : Int) + 2 ≤ signSum e t n) →
    (∃ n : Nat, M ≤ unsuppliedCount e t n) := by
  intro ⟨n, hn⟩
  have hd := unsuppliedCount_ge_signSum_sub_two e t n
  refine ⟨n, ?_⟩
  omega

/-- Canonical Recamán Sequence: unsupplied additions are monotonically non-decreasing over time. -/
theorem canonical_unsuppliedCount_mono (t : Int) (n m : Nat) :
    unsuppliedCount canonicalSign t n ≤ unsuppliedCount canonicalSign t (n + m) :=
  unsuppliedCount_mono canonicalSign t n m

/-- Canonical Recamán Sequence: drift deficit inequality. -/
theorem canonical_unsuppliedCount_ge_drift (t : Int) (n : Nat) :
    signSum canonicalSign t n - 2 ≤ (unsuppliedCount canonicalSign t n : Int) :=
  unsuppliedCount_ge_signSum_sub_two canonicalSign t n

/-- Corridor Unsupplied Accumulation:
In any corridor of a least missing target, any two disjoint drift episodes
accumulate at least 2 unsupplied additions. -/
theorem corridor_unsupplied_two_drift_blocks (t : Int) (n1 g n2 : Nat)
    (hdrift1 : 3 ≤ signSum canonicalSign t n1)
    (hdrift2 : 3 ≤ signSum canonicalSign (t + (n1 : Int) + (g : Int)) n2) :
    2 ≤ unsuppliedCount canonicalSign t (n1 + g + n2) :=
  unsuppliedCount_ge_two_of_two_drift_blocks canonicalSign t n1 g n2 hdrift1 hdrift2

end Recaman.DriftResetAccumulation
