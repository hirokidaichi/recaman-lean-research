import Recaman.ShortPeriodicSupply
import Recaman.CanonicalSSFreeSupply
import Recaman.FiniteSeedPeriodicSupply

/-!
# Finite Block Capacity and Boundary Defects

This module formalizes capacity bounds across arbitrary finite intervals (blocks)
for boolean sign sequences and exact Recamán orbits without requiring periodicity.

Key results:
1. `potential_nonneg` / `potential_le_two`:
   The 7-bit window potential satisfies `0 ≤ potential s ≤ 2` for all `s : Window`.
2. `potential_diff_le_two`:
   The variation of the potential between any two windows is bounded by `2`.
3. `chargeSum_le_two`:
   Across any finite interval of length `n`, `chargeSum e t n ≤ 2`.
4. `finite_block_capacity`:
   Unconditionally, `suppliedCount e t n ≤ subtractionCount e t n + 2`.
   The boundary defect is at most `2`, independent of block length `n`.
5. `finite_block_unsupplied_of_signSum_ge_three`:
   Any block with net upward drift `signSum ≥ 3` must contain at least one unsupplied addition.
6. `finite_block_unsupplied_deficit`:
   Quantitative deficit: `signSum - 2 ≤ additionCount - suppliedCount`.
7. `chargeSum_add`:
   Internal concatenation identity: `chargeSum` is additive across adjacent blocks.
8. `multiblock_composite_capacity`:
   Across any composite interval formed by concatenating `k` contiguous blocks,
   internal boundary defects cancel telescopically and the total defect remains `≤ 2`.
9. `seeded_orbit_finite_block_capacity` / `canonical_orbit_finite_block_capacity`:
   Application to exact seeded orbits and canonical Recamán sequence `a_0 = 0`.
-/

open Recaman.ShortPeriodicSupply
open Recaman.CanonicalSSFreeSupply
open Recaman.FiniteSeedPeriodicSupply

namespace Recaman.FiniteBlockCapacity

/-- Lower bound on the 7-bit window potential: always non-negative. -/
theorem potential_nonneg (s : Window) : 0 ≤ ShortPeriodicSupply.potential s := by
  revert s
  decide

/-- Upper bound on the 7-bit window potential: always at most 2. -/
theorem potential_le_two (s : Window) : ShortPeriodicSupply.potential s ≤ 2 := by
  revert s
  decide

/-- Potential variation between any two windows is bounded by 2. -/
theorem potential_diff_le_two (s1 s2 : Window) :
    ShortPeriodicSupply.potential s1 - ShortPeriodicSupply.potential s2 ≤ 2 := by
  have h1 := potential_le_two s1
  have h2 := potential_nonneg s2
  omega

/-- The total charge sum across any finite block of length n is bounded by 2. -/
theorem chargeSum_le_two (e : Int → Bool) (t : Int) (n : Nat) :
    chargeSum e t n ≤ 2 := by
  have h := chargeSum_le_potential e t n
  have hd := potential_diff_le_two (window e (t + (n : Int))) (window e t)
  omega

/-- Finite Block Capacity Theorem (Unconditional):
For any boolean sign sequence e (no periodicity required), any start time t, and any length n,
the number of short-supplied additions is bounded by the number of subtractions plus 2. -/
theorem finite_block_capacity (e : Int → Bool) (t : Int) (n : Nat) :
    suppliedCount e t n ≤ subtractionCount e t n + 2 := by
  have hc := chargeSum_le_two e t n
  rw [chargeSum_eq_counts] at hc
  omega

/-- Finite Block Excess/Drift Obstruction:
Whenever the positive drift across a block satisfies `signSum ≥ 3`,
there must exist at least one unsupplied addition within the block. -/
theorem finite_block_unsupplied_of_signSum_ge_three (e : Int → Bool) (t : Int) (n : Nat)
    (hdrift : 3 ≤ signSum e t n) :
    suppliedCount e t n < additionCount e t n := by
  have hcap := finite_block_capacity e t n
  have hcounts := signSum_eq_counts e t n
  omega

/-- Quantitative deficit: The number of unsupplied additions is at least `signSum - 2`. -/
theorem finite_block_unsupplied_deficit (e : Int → Bool) (t : Int) (n : Nat) :
    signSum e t n - 2 ≤ (additionCount e t n : Int) - (suppliedCount e t n : Int) := by
  have hcap := finite_block_capacity e t n
  have hcounts := signSum_eq_counts e t n
  omega

/-- Internal concatenation cancellation:
For contiguous blocks [t, t+n) and [t+n, t+n+m), the chargeSum is additive. -/
theorem chargeSum_add (e : Int → Bool) (t : Int) (n m : Nat) :
    chargeSum e t (n + m) = chargeSum e t n + chargeSum e (t + (n : Int)) m := by
  induction m with
  | zero => simp [chargeSum]
  | succ m ih =>
    have h1 : n + (m + 1) = (n + m) + 1 := by omega
    rw [h1]
    simp only [chargeSum]
    rw [ih]
    have hT1 : t + ((n + m : Nat) : Int) = (t + (n : Int)) + (m : Int) := by omega
    rw [hT1]
    omega

/-- Multi-block internal interface theorem:
Across any composite interval of k contiguous blocks, the total defect remains ≤ 2,
independent of the number of blocks k. -/
theorem multiblock_composite_capacity (e : Int → Bool) (t : Int) (lengths : List Nat) :
    chargeSum e t lengths.sum ≤ 2 := by
  exact chargeSum_le_two e t lengths.sum

/-- Seeded orbit finite block capacity:
In any seeded Recamán orbit, across any interval of length n,
short supplied additions cannot exceed subtractions plus 2. -/
theorem seeded_orbit_finite_block_capacity (b : Nat) (s : State) (t : Int) (n : Nat) :
    suppliedCount (absoluteSign b s) t n ≤ subtractionCount (absoluteSign b s) t n + 2 :=
  finite_block_capacity (absoluteSign b s) t n

/-- Seeded orbit finite block drift obstruction:
Any interval in a seeded orbit with net drift ≥ 3 has an unsupplied addition. -/
theorem seeded_orbit_unsupplied_of_drift (b : Nat) (s : State) (t : Int) (n : Nat)
    (hdrift : 3 ≤ signSum (absoluteSign b s) t n) :
    suppliedCount (absoluteSign b s) t n < additionCount (absoluteSign b s) t n :=
  finite_block_unsupplied_of_signSum_ge_three (absoluteSign b s) t n hdrift

/-- Canonical Recamán orbit finite block capacity:
In the canonical sequence (a0 = 0), across any interval of length n,
short supplied additions cannot exceed subtractions plus 2. -/
theorem canonical_orbit_finite_block_capacity (t : Int) (n : Nat) :
    suppliedCount canonicalSign t n ≤ subtractionCount canonicalSign t n + 2 :=
  finite_block_capacity canonicalSign t n

/-- Canonical Recamán orbit finite block drift obstruction:
Any interval in the canonical orbit with net drift ≥ 3 has an unsupplied addition. -/
theorem canonical_orbit_unsupplied_of_drift (t : Int) (n : Nat)
    (hdrift : 3 ≤ signSum canonicalSign t n) :
    suppliedCount canonicalSign t n < additionCount canonicalSign t n :=
  finite_block_unsupplied_of_signSum_ge_three canonicalSign t n hdrift

end Recaman.FiniteBlockCapacity
