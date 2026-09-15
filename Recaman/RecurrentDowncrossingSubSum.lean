import Recaman.TailDowncrossingInevitability
import Recaman.TailDowncrossingDichotomy
import Recaman.TailDowncrossingLedger
import Recaman.EventualHighCorridorStructure
import Recaman.GlobalUnboundednessSupply

namespace Recaman

/-! # Recurrent Downcrossing Subtraction Ledger Divergence

This module formalizes the global divergence of the subtraction ledger mass
(`subSum`) and counter (`subCount`), both unconditionally for the entire
canonical Recamán orbit and specifically along recurrent downcrossings in
any hypothetical least-missing tail:

1. **Unconditional SubSum Unboundedness (`subSum_unbounded_after`)**:
   Because legal subtractions recur after every cutoff (`exists_canSubtract_of_ray`),
   every subtraction step `n + 1` books at least `n + 1` into `subSum`.
   Consequently, `subSum` strictly exceeds every ceiling `B` past any cutoff:
   `∀ cutoff B, ∃ u, cutoff ≤ u ∧ B < subSum u`.

2. **Unconditional SubCount Unboundedness (`subCount_unbounded_after`)**:
   By strong recurrence of legal subtractions, the subtraction counter `subCount`
   is also unbounded after any cutoff:
   `∀ cutoff B, ∃ u, cutoff ≤ u ∧ B ≤ subCount u`.

3. **Downcrossing Clock Deposit Bound (`downcrossing_deposit_exceeds_bound`)**:
   Every downcrossing step `k ≥ B` deposits its entire clock `k + 1` into `subSum`:
   `B < k + 1 ≤ subSum (k + 1)`.

4. **Tail Re-entry Ledger Divergence (`tail_downcrossing_reentry_ledger_divergence`)**:
   In any hypothetical least missing tail with certified minimum at `time`,
   any downcrossing step `k ≥ time` deposits at least `k + 1` on top of `subSum time`:
   `subSum time + (k + 1) ≤ subSum (k + 1)`.
   Its landing value re-enters the corridor, tightly sandwiching `upperTri (k + 1)`:
   `2 * (subSum time + (k + 1)) + (a time + 1) ≤ upperTri (k + 1) < 2 * subSum (k + 1) + 2 * (k + 1)`.

5. **Recurrent Downcrossing Ledger Growth (`recurrent_downcrossings_force_arbitrary_ledger_growth`)**:
   If downcrossings recur indefinitely, `subSum` at downcrossing re-entry steps
   exceeds arbitrary bounds while simultaneously satisfying the corridor bounds.

6. **Grand Recurrent Downcrossing SubSum Synthesis**:
   Unifies the unconditional ledger unboundedness, downcrossing clock deposits,
   tail ledger divergence, and corridor re-entry into a master synthesis theorem.
-/

/-! ### Part 1: Unconditional Ledger Unboundedness -/

/-- Any legal subtraction at step `n + 1` books at least `n + 1` into `subSum`. -/
theorem subSum_ge_of_canSubtract {n : Nat}
    (hcan : CanSubtract (n + 1) (stateAt n)) :
    n + 1 ≤ subSum (n + 1) := by
  rw [subSum_succ, if_pos hcan]
  omega

/-- **Unconditional SubSum Unboundedness After Any Cutoff**:
The subtraction ledger mass strictly exceeds every ceiling `B` past any prescribed cutoff. -/
theorem subSum_unbounded_after (cutoff B : Nat) :
    ∃ u, cutoff ≤ u ∧ B < subSum u := by
  let M := max cutoff B
  rcases exists_canSubtract_of_ray M with ⟨n, hn, hcan⟩
  have hu_cutoff : cutoff ≤ n + 1 := by
    have : cutoff ≤ M := Nat.le_max_left cutoff B
    omega
  have hsub_ge := subSum_ge_of_canSubtract hcan
  have hgt_B : B < subSum (n + 1) := by
    have : B ≤ M := Nat.le_max_right cutoff B
    omega
  exact ⟨n + 1, hu_cutoff, hgt_B⟩

/-- Unconditional SubSum unboundedness: `subSum` exceeds every bound `B`. -/
theorem subSum_unbounded (B : Nat) :
    ∃ u, B < subSum u := by
  rcases subSum_unbounded_after 0 B with ⟨u, _, hgt⟩
  exact ⟨u, hgt⟩

/-- **Unconditional SubCount Unboundedness After Any Cutoff**:
The subtraction counter `subCount` is unbounded after any prescribed cutoff. -/
theorem subCount_unbounded_after (cutoff B : Nat) :
    ∃ u, cutoff ≤ u ∧ B ≤ subCount u := by
  induction B with
  | zero =>
      exact ⟨cutoff, Nat.le_refl cutoff, Nat.zero_le _⟩
  | succ B ih =>
      rcases ih with ⟨u, hcut, hB⟩
      rcases exists_canSubtract_of_ray u with ⟨n, hn, hcan⟩
      have hu_succ : cutoff ≤ n + 1 := by omega
      have hcount_step : subCount (n + 1) = subCount n + 1 := by
        rw [subCount_succ, if_pos hcan]
      have hmono : subCount u ≤ subCount n := subCount_mono hn
      have hsucc_le : B + 1 ≤ subCount (n + 1) := by omega
      exact ⟨n + 1, hu_succ, hsucc_le⟩

/-- Unconditional SubCount unboundedness: `subCount` exceeds every bound `B`. -/
theorem subCount_unbounded (B : Nat) :
    ∃ u, B ≤ subCount u := by
  rcases subCount_unbounded_after 0 B with ⟨u, _, hle⟩
  exact ⟨u, hle⟩

/-! ### Part 2: Downcrossing Deposits and Tail Ledger Divergence -/

/-- Every downcrossing step `k ≥ B` deposits its entire clock `k + 1` into `subSum`,
exceeding `B`. -/
theorem downcrossing_deposit_exceeds_bound
    {k B : Nat} (hk : 1 ≤ k) (hB : B ≤ k)
    (hhigh : 2 * k ≤ a k)
    (hlow : a (k + 1) < 2 * (k + 1)) :
    B < k + 1 ∧ k + 1 ≤ subSum (k + 1) := by
  have hdep := downcrossing_subSum_ge_clock hk hhigh hlow
  exact ⟨by omega, hdep⟩

/-- In any hypothetical least missing tail, a downcrossing step `k ≥ time` deposits
at least `k + 1` on top of `subSum time` and re-enters the corridor. -/
theorem tail_downcrossing_reentry_ledger_divergence
    {target start time firstTime k : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (hk_time : time ≤ k) (hk_pos : 1 ≤ k)
    (hhigh : 2 * k ≤ a k)
    (hlow : a (k + 1) < 2 * (k + 1)) :
    subSum time + (k + 1) ≤ subSum (k + 1) ∧
    subCount time + 1 ≤ subCount (k + 1) ∧
    2 * (subSum time + (k + 1)) + (a time + 1) ≤ upperTri (k + 1) ∧
    upperTri (k + 1) < 2 * subSum (k + 1) + 2 * (k + 1) := by
  have hsum := tail_downcrossing_subSum_ge_time hmin hk_time hk_pos hhigh hlow
  have hcount := tail_downcrossing_subCount_gt_time hmin hk_time hk_pos hhigh hlow
  have hledger := tail_downcrossing_ledger_corridor_reentry hmin hk_time hk_pos hhigh hlow
  refine ⟨hsum, hcount, by omega, hledger.2⟩

/-- Recurrent downcrossings force arbitrarily large ledger mass at downcrossing
re-entry points while satisfying the corridor bounds. -/
theorem recurrent_downcrossings_force_arbitrary_ledger_growth
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (hrec : ∀ H, ∃ k, H ≤ k ∧ 1 ≤ k ∧ 2 * k ≤ a k ∧ a (k + 1) < 2 * (k + 1))
    (B : Nat) :
    ∃ k, time ≤ k ∧ B < subSum (k + 1) ∧
      2 * subSum (k + 1) + (a time + 1) ≤ upperTri (k + 1) ∧
      upperTri (k + 1) < 2 * subSum (k + 1) + 2 * (k + 1) := by
  let H := max time B
  rcases hrec H with ⟨k, hH_le, hk_pos, hhigh, hlow⟩
  have hk_time : time ≤ k := by
    have : time ≤ H := Nat.le_max_left time B
    omega
  have hk_B : B ≤ k := by
    have : B ≤ H := Nat.le_max_right time B
    omega
  have hdep := downcrossing_subSum_ge_clock hk_pos hhigh hlow
  have hledger := tail_downcrossing_ledger_corridor_reentry hmin hk_time hk_pos hhigh hlow
  refine ⟨k, hk_time, by omega, hledger.1, hledger.2⟩

/-! ### Part 3: Grand Recurrent Downcrossing SubSum Synthesis -/

/-- Grand Recurrent Downcrossing SubSum Synthesis:
1. SubSum is unconditionally unbounded past any cutoff.
2. SubCount is unconditionally unbounded past any cutoff.
3. Every downcrossing step deposits its clock into subSum.
4. Tail downcrossings strictly increase subSum and subCount over the tail minimum,
   re-entering the corridor.
5. Indefinitely recurrent downcrossings force subSum past every bound at corridor
   re-entry states. -/
theorem grand_recurrent_downcrossing_subSum_synthesis
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    (∀ cutoff B, ∃ u, cutoff ≤ u ∧ B < subSum u) ∧
    (∀ cutoff B, ∃ u, cutoff ≤ u ∧ B ≤ subCount u) ∧
    (∀ k, 1 ≤ k → 2 * k ≤ a k → a (k + 1) < 2 * (k + 1) →
       k + 1 ≤ subSum (k + 1)) ∧
    (∀ k, time ≤ k → 1 ≤ k → 2 * k ≤ a k → a (k + 1) < 2 * (k + 1) →
       subSum time + (k + 1) ≤ subSum (k + 1) ∧
       2 * (subSum time + (k + 1)) + (a time + 1) ≤ upperTri (k + 1) ∧
       upperTri (k + 1) < 2 * subSum (k + 1) + 2 * (k + 1)) ∧
    ((∀ H, ∃ k, H ≤ k ∧ 1 ≤ k ∧ 2 * k ≤ a k ∧ a (k + 1) < 2 * (k + 1)) →
       ∀ B, ∃ k, time ≤ k ∧ B < subSum (k + 1) ∧
         2 * subSum (k + 1) + (a time + 1) ≤ upperTri (k + 1) ∧
         upperTri (k + 1) < 2 * subSum (k + 1) + 2 * (k + 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro cutoff B
    exact subSum_unbounded_after cutoff B
  · intro cutoff B
    exact subCount_unbounded_after cutoff B
  · intro k hk hhigh hlow
    exact downcrossing_subSum_ge_clock hk hhigh hlow
  · intro k hk_time hk_pos hhigh hlow
    have hdiv := tail_downcrossing_reentry_ledger_divergence hmin hk_time hk_pos hhigh hlow
    exact ⟨hdiv.1, hdiv.2.2.1, hdiv.2.2.2⟩
  · intro hrec B
    exact recurrent_downcrossings_force_arbitrary_ledger_growth hmin hrec B

end Recaman
