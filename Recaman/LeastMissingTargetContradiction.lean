import Recaman.RecurrentDowncrossingSubSum
import Recaman.TailDowncrossingInevitability
import Recaman.TailDowncrossingDichotomy
import Recaman.TailDowncrossingLedger
import Recaman.PermanentHighGlobalSynthesis
import Recaman.LeastTailLedgerMinimum
import Recaman.TargetTailResidualKernel
import Recaman.CrossingTailRefined

namespace Recaman

/-! # Least Missing Target Contradiction Synthesis

This module formalizes the structural obstruction and contradiction machinery
for any hypothetical least missing value (`LeastMissingTarget target`) in the
Recamán sequence:

1. **Escape State Upper Bound (`tail_escape_strictly_lt_six_times`)**:
   At the canonical tail minimum `time`, the orbit satisfies `a time < 2 * time`.
   Consequently, the escape state `n = time + 2` strictly satisfies:
   `a (time + 2) < 6 * (time + 2) + 1`.

2. **Dichotomy Resolution at Escape State (`permanent_high_escape_dichotomy_resolution`)**:
   Because `a (time + 2) < 6(time + 2) + 1`, the high-horizon branch `6n + 1 ≤ a n`
   is strictly impossible at the escape state. The orbit strictly falls into the
   downcrossing-forcing branch of `permanent_high_universal_dichotomy`.

3. **Refutation of Tail Return (`contradiction_of_least_missing_and_tail_return`)**:
   Any `LeastMissingTarget target` is in direct contradiction with the tail-return
   hypothesis `TargetTailReturnHypothesis target`.

4. **Pre-Tail Oracle Contradiction (`contradiction_of_least_missing_and_preTail_oracle`)**:
   In any missing permanent tail, the finite pre-tail coverage oracle
   `PreTailCoverageOracle target start` is strictly impossible.

5. **Recurrent Downcrossing vs. Bounded Ledger Contradiction**:
   `recurrent_downcrossings_contradicts_bounded_ledger`:
   Indefinitely recurrent downcrossings strictly refute any uniform upper bound
   on the subtraction ledger `subSum`.

6. **Grand Least Missing Target Contradiction Synthesis**:
   `grand_least_missing_target_contradiction_synthesis`:
   Unifies the escape state height bounds, the dichotomy resolution, the
   tail-return contradiction, the pre-tail oracle contradiction, and the
   ledger divergence into a master contradiction synthesis theorem.
-/

/-! ### Part 1: Escape State Height Bounds and Dichotomy Resolution -/

/-- At the certified tail minimum, the escape state `time + 2` strictly satisfies
`a (time + 2) < 6 * (time + 2) + 1`. -/
theorem tail_escape_strictly_lt_six_times
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (htwice : a time < 2 * time) :
    a (time + 2) < 6 * (time + 2) + 1 := by
  have hval := tail_minimum_followup_value hmin
  omega

/-- For any hypothetical least missing target, the certified escape state
satisfies `a (time + 2) < 6 * (time + 2) + 1`. -/
theorem least_missing_target_escape_strictly_lt_six_times
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ start time firstTime,
      PermanentTailMinimumCertificate target start time firstTime ∧
      a (time + 2) < 6 * (time + 2) + 1 := by
  rcases h.exists_leastTailLedgerMinimum with
    ⟨start, time, firstTime, _q, _r, _htail, _hleast, hmin,
     _hcoord, _htargetMin, _hminUpper, hminTwice, _hq, _hpot, _hledgLower, _hledgUpper⟩
  refine ⟨start, time, firstTime, hmin, ?_⟩
  exact tail_escape_strictly_lt_six_times hmin hminTwice

/-- Dichotomy resolution at the escape state:
the escape state `time + 2` strictly falls into the second branch of the universal
high regime dichotomy, forcing toothcomb landing values below twice the clock. -/
theorem permanent_high_escape_dichotomy_resolution
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (htwice : a time < 2 * time) :
    a (time + 2) < 6 * (time + 2) + 1 ∧
    (∀ val, val = a (time + 2) + (time + 2) - (time + 2) →
      val < 2 * ((time + 2) + 3 + 2 * (time + 2))) := by
  have hlt := tail_escape_strictly_lt_six_times hmin htwice
  have hval_lt : ∀ val, val = a (time + 2) + (time + 2) - (time + 2) →
      val < 2 * ((time + 2) + 3 + 2 * (time + 2)) := fun val hval =>
    toothcomb_forced_downcrossing_at_step_n hlt hval
  exact ⟨hlt, hval_lt⟩

/-! ### Part 2: Tail Return and Pre-Tail Oracle Contradictions -/

/-- Direct contradiction between LeastMissingTarget and TargetTailReturnHypothesis. -/
theorem contradiction_of_least_missing_and_tail_return
    {target : Nat} (h : LeastMissingTarget target)
    (hreturn : TargetTailReturnHypothesis target) : False :=
  h.not_targetTailReturn hreturn

/-- Direct contradiction between MissingPermanentAboveTail and PreTailCoverageOracle. -/
theorem contradiction_of_least_missing_and_preTail_oracle
    {target start : Nat}
    (htail : MissingPermanentAboveTail target start)
    (hpre : PreTailCoverageOracle target start) : False :=
  htail.not_preTailCoverageOracle hpre

/-! ### Part 3: Ledger Divergence Contradiction -/

/-- Indefinitely recurrent downcrossings strictly refute any uniform upper bound
on the subtraction ledger `subSum`. -/
theorem recurrent_downcrossings_contradicts_bounded_ledger
    (hrec : ∀ H, ∃ k, H ≤ k ∧ 1 ≤ k ∧ 2 * k ≤ a k ∧ a (k + 1) < 2 * (k + 1))
    (hbound : ∃ C, ∀ k, 1 ≤ k → 2 * k ≤ a k → a (k + 1) < 2 * (k + 1) → subSum (k + 1) ≤ C) :
    False := by
  rcases hbound with ⟨C, hC⟩
  rcases recurrent_downcrossing_subSum_unbounded hrec C with ⟨_u, _hgt⟩
  rcases hrec (C + 1) with ⟨k, _hH, hk_pos, hhigh, hlow⟩
  have hdep := downcrossing_subSum_ge_clock hk_pos hhigh hlow
  have hle := hC k hk_pos hhigh hlow
  omega

/-! ### Part 4: Grand Least Missing Target Contradiction Synthesis -/

/-- Grand Least Missing Target Contradiction Synthesis:
1. Canonical tail escape state strictly satisfies `a (time + 2) < 6 * (time + 2) + 1`
   and forces toothcomb landing below twice the clock.
2. `LeastMissingTarget target` refutes `TargetTailReturnHypothesis target`.
3. `MissingPermanentAboveTail target start` refutes `PreTailCoverageOracle target start`.
4. Recurrent downcrossings contradict any uniform upper bound on `subSum`. -/
theorem grand_least_missing_target_contradiction_synthesis
    {target : Nat} (h : LeastMissingTarget target) :
    (∃ start time firstTime,
       PermanentTailMinimumCertificate target start time firstTime ∧
       a (time + 2) < 6 * (time + 2) + 1 ∧
       (∀ val, val = a (time + 2) + (time + 2) - (time + 2) →
         val < 2 * ((time + 2) + 3 + 2 * (time + 2)))) ∧
    (TargetTailReturnHypothesis target → False) ∧
    (∀ start, MissingPermanentAboveTail target start → PreTailCoverageOracle target start → False) ∧
    ((∀ H, ∃ k, H ≤ k ∧ 1 ≤ k ∧ 2 * k ≤ a k ∧ a (k + 1) < 2 * (k + 1)) →
     (∃ C, ∀ k, 1 ≤ k → 2 * k ≤ a k → a (k + 1) < 2 * (k + 1) → subSum (k + 1) ≤ C) → False) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases h.exists_leastTailLedgerMinimum with
      ⟨start, time, firstTime, _q, _r, _htail, _hleast, hmin,
       _hcoord, _htargetMin, _hminUpper, hminTwice, _hq, _hpot, _hledgLower, _hledgUpper⟩
    have hboth := permanent_high_escape_dichotomy_resolution hmin hminTwice
    exact ⟨start, time, firstTime, hmin, hboth.1, hboth.2⟩
  · exact contradiction_of_least_missing_and_tail_return h
  · intro start htail hpre
    exact contradiction_of_least_missing_and_preTail_oracle htail hpre
  · intro hrec hbound
    exact recurrent_downcrossings_contradicts_bounded_ledger hrec hbound

end Recaman
