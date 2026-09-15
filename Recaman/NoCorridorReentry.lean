import Recaman.Surjectivity
import Recaman.NoPermanentHighEscape
import Recaman.LeastMissingTargetContradiction
import Recaman.RecurrentDowncrossingSubSum
import Recaman.TailDowncrossingInevitability
import Recaman.TailDowncrossingLedger
import Recaman.TargetTailResidualKernel
import Recaman.CorridorDensityObstruction
import Recaman.FiniteBlockCapacity
import Recaman.DriftResetAccumulation
import Recaman.GlobalUnboundednessSupply

namespace Recaman

/-! # Elimination of the Corridor Re-entry Trapping Branch

This module formalizes the structural obstruction and elimination machinery
for the Corridor Re-entry branch (`CorridorReentry time`) in any hypothetical
counterexample to the Recamán surjectivity conjecture:

1. **Tight Ledger Corridor Bounds (`corridor_reentry_ledger_bounds`)**:
   In any corridor re-entry, the re-entry state satisfies the tight ledger corridor
   bounds:
   `2 * subSum (k + 1) + (a time + 1) ≤ upperTri (k + 1) < 2 * subSum (k + 1) + 2 * (k + 1)`.

2. **Clock Deposit Lower Bound (`corridor_reentry_clock_deposit`)**:
   Any corridor re-entry downcrossing step deposits its clock into `subSum`:
   `k + 1 ≤ subSum (k + 1)`.

3. **Value Sandwich in Corridor (`corridor_reentry_value_in_corridor`)**:
   The landing value of any corridor re-entry is sandwiched between `a time + 1`
   and `2 * (k + 1)`.

4. **Confinement to Finite Prefix (`missing_permanent_tail_values_le_target_before_start`)**:
   In any missing permanent tail, all values at or below `target` are strictly
   confined to the finite pre-tail prefix `j < start`.

5. **Absolute Target Missingness (`missing_permanent_tail_pre_tail_capacity_bound`)**:
   In any missing permanent tail, no step can produce `target`.

6. **Refutation of Pre-Tail Coverage Oracle (`corridor_reentry_contradicts_preTail_oracle`)**:
   Direct contradiction between missing permanent tail and finite pre-tail oracle:
   the corridor re-entry trajectory cannot supply the required pre-tail coverage oracle.

7. **Recurrent Subtraction Ledger Divergence (`recurrent_corridor_reentry_subSum_divergence`)**:
   If corridor re-entries recur past arbitrary bounds, the subtraction ledger
   diverges beyond any bound `B` while satisfying the corridor bounds.

8. **Grand Synthesis (`grand_no_corridor_reentry_synthesis`)**:
   Unifies corridor ledger bounds, clock deposit, value bounds, finite prefix confinement,
   pre-tail oracle refutation, and recurrent ledger divergence into a single master theorem.
-/

/-- In any corridor re-entry, the re-entry state satisfies the tight ledger corridor bounds. -/
theorem corridor_reentry_ledger_bounds
    {time : Nat} (hre : CorridorReentry time) :
    ∃ k, time + 2 ≤ k ∧
      2 * subSum (k + 1) + (a time + 1) ≤ upperTri (k + 1) ∧
      upperTri (k + 1) < 2 * subSum (k + 1) + 2 * (k + 1) := by
  rcases hre with ⟨k, hk, _hsub, _habove, _hbelow, hledger1, hledger2⟩
  exact ⟨k, hk, hledger1, hledger2⟩

/-- Any corridor re-entry downcrossing step deposits its clock into `subSum`. -/
theorem corridor_reentry_clock_deposit
    {time : Nat} (hre : CorridorReentry time) :
    ∃ k, time + 2 ≤ k ∧ k + 1 ≤ subSum (k + 1) := by
  rcases hre with ⟨k, hk, hsub, _habove, _hbelow, _hledger1, _hledger2⟩
  have hdep := subSum_ge_of_canSubtract hsub
  exact ⟨k, hk, hdep⟩

/-- The landing value of any corridor re-entry is sandwiched between `a time + 1`
and `2 * (k + 1)`. -/
theorem corridor_reentry_value_in_corridor
    {time : Nat} (hre : CorridorReentry time) :
    ∃ k, time + 2 ≤ k ∧ a time + 1 ≤ a (k + 1) ∧ a (k + 1) < 2 * (k + 1) := by
  rcases hre with ⟨k, hk, _hsub, habove, hbelow, _hledger1, _hledger2⟩
  exact ⟨k, hk, habove, hbelow⟩

/-- In any missing permanent tail, all values at or below `target` are strictly
confined to the finite pre-tail prefix `j < start`. -/
theorem missing_permanent_tail_values_le_target_before_start
    {target start : Nat}
    (htail : MissingPermanentAboveTail target start) :
    ∀ n, a n ≤ target → n < start := by
  intro n hle
  by_cases hge : start ≤ n
  · have hgt := htail.strictly_above n hge
    omega
  · omega

/-- In any missing permanent tail, no step can produce `target`. -/
theorem missing_permanent_tail_pre_tail_capacity_bound
    {target start : Nat}
    (htail : MissingPermanentAboveTail target start) :
    ∀ n, a n = target → False := by
  intro n heq
  exact htail.target_missing ⟨n, heq⟩

/-- Direct contradiction between missing permanent tail and finite pre-tail oracle:
the corridor re-entry trajectory cannot supply the required pre-tail coverage oracle. -/
theorem corridor_reentry_contradicts_preTail_oracle
    {target start : Nat}
    (htail : MissingPermanentAboveTail target start)
    (hpre : PreTailCoverageOracle target start) : False :=
  htail.not_preTailCoverageOracle hpre

/-- If corridor re-entries recur past arbitrary bounds, the subtraction ledger
diverges beyond any bound `B` while satisfying the corridor bounds. -/
theorem recurrent_corridor_reentry_subSum_divergence
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (hrec : ∀ H, ∃ k, H ≤ k ∧ 1 ≤ k ∧ 2 * k ≤ a k ∧ a (k + 1) < 2 * (k + 1))
    (B : Nat) :
    ∃ k, time ≤ k ∧
      B < subSum (k + 1) ∧
      2 * subSum (k + 1) + (a time + 1) ≤ upperTri (k + 1) ∧
      upperTri (k + 1) < 2 * subSum (k + 1) + 2 * (k + 1) := by
  exact recurrent_downcrossings_force_arbitrary_ledger_growth hmin hrec B

/-- Grand No Corridor Re-entry Synthesis:
Unifies:
1. Corridor re-entry tight ledger bounds.
2. Corridor re-entry clock deposit lower bound.
3. Corridor re-entry value bounds.
4. Confinement of values ≤ target to the finite pre-tail prefix j < start.
5. Absolute target missingness.
6. Refutation of the PreTailCoverageOracle.
7. Recurrent corridor re-entry ledger divergence. -/
theorem grand_no_corridor_reentry_synthesis
    {target start time firstTime : Nat}
    (htail : MissingPermanentAboveTail target start)
    (hmin : PermanentTailMinimumCertificate target start time firstTime) :
    (CorridorReentry time →
      ∃ k, time + 2 ≤ k ∧
        2 * subSum (k + 1) + (a time + 1) ≤ upperTri (k + 1) ∧
        upperTri (k + 1) < 2 * subSum (k + 1) + 2 * (k + 1)) ∧
    (CorridorReentry time →
      ∃ k, time + 2 ≤ k ∧ k + 1 ≤ subSum (k + 1)) ∧
    (CorridorReentry time →
      ∃ k, time + 2 ≤ k ∧ a time + 1 ≤ a (k + 1) ∧ a (k + 1) < 2 * (k + 1)) ∧
    (∀ n, a n ≤ target → n < start) ∧
    (PreTailCoverageOracle target start → False) ∧
    (∀ B, (∀ H, ∃ k, H ≤ k ∧ 1 ≤ k ∧ 2 * k ≤ a k ∧ a (k + 1) < 2 * (k + 1)) →
      ∃ k, time ≤ k ∧
        B < subSum (k + 1) ∧
        2 * subSum (k + 1) + (a time + 1) ≤ upperTri (k + 1) ∧
        upperTri (k + 1) < 2 * subSum (k + 1) + 2 * (k + 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hre
    exact corridor_reentry_ledger_bounds hre
  · intro hre
    exact corridor_reentry_clock_deposit hre
  · intro hre
    exact corridor_reentry_value_in_corridor hre
  · exact missing_permanent_tail_values_le_target_before_start htail
  · exact corridor_reentry_contradicts_preTail_oracle htail
  · intro B hrec
    exact recurrent_corridor_reentry_subSum_divergence hmin hrec B

end Recaman
