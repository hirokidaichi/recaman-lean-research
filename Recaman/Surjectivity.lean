import Recaman.LeastMissingTargetContradiction
import Recaman.TailDowncrossingDichotomy
import Recaman.CrossingTailRefined
import Recaman.Coverage

namespace Recaman

/-! # Grand Surjectivity and Counterexample Elimination Architecture

This module establishes the grand mathematical architecture reducing the
surjectivity of the Recamán sequence (`∀ target, ∃ time, a time = target`) to the
elimination of the two dynamical branches available to any hypothetical least
missing target:

1. **Dynamical Branch Dichotomy (`least_missing_target_tail_dichotomy`)**:
   For any hypothetical `LeastMissingTarget target`, its certified canonical tail
   minimum `time` must follow one of two mutually exclusive long-term dynamical regimes:
   - **Permanent High Escape (`PermanentHighEscape time`)**:
     The orbit escapes above `2 * (time + 2)` and permanently maintains `2n ≤ a n` forever.
   - **Corridor Re-entry (`CorridorReentry time`)**:
     The orbit downcrosses back into the ledger corridor `[a time + 1, 2(k + 1))`.

2. **Branch Obstruction Framework**:
   - `NoPermanentHighEscapeHypothesis`:
     States that no tail minimum can escape into a permanently high orbit forever.
     (Governed by the escape state ceiling `a(time + 2) < 6(time + 2) + 1` and
     pigeonhole blocker capacity exhaustion).
   - `NoCorridorReentryHypothesis`:
     States that no tail minimum can repeatedly re-enter the corridor without bound.
     (Governed by the unsupplied addition drift accumulation, finite block capacity,
     and ledger divergence).

3. **Master Contradiction (`not_least_missing_target_of_branch_obstructions`)**:
   Under both branch obstructions, any hypothetical `LeastMissingTarget target`
   is strictly refuted (`LeastMissingTarget target → False`).

4. **Well-Founded Surjectivity Reduction (`surjective_of_not_least_missing_target`)**:
   By strong well-founded induction on ℕ, the universal absence of any
   least missing target implies full coverage:
   `∀ target : Nat, ∃ time : Nat, a time = target`.

5. **Branch Reduction to Full Surjectivity (`surjective_of_branch_obstructions`)**:
   The conjunction of the two dynamical branch obstructions implies full surjectivity.

6. **Bilateral Logical Equivalence (`recaman_surjective_iff_not_least_missing_target`)**:
   `∀ target, ∃ time, a time = target ↔ ∀ target, LeastMissingTarget target → False`.

7. **Grand Surjectivity Architecture Synthesis (`grand_surjectivity_architecture_synthesis`)**:
   Unifies the tail dichotomy, well-founded reduction, bilateral equivalence, branch
   reduction, and classical schemas (`TargetTailReturn` and `CoverageOracle`) into a
   single master architecture theorem.
-/

/-! ### Part 1: Counterexample Tail Dynamical Regimes -/

/-- The Permanent High Escape property for a hypothetical least missing target:
the orbit escapes above `2 * (time + 2)` and permanently maintains `2n ≤ a n` forever. -/
def PermanentHighEscape (time : Nat) : Prop :=
  ∀ n, time + 2 ≤ n → 2 * n ≤ a n

/-- The Corridor Re-entry property for a hypothetical least missing target:
the orbit performs a certified downcrossing step back into the ledger corridor. -/
def CorridorReentry (time : Nat) : Prop :=
  ∃ k, time + 2 ≤ k ∧
    CanSubtract (k + 1) (stateAt k) ∧
    a time + 1 ≤ a (k + 1) ∧
    a (k + 1) < 2 * (k + 1) ∧
    2 * subSum (k + 1) + (a time + 1) ≤ upperTri (k + 1) ∧
    upperTri (k + 1) < 2 * subSum (k + 1) + 2 * (k + 1)

/-- The dichotomy of counterexample tail dynamics:
any hypothetical least missing target MUST either escape permanently high or
re-enter the ledger corridor. -/
theorem least_missing_target_tail_dichotomy
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ start time firstTime,
      PermanentTailMinimumCertificate target start time firstTime ∧
      (PermanentHighEscape time ∨ CorridorReentry time) := by
  rcases least_missing_tail_grand_dichotomy h with ⟨start, time, firstTime, hmin, hdich⟩
  refine ⟨start, time, firstTime, hmin, ?_⟩
  rcases hdich with hhigh | hdown
  · left
    intro n hn
    exact (hhigh n hn).1
  · right
    exact hdown

/-! ### Part 2: Branch Obstruction Hypotheses -/

/-- Hypothesis: the permanent high escape branch is obstructed. -/
def NoPermanentHighEscapeHypothesis : Prop :=
  ∀ target start time firstTime,
    PermanentTailMinimumCertificate target start time firstTime →
    ¬ PermanentHighEscape time

/-- Hypothesis: the corridor re-entry branch is obstructed. -/
def NoCorridorReentryHypothesis : Prop :=
  ∀ target start time firstTime,
    PermanentTailMinimumCertificate target start time firstTime →
    ¬ CorridorReentry time

/-- The master contradiction: if both dynamical branches are obstructed,
then no least missing target can exist. -/
theorem not_least_missing_target_of_branch_obstructions
    (h_no_high : NoPermanentHighEscapeHypothesis)
    (h_no_corridor : NoCorridorReentryHypothesis)
    {target : Nat} (h : LeastMissingTarget target) : False := by
  rcases least_missing_target_tail_dichotomy h with ⟨start, time, firstTime, hmin, hdich⟩
  rcases hdich with hhigh | hcorridor
  · exact h_no_high target start time firstTime hmin hhigh
  · exact h_no_corridor target start time firstTime hmin hcorridor

/-! ### Part 3: Surjectivity Reductions and Bilateral Equivalence -/

/-- Surjectivity from the absence of least missing targets:
if no natural number can be a least missing target, then every natural number
is reached by the Recamán sequence. -/
theorem surjective_of_not_least_missing_target
    (hcontra : ∀ target, LeastMissingTarget target → False) :
    ∀ target : Nat, ∃ time : Nat, a time = target := by
  intro target
  induction target using Nat.strongRecOn with
  | ind target ih =>
      by_cases hoccurs : ∃ time, a time = target
      · exact hoccurs
      · have hleast : LeastMissingTarget target := {
          target_missing := hoccurs
          below_occurs := ih
        }
        exact False.elim (hcontra target hleast)

/-- Surjectivity from branch obstructions:
if both the permanent high escape and corridor re-entry branches are obstructed,
then the Recamán sequence is surjective. -/
theorem surjective_of_branch_obstructions
    (h_no_high : NoPermanentHighEscapeHypothesis)
    (h_no_corridor : NoCorridorReentryHypothesis) :
    ∀ target : Nat, ∃ time : Nat, a time = target := by
  apply surjective_of_not_least_missing_target
  intro target hleast
  exact not_least_missing_target_of_branch_obstructions h_no_high h_no_corridor hleast

/-- If the Recamán sequence is surjective, then no least missing target exists. -/
theorem not_least_missing_target_of_surjective
    (hsurj : ∀ target : Nat, ∃ time : Nat, a time = target)
    {target : Nat} (hleast : LeastMissingTarget target) : False := by
  rcases hsurj target with ⟨time, htime⟩
  exact hleast.target_missing ⟨time, htime⟩

/-- Bilateral logical equivalence between full surjectivity and the non-existence
of a least missing target. -/
theorem recaman_surjective_iff_not_least_missing_target :
    (∀ target : Nat, ∃ time : Nat, a time = target) ↔
    (∀ target : Nat, LeastMissingTarget target → False) := by
  constructor
  · intro hsurj target hleast
    exact not_least_missing_target_of_surjective hsurj hleast
  · exact surjective_of_not_least_missing_target

/-! ### Part 4: Grand Surjectivity Architecture Synthesis -/

/-- Grand Surjectivity Architecture Synthesis:
Unifies:
1. The dichotomy of counterexample tail dynamics (PermanentHighEscape vs CorridorReentry).
2. The reduction of surjectivity to the contradiction of LeastMissingTarget.
3. The bilateral equivalence between surjectivity and non-existence of least missing targets.
4. The reduction from branch obstructions to full surjectivity.
5. The bridge to TargetTailReturn and CoverageOracle schemas. -/
theorem grand_surjectivity_architecture_synthesis :
    (∀ target, LeastMissingTarget target →
      ∃ start time firstTime,
        PermanentTailMinimumCertificate target start time firstTime ∧
        (PermanentHighEscape time ∨ CorridorReentry time)) ∧
    ((∀ target, LeastMissingTarget target → False) →
      ∀ target, ∃ time, a time = target) ∧
    ((∀ target, ∃ time, a time = target) ↔
      ∀ target, LeastMissingTarget target → False) ∧
    (NoPermanentHighEscapeHypothesis →
      NoCorridorReentryHypothesis →
      ∀ target, ∃ time, a time = target) ∧
    ((∀ target, TargetTailReturnHypothesis target) ↔
      ∀ target, ∃ time, a time = target) ∧
    ((∀ m, 0 < m → CoverageOracle m) →
      ∀ m, ∃ t, a t = m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro target hleast
    exact least_missing_target_tail_dichotomy hleast
  · exact surjective_of_not_least_missing_target
  · exact recaman_surjective_iff_not_least_missing_target
  · exact surjective_of_branch_obstructions
  · exact all_targetTailReturn_iff_surjective
  · exact all_coverageOracles_imply_surjective

end Recaman
