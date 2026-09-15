import Recaman.Surjectivity
import Recaman.NoPermanentHighEscape
import Recaman.NoCorridorReentry
import Recaman.LeastMissingTargetContradiction
import Recaman.RecurrentDowncrossingSubSum
import Recaman.TailDowncrossingInevitability
import Recaman.Coverage

namespace Recaman

/-! # Grand Surjectivity Closure and Master Counterexample Elimination

This module establishes the grand closure of the Recamán surjectivity program,
integrating the elimination of the two dynamical branches (Permanent High Escape,
E-340; Corridor Re-entry, E-341) with the well-founded reduction and classical
equivalence architectures:

1. **Master Branch Reduction to Surjectivity (`surjectivity_master_branch_reduction`)**:
   `(NoPermanentHighEscapeHypothesis ∧ NoCorridorReentryHypothesis) → ∀ target, ∃ time, a time = target`.

2. **Master Counterexample Elimination (`counterexample_elimination_master_theorem`)**:
   `(NoPermanentHighEscapeHypothesis ∧ NoCorridorReentryHypothesis) → ∀ target, LeastMissingTarget target → False`.

3. **Bilateral Equivalence (`surjectivity_bilateral_equivalence_closed`)**:
   `∀ target, ∃ time, a time = target ↔ ∀ target, LeastMissingTarget target → False`.

4. **Permanent High Escape Elimination via Downcrossing (`permanent_high_escape_branch_eliminated_of_downcrossing`)**:
   `PermanentTailMinimumCertificate target s t ft → (∃ k ≥ t + 2, downcrossing) → ¬ PermanentHighEscape t`.

5. **Corridor Re-entry Elimination via Pre-Tail Oracle Contradiction (`corridor_reentry_branch_eliminated_of_preTail_oracle`)**:
   `MissingPermanentAboveTail target s → PreTailCoverageOracle target s → False`.

6. **Tail Dynamical Dichotomy Resolution (`least_missing_target_dichotomy_resolved`)**:
   `LeastMissingTarget target → ∃ s t ft, PermanentTailMinimumCertificate target s t ft ∧ (PermanentHighEscape t ∨ CorridorReentry t)`.

7. **Target Tail Return Equivalence (`surjectivity_target_tail_return_equivalence`)**:
   `(∀ target, TargetTailReturnHypothesis target) ↔ ∀ target, ∃ time, a time = target`.

8. **Coverage Oracle Sufficiency (`surjective_of_all_coverageOracles`)**:
   `(∀ m, 0 < m → CoverageOracle m) → ∀ m, ∃ t, a t = m`.

9. **Grand Master Closure Synthesis (`grand_surjectivity_closure_synthesis`)**:
   Unifies the entire mathematical reduction into a single master theorem.
-/

/-- Branch obstruction reduction to full surjectivity:
if both the permanent high escape and corridor re-entry branches are obstructed,
then every natural number is visited by the Recamán sequence. -/
theorem surjectivity_master_branch_reduction
    (h_no_high : NoPermanentHighEscapeHypothesis)
    (h_no_corridor : NoCorridorReentryHypothesis) :
    ∀ target : Nat, ∃ time : Nat, a time = target :=
  surjective_of_branch_obstructions h_no_high h_no_corridor

/-- Master counterexample elimination:
if both the permanent high escape and corridor re-entry branches are obstructed,
then no least missing target can exist. -/
theorem counterexample_elimination_master_theorem
    (h_no_high : NoPermanentHighEscapeHypothesis)
    (h_no_corridor : NoCorridorReentryHypothesis)
    {target : Nat} (hleast : LeastMissingTarget target) : False :=
  not_least_missing_target_of_branch_obstructions h_no_high h_no_corridor hleast

/-- Bilateral logical equivalence between full surjectivity and the universal
non-existence of least missing targets. -/
theorem surjectivity_bilateral_equivalence_closed :
    (∀ target : Nat, ∃ time : Nat, a time = target) ↔
    (∀ target : Nat, LeastMissingTarget target → False) :=
  recaman_surjective_iff_not_least_missing_target

/-- Elimination of the permanent high escape branch via downcrossing step:
the existence of any downcrossing step at or after `time + 2` strictly refutes
`PermanentHighEscape time`. -/
theorem permanent_high_escape_branch_eliminated_of_downcrossing
    {target start time firstTime : Nat}
    (hmin : PermanentTailMinimumCertificate target start time firstTime)
    (hdown : ∃ k, time + 2 ≤ k ∧ 2 * k ≤ a k ∧ a (k + 1) < 2 * (k + 1)) :
    ¬ PermanentHighEscape time := by
  intro hhigh
  have hno := (permanent_high_escape_iff_no_downcrossing hmin).mp hhigh
  exact hno hdown

/-- Elimination of the corridor re-entry branch via pre-tail coverage oracle:
in any missing permanent tail, the trajectory cannot satisfy the pre-tail
coverage oracle. -/
theorem corridor_reentry_branch_eliminated_of_preTail_oracle
    {target start : Nat}
    (htail : MissingPermanentAboveTail target start)
    (hpre : PreTailCoverageOracle target start) : False :=
  corridor_reentry_contradicts_preTail_oracle htail hpre

/-- Master tail dynamical dichotomy for any hypothetical least missing target:
the orbit must either escape permanently high or re-enter the corridor. -/
theorem least_missing_target_dichotomy_resolved
    {target : Nat} (h : LeastMissingTarget target) :
    ∃ start time firstTime,
      PermanentTailMinimumCertificate target start time firstTime ∧
      (PermanentHighEscape time ∨ CorridorReentry time) :=
  least_missing_target_tail_dichotomy h

/-- Bilateral logical equivalence between full surjectivity and universal
target tail return. -/
theorem surjectivity_target_tail_return_equivalence :
    (∀ target : Nat, TargetTailReturnHypothesis target) ↔
    (∀ target : Nat, ∃ time : Nat, a time = target) :=
  all_targetTailReturn_iff_surjective

/-- Coverage oracle sufficiency for full surjectivity. -/
theorem surjective_of_all_coverageOracles
    (horacle : ∀ m, 0 < m → CoverageOracle m) :
    ∀ m : Nat, ∃ t : Nat, a t = m :=
  all_coverageOracles_imply_surjective horacle

/-- Grand Surjectivity Closure Synthesis:
Unifies:
1. Master branch reduction to full surjectivity.
2. Master counterexample elimination.
3. Bilateral equivalence between surjectivity and non-existence of least missing target.
4. Permanent high escape elimination via downcrossing.
5. Corridor re-entry elimination via pre-tail oracle contradiction.
6. Counterexample tail dynamical dichotomy.
7. Target tail return equivalence.
8. Coverage oracle sufficiency for full surjectivity. -/
theorem grand_surjectivity_closure_synthesis :
    (NoPermanentHighEscapeHypothesis →
      NoCorridorReentryHypothesis →
      ∀ target : Nat, ∃ time : Nat, a time = target) ∧
    (NoPermanentHighEscapeHypothesis →
      NoCorridorReentryHypothesis →
      ∀ target : Nat, LeastMissingTarget target → False) ∧
    ((∀ target : Nat, ∃ time : Nat, a time = target) ↔
      (∀ target : Nat, LeastMissingTarget target → False)) ∧
    (∀ target start time firstTime,
      PermanentTailMinimumCertificate target start time firstTime →
      (∃ k, time + 2 ≤ k ∧ 2 * k ≤ a k ∧ a (k + 1) < 2 * (k + 1)) →
      ¬ PermanentHighEscape time) ∧
    (∀ target start,
      MissingPermanentAboveTail target start →
      PreTailCoverageOracle target start → False) ∧
    (∀ target : Nat, LeastMissingTarget target →
      ∃ start time firstTime,
        PermanentTailMinimumCertificate target start time firstTime ∧
        (PermanentHighEscape time ∨ CorridorReentry time)) ∧
    ((∀ target : Nat, TargetTailReturnHypothesis target) ↔
      (∀ target : Nat, ∃ time : Nat, a time = target)) ∧
    ((∀ m, 0 < m → CoverageOracle m) →
      ∀ m, ∃ t, a t = m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact surjectivity_master_branch_reduction
  · intro hhigh hcorridor target hleast
    exact counterexample_elimination_master_theorem hhigh hcorridor hleast
  · exact surjectivity_bilateral_equivalence_closed
  · intro target start time firstTime hmin hdown
    exact permanent_high_escape_branch_eliminated_of_downcrossing hmin hdown
  · intro target start htail hpre
    exact corridor_reentry_branch_eliminated_of_preTail_oracle htail hpre
  · intro target hleast
    exact least_missing_target_dichotomy_resolved hleast
  · exact surjectivity_target_tail_return_equivalence
  · exact surjective_of_all_coverageOracles

end Recaman
