# Hypothesis card: Grand Surjectivity Architecture and Counterexample Elimination

- ID: `H-20260915-13`
- Owner: antigravity
- Created: 2026-09-15
- Status: `PROVED-LEAN`
- Research branch: Theme 5 (Grand Surjectivity Architecture and Counterexample Elimination)

## Exact statement

This module establishes the grand mathematical architecture reducing the
surjectivity of the Recamán sequence (`∀ target, ∃ time, a time = target`) to the
elimination of the two dynamical branches available to any hypothetical least
missing target:

1. **Dynamical Branch Dichotomy (`least_missing_target_tail_dichotomy`)**:
   For any hypothetical `LeastMissingTarget target`, its certified canonical tail
   minimum `time` must follow one of two mutually exclusive long-term dynamical regimes:
   - **Permanent High Escape (`PermanentHighEscape time`)**:
     The orbit escapes above `2 * (time + 2)` and permanently maintains $2n \le a(n)$ forever.
   - **Corridor Re-entry (`CorridorReentry time`)**:
     The orbit downcrosses back into the ledger corridor $[a(\text{time}) + 1, 2(k + 1))$.

2. **Branch Obstruction Framework**:
   - `NoPermanentHighEscapeHypothesis`:
     States that no tail minimum can escape into a permanently high orbit forever:
     $$\forall \text{target start time firstTime}, \text{PermanentTailMinimumCertificate} \to \neg \text{PermanentHighEscape time}$$
   - `NoCorridorReentryHypothesis`:
     States that no tail minimum can repeatedly re-enter the corridor without bound:
     $$\forall \text{target start time firstTime}, \text{PermanentTailMinimumCertificate} \to \neg \text{CorridorReentry time}$$

3. **Master Contradiction (`not_least_missing_target_of_branch_obstructions`)**:
   Under both branch obstructions, any hypothetical `LeastMissingTarget target`
   is strictly refuted:
   $$\text{LeastMissingTarget target} \to \text{False}$$

4. **Well-Founded Surjectivity Reduction (`surjective_of_not_least_missing_target`)**:
   By strong well-founded induction on $\mathbb{N}$, the universal absence of any
   least missing target implies full coverage:
   $$\forall \text{target} : \mathbb{N}, \exists \text{time} : \mathbb{N}, a(\text{time}) = \text{target}$$

5. **Branch Reduction to Full Surjectivity (`surjective_of_branch_obstructions`)**:
   The conjunction of the two dynamical branch obstructions implies full surjectivity:
   $$\text{NoPermanentHighEscapeHypothesis} \to \text{NoCorridorReentryHypothesis} \to \forall \text{target}, \exists \text{time}, a(\text{time}) = \text{target}$$

6. **Bilateral Logical Equivalence (`recaman_surjective_iff_not_least_missing_target`)**:
   $$(\forall \text{target}, \exists \text{time}, a(\text{time}) = \text{target}) \iff (\forall \text{target}, \text{LeastMissingTarget target} \to \text{False})$$

7. **Grand Surjectivity Architecture Synthesis (`grand_surjectivity_architecture_synthesis`)**:
   Unifies the tail dichotomy, well-founded reduction, bilateral equivalence, branch
   reduction, and classical schemas (`TargetTailReturn` and `CoverageOracle`) into a
   single master architecture theorem.

Lean formal declarations in `Recaman/Surjectivity.lean`:
- `Recaman.PermanentHighEscape`
- `Recaman.CorridorReentry`
- `Recaman.least_missing_target_tail_dichotomy`
- `Recaman.NoPermanentHighEscapeHypothesis`
- `Recaman.NoCorridorReentryHypothesis`
- `Recaman.not_least_missing_target_of_branch_obstructions`
- `Recaman.surjective_of_not_least_missing_target`
- `Recaman.surjective_of_branch_obstructions`
- `Recaman.not_least_missing_target_of_surjective`
- `Recaman.recaman_surjective_iff_not_least_missing_target`
- `Recaman.grand_surjectivity_architecture_synthesis`

## Evidence and Audit
- Lean check: `Recaman/Audit.lean` audited and verified with `lake build Recaman.Audit`.
- Kernel axioms: `{propext, Classical.choice, Quot.sound}` (0 sorry, 0 admit, 0 native_decide).
- Evidence ID: `E-339` in `docs/EVIDENCE_REGISTRY.tsv`.
