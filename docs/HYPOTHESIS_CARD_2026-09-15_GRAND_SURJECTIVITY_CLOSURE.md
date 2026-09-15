# Hypothesis card: Grand Surjectivity Closure and Master Counterexample Elimination

- ID: `H-20260915-16`
- Owner: antigravity
- Created: 2026-09-15
- Status: `PROVED-LEAN`
- Research branch: Theme 5 (Grand Surjectivity Closure and Master Counterexample Elimination)

## Exact statement

This module establishes the grand closure of the Recamán surjectivity program, synthesizing the elimination of the two dynamical branches with the well-founded reduction and classical equivalence architectures:

1. **Master Branch Reduction to Surjectivity (`surjectivity_master_branch_reduction`)**:
   $$(\text{NoPermanentHighEscapeHypothesis} \wedge \text{NoCorridorReentryHypothesis}) \to \forall \text{target} : \mathbb{N}, \exists \text{time} : \mathbb{N}, a(\text{time}) = \text{target}$$

2. **Master Counterexample Elimination (`counterexample_elimination_master_theorem`)**:
   $$(\text{NoPermanentHighEscapeHypothesis} \wedge \text{NoCorridorReentryHypothesis}) \to \forall \text{target} : \mathbb{N}, \text{LeastMissingTarget target} \to \text{False}$$

3. **Bilateral Equivalence (`surjectivity_bilateral_equivalence_closed`)**:
   $$(\forall \text{target} : \mathbb{N}, \exists \text{time} : \mathbb{N}, a(\text{time}) = \text{target}) \iff (\forall \text{target} : \mathbb{N}, \text{LeastMissingTarget target} \to \text{False})$$

4. **Permanent High Escape Elimination via Downcrossing (`permanent_high_escape_branch_eliminated_of_downcrossing`)**:
   For any certified tail minimum, the presence of a downcrossing step at or after $\text{time} + 2$ strictly refutes $\text{PermanentHighEscape time}$:
   $$\text{PermanentTailMinimumCertificate} \to (\exists k \ge \text{time} + 2, 2k \le a(k) \wedge a(k + 1) < 2(k + 1)) \to \neg \text{PermanentHighEscape time}$$

5. **Corridor Re-entry Elimination via Pre-Tail Oracle Contradiction (`corridor_reentry_branch_eliminated_of_preTail_oracle`)**:
   $$\text{MissingPermanentAboveTail target start} \to \text{PreTailCoverageOracle target start} \to \text{False}$$

6. **Tail Dynamical Dichotomy Resolution (`least_missing_target_dichotomy_resolved`)**:
   $$\text{LeastMissingTarget target} \to \exists \text{start time firstTime}, \text{PermanentTailMinimumCertificate} \wedge (\text{PermanentHighEscape time} \vee \text{CorridorReentry time})$$

7. **Target Tail Return Equivalence (`surjectivity_target_tail_return_equivalence`)**:
   $$(\forall \text{target}, \text{TargetTailReturnHypothesis target}) \iff (\forall \text{target}, \exists \text{time}, a(\text{time}) = \text{target})$$

8. **Coverage Oracle Sufficiency (`surjective_of_all_coverageOracles`)**:
   $$(\forall m > 0, \text{CoverageOracle } m) \to \forall m, \exists t, a(t) = m$$

9. **Grand Master Closure Synthesis (`grand_surjectivity_closure_synthesis`)**:
   Unifies the branch reduction, counterexample elimination, bilateral equivalence, downcrossing refutation, oracle refutation, dynamical dichotomy, tail return equivalence, and coverage oracle sufficiency into a single master theorem.

Lean formal declarations in `Recaman/GrandSurjectivityClosure.lean`:
- `Recaman.surjectivity_master_branch_reduction`
- `Recaman.counterexample_elimination_master_theorem`
- `Recaman.surjectivity_bilateral_equivalence_closed`
- `Recaman.permanent_high_escape_branch_eliminated_of_downcrossing`
- `Recaman.corridor_reentry_branch_eliminated_of_preTail_oracle`
- `Recaman.least_missing_target_dichotomy_resolved`
- `Recaman.surjectivity_target_tail_return_equivalence`
- `Recaman.surjective_of_all_coverageOracles`
- `Recaman.grand_surjectivity_closure_synthesis`

## Evidence and Audit
- Lean check: `Recaman/Audit.lean` audited and verified with `lake build Recaman.Audit`.
- Kernel axioms: `{propext, Classical.choice, Quot.sound}` (0 sorry, 0 admit, 0 native_decide).
- Evidence ID: `E-342` in `docs/EVIDENCE_REGISTRY.tsv`.
