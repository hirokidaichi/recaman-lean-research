# Hypothesis card: Elimination of the Permanent High Escape Branch

- ID: `H-20260915-14`
- Owner: antigravity
- Created: 2026-09-15
- Status: `PROVED-LEAN`
- Research branch: Theme 5 (Elimination of the Permanent High Escape Branch)

## Exact statement

For any certified tail minimum certificate `PermanentTailMinimumCertificate target start time firstTime`:

1. **Downcrossing Contradiction (`downcrossing_contradicts_permanent_high`)**:
   Any downcrossing step $k \ge \text{time} + 2$ with $a(k + 1) < 2(k + 1)$ directly
   refutes `PermanentHighEscape time`:
   $$\text{time} + 2 \le k \to a(k + 1) < 2(k + 1) \to \text{PermanentHighEscape time} \to \text{False}$$

2. **Downcrossing Equivalence (`permanent_high_escape_iff_no_downcrossing`)**:
   `PermanentHighEscape time` is logically equivalent to the complete absence of
   downcrossing steps at or after $\text{time} + 2$:
   $$\text{PermanentHighEscape time} \iff \neg \exists k, \text{time} + 2 \le k \wedge 2k \le a(k) \wedge a(k + 1) < 2(k + 1)$$

3. **Corridor Re-entry Forcing (`corridor_reentry_of_not_permanent_high`)**:
   Refuting `PermanentHighEscape time` unconditionally forces the counterexample
   to perform a certified corridor re-entry (`CorridorReentry time`):
   $$\text{LeastMissingTarget target} \to \text{NoPermanentHighEscapeHypothesis} \to \exists s t ft, \text{PermanentTailMinimumCertificate} \wedge \text{CorridorReentry } t$$

4. **Pigeonhole Blocker Capacity at Escape State (`escape_state_pigeonhole_capacity`)**:
   At $n = \text{time} + 2$, the $n$ candidate values cannot all be blocked by the
   $n - 1$ historical values $j < n$, guaranteeing an unblocked candidate exceeding $2n$:
   $$\exists m < n, (\forall j < n, a(j) \neq a(n) + n - m) \wedge 2n < a(n) + n - m$$

5. **Historical Avoidance (`escape_state_unblocked_candidate_avoids_history`)**:
   The unblocked candidate strictly avoids $\text{valuesThrough}(n - 1)$ and all $a(j)$ for $j < n$.

6. **Descent Landing Below Twice Clock (`escape_state_descent_strictly_below_twice_clock`)**:
   Because $a(\text{time} + 2) < 6(\text{time} + 2) + 1$ (E-338), the toothcomb descent at step $m = n$
   strictly forces landing below twice its clock: $\text{val} < 2(n + 3 + 2n)$.

7. **Ledger and Counter Caps in High Regime (`permanent_high_subSum_capped_of_escape`)**:
   In any permanent high orbit, $\text{subSum}$ and $\text{subCount}$ are permanently constrained
   by the triangular capacity bounds:
   $$\forall n \ge \text{time} + 2, 2 \cdot \text{subSum}(n) \le \text{upperTri}(n) - 2n \wedge 2 \cdot \text{upperTri}(\text{subCount } n) + 2n \le \text{upperTri}(n)$$

8. **Grand Synthesis (`grand_no_permanent_high_escape_synthesis`)**:
   Unifies downcrossing contradictions, corridor re-entry forcing, pigeonhole blocker
   capacity, and descent forcing into a single master theorem.

Lean formal declarations in `Recaman/NoPermanentHighEscape.lean`:
- `Recaman.downcrossing_contradicts_permanent_high`
- `Recaman.permanent_high_escape_iff_no_downcrossing`
- `Recaman.corridor_reentry_of_not_permanent_high`
- `Recaman.escape_state_pigeonhole_capacity`
- `Recaman.escape_state_unblocked_candidate_avoids_history`
- `Recaman.escape_state_descent_strictly_below_twice_clock`
- `Recaman.permanent_high_subSum_capped_of_escape`
- `Recaman.permanent_high_subCount_capped_of_escape`
- `Recaman.grand_no_permanent_high_escape_synthesis`

## Evidence and Audit
- Lean check: `Recaman/Audit.lean` audited and verified with `lake build Recaman.Audit`.
- Kernel axioms: `{propext, Classical.choice, Quot.sound}` (0 sorry, 0 admit, 0 native_decide).
- Evidence ID: `E-340` in `docs/EVIDENCE_REGISTRY.tsv`.
