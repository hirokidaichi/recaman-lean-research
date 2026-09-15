# Hypothesis card: Elimination of the Corridor Re-entry Branch

- ID: `H-20260915-15`
- Owner: antigravity
- Created: 2026-09-15
- Status: `PROVED-LEAN`
- Research branch: Theme 5 (Elimination of the Corridor Re-entry Branch)

## Exact statement

For any certified tail minimum certificate `PermanentTailMinimumCertificate target start time firstTime` and missing permanent tail `MissingPermanentAboveTail target start`:

1. **Tight Ledger Corridor Bounds (`corridor_reentry_ledger_bounds`)**:
   In any corridor re-entry, the re-entry state satisfies the tight ledger corridor bounds:
   $$\exists k \ge \text{time} + 2, 2 \cdot \text{subSum}(k + 1) + (a(\text{time}) + 1) \le \text{upperTri}(k + 1) < 2 \cdot \text{subSum}(k + 1) + 2(k + 1)$$

2. **Clock Deposit Lower Bound (`corridor_reentry_clock_deposit`)**:
   Any corridor re-entry downcrossing step deposits its clock into $\text{subSum}$:
   $$\exists k \ge \text{time} + 2, k + 1 \le \text{subSum}(k + 1)$$

3. **Value Sandwich in Corridor (`corridor_reentry_value_in_corridor`)**:
   The landing value of any corridor re-entry is sandwiched between $a(\text{time}) + 1$ and $2(k + 1)$:
   $$\exists k \ge \text{time} + 2, a(\text{time}) + 1 \le a(k + 1) < 2(k + 1)$$

4. **Confinement to Finite Prefix (`missing_permanent_tail_values_le_target_before_start`)**:
   In any missing permanent tail, all values at or below $\text{target}$ are strictly confined to the finite pre-tail prefix $j < \text{start}$:
   $$\forall n, a(n) \le \text{target} \to n < \text{start}$$

5. **Absolute Target Missingness (`missing_permanent_tail_pre_tail_capacity_bound`)**:
   In any missing permanent tail, no step can produce $\text{target}$:
   $$\forall n, a(n) = \text{target} \to \text{False}$$

6. **Refutation of Pre-Tail Coverage Oracle (`corridor_reentry_contradicts_preTail_oracle`)**:
   Direct contradiction between missing permanent tail and finite pre-tail oracle:
   $$\text{PreTailCoverageOracle target start} \to \text{False}$$

7. **Recurrent Subtraction Ledger Divergence (`recurrent_corridor_reentry_subSum_divergence`)**:
   If corridor re-entries recur past arbitrary bounds, the subtraction ledger diverges beyond any bound $B$ while satisfying the corridor bounds:
   $$\forall B, (\forall H, \dots) \to \exists k \ge \text{time}, B < \text{subSum}(k + 1) \wedge \dots$$

8. **Grand Synthesis (`grand_no_corridor_reentry_synthesis`)**:
   Unifies corridor ledger bounds, clock deposit, value bounds, finite prefix confinement, pre-tail oracle refutation, and recurrent ledger divergence into a single master theorem.

Lean formal declarations in `Recaman/NoCorridorReentry.lean`:
- `Recaman.corridor_reentry_ledger_bounds`
- `Recaman.corridor_reentry_clock_deposit`
- `Recaman.corridor_reentry_value_in_corridor`
- `Recaman.missing_permanent_tail_values_le_target_before_start`
- `Recaman.missing_permanent_tail_pre_tail_capacity_bound`
- `Recaman.corridor_reentry_contradicts_preTail_oracle`
- `Recaman.recurrent_corridor_reentry_subSum_divergence`
- `Recaman.grand_no_corridor_reentry_synthesis`

## Evidence and Audit
- Lean check: `Recaman/Audit.lean` audited and verified with `lake build Recaman.Audit`.
- Kernel axioms: `{propext, Quot.sound}` (0 sorry, 0 admit, 0 native_decide).
- Evidence ID: `E-341` in `docs/EVIDENCE_REGISTRY.tsv`.
