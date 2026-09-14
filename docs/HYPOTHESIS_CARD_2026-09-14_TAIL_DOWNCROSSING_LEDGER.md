# Hypothesis card: Tail Downcrossing Dynamics and Ledger Obstructions

- ID: `H-20260914-08`
- Owner: antigravity
- Created: 2026-09-14
- Status: `PROVED-LEAN`
- Research branch: Theme 5 (Least Tail Downcrossing Dynamics and Ledger Constraints)

## Exact statement

For any hypothetical least missing target `target` and its canonical permanent tail minimum `time` certified by `PermanentTailMinimumCertificate target start time firstTime`:

1. **Subtraction Counter Monotonicity**:
   The subtraction counter $\text{subCount}$ is monotonically non-decreasing:
   $$\forall a, b \in \mathbb{N}, \quad a \le b \implies \text{subCount}(a) \le \text{subCount}(b)$$

2. **Tail Descent Barrier**:
   At any time $k \ge \text{start}$ in the tail, if the orbit value is below $k + 1 + a(\text{time})$, subtraction is strictly impossible:
   $$a(k) < k + 1 + a(\text{time}) \implies \neg \text{CanSubtract}(k + 1)(\text{stateAt } k)$$
   Consequently, any legal subtraction in the tail requires:
   $$\text{CanSubtract}(k + 1)(\text{stateAt } k) \implies k + 1 + a(\text{time}) \le a(k)$$

3. **Strict Landing Elevation Above Minimum**:
   Every subtraction in the tail at time $k \ge \text{time}$ lands strictly above the tail minimum:
   $$\text{CanSubtract}(k + 1)(\text{stateAt } k) \implies a(\text{time}) < a(k + 1)$$
   because $a(\text{time})$ is already a historical value ($\in \text{valuesThrough } k$) and cannot be revisited by a legal subtraction.
   Consequently, the prior height bound is sharpened to:
   $$k + 2 + a(\text{time}) \le a(k)$$

4. **Downcrossing Step Characterization**:
   An addition step from $2k \le a(k)$ can never cross below $2(k + 1)$ (since $a(k + 1) = a(k) + k + 1 \ge 3k + 1 \ge 2k + 2$).
   Therefore, every downcrossing from $2k \le a(k)$ to $a(k + 1) < 2(k + 1)$ MUST be a subtraction step:
   $$2k \le a(k) \land a(k + 1) < 2(k + 1) \implies \text{CanSubtract}(k + 1)(\text{stateAt } k)$$

5. **Prior State in Quotient Band $q = 2$**:
   At any downcrossing step, the prior state satisfies:
   $$2k \le a(k) < 3k + 3$$
   placing the prior state firmly in quotient band $q = 2$.

6. **Ledger Clock Consumption and Cumulative Growth**:
   Every downcrossing step deposits the entire clock into the subtraction ledger:
   $$\text{subSum}(k + 1) = \text{subSum}(k) + k + 1, \quad \text{subCount}(k + 1) = \text{subCount}(k) + 1$$
   $$\text{subSum}(\text{time}) + (k + 1) \le \text{subSum}(k + 1), \quad \text{subCount}(\text{time}) + 1 \le \text{subCount}(k + 1)$$

7. **Two-Sided Ledger Corridor Re-entry**:
   The downcrossing landing value satisfies the two-sided ledger corridor:
   $$2 \cdot \text{subSum}(k + 1) + (a(\text{time}) + 1) \le \text{upperTri}(k + 1) < 2 \cdot \text{subSum}(k + 1) + 2(k + 1)$$

8. **Quotient Band 0 Ephemerality**:
   Quotient band 0 ($a(k) < k$) is strictly ephemeral in the tail: any visit forces the next step to add and immediately jump to quotient band $q \ge 1$.

9. **Double Subtraction Exclusion from Escape**:
   Two consecutive subtractions cannot occur immediately from the escape state at $\text{time} + 2$:
   $$\neg (\text{CanSubtract}(\text{time} + 3)(\text{stateAt}(\text{time} + 2)) \land \text{CanSubtract}(\text{time} + 4)(\text{stateAt}(\text{time} + 3)))$$

10. **Least Missing Target Downcrossing Synthesis**:
    In any hypothetical `LeastMissingTarget target`, every downcrossing from $q \ge 2$ back into the corridor is a certified subtraction that advances the subtraction ledger, lands strictly above $a(\text{time})$, and satisfies the corridor bounds.

Lean formal declarations in `Recaman/TailDowncrossingLedger.lean`:
- `Recaman.subCount_mono`
- `Recaman.tail_descent_barrier`
- `Recaman.tail_subtraction_lower_bound`
- `Recaman.tail_subtraction_result_ge_minimum`
- `Recaman.tail_subtraction_result_gt_minimum`
- `Recaman.tail_subtraction_prior_bound_sharp`
- `Recaman.addition_step_cannot_cross_below_twice`
- `Recaman.downcrossing_step_must_be_subtraction`
- `Recaman.downcrossing_prior_height_bounds`
- `Recaman.downcrossing_subSum_increase`
- `Recaman.downcrossing_subCount_increase`
- `Recaman.tail_downcrossing_value_bounds`
- `Recaman.tail_downcrossing_ledger_corridor_reentry`
- `Recaman.quotient_zero_ephemeral_in_tail`
- `Recaman.no_double_subtraction_from_tail_escape`
- `Recaman.tail_downcrossing_subSum_ge_time`
- `Recaman.tail_downcrossing_subCount_gt_time`
- `Recaman.least_missing_tail_downcrossing_ledger_obstruction`

## Why it matters

- Discovers and formalizes the **Tail Descent Barrier**: in any tail, no subtraction can ever occur unless $a(k) \ge k + 1 + a(\text{time})$.
- Proves that every downcrossing below the linear ray $2(k + 1)$ is strictly a subtraction step from quotient band $q = 2$.
- Establishes that every downcrossing strictly advances the subtraction ledger and counter ($\text{subSum}$ and $\text{subCount}$), preventing infinite downcrossings without ledger exhaustion.

## Provenance and dependencies

- Subtraction ledger identities: `Recaman.SubtractionLedger` (`PROVED-LEAN`).
- Least tail minimum dynamics: `Recaman.LeastTailMinimumDynamics` (`PROVED-LEAN`).
- Least tail ledger minimum: `Recaman.LeastTailLedgerMinimum` (`PROVED-LEAN`).
- Least tail ledger provenance: `Recaman.LeastTailLedgerProvenance` (`PROVED-LEAN`).
