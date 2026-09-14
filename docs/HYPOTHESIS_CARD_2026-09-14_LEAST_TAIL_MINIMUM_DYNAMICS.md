# Hypothesis card: Forced Addition Dynamics and Ledger Expansion at Least Tail Minimum

- ID: `H-20260914-07`
- Owner: antigravity
- Created: 2026-09-14
- Status: `PROVED-LEAN`
- Research branch: Theme 5 (Least Tail Minimum Dynamics and Unsupplied Drift)

## Exact statement

For any hypothetical least missing target `target` and its canonical permanent tail minimum `time` certified by `PermanentTailMinimumCertificate target start time firstTime`:

1. **Immediate Step Addition and Subtraction Ledger Conservation**:
   Step $\text{time} + 1$ is a forced addition:
   $$\text{canonicalSign}(\text{time}) = \text{true}, \quad a(\text{time} + 1) = a(\text{time}) + \text{time} + 1$$
   while the subtraction ledger remains strictly constant:
   $$\text{subSum}(\text{time} + 1) = \text{subSum}(\text{time}), \quad \text{subCount}(\text{time} + 1) = \text{subCount}(\text{time})$$

2. **Follow-Up Step Addition and Elevated Ledger Identity**:
   Step $\text{time} + 2$ is also a forced addition:
   $$\text{canonicalSign}(\text{time} + 1) = \text{true}, \quad a(\text{time} + 2) = a(\text{time}) + 2 \cdot \text{time} + 3$$
   $$\text{subSum}(\text{time} + 2) = \text{subSum}(\text{time}), \quad \text{subCount}(\text{time} + 2) = \text{subCount}(\text{time})$$
   satisfying the unshifted ledger identities:
   $$a(\text{time} + 1) + 2 \cdot \text{subSum}(\text{time}) = \text{upperTri}(\text{time} + 1)$$
   $$a(\text{time} + 2) + 2 \cdot \text{subSum}(\text{time}) = \text{upperTri}(\text{time} + 2)$$

3. **Escape to Quotient Band $q \ge 2$**:
   Since $a(\text{time}) \ge \text{target} + 2 \ge 3$, the value at $\text{time} + 2$ strictly exceeds twice the clock:
   $$2 \cdot (\text{time} + 2) < a(\text{time} + 2)$$
   Consequently, in quotient/remainder coordinates $\text{CoordinatesAt}(\text{time} + 2, q_2, r_2)$, the quotient satisfies:
   $$q_2 \ge 2$$

4. **Step $\text{time} + 3$ Dichotomy and Step $\text{time} + 4$ Forced Addition**:
   Step $\text{time} + 3$ is either an addition ($a(\text{time} + 3) = a(\text{time}) + 3 \cdot \text{time} + 6$) or a subtraction ($a(\text{time} + 3) = a(\text{time}) + \text{time}$).
   In either case, $a(\text{time}) < a(\text{time} + 3)$.
   If step $\text{time} + 3$ is a subtraction, then step $\text{time} + 4$ is forced to add ($\neg \text{CanSubtract}(\text{time} + 4)(\text{stateAt}(\text{time} + 3))$) to preserve the tail minimum.

5. **Universal Three-Consecutive-Addition Run (`AAA`)**:
   By `double_forcedAddition_extends`, either step $\text{time}$ was an addition or step $\text{time} + 3$ is a forced addition:
   $$(\neg \text{CanSubtract}(\text{time})(\text{stateAt}(\text{time} - 1))) \lor (\neg \text{CanSubtract}(\text{time} + 3)(\text{stateAt}(\text{time} + 2)))$$
   Consequently, there unconditionally exists a run of three consecutive additions centered at the tail minimum:
   $$\exists t \in \{\text{time} - 1, \text{time}\}, \quad \text{canonicalSign}(t) = \text{true} \land \text{canonicalSign}(t + 1) = \text{true} \land \text{canonicalSign}(t + 2) = \text{true}$$

6. **Unconditional Unsupplied Addition Deficit**:
   Every canonical tail minimum unconditionally forces at least one unsupplied addition:
   $$\exists t \in \{\text{time} - 1, \text{time}\}, \quad 1 \le \text{unsuppliedCount}(\text{canonicalSign}, t, 3)$$
   In particular, a fully supplied regime ($\text{unsuppliedCount} = 0$) is strictly incompatible with the local dynamics at the tail minimum.

7. **Least Missing Target Corridor Deficit**:
   In any hypothetical `LeastMissingTarget target`, the canonical tail minimum in the ledger corridor ($q \le 1$, $2 \cdot \text{subSum}(\text{time}) \le \text{upperTri}(\text{time}) < 2 \cdot \text{subSum}(\text{time}) + 2 \cdot \text{time}$) unconditionally admits an unsupplied addition deficit.

Lean formal declarations in `Recaman/LeastTailMinimumDynamics.lean`:
- `Recaman.tail_minimum_first_canonicalSign`
- `Recaman.tail_minimum_first_value`
- `Recaman.tail_minimum_first_subSum`
- `Recaman.tail_minimum_first_subCount`
- `Recaman.tail_minimum_followup_canonicalSign`
- `Recaman.tail_minimum_followup_value`
- `Recaman.tail_minimum_followup_subSum`
- `Recaman.tail_minimum_followup_subCount`
- `Recaman.tail_minimum_first_ledger_identity`
- `Recaman.tail_minimum_followup_ledger_identity`
- `Recaman.tail_minimum_followup_gt_twice_time`
- `Recaman.tail_minimum_followup_quotient_ge_two`
- `Recaman.tail_minimum_step3_cases`
- `Recaman.tail_minimum_step3_gt_minimum`
- `Recaman.tail_minimum_step3_subtraction_forces_step4_addition`
- `Recaman.tail_minimum_step_before_addition_or_step3_addition`
- `Recaman.tail_minimum_forces_three_consecutive_additions`
- `Recaman.tail_minimum_forces_unsupplied_addition`
- `Recaman.tail_minimum_incompatible_with_all_supplied`
- `Recaman.least_missing_tail_ledger_unsupplied_deficit`

## Why it matters

- Connects `LeastTailLedgerMinimum` (E-322 corridor and $q \le 1$ classification) with Theme 4 (`DriftResetAccumulation`) and E-324 (`GlobalUnboundednessSupply`).
- Resolves the exact local step dynamics: the tail minimum is not an isolated point, but the anchor of a 2-step forced addition burst followed by a strict escape to $q \ge 2$.
- Eliminates the possibility that the tail minimum belongs to a fully supplied short-periodic regime: an `AAA` run is mathematically forced, generating an unconditional unsupplied addition deficit.

## Provenance and dependencies

- Least tail ledger minimum: `Recaman.LeastTailLedgerMinimum` (`PROVED-LEAN`).
- Subtraction ledger identities: `Recaman.SubtractionLedger` (`PROVED-LEAN`).
- Run extension theorem: `Recaman.NoDoubleAdditionRun` (`PROVED-LEAN`).
- Drift reset accumulation: `Recaman.DriftResetAccumulation` (`PROVED-LEAN`).
- Global unboundedness synthesis: `Recaman.GlobalUnboundednessSupply` (`PROVED-LEAN`).
- Canonical sequence bridge: `Recaman.CanonicalSSFreeSupply` (`PROVED-LEAN`).
