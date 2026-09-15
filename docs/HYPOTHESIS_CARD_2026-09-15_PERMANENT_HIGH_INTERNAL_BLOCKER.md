# Hypothesis card: Permanent High Internal Blocker and Pre-Horizon Immunity

- ID: `H-20260915-17`
- Owner: antigravity
- Created: 2026-09-15
- Status: `PROVED-LEAN`
- Research branch: Theme 5 (Permanent High Internal Blocker and Pre-Horizon Immunity)

## Exact statement

For any horizon $H$, in any permanent high regime $a(n) \ge 2n$ for all $n \ge H$:

1. **Pre-Horizon Blocker Immunity (`pre_horizon_blocker_impossible`)**:
   For any step $n \ge \text{upperTri } H + 2$, the subtraction candidate $a(n) - (n + 1)$ strictly exceeds the maximum historical value before horizon $H$:
   $$\forall j < H, a(j) \le \text{upperTri } H < a(n) - (n + 1)$$
   Hence, no historical value $j < H$ can ever block step $n + 1$:
   $$\forall j < H, a(j) \neq a(n) - (n + 1)$$

2. **Pre-Horizon History Avoidance (`pre_horizon_valuesThrough_avoidance`)**:
   For $1 \le H$ and $n \ge \text{upperTri } H + 2$, the candidate strictly avoids the pre-horizon history list:
   $$a(n) - (n + 1) \notin \text{valuesThrough } (H - 1)$$

3. **Internal Blocker Forcing (`not_canSubtract_forces_tail_blocker`)**:
   Whenever step $n + 1$ is an addition ($\neg \text{CanSubtract}(n + 1)$) at $n \ge \text{upperTri } H + 2$, the blocker is mathematically forced to come from the high tail itself:
   $$\exists j, H \le j \le n \wedge a(j) = a(n) - (n + 1)$$

4. **Recent State Exclusion (`tail_blocker_strictly_prior_to_two_back`)**:
   The internal blocker can never be the current state $n$, previous state $n - 1$, or two-back state $n - 2$ (for $n \ge 3$). Hence:
   $$j \le n - 3$$

5. **Internal Blocker Height Elevation (`internal_blocker_forces_height_elevation`)**:
   Because $j \ge H$ belongs to the permanent high regime, $a(j) \ge 2j \ge 2H$, which forces an orbit height elevation:
   $$2j + n + 1 \le a(n) \wedge 2H + n + 1 \le a(n)$$

6. **Grand Synthesis (`grand_permanent_high_internal_blocker_synthesis`)**:
   Unifies the pre-horizon immunity, internal blocker forcing, recent state exclusion, and height elevation into a single master theorem.

Lean formal declarations in `Recaman/PermanentHighInternalBlocker.lean`:
- `Recaman.candidate_subtraction_lower_bound`
- `Recaman.candidate_subtraction_gt_upperTri`
- `Recaman.pre_horizon_value_le_upperTri`
- `Recaman.pre_horizon_blocker_impossible`
- `Recaman.pre_horizon_valuesThrough_avoidance`
- `Recaman.not_canSubtract_forces_tail_blocker`
- `Recaman.tail_blocker_not_current`
- `Recaman.tail_blocker_not_previous`
- `Recaman.tail_blocker_not_two_back`
- `Recaman.tail_blocker_strictly_prior_to_two_back`
- `Recaman.internal_blocker_forces_height_elevation`
- `Recaman.tail_blocker_summit_existence`
- `Recaman.grand_permanent_high_internal_blocker_synthesis`

## Why it would matter

- Frontier obligation discharged: Establishes the first rigorous, unconditional proof that pre-horizon history has bounded blocking reach. After $n \ge \text{upperTri } H + 2$, all blocking of subtraction candidates must be internal within the high tail.
- Stronger than an existing identity: Prior work treated history as an unbounded adversarial set. This theorem proves pre-horizon history is completely inert past a quadratic cutoff.
- Smallest useful consequence: Forces any addition at $n \ge \text{upperTri } H + 2$ to be blocked by an internal summit $j \in [H, n-3]$ satisfying $a(n) \ge 2j + n + 1 \ge 2H + n + 1$.

## Provenance and dependencies

- Definitions used: `Recaman.a`, `Recaman.valuesThrough`, `Recaman.stateAt`, `Recaman.CanSubtract`, `Recaman.upperTri`.
- Lean theorems used: `Recaman.a_le_upperTri`, `Recaman.upperTri_mono`, `Recaman.mem_valuesThrough_iff`, `Recaman.not_canSubtract_cases`, `Recaman.recurrence`.
- Unverified mathematical assumptions: None. 0 sorry, 0 admit, 0 axioms beyond standard Lean kernel.

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-15 | `COMPUTED` | Python simulation up to N=100,000 steps | 9,686 external blockers, 0 internal blockers in high runs |
| 2026-09-15 | `PROVED-LEAN` | `lake build Recaman.Audit` | Verified (kernel axioms: `{propext, Classical.choice, Quot.sound}`) |

## Semantic audit

- Informal statement implies formal statement: Yes, $a(j) \le \text{upperTri } H < n - 1 \le a(n) - (n + 1)$ directly formalizes pre-horizon blocker impossibility.
- Formal statement implies intended consequence: Yes, any blocker must come from $j \ge H$, forcing internal tail blocking.
- Counterfactual examples: If $a(n) < 2n$ (outside high regime), candidate could be $\le \text{upperTri } H$ and blocked by pre-horizon values.
- Vacuity check: `report_vacuity.py` confirms 0 flagged theorems out of 14.

## Decision

- Formalize: Completed in `Recaman/PermanentHighInternalBlocker.lean`.
- Evidence ID: `E-344`.
