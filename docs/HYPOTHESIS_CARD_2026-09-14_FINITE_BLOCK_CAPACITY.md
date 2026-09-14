# Hypothesis card: Unconditional Finite Block Capacity and Boundary Defect Bounds

- ID: `H-20260914-03`
- Owner: antigravity
- Created: 2026-09-14
- Status: `PROVED-LEAN`
- Research branch: Theme 2 (Finite Block Capacity and Non-Periodic Drift Constraints)

## Exact statement

For any boolean sign sequence $e : \mathbb{Z} \to \text{Bool}$ (with no periodicity assumed), any initial time $t \in \mathbb{Z}$, and any block length $n \in \mathbb{N}$:

1. **Window Potential Bounds**:
   The 7-bit window potential function $\Phi : \text{Window} \to \mathbb{Z}$ satisfies:
   $$0 \le \Phi(s) \le 2 \quad (\forall s \in \text{Window})$$
   Consequently, for any two windows $s_1, s_2$, $\Phi(s_1) - \Phi(s_2) \le 2$.

2. **Unconditional Finite Block Capacity Inequality**:
   Across any interval $[t, t + n)$:
   $$\text{suppliedCount}(e, t, n) \le \text{subtractionCount}(e, t, n) + 2$$
   The boundary defect is universally bounded by 2, independent of the block length $n$.
   This constant 2 is sharp (achieved by the 2-step trajectory `[True, True]` starting from window 45).

3. **Finite Block Net Drift Obstruction**:
   Whenever a block exhibits a net upward drift satisfying $\text{signSum}(e, t, n) \ge 3$,
   there must exist at least one unsupplied addition within the block:
   $$\text{suppliedCount}(e, t, n) < \text{additionCount}(e, t, n)$$
   Quantitatively, the supply deficit satisfies:
   $$\text{additionCount}(e, t, n) - \text{suppliedCount}(e, t, n) \ge \text{signSum}(e, t, n) - 2$$

4. **Internal Concatenation Cancellation**:
   Across any composite interval formed by concatenating $k$ contiguous sub-blocks,
   the telescoping nature of $\Phi$ ensures that all internal interface defects cancel identically:
   $$\sum_{i=0}^{k-1} (\Phi(w_{i+1}) - \Phi(w_i)) = \Phi(w_k) - \Phi(w_0) \le 2$$
   Hence the total defect remains $\le 2$ regardless of the number of partition blocks $k$.

5. **Application to Exact Recamán Orbits**:
   For any seeded orbit $\text{absoluteSign}(b, s, n)$ or canonical Recamán sequence $\text{canonicalSign}(n)$,
   every interval of length $n$ with net drift $\ge 3$ contains an addition phase that cannot be supplied by any lag $\le 7$.

Lean formal declarations:
- `Recaman.FiniteBlockCapacity.potential_nonneg`
- `Recaman.FiniteBlockCapacity.potential_le_two`
- `Recaman.FiniteBlockCapacity.potential_diff_le_two`
- `Recaman.FiniteBlockCapacity.chargeSum_le_two`
- `Recaman.FiniteBlockCapacity.finite_block_capacity`
- `Recaman.FiniteBlockCapacity.finite_block_unsupplied_of_signSum_ge_three`
- `Recaman.FiniteBlockCapacity.finite_block_unsupplied_deficit`
- `Recaman.FiniteBlockCapacity.chargeSum_add`
- `Recaman.FiniteBlockCapacity.multiblock_composite_capacity`
- `Recaman.FiniteBlockCapacity.seeded_orbit_finite_block_capacity`
- `Recaman.FiniteBlockCapacity.seeded_orbit_unsupplied_of_drift`
- `Recaman.FiniteBlockCapacity.canonical_orbit_finite_block_capacity`
- `Recaman.FiniteBlockCapacity.canonical_orbit_unsupplied_of_drift`

## Why it matters

- Discharges Theme 2 of the post-Issue #73 research roadmap: extending capacity inequalities beyond periodic words to arbitrary finite blocks and variable-length segments.
- Shows that non-periodic, pseudo-periodic, and drift-reset regimes are strictly constrained by finite block capacity with an explicit, non-accumulating boundary defect ($C = 2$).
- Proves that any interval with net drift $\ge 3$ forces the existence of unsupplied additions, directly constraining positive drift in actual Recamán orbits.

## Provenance and dependencies

- Potential step inequality: `Recaman.ShortPeriodicSupply.potential_step` (`PROVED-LEAN`).
- Charge sum count decomposition: `Recaman.ShortPeriodicSupply.chargeSum_eq_counts` (`PROVED-LEAN`).
- Sign sum count decomposition: `Recaman.ShortPeriodicSupply.signSum_eq_counts` (`PROVED-LEAN`).
- Telescoping inequality: `Recaman.ShortPeriodicSupply.chargeSum_le_potential` (`PROVED-LEAN`).
- Axioms: Only standard Lean 4 kernel axioms (`propext`, `Quot.sound`). No `Classical.choice`, `sorry`, `admit`, or `native_decide`.

## Falsification plan and audit results

- Sharpness of $C = 2$: Verified via exhaustive BFS over all 128 states and paths up to length 20 that $\max \text{chargeSum} = 2$.
- Explicit witness: Window $s = 45$ (`0101101`) followed by `[True, True]` achieves $\text{chargeSum} = 2$ with $\text{subtractionCount} = 0$, $\text{suppliedCount} = 2$.
- Defect $\ge 3$ impossibility: Formally checked by Lean kernel without axioms beyond `propext` and `Quot.sound`.
- Full Lean check: `./scripts/check.sh` builds 451 jobs and passes kernel audit with 3,023 declarations.

## Decision

- Status: `PROVED-LEAN`
- Milestone: Registered as **E-321**.
