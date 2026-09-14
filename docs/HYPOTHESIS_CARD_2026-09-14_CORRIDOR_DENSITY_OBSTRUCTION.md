# Hypothesis card: Corridor Density Bounds and Supply Obstruction in Least Missing Tail

- ID: `H-20260914-04`
- Owner: antigravity
- Created: 2026-09-14
- Status: `PROVED-LEAN`
- Research branch: Theme 3 (Corridor Density Bounds and Supply Obstruction in Least Missing Tail)

## Exact statement

For any hypothetical least missing target $m$ in the Recamán sequence:

1. **Linear Subtraction Lower Bound (Non-Sparsity of Subtractions)**:
   In any ledger corridor satisfying $\text{upperTri}(t) < 2 \cdot \text{subSum}(t) + 2t$ for $t > 0$:
   $$t \le 4 \cdot \text{subCount}(t) + 2$$
   Consequently, the asymptotic density of subtractions in the corridor satisfies:
   $$\liminf_{t \to \infty} \frac{\text{subCount}(t)}{t} \ge \frac{1}{4}$$
   Subtractions can never become sparse.

2. **Quadratic Subtraction Upper Bound (Non-Dominance of Subtractions)**:
   In any ledger corridor satisfying $2 \cdot \text{subSum}(t) < \text{upperTri}(t)$:
   $$2 \cdot (\text{subCount}(t) \cdot (\text{subCount}(t) + 1)) < t(t + 1)$$
   Consequently, the asymptotic density of subtractions satisfies:
   $$\limsup_{t \to \infty} \frac{\text{subCount}(t)}{t} \le \frac{1}{\sqrt{2}} \approx 0.707$$
   and additions must also have strictly positive asymptotic density:
   $$\liminf_{t \to \infty} \frac{\text{addCount}(t)}{t} \ge 1 - \frac{1}{\sqrt{2}} \approx 0.293$$

3. **Simultaneous Density Rigidity at Canonical Tail Minimum**:
   At the canonical tail minimum of any least missing target $m$ (`LeastMissingTarget target`):
   $$\exists \text{start}, t > 0, \quad \text{MissingStrictAboveTail}(m, \text{start}) \land (t \le 4 \cdot \text{subCount}(t) + 2) \land (2 \cdot \text{subCount}(t)(\text{subCount}(t) + 1) < t(t + 1))$$

4. **Exclusion of Eventual Periodic Behaviors in the Corridor**:
   The canonical Recamán sequence in any least missing target corridor cannot enter an eventual low-SS periodic sign pattern, nor can it enter an eventual periodic sign pattern under Gate T6 capacity induction.

5. **Finite Block Capacity and Drift Obstruction in the Corridor**:
   Across any interval within the corridor:
   $$\text{suppliedCount}(\text{canonicalSign}, t, n) \le \text{subtractionCount}(\text{canonicalSign}, t, n) + 2$$
   Furthermore, any interval in the corridor with net upward drift $\text{signSum}(\text{canonicalSign}, t, n) \ge 3$ must contain at least one unsupplied addition.

Lean formal declarations:
- `Recaman.CorridorDensityObstruction.subCount_lower_bound_of_ledger_corridor`
- `Recaman.CorridorDensityObstruction.subCount_upper_bound_of_ledger_corridor`
- `Recaman.CorridorDensityObstruction.tail_minimum_subCount_bounds`
- `Recaman.CorridorDensityObstruction.corridor_tail_not_eventual_low_ss_periodic`
- `Recaman.CorridorDensityObstruction.corridor_tail_not_eventual_periodic_of_capacity_induction`
- `Recaman.CorridorDensityObstruction.corridor_finite_block_capacity`
- `Recaman.CorridorDensityObstruction.corridor_unsupplied_of_drift`

## Why it matters

- Completes Theme 3 of the post-Issue #73 research roadmap: connecting the hypothetical counterexample to surjectivity (a least missing target $m$) with the non-periodicity theorems (Theme 1 / E-320) and finite block capacity inequalities (Theme 2 / E-321).
- Rigorously bounds the density of the sign sequence in the permanent-above corridor of any least missing target: neither additions nor subtractions can vanish or become sparse, with subtraction density confined to $[0.25, 0.707]$.
- Projects the exact orbit non-periodicity and finite block capacity obstruction into the ledger corridor, establishing that any corridor trajectory is subject to rigid non-periodic drift constraints.

## Provenance and dependencies

- Subtraction ledger and coordinates: `Recaman.SubtractionLedger`, `Recaman.LeastTailLedgerMinimum` (`PROVED-LEAN`).
- Orbit bounds and upper triangular identities: `Recaman.OrbitBounds` (`PROVED-LEAN`).
- Exact orbit non-periodicity: `Recaman.ExactOrbitNonperiodicity` (E-320, `PROVED-LEAN`).
- Finite block capacity: `Recaman.FiniteBlockCapacity` (E-321, `PROVED-LEAN`).
- Axioms: Only standard Lean 4 kernel axioms (`propext`, `Quot.sound`). No `sorry`, `admit`, or `native_decide`.

## Falsification plan and audit results

- Bounds verification: For $t = 1$, $1 \le 4(0) + 2 = 2$ holds trivially, and for $t \ge 1$, $t \le 4 \cdot \text{subCount}(t) + 2$ matches the ledger requirement $a_t < t + m \le 2t$.
- Quadratic bound sharpness: For any sequence where $\text{subSum}(t) \ge \text{upperTri}(\text{subCount}(t))$, the bound is tight.
- Full Lean check: `./scripts/check.sh` builds 452 jobs and passes kernel audit with 3,030 declarations.

## Decision

- Status: `PROVED-LEAN`
- Milestone: Registered as **E-322**.
