# Hypothesis card: Drift Resets and Accumulation of Unsupplied Additions

- ID: `H-20260914-05`
- Owner: antigravity
- Created: 2026-09-14
- Status: `PROVED-LEAN`
- Research branch: Theme 4 (Drift Resets and Accumulation of Unsupplied Additions in Non-Periodic Streams)

## Exact statement

For any boolean sign sequence $e : \mathbb{Z} \to \text{Bool}$, any time $t \in \mathbb{Z}$, and block lengths $n, m, g \in \mathbb{N}$:

1. **Supplied Count Upper Bound**:
   The number of short-supplied additions is unconditionally bounded by the total number of additions:
   $$\text{suppliedCount}(e, t, n) \le \text{additionCount}(e, t, n)$$

2. **Exact Unsupplied Additions Definition**:
   $$\text{unsuppliedCount}(e, t, n) := \text{additionCount}(e, t, n) - \text{suppliedCount}(e, t, n)$$
   which is non-negative and integer-exact:
   $$(\text{unsuppliedCount}(e, t, n) : \mathbb{Z}) = (\text{additionCount}(e, t, n) : \mathbb{Z}) - (\text{suppliedCount}(e, t, n) : \mathbb{Z})$$

3. **Strict Additivity Across Adjacent Intervals**:
   All count metrics are strictly additive across adjacent intervals $[t, t+n)$ and $[t+n, t+n+m)$:
   - $\text{additionCount}(e, t, n + m) = \text{additionCount}(e, t, n) + \text{additionCount}(e, t + n, m)$
   - $\text{subtractionCount}(e, t, n + m) = \text{subtractionCount}(e, t, n) + \text{subtractionCount}(e, t + n, m)$
   - $\text{suppliedCount}(e, t, n + m) = \text{suppliedCount}(e, t, n) + \text{suppliedCount}(e, t + n, m)$
   - $\text{signSum}(e, t, n + m) = \text{signSum}(e, t, n) + \text{signSum}(e, t + n, m)$
   - $\text{unsuppliedCount}(e, t, n + m) = \text{unsuppliedCount}(e, t, n) + \text{unsuppliedCount}(e, t + n, m)$

4. **Monotonic Accumulation**:
   The cumulative count of unsupplied additions is monotonically non-decreasing over time:
   $$\text{unsuppliedCount}(e, t, n) \le \text{unsuppliedCount}(e, t, n + m)$$
   Unsupplied additions are never erased or cancelled by future events.

5. **Drift Deficit Inequality**:
   Across any interval:
   $$\text{signSum}(e, t, n) - 2 \le (\text{unsuppliedCount}(e, t, n) : \mathbb{Z})$$
   Whenever $\text{signSum}(e, t, n) \ge 3$, at least $\text{signSum} - 2 \ge 1$ unsupplied additions are produced.

6. **Two-Block Accumulation Across Intervening Resets**:
   Given two disjoint intervals $[t, t + n_1)$ and $[t + n_1 + g, t + n_1 + g + n_2)$ separated by an arbitrary gap of length $g$ (which may feature severe downward drift resets):
   $$\text{unsuppliedCount}(e, t, n_1) + \text{unsuppliedCount}(e, t + n_1 + g, n_2) \le \text{unsuppliedCount}(e, t, n_1 + g + n_2)$$
   Consequently, if both blocks have net drift $\ge 3$, the total span contains at least 2 unsupplied additions, regardless of the drift in the gap.

7. **Drift Boundedness vs. Infinite Unsupplied Additions Dichotomy**:
   - If unsupplied additions on all sub-intervals are bounded by $K$, then the net drift across all sub-intervals is uniformly bounded:
     $$\text{unsuppliedCount}(e, t, n) \le K \implies \text{signSum}(e, t, n) \le K + 2$$
   - Conversely, unbounded drift excursions force unbounded unsupplied additions:
     $$(\forall M, \exists n, M + 2 \le \text{signSum}(e, t, n)) \implies (\forall M, \exists n, M \le \text{unsuppliedCount}(e, t, n))$$

8. **Application to Canonical Recamán Sequence and Corridors**:
   In the canonical sequence $\text{canonicalSign}$ and in any least missing target corridor, unsupplied additions accumulate monotonically, and any sequence of upward drift episodes forces a corresponding accumulation of unsupplied additions.

Lean formal declarations:
- `Recaman.DriftResetAccumulation.suppliedCount_le_additionCount`
- `Recaman.DriftResetAccumulation.unsuppliedCount_eq`
- `Recaman.DriftResetAccumulation.additionCount_add`
- `Recaman.DriftResetAccumulation.subtractionCount_add`
- `Recaman.DriftResetAccumulation.suppliedCount_add`
- `Recaman.DriftResetAccumulation.signSum_add`
- `Recaman.DriftResetAccumulation.unsuppliedCount_add`
- `Recaman.DriftResetAccumulation.unsuppliedCount_mono`
- `Recaman.DriftResetAccumulation.unsuppliedCount_ge_signSum_sub_two`
- `Recaman.DriftResetAccumulation.unsuppliedCount_pos_of_signSum_ge_three`
- `Recaman.DriftResetAccumulation.unsuppliedCount_ge_of_signSum`
- `Recaman.DriftResetAccumulation.unsuppliedCount_two_blocks`
- `Recaman.DriftResetAccumulation.unsuppliedCount_ge_two_of_two_drift_blocks`
- `Recaman.DriftResetAccumulation.drift_le_of_unsupplied_le`
- `Recaman.DriftResetAccumulation.exists_unsupplied_ge_of_exists_signSum_ge`
- `Recaman.DriftResetAccumulation.canonical_unsuppliedCount_mono`
- `Recaman.DriftResetAccumulation.canonical_unsuppliedCount_ge_drift`
- `Recaman.DriftResetAccumulation.corridor_unsupplied_two_drift_blocks`

## Why it matters

- Completes Theme 4 of the post-Issue #73 research program: analyzing drift resets, boundary effects, and the cumulative accumulation of unsupplied additions in non-periodic regimes.
- Resolves the interaction between downward resets and supply deficits: because unsupplied additions are defined by local past windows, they are strictly additive and monotonic. Intervening negative drift (downward resets) can never "repay" or erase previously incurred unsupplied additions.
- Establishes a fundamental dichotomy between uniform drift boundedness and infinite unsupplied addition accumulation, providing a concrete mathematical bridge toward global unboundedness and surjectivity.

## Provenance and dependencies

- Finite block capacity and potential variation: `Recaman.FiniteBlockCapacity` (E-321, `PROVED-LEAN`).
- Short periodic supply count definitions: `Recaman.ShortPeriodicSupply` (E-067 / E-070, `PROVED-LEAN`).
- Canonical signs: `Recaman.CanonicalSSFreeSupply` (`PROVED-LEAN`).
- Corridor density bounds: `Recaman.CorridorDensityObstruction` (E-322, `PROVED-LEAN`).
- Axioms: Only standard Lean 4 kernel axioms (`propext`, `Quot.sound`). 0 `Classical.choice`, 0 `sorry`, 0 `admit`, 0 `native_decide`.

## Falsification plan and audit results

- Additivity verification: Tested on trivial (n=0) and composite blocks with alternating signs and large negative reset gaps.
- Non-cancellation property: Formally verified that an arbitrary gap $g$ with negative drift cannot reduce $\text{unsuppliedCount}$.
- Full Lean check: `./scripts/check.sh` builds 453 jobs and passes kernel audit with 3,048 declarations.

## Decision

- Status: `PROVED-LEAN`
- Milestone: Registered as **E-323**.
