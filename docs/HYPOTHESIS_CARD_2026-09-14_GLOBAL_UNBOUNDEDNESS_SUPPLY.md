# Hypothesis card: Global Value Unboundedness and Supply Obstruction Synthesis

- ID: `H-20260914-06`
- Owner: antigravity
- Created: 2026-09-14
- Status: `PROVED-LEAN`
- Research branch: Synthesis (Global Value Unboundedness and Structural Supply Obstructions)

## Exact statement

For the Recamán sequence $a_n$ and any hypothetical missing permanent tail:

1. **Upper Triangular Monotonicity**:
   The triangular numbers $\text{upperTri}(n) = \frac{n(n+1)}{2}$ are monotonically non-decreasing and strictly increasing, reflecting strict inequalities back to the indices:
   $$\forall a, b \in \mathbb{N}, \quad \text{upperTri}(a) < \text{upperTri}(b) \implies a < b$$

2. **Corridor Linear Unboundedness**:
   In any sharp corridor `SharpCorridor target tailStart cutoff`, values grow strictly faster than the linear ray $n + \text{target} + 1$:
   $$\forall c, B \in \mathbb{N}, \exists n > c, \quad B < a_n$$
   with an explicit constructive witness $n = (\text{cutoff} + c + 1) + (B + 1)$.

3. **Reset Stream Blocker and Entry Escalation**:
   In any sharp reset stream `SharpResetStream target tailStart root rootFirstTime`, comb entries strictly exceed every ceiling after any prescribed cutoff:
   $$\forall c, B \in \mathbb{N}, \exists n > c, \quad B < a_n$$
   driven by the escape of terminal blockers past the triangular threshold $\text{upperTri}(c)$.

4. **Universal Missing Permanent Tail Unboundedness**:
   In any hypothetical missing permanent tail `MissingPermanentAboveTail target tailStart`:
   $$\forall \text{cutoff}, B \in \mathbb{N}, \exists n > \text{cutoff}, \quad B < a_n$$
   Consequently, every hypothetical missing tail orbit is unconditionally unbounded in value: $\limsup_{n \to \infty} a_n = \infty$.

5. **Canonical Recamán Orbit Unboundedness**:
   For the standard sequence $a_0 = 0$:
   $$\forall \text{cutoff}, B \in \mathbb{N}, \exists n > \text{cutoff}, \quad B < a_n$$

6. **Structural Addition Run Deficit**:
   Any run of $K \ge 3$ consecutive additions has $\text{signSum} = K$ and forces at least $K - 2$ unsupplied additions:
   $$K - 2 \le (\text{unsuppliedCount}(e, t, K) : \mathbb{Z})$$
   In particular, three consecutive additions `[True, True, True]` force at least one unsupplied addition.

7. **Pattern Exclusion under Full Supply**:
   If all additions in an interval are short-supplied, three consecutive additions (`AAA`) cannot occur anywhere within that interval:
   $$\text{unsuppliedCount}(e, t, 3) = 0 \implies \neg (e(t) \land e(t+1) \land e(t+2))$$

Lean formal declarations:
- `Recaman.GlobalUnboundednessSupply.upperTri_le_upperTri`
- `Recaman.GlobalUnboundednessSupply.upperTri_lt_upperTri`
- `Recaman.GlobalUnboundednessSupply.lt_of_upperTri_lt_upperTri`
- `Recaman.GlobalUnboundednessSupply.corridor_values_unbounded_after`
- `Recaman.GlobalUnboundednessSupply.reset_stream_values_unbounded_after`
- `Recaman.GlobalUnboundednessSupply.missing_permanent_tail_values_unbounded_after`
- `Recaman.GlobalUnboundednessSupply.missing_permanent_tail_values_unbounded`
- `Recaman.GlobalUnboundednessSupply.canonical_orbit_unbounded`
- `Recaman.GlobalUnboundednessSupply.canonical_orbit_unbounded_after`
- `Recaman.GlobalUnboundednessSupply.signSum_of_all_additions`
- `Recaman.GlobalUnboundednessSupply.consecutive_additions_unsupplied_deficit`
- `Recaman.GlobalUnboundednessSupply.three_consecutive_additions_unsupplied`
- `Recaman.GlobalUnboundednessSupply.no_three_consecutive_additions_if_all_supplied`

## Why it matters

- Connects the structural bifurcation of `SharpResidualKernel` (corridor linear ray vs. reset-stream blocker escape) with the unsupplied additions deficit from Theme 4 (`DriftResetAccumulation`).
- Proves that ANY hypothetical counterexample to surjectivity must have strictly unbounded values $a_n \to \infty$ across both residual branches.
- Establishes a concrete local pattern exclusion: if an orbit were to operate under full short supply ($\text{unsuppliedCount} = 0$), runs of three consecutive additions (`AAA`) are universally excluded.

## Provenance and dependencies

- Sharp residual kernel: `Recaman.SharpResidualKernel` (`PROVED-LEAN`).
- Orbit bounds and upper triangular identities: `Recaman.OrbitBounds` (`PROVED-LEAN`).
- Eventual escape: `Recaman.EventualEscape` (`PROVED-LEAN`).
- Drift resets and unsupplied accumulation: `Recaman.DriftResetAccumulation` (E-323, `PROVED-LEAN`).
- Axioms: Standard Lean 4 kernel axioms `{propext, Classical.choice, Quot.sound}`.

## Falsification plan and audit results

- Triplet addition witness: Step 1, 2, 3 in the standard sequence produce values 1, 3, 6 with signs `[True, True, True]`. Step 3 is verified to have $\text{lagSum} = 3 \ne 1$, confirming it is unsupplied as predicted by the theorem.
- Triangular reflection: Checked by Lean arithmetic that $\text{upperTri}(c) < \text{upperTri}(n) \implies c < n$.
- Full Lean check: `./scripts/check.sh` builds 454 jobs and passes kernel audit with 3,061 declarations.

## Decision

- Status: `PROVED-LEAN`
- Milestone: Registered as **E-324**.
