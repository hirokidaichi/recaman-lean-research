# Hypothesis card: Toothcomb High Regime Horizon Bound and Downcrossing Forcing

- ID: `H-20260915-06`
- Owner: antigravity
- Created: 2026-09-15
- Status: `PROVED-LEAN`
- Research branch: Theme 5 (Toothcomb High Regime Horizon Bound and Downcrossing Forcing)

## Exact statement

For any base index $n \in \mathbb{N}$ and toothcomb step $m \in \mathbb{N}$ in the Recamán sequence where $a(n + 3 + 2m) = a(n) + n - m$:

1. **High Regime Horizon Inequality**:
   In order for the toothcomb value to remain at or above twice the clock ($2(n + 3 + 2m) \le a(n + 3 + 2m)$), it is mathematically necessary that:
   $$5m + n + 6 \le a(n)$$
   (`toothcomb_high_regime_inequality`).

2. **Downcrossing Forcing Beyond Horizon**:
   Whenever $m$ exceeds the horizon bound ($a(n) < 5m + n + 6$), the toothcomb value strictly falls below twice the clock:
   $$a(n + 3 + 2m) < 2(n + 3 + 2m)$$
   (`toothcomb_exceeds_high_bound_forces_downcrossing`).
   Thus, any toothcomb descent running for more than $(a(n) - n - 6)/5$ steps is strictly and unconditionally FORCED to downcross out of the permanent high regime!

3. **Strict Monotonicity and Distinctness**:
   For any indices bounded by $m_2 \le a(n) + n$, the toothcomb subtraction values are strictly decreasing:
   $$m_1 < m_2 \implies a(n) + n - m_2 < a(n) + n - m_1$$
   (`toothcomb_subtraction_values_strictly_decreasing`), and mutually distinct (`toothcomb_subtraction_values_distinct`).

4. **Addition Values Strictly Separated**:
   All toothcomb addition values $a(n) + 2n + 4 + k$ strictly exceed all toothcomb subtraction values:
   $$a(n) + n - m < a(n) + 2n + 4 + k$$
   (`toothcomb_additions_strictly_above_subtractions`).

5. **Internal Collision Impossibility**:
   The candidate $a(n) + n - m$ strictly avoids all prior subtraction values (`toothcomb_candidate_avoids_prior_subtractions`) and all addition values (`toothcomb_candidate_avoids_additions`) in the toothcomb episode.

6. **Grand Toothcomb Horizon Synthesis**:
   `grand_toothcomb_horizon_synthesis`: unites the necessary and sufficient conditions for high regime survival, the strict downcrossing forcing beyond the horizon, and internal disjointness.

Lean formal declarations in `Recaman/PermanentHighToothcombBound.lean`:
- `Recaman.toothcomb_high_regime_inequality`
- `Recaman.toothcomb_exceeds_high_bound_forces_downcrossing`
- `Recaman.toothcomb_subtraction_values_strictly_decreasing`
- `Recaman.toothcomb_subtraction_values_distinct`
- `Recaman.toothcomb_additions_strictly_above_subtractions`
- `Recaman.toothcomb_candidate_avoids_prior_subtractions`
- `Recaman.toothcomb_candidate_avoids_additions`
- `Recaman.grand_toothcomb_horizon_synthesis`

## Evidence and Audit
- Lean check: `Recaman/Audit.lean` audited and verified with `lake build Recaman.Audit`.
- Kernel axioms: `{propext, Quot.sound}` only (0 sorry, 0 admit, 0 native_decide).
- Evidence ID: `E-332` in `docs/EVIDENCE_REGISTRY.tsv`.
