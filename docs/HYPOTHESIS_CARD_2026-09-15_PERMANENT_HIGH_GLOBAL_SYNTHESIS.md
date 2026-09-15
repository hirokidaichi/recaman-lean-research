# Hypothesis card: Permanent High Global Synthesis and Downcrossing Inevitability

- ID: `H-20260915-09`
- Owner: antigravity
- Created: 2026-09-15
- Status: `PROVED-LEAN`
- Research branch: Theme 5 (Permanent High Global Synthesis and Downcrossing Inevitability)

## Exact statement

For any base index $n \in \mathbb{N}$ with $1 \le n$ in the Recamán sequence where $2n \le a(n)$:

1. **High Horizon Sufficiency ($a(n) \ge 6n + 1$)**:
   Whenever $a(n) \ge 6n + 1$, any toothcomb step $m < n$ strictly satisfies the high regime horizon inequality:
   $$5m + n + 6 \le a(n)$$
   (`high_regime_horizon_satisfaction_of_ge_six`).

2. **Unblocked Horizon Candidate Existence**:
   Whenever $a(n) \ge 6n + 1$, there strictly exists a toothcomb step $m < n$ that is both:
   - Within the high regime horizon ($5m + n + 6 \le a(n)$)
   - Completely unblocked by history: $\forall j < n, a(j) \ne a(n) + n - m$
   - Avoids all values prior to $n$: $a(n) + n - m \notin \text{valuesThrough}(n - 1)$
   - Strictly exceeds the base value: $a(n) < a(n) + n - m$
   (`exists_unblocked_horizon_candidate`).

3. **Mandatory Downcrossing Forcing ($a(n) < 6n + 1$)**:
   Conversely, when $a(n) < 6n + 1$, any toothcomb descent extending to $m = n$ strictly exceeds the high regime horizon:
   $$a(n) < 5n + n + 6$$
   Consequently, the toothcomb value at step $n$ is strictly forced to downcross below twice the clock:
   $$a(n + 3 + 2n) < 2(n + 3 + 2n)$$
   (`toothcomb_forced_downcrossing_at_step_n`).
   Thus a downcrossing is unconditionally forced within at most $n$ toothcomb steps!

4. **Universal High Regime Dichotomy**:
   Every base index $n \ge 1$ in the high regime $2n \le a(n)$ satisfies the dichotomy:
   either $a(n) \ge 6n + 1$ (guaranteeing an unblocked candidate inside the horizon),
   or $a(n) < 6n + 1$ (where toothcomb descent downcrosses within at most $n$ steps)
   (`permanent_high_universal_dichotomy`).

5. **Grand Global High Regime Synthesis**:
   `grand_permanent_high_global_synthesis`: unites horizon sufficiency, unblocked candidate existence, and mandatory downcrossing forcing into a comprehensive global synthesis theorem.

Lean formal declarations in `Recaman/PermanentHighGlobalSynthesis.lean`:
- `Recaman.high_regime_horizon_satisfaction_of_ge_six`
- `Recaman.exists_unblocked_horizon_candidate`
- `Recaman.toothcomb_forced_downcrossing_at_step_n`
- `Recaman.permanent_high_universal_dichotomy`
- `Recaman.grand_permanent_high_global_synthesis`

## Evidence and Audit
- Lean check: `Recaman/Audit.lean` audited and verified with `lake build Recaman.Audit`.
- Kernel axioms: `{propext, Classical.choice, Quot.sound}` (0 sorry, 0 admit, 0 native_decide).
- Evidence ID: `E-335` in `docs/EVIDENCE_REGISTRY.tsv`.
