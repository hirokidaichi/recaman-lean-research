# Hypothesis card: Permanent High Historical Blocker Exhaustion and Downcrossing Inevitability

- ID: `H-20260915-07`
- Owner: antigravity
- Created: 2026-09-15
- Status: `PROVED-LEAN`
- Research branch: Theme 5 (Historical Blocker Exhaustion and Downcrossing Inevitability)

## Exact statement

For any base index $n \in \mathbb{N}$ and toothcomb step $m \in \mathbb{N}$ in the Recamán sequence where $2n \le a(n)$:

1. **Blocker Injectivity**:
   Because subtraction candidates $c(m) = a(n) + n - m$ are strictly distinct for distinct toothcomb steps $m_1 \ne m_2$, historical blockers $a(j_1) = c(m_1)$ and $a(j_2) = c(m_2)$ must occur at strictly distinct historical indices:
   $$j_1 \ne j_2$$
   (`toothcomb_blocker_injective`, `toothcomb_blocker_index_unique`).
   Consequently, each blocked toothcomb step consumes a unique historical peak!

2. **Severe Blocker Height Escalation**:
   Any historical blocker $a(j) = a(n) + n - m$ for a step within the high regime horizon ($5m + n + 6 \le a(n)$) must satisfy the sharp linear lower bound:
   $$14n + 6 \le 5 \cdot a(j)$$
   (`toothcomb_blocker_height_escalation`).
   This requires $a(j) \ge 2.8n + 1.2$, an extreme peak scaling with the future clock $n$.

3. **Relative Historical Height**:
   Since historical blockers precede $n$ ($j < n$), the blocker height satisfies:
   $$14j + 20 \le 5 \cdot a(j) \quad \text{and} \quad 2j < a(j)$$
   (`toothcomb_blocker_relative_height`), strictly exceeding $2.8j + 4$.

4. **Historical Blocker Exhaustion**:
   If the history prior to $n$ satisfies the ceiling $\forall j < n, 5 \cdot a(j) < 14n + 6$, then:
   NO historical blocker can exist for ANY toothcomb step $m$ within the high regime horizon:
   $$\forall j < n, \; a(j) \ne a(n) + n - m$$
   (`toothcomb_no_historical_blocker_under_ceiling`).

5. **Complete Candidate Isolation**:
   Under the historical ceiling, the toothcomb candidate $a(n) + n - m$ strictly avoids all past history:
   $$a(n) + n - m \notin \text{valuesThrough}(n - 1)$$
   (`toothcomb_candidate_avoids_all_past_history`).

6. **Grand Historical Exhaustion Synthesis**:
   `grand_permanent_high_history_exhaustion_synthesis`: unites blocker injectivity, height escalation, historical ceiling exhaustion, and downcrossing forcing beyond the horizon.

Lean formal declarations in `Recaman/PermanentHighHistoryExhaustion.lean`:
- `Recaman.toothcomb_blocker_injective`
- `Recaman.toothcomb_blocker_index_unique`
- `Recaman.toothcomb_blocker_height_escalation`
- `Recaman.toothcomb_blocker_relative_height`
- `Recaman.toothcomb_no_historical_blocker_under_ceiling`
- `Recaman.toothcomb_candidate_avoids_all_past_history`
- `Recaman.grand_permanent_high_history_exhaustion_synthesis`

## Evidence and Audit
- Lean check: `Recaman/Audit.lean` audited and verified with `lake build Recaman.Audit`.
- Kernel axioms: `{propext, Quot.sound}` only (0 sorry, 0 admit, 0 native_decide).
- Evidence ID: `E-333` in `docs/EVIDENCE_REGISTRY.tsv`.
