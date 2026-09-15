# Hypothesis card: Tail Downcrossing Inevitability and Corridor Re-entry Synthesis

- ID: `H-20260915-10`
- Owner: antigravity
- Created: 2026-09-15
- Status: `PROVED-LEAN`
- Research branch: Theme 5 (Tail Downcrossing Inevitability and Corridor Re-entry)

## Exact statement

For any base index $H, T \in \mathbb{N}$ with $H \le T$ and certified tail minimum certificate in the Recamán sequence:

1. **Discrete Boundary Crossing Lemma**:
   Whenever an orbit satisfies $2H \le a(H)$ and strictly falls below twice the clock at a later time $T$ ($a(T) < 2T$), there strictly exists a downcrossing step $k \in [H, T-1]$:
   $$H \le k < T \wedge 2k \le a(k) \wedge a(k + 1) < 2(k + 1)$$
   (`exists_downcrossing_of_high_to_low`).

2. **Toothcomb Downcrossing Forcing**:
   Whenever a toothcomb descent extends beyond the high regime horizon ($a(n) < 5m + n + 6$), the toothcomb landing value $val = a(T) < 2T$ strictly falls below twice the clock, unconditionally forcing a certified downcrossing step $k \in [H, T-1]$
   (`toothcomb_forced_downcrossing_step`).

3. **Downcrossing Properties**:
   Every downcrossing step $k \ge 1$ is a legal subtraction:
   - `CanSubtract (k + 1) (stateAt k)`
   - Deposits its full clock into the subtraction ledger: $k + 1 \le \text{subSum}(k + 1)$
   - Lands on a historically fresh value: $a(k + 1) \notin \text{valuesThrough}(k)$
   (`downcrossing_step_properties`).

4. **Corridor Re-entry**:
   In any hypothetical least missing tail, the downcrossing landing value strictly lands above the tail minimum:
   $$a(\text{time}) + 1 \le a(k + 1) < 2(k + 1)$$
   and re-enters the subtraction ledger corridor:
   $$2 \cdot \text{subSum}(k + 1) + (a(\text{time}) + 1) \le \text{upperTri}(k + 1) < 2 \cdot \text{subSum}(k + 1) + 2(k + 1)$$
   (`tail_downcrossing_corridor_reentry_synthesis`).

5. **Grand Downcrossing Inevitability Synthesis**:
   `grand_tail_downcrossing_inevitability_synthesis`: unites the discrete boundary crossing lemma, toothcomb downcrossing forcing, downcrossing legal subtraction freshness, and corridor re-entry into a comprehensive master synthesis theorem.

Lean formal declarations in `Recaman/TailDowncrossingInevitability.lean`:
- `Recaman.exists_downcrossing_of_high_to_low`
- `Recaman.toothcomb_forced_downcrossing_step`
- `Recaman.downcrossing_step_properties`
- `Recaman.tail_downcrossing_corridor_reentry_synthesis`
- `Recaman.grand_tail_downcrossing_inevitability_synthesis`

## Evidence and Audit
- Lean check: `Recaman/Audit.lean` audited and verified with `lake build Recaman.Audit`.
- Kernel axioms: `{propext, Classical.choice, Quot.sound}` (0 sorry, 0 admit, 0 native_decide).
- Evidence ID: `E-336` in `docs/EVIDENCE_REGISTRY.tsv`.
