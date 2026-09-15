# Hypothesis card: Recurrent Downcrossing Subtraction Ledger Divergence

- ID: `H-20260915-11`
- Owner: antigravity
- Created: 2026-09-15
- Status: `PROVED-LEAN`
- Research branch: Theme 5 (Recurrent Downcrossing Subtraction Ledger Divergence)

## Exact statement

For any bound $B \in \mathbb{N}$, cutoff $\in \mathbb{N}$, and certified tail minimum certificate in the Recamán sequence:

1. **Unconditional SubSum Unboundedness After Any Cutoff**:
   Because legal subtractions recur after every cutoff (`exists_canSubtract_of_ray`), every subtraction step $n + 1$ books at least $n + 1$ into $\text{subSum}$.
   Consequently, $\text{subSum}$ strictly exceeds every ceiling $B$ past any prescribed cutoff:
   $$\forall \text{cutoff } B, \exists u, \text{cutoff} \le u \wedge B < \text{subSum}(u)$$
   (`subSum_unbounded_after`).

2. **Unconditional SubCount Unboundedness After Any Cutoff**:
   By strong recurrence of legal subtractions, the subtraction counter $\text{subCount}$ is also unbounded after any cutoff:
   $$\forall \text{cutoff } B, \exists u, \text{cutoff} \le u \wedge B \le \text{subCount}(u)$$
   (`subCount_unbounded_after`).

3. **Downcrossing Clock Deposit Bound**:
   Every downcrossing step $k \ge B$ deposits its entire clock $k + 1$ into $\text{subSum}$:
   $$B < k + 1 \le \text{subSum}(k + 1)$$
   (`downcrossing_deposit_exceeds_bound`).

4. **Tail Re-entry Ledger Divergence**:
   In any hypothetical least missing tail with certified minimum at $\text{time}$, any downcrossing step $k \ge \text{time}$ deposits at least $k + 1$ on top of $\text{subSum}(\text{time})$:
   $$\text{subSum}(\text{time}) + (k + 1) \le \text{subSum}(k + 1)$$
   Its landing value re-enters the corridor, tightly sandwiching $\text{upperTri}(k + 1)$:
   $$2 \cdot (\text{subSum}(\text{time}) + (k + 1)) + (a(\text{time}) + 1) \le \text{upperTri}(k + 1) < 2 \cdot \text{subSum}(k + 1) + 2(k + 1)$$
   (`tail_downcrossing_reentry_ledger_divergence`).

5. **Recurrent Downcrossing Ledger Growth**:
   If downcrossings recur indefinitely, $\text{subSum}$ at downcrossing re-entry steps exceeds arbitrary bounds while simultaneously satisfying the corridor bounds:
   $$\forall B, \exists k, \text{time} \le k \wedge B < \text{subSum}(k + 1) \wedge 2 \cdot \text{subSum}(k + 1) + (a(\text{time}) + 1) \le \text{upperTri}(k + 1) < 2 \cdot \text{subSum}(k + 1) + 2(k + 1)$$
   (`recurrent_downcrossings_force_arbitrary_ledger_growth`).

6. **Grand Recurrent Downcrossing SubSum Synthesis**:
   `grand_recurrent_downcrossing_subSum_synthesis`: unites unconditional ledger unboundedness, downcrossing clock deposits, tail ledger divergence, and corridor re-entry into a comprehensive master synthesis theorem.

Lean formal declarations in `Recaman/RecurrentDowncrossingSubSum.lean`:
- `Recaman.subSum_ge_of_canSubtract`
- `Recaman.subSum_unbounded_after`
- `Recaman.subSum_unbounded`
- `Recaman.subCount_unbounded_after`
- `Recaman.subCount_unbounded`
- `Recaman.downcrossing_deposit_exceeds_bound`
- `Recaman.tail_downcrossing_reentry_ledger_divergence`
- `Recaman.recurrent_downcrossings_force_arbitrary_ledger_growth`
- `Recaman.grand_recurrent_downcrossing_subSum_synthesis`

## Evidence and Audit
- Lean check: `Recaman/Audit.lean` audited and verified with `lake build Recaman.Audit`.
- Kernel axioms: `{propext, Classical.choice, Quot.sound}` (0 sorry, 0 admit, 0 native_decide).
- Evidence ID: `E-337` in `docs/EVIDENCE_REGISTRY.tsv`.
