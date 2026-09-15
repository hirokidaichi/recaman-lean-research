# Hypothesis card: Tail Downcrossing Dichotomy and Permanent High Ledger Capping

- ID: `H-20260915-01`
- Owner: antigravity
- Created: 2026-09-15
- Status: `PROVED-LEAN`
- Research branch: Theme 5 (Tail Downcrossing Dichotomy and Grand Synthesis)

## Exact statement

For any horizon $H \ge 0$ where $2H \le a(H)$ (in particular from the certified tail escape state $H = \text{time} + 2$ of any hypothetical least missing target `target`):

1. **Eventual Permanent High Regime ($q \ge 2$)**:
   If the orbit never downcrosses below $2n$ after $H$ ($\forall n \ge H, 2n \le a(n)$):
   - **Subtraction Threshold Jump**: Every subtraction step requires the prior value to satisfy $a(k) \ge 3(k + 1)$ (jumping out of quotient band $q = 2$).
   - **Quotient Band 2 Frozen to Additions**: Any state with $a(k) < 3(k + 1)$ cannot subtract ($\neg \text{CanSubtract}(k + 1)$) and is strictly forced to add.
   - **Forced Addition Expansion**: Forced additions in $q = 2$ expand the orbit value to $a(k + 1) \ge 3k + 1$.
   - **Ledger Mass Upper Bound**: The subtraction ledger mass is permanently capped:
     $$2 \cdot \text{subSum}(n) \le \text{upperTri}(n) - 2n$$
   - **Subtraction Counter Triangular Cap**: The subtraction counter is permanently bounded by:
     $$2 \cdot \text{upperTri}(\text{subCount } n) + 2n \le \text{upperTri}(n)$$
     forcing addition steps to maintain a positive asymptotic density $\ge 1 - 1/\sqrt{2} \approx 0.293$.
   - **Inductive Preservation**: An orbit segment starting with $2H \le a(H)$ without downcrossings maintains $2n \le a(n)$ for all $n \ge H$.

2. **Downcrossing Dynamics**:
   If downcrossings occur:
   - **Clock Deposit**: Every downcrossing step deposits its full clock into the ledger: $k + 1 \le \text{subSum}(k + 1)$.
   - **Historical Freshness**: Every downcrossing lands on a fresh value never visited previously: $\forall \text{earlier} \le k, a(k + 1) \ne a(\text{earlier})$.
   - **Distinctness**: Downcrossing landing values at different times are pairwise distinct: $k_1 < k_2 \implies a(k_1 + 1) \ne a(k_2 + 1)$.
   - **Unbounded Mass under Recurrence**: If downcrossings recur indefinitely, the subtraction ledger mass grows unboundedly: $\forall B, \exists u, B < \text{subSum}(u)$.

3. **The Grand Synthesis Dichotomy**:
   At any horizon $H$ with $2H \le a(H)$, the orbit either stays high permanently ($\forall n \ge H, 2n \le a(n)$) or performs a certified downcrossing at or after $H$.
   In any hypothetical `LeastMissingTarget target`, either:
   - The tail permanently stays high with capped subtraction ledger and forced additions on $a(k) < 3(k + 1)$, OR
   - It performs a certified downcrossing back into the two-sided ledger corridor landing strictly above $a(\text{time})$.

Lean formal declarations in `Recaman/TailDowncrossingDichotomy.lean`:
- `Recaman.permanent_high_subtraction_requires_three_times`
- `Recaman.permanent_high_not_canSubtract_of_lt_three`
- `Recaman.permanent_high_forced_addition_value`
- `Recaman.permanent_high_subSum_upper_bound`
- `Recaman.permanent_high_subCount_upper_bound`
- `Recaman.permanent_high_of_no_downcrossing`
- `Recaman.downcrossing_subSum_ge_clock`
- `Recaman.downcrossing_value_fresh`
- `Recaman.downcrossing_values_distinct`
- `Recaman.recurrent_downcrossing_subSum_unbounded`
- `Recaman.exists_permanent_high_or_downcrossing`
- `Recaman.tail_escape_downcrossing_dichotomy`
- `Recaman.least_missing_tail_grand_dichotomy`

## Why it matters

- Unifies the two complementary tail dynamics into an unconditional grand dichotomy.
- Completely resolves the behavior in the Permanent High Regime: eliminates all subtractions in $2k \le a(k) < 3(k + 1)$, strictly capping both $\text{subSum}$ and $\text{subCount}$.
- Proves that the recurrent downcrossing regime continuously deposits clocks and creates distinct fresh values, driving $\text{subSum} \to \infty$.

## Provenance and dependencies

- Subtraction ledger identities: `Recaman.SubtractionLedger` (`PROVED-LEAN`).
- Least tail minimum dynamics: `Recaman.LeastTailMinimumDynamics` (`PROVED-LEAN`).
- Tail downcrossing dynamics: `Recaman.TailDowncrossingLedger` (`PROVED-LEAN`).
- Least tail ledger minimum: `Recaman.LeastTailLedgerMinimum` (`PROVED-LEAN`).
