# Hypothesis card: Permanent High Structural Rigidity and Oscillation Obstructions

- ID: `H-20260915-02`
- Owner: antigravity
- Created: 2026-09-15
- Status: `PROVED-LEAN`
- Research branch: Theme 5 (Permanent High Structural Rigidity and Oscillation Obstructions)

## Exact statement

In the Permanent High Regime ($a(n) \ge 2n$ for all $n \ge H$):

1. **Subtraction Escalation**:
   - Single subtraction requires $3(k + 1) \le a(k)$ (`permanent_high_subtraction_requires_three_times`).
   - Two consecutive subtractions require $4k + 7 \le a(k)$ (`permanent_high_two_subtractions_requires_four_times`).
   - Three consecutive subtractions require $5k + 12 \le a(k)$ (`permanent_high_three_subtractions_requires_five_times`).
   - If $a(k) < 4k + 7$, two consecutive subtractions are strictly impossible (`permanent_high_not_two_subtractions_of_lt_four`).
   - If $a(k) < 5k + 12$, three consecutive subtractions are strictly impossible (`permanent_high_not_three_subtractions_of_lt_five`).

2. **Forced Addition Height Elevation**:
   - For any $n \ge \max(H, 6)$, two consecutive additions strictly elevate the orbit height to:
     $$3(n + 3) \le a(n + 2)$$
     (`permanent_high_two_additions_reach_three`).

3. **Historical Blocker Requirement for Three Additions**:
   - The candidate after two additions satisfies $a(n + 2) - (n + 3) = a(n + 1) - 1$ (`permanent_high_candidate_after_two_additions`).
   - The candidate strictly sits between $a(n)$ and $a(n + 1)$:
     $$a(n) < a(n + 1) - 1 < a(n + 1) < a(n + 2)$$
     (`permanent_high_candidate_between`).
   - A third consecutive addition at step $n + 3$ cannot be caused by insufficient height; it MUST be blocked by $a(n + 1) - 1 \in \text{valuesThrough}(n + 2)$ (`permanent_high_third_addition_must_be_blocked`).
   - The blocker must have appeared at an earlier time $j \le n - 1$:
     $$a(n + 1) - 1 \in \text{valuesThrough}(n - 1)$$
     (`permanent_high_third_addition_blocker_prior`).
   - Any three-addition run forces the existence of a prior summit of height at least $3n$:
     $$\exists j \le n - 1, \quad 3n \le a(j) \land a(j) = a(n) + n$$
     (`permanent_high_third_addition_prior_summit`).
   - In any segment without a prior summit of height $3n$, three consecutive additions are strictly impossible: step $n + 3$ is guaranteed to subtract (`permanent_high_no_three_consecutive_additions_under_summit_bound`).

4. **Landing Law of Forced Subtraction**:
   - When step $n + 3$ subtracts after two additions, it lands precisely on $a(n + 3) = a(n) + n$ (`permanent_high_forced_subtraction_landing_value`).
   - The landing value is historically fresh: $a(n + 3) \notin \text{valuesThrough}(n + 2)$ (`permanent_high_forced_subtraction_landing_fresh`).

5. **Infinitely Many Subtractions**:
   - An infinite forced-addition ray is unconditionally impossible (`no_perpetual_forcedAddition_ray`).
   - Therefore, legal subtractions must recur infinitely often in the permanent high regime (`permanent_high_infinitely_many_subtractions`).
   - But the subtraction ledger mass is permanently capped:
     $$2 \cdot \text{subSum}(n) \le \text{upperTri}(n) - 2n$$
     and the subtraction count is capped:
     $$2 \cdot \text{upperTri}(\text{subCount } n) + 2n \le \text{upperTri}(n)$$
     forcing addition density $\ge 1 - 1/\sqrt{2} \approx 0.293$.

6. **Grand Synthesis**:
   - `permanent_high_bilateral_rigidity`: combines the full bilateral rigidity package.

Lean formal declarations in `Recaman/PermanentHighRigidity.lean`:
- `Recaman.permanent_high_two_subtractions_requires_four_times`
- `Recaman.permanent_high_three_subtractions_requires_five_times`
- `Recaman.permanent_high_not_two_subtractions_of_lt_four`
- `Recaman.permanent_high_not_three_subtractions_of_lt_five`
- `Recaman.permanent_high_two_additions_reach_three`
- `Recaman.permanent_high_candidate_after_two_additions`
- `Recaman.permanent_high_candidate_between`
- `Recaman.permanent_high_third_addition_must_be_blocked`
- `Recaman.permanent_high_third_addition_blocker_prior`
- `Recaman.permanent_high_third_addition_prior_summit`
- `Recaman.permanent_high_no_three_consecutive_additions_under_summit_bound`
- `Recaman.permanent_high_forced_subtraction_landing_value`
- `Recaman.permanent_high_forced_subtraction_landing_fresh`
- `Recaman.permanent_high_infinitely_many_subtractions`
- `Recaman.permanent_high_bilateral_rigidity`

## Why it matters

- Fully characterizes the extreme bilateral rigidity of the Permanent High Regime.
- Proves that runs of consecutive subtractions require steep linear heights ($3(k+1), 4k+7, 5k+12$).
- Proves that runs of three consecutive additions are strictly impossible unless a historical summit of height at least $3n$ existed at $j \le n - 1$.
- Shows that without historical summits, the sequence is forced into rapid addition-subtraction oscillations, with forced subtractions depositing clocks into $\text{subSum}$, which is strictly capped.

## Provenance and dependencies

- Tail downcrossing dichotomy: `Recaman.TailDowncrossingDichotomy` (`PROVED-LEAN`).
- Tail downcrossing ledger: `Recaman.TailDowncrossingLedger` (`PROVED-LEAN`).
- Eventual high corridor structure: `Recaman.EventualHighCorridorStructure` (`PROVED-LEAN`).
- Debt invariant: `Recaman.DebtInvariant` (`PROVED-LEAN`).
