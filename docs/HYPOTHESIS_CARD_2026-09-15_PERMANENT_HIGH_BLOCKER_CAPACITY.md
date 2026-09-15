# Hypothesis card: Permanent High Blocker Capacity and Pigeonhole Exhaustion

- ID: `H-20260915-08`
- Owner: antigravity
- Created: 2026-09-15
- Status: `PROVED-LEAN`
- Research branch: Theme 5 (Permanent High Blocker Capacity and Pigeonhole Exhaustion)

## Exact statement

For any base index $n \in \mathbb{N}$ with $1 \le n$ and toothcomb step $m < n$ in the Recamán sequence where $2n \le a(n)$:

1. **Strict Candidate Height Lower Bound**:
   Every toothcomb candidate strictly exceeds twice the base clock:
   $$2n < a(n) + n - m$$
   (`toothcomb_candidate_gt_two_n`).
   In particular, $2n + 1 \le a(n) + n - m$ and $0 < a(n) + n - m$ (`toothcomb_candidate_pos`).

2. **Small Index Historical Exclusion**:
   Because $a(0) = 0$ (`a_zero_eq_zero`) and $a(1) = 1$ (`a_one_eq_one`), neither $j = 0$ nor $j = 1$ can ever equal any toothcomb candidate $a(n) + n - m$:
   $$a(0) \ne a(n) + n - m \quad \text{and} \quad a(1) \ne a(n) + n - m$$
   (`toothcomb_candidate_ne_a_zero`, `toothcomb_candidate_ne_a_one`).
   Therefore, any historical blocker index $j$ must satisfy $j \ne 0$ and $j \ne 1$ (`toothcomb_blocker_ne_zero`, `toothcomb_blocker_ne_one`).

3. **Pigeonhole Blocker Capacity Impossibility**:
   The list of $n$ distinct toothcomb candidates $[c(0), \dots, c(n-1)]$ has length $n$ and no duplicates (`toothcomb_candidates_nodup`).
   If all $n$ candidates were blocked by historical indices $j < n$, their blocker values would have to be drawn from $\{a(1), \dots, a(n-1)\}$, a list of length at most $n - 1$ (`historical_nonzero_values_length`).
   By the Pigeonhole Principle (`List.Nodup.length_le_of_subset`), this would force:
   $$n \le n - 1$$
   which is impossible (`toothcomb_not_all_blocked_by_history`).

4. **Existence of Unblocked Toothcomb Candidate**:
   For any $n \ge 1$ in the permanent high regime $2n \le a(n)$, there strictly exists a toothcomb step $m < n$ whose candidate is completely unblocked by history:
   $$\exists m < n, \; \forall j < n, \; a(j) \ne a(n) + n - m$$
   (`toothcomb_exists_unblocked_candidate`).

5. **Complete Episode and History Isolation**:
   The unblocked candidate $a(n) + n - m$ strictly avoids all past history:
   $$a(n) + n - m \notin \text{valuesThrough}(n - 1)$$
   (`toothcomb_unblocked_candidate_avoids_valuesThrough`), strictly exceeds the base value ($a(n) < a(n) + n - m$), avoids all prior toothcomb subtractions, and avoids all toothcomb additions.

6. **Grand Blocker Capacity Synthesis**:
   `grand_permanent_high_blocker_capacity_synthesis`: unifies the strict candidate lower bound, small index exclusion, pigeonhole capacity impossibility, and the existence of an unblocked candidate.

Lean formal declarations in `Recaman/PermanentHighBlockerCapacity.lean`:
- `Recaman.toothcomb_candidate_gt_two_n`
- `Recaman.toothcomb_blocker_ne_zero`
- `Recaman.toothcomb_blocker_ne_one`
- `Recaman.toothcomb_candidates_nodup`
- `Recaman.toothcomb_not_all_blocked_by_history`
- `Recaman.toothcomb_exists_unblocked_candidate`
- `Recaman.toothcomb_unblocked_candidate_avoids_valuesThrough`
- `Recaman.grand_permanent_high_blocker_capacity_synthesis`

## Evidence and Audit
- Lean check: `Recaman/Audit.lean` audited and verified with `lake build Recaman.Audit`.
- Kernel axioms: `{propext, Classical.choice, Quot.sound}` (0 sorry, 0 admit, 0 native_decide).
- Evidence ID: `E-334` in `docs/EVIDENCE_REGISTRY.tsv`.
