# Hypothesis card: Permanent High Self-Blocking Collision Identity and Forced Summit Escalation

- ID: `H-20260915-03`
- Owner: antigravity
- Created: 2026-09-15
- Status: `PROVED-LEAN`
- Research branch: Theme 5 (Permanent High Self-Blocking Collision and Forced Summit Escalation)

## Exact statement

For any base index $n \in \mathbb{N}$:

1. **The Universal Collision Identity**:
   Under any sequence of 5 steps executing the pattern `A A S A A` starting at $n$:
   - $a(n + 1) = a(n) + n + 1$
   - $a(n + 2) = a(n + 1) + n + 2 = a(n) + 2n + 3$
   - $a(n + 3) = a(n + 2) - (n + 3) = a(n) + n$
   - $a(n + 4) = a(n + 3) + n + 4 = a(n) + 2n + 4$
   - $a(n + 5) = a(n + 4) + n + 5 = a(n) + 3n + 9$
   Then the subtraction candidate for step $n + 6$ satisfies the exact algebraic identity:
   $$a(n + 5) - (n + 6) = a(n + 2)$$
   (`aasaas_subtraction_candidate_collision`).

2. **Historical Collision and Refutation of Pattern `A A S A A S`**:
   Because $n + 2 \le n + 5$, $a(n + 2) \in \text{valuesThrough}(n + 5)$ unconditionally (`aasaas_candidate_in_valuesThrough`).
   Consequently, the subtraction candidate at step $n + 6$ has already been visited, and step $n + 6$ CANNOT subtract:
   $$\neg \text{CanSubtract}(n + 6)(\text{stateAt}(n + 5))$$
   (`no_aasaas_pattern`).
   The 3-periodic repetition `A A S A A S` is strictly and unconditionally impossible in the Recamán sequence.

3. **Forced Third Addition Transition**:
   Any `A A S A A` sequence is strictly forced to execute a third addition at step $n + 6$, yielding `A A S A A A`:
   $$a(n + 6) = a(n) + 4n + 15$$
   (`aasaa_forces_third_addition`).

4. **Summit Escalation**:
   In the high regime $2n \le a(n)$, the forced third addition elevates the value to:
   $$a(n + 6) \ge 6n + 15$$
   (`aasaaa_value_ge_six_times`), rapidly driving the quotient into band $q \ge 4$.

5. **Self-Consistent Summit Justification**:
   For $n \ge 6$, the peak $a(n + 2) = a(n) + 2n + 3 \ge 3(n + 3)$ (`aasaaa_satisfies_prior_summit`),
   providing the prior summit required for the 3-addition run `A A A`.

6. **Next Candidate Isolation**:
   At step $n + 7$, the subtraction candidate $a(n + 6) - (n + 7) = a(n) + 3n + 8$ sits strictly between $a(n + 4)$ and $a(n + 5)$ (`aasaaa_subtraction_candidate_strictly_between`), hence cannot match any value in the entire 6-step episode.

7. **Grand Collision Resolution**:
   `grand_permanent_high_collision_resolution`: synthesizes the full collision, pattern refutation, and forced escalation package.

Lean formal declarations in `Recaman/PermanentHighCollision.lean`:
- `Recaman.aasaas_subtraction_candidate_collision`
- `Recaman.aasaas_candidate_in_valuesThrough`
- `Recaman.no_aasaas_pattern`
- `Recaman.aasaa_forces_third_addition`
- `Recaman.aasaaa_value_ge_six_times`
- `Recaman.aasaaa_satisfies_prior_summit`
- `Recaman.aasaaa_subtraction_candidate`
- `Recaman.aasaaa_subtraction_candidate_strictly_between`
- `Recaman.grand_permanent_high_collision_resolution`

## Why it matters

- Discovers and formalizes an exact, universal algebraic identity: the subtraction candidate after `AASAA` hits its own previous peak $a(n + 2)$ identically.
- Completely eliminates any pseudo-periodic 3-cycle `AAS AAS` from the Recamán sequence.
- Proves that `AASAA` must transition to `AASAAA`, launching a quadratic height escalation and elevating quotient bands.

## Provenance and dependencies

- Permanent high rigidity: `Recaman.PermanentHighRigidity` (`PROVED-LEAN`).
- Tail downcrossing dichotomy: `Recaman.TailDowncrossingDichotomy` (`PROVED-LEAN`).
- Tail downcrossing ledger: `Recaman.TailDowncrossingLedger` (`PROVED-LEAN`).
- Debt invariant: `Recaman.DebtInvariant` (`PROVED-LEAN`).
