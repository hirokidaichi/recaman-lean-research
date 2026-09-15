# Hypothesis card: Permanent High Unsupplied Deficit and Super-Summit Escalation

- ID: `H-20260915-04`
- Owner: antigravity
- Created: 2026-09-15
- Status: `PROVED-LEAN`
- Research branch: Theme 5 (Permanent High Unsupplied Deficit and Super-Summit Escalation)

## Exact statement

For any base index $n \in \mathbb{N}$ in the high regime $2n \le a(n)$ executing an `AASAA` sequence:

1. **Canonical Sign Connection**:
   Step $n + 1$ being an addition ($\neg \text{CanSubtract}(n + 1)(\text{stateAt } n)$) implies $\text{canonicalSign } n = \text{true}$ (`canonicalSign_of_not_canSubtract`).
   An `AASAA` episode starting at $n$ unconditionally produces three consecutive additions in `canonicalSign` at clocks $n + 3, n + 4, n + 5$:
   $$\text{canonicalSign } (n + 3) = \text{true} \wedge \text{canonicalSign } (n + 4) = \text{true} \wedge \text{canonicalSign } (n + 5) = \text{true}$$
   (`aasaa_three_consecutive_canonicalSigns`).

2. **Forced Unsupplied Addition in Every `AASAA` Episode**:
   By the fundamental unsupplied addition theorem for three consecutive additions (`three_consecutive_additions_unsupplied`), every `AASAA` episode unconditionally forces at least one unsupplied addition:
   $$1 \le \text{unsuppliedCount}(\text{canonicalSign}, n + 3, 3)$$
   (`aasaa_forces_unsupplied_addition`).

3. **Fourth Addition Deficit Amplification**:
   If step $n + 7$ is also an addition, producing four consecutive additions `A A A A`, the unsupplied deficit increases to at least 2:
   $$2 \le \text{unsuppliedCount}(\text{canonicalSign}, n + 3, 4)$$
   (`aasaaa_four_additions_unsupplied_deficit`).

4. **Candidate Episode Isolation**:
   The subtraction candidate at step $n + 7$ is $c(n + 7) = a(n + 6) - (n + 7) = a(n) + 3n + 8$.
   This candidate strictly differs from all 7 values in the current episode:
   $$\forall t \in [n, n + 6], \quad a(t) \ne a(n) + 3n + 8$$
   (`aasaaa_candidate_not_in_current_episode`).

5. **Super-Summit Escalation at Step $n + 7$**:
   If step $n + 7$ fails to subtract, its blocker must have appeared at an earlier time $j \le n - 1$, forcing a historical super-summit of height:
   $$a(j) = a(n) + 3n + 8 \ge 5n + 8$$
   (`aasaaa_fourth_addition_requires_super_summit`).

6. **Guaranteed Subtraction under Super-Summit Bound**:
   In any segment where past values are bounded by $5n + 8$ ($\forall j \le n - 1, a(j) < 5n + 8$), step $n + 7$ is GUARANTEED to subtract:
   $$\text{CanSubtract}(n + 7)(\text{stateAt } (n + 6))$$
   (`aasaaa_forced_subtraction_under_super_summit_bound`).
   When it subtracts, it lands on $a(n + 7) = a(n) + 3n + 8 \ge 5n + 8$ (`aasaaa_forced_subtraction_landing_value`).

7. **Grand Unsupplied Deficit Synthesis**:
   `grand_permanent_high_unsupplied_deficit_synthesis`: unites the forced unsupplied addition deficit with the super-summit dichotomy.

Lean formal declarations in `Recaman/PermanentHighUnsuppliedDeficit.lean`:
- `Recaman.canonicalSign_of_not_canSubtract`
- `Recaman.aasaa_three_consecutive_canonicalSigns`
- `Recaman.aasaa_forces_unsupplied_addition`
- `Recaman.aasaaa_four_consecutive_canonicalSigns`
- `Recaman.aasaaa_four_additions_unsupplied_deficit`
- `Recaman.aasaaa_candidate_not_in_current_episode`
- `Recaman.aasaaa_fourth_addition_requires_super_summit`
- `Recaman.aasaaa_forced_subtraction_under_super_summit_bound`
- `Recaman.aasaaa_forced_subtraction_landing_value`
- `Recaman.grand_permanent_high_unsupplied_deficit_synthesis`

## Evidence and Audit
- Lean check: `Recaman/Audit.lean` audited and verified with `lake build Recaman.Audit`.
- Kernel axioms: `{propext, Quot.sound}` only (0 sorry, 0 admit, 0 native_decide).
- Evidence ID: `E-330` in `docs/EVIDENCE_REGISTRY.tsv`.
