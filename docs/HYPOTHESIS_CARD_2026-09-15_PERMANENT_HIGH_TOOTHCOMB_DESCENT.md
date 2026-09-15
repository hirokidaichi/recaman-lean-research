# Hypothesis card: Permanent High Toothcomb Descent and AASA Branching Dichotomy

- ID: `H-20260915-05`
- Owner: antigravity
- Created: 2026-09-15
- Status: `PROVED-LEAN`
- Research branch: Theme 5 (Permanent High Toothcomb Descent and AASA Branching Dichotomy)

## Exact statement

For any base index $n \in \mathbb{N}$ in the high regime $2n \le a(n)$ executing an `AASA` sequence:

1. **Universal Toothcomb Unit Decrement Identity**:
   Whenever step $k + 1$ is an addition, the subtraction candidate at step $k + 2$ is precisely $a(k) - 1$:
   $$c(k + 2) = a(k + 1) - (k + 2) = a(k) - 1$$
   (`toothcomb_unit_decrement_candidate`).
   When step $k + 2$ can subtract, it decrements the value by 1: $a(k + 2) = a(k) - 1$ (`toothcomb_subtraction_landing_value`).

2. **The `AASA` Subtraction Candidate**:
   In any `AASA` episode starting at $n$:
   - $a(n + 1) = a(n) + n + 1$ (A)
   - $a(n + 2) = a(n) + 2n + 3$ (A)
   - $a(n + 3) = a(n) + n$ (S)
   - $a(n + 4) = a(n) + 2n + 4$ (A)
   Then the subtraction candidate at step $n + 5$ satisfies:
   $$a(n + 4) - (n + 5) = a(n) + n - 1 = a(n + 3) - 1$$
   (`aasa_subtraction_candidate`).

3. **Episode Avoidance for $n \ge 2$**:
   For any $n \ge 2$, this candidate strictly differs from all 5 values in the episode $\{a(n), \dots, a(n + 4)\}$:
   $$\forall t \in [n, n + 4], \quad a(t) \ne a(n) + n - 1$$
   (`aasa_candidate_not_in_current_episode`).

4. **Fifth Addition Requires Prior Summit $a(j) \ge 3n - 1$**:
   Because the candidate avoids the current episode, step $n + 5$ can fail to subtract (yielding `AASAA`) ONLY IF the candidate already appeared at an earlier time $j \le n - 1$.
   In the high regime $2n \le a(n)$, this forces a historical summit:
   $$\exists j \le n - 1, \quad a(j) = a(n) + n - 1 \ge 3n - 1$$
   (`aasa_fifth_addition_requires_prior_summit`).

5. **Guaranteed `AASAS` Toothcomb Initiation**:
   In any segment where past values are bounded by $3n - 1$ ($\forall j \le n - 1, a(j) < 3n - 1$), step $n + 5$ is GUARANTEED to subtract:
   $$\text{CanSubtract}(n + 5)(\text{stateAt}(n + 4))$$
   (`aasa_forced_subtraction_under_summit_bound`).
   This forces the transition to `AASAS`, strictly preventing `AASAA` from forming, and lands on $a(n + 5) = a(n + 3) - 1 = a(n) + n - 1$ (`aasa_forced_subtraction_landing_value`).

6. **Step $n + 7$ Candidate and Continued Decrement**:
   If step $n + 6$ adds after `AASAS`, the subtraction candidate at step $n + 7$ is:
   $$a(n + 6) - (n + 7) = a(n + 5) - 1 = a(n) + n - 2$$
   (`aasas_step7_subtraction_candidate`).
   For $n \ge 3$, this candidate strictly avoids all 7 values in $\{a(n), \dots, a(n + 6)\}$ (`aasas_step7_candidate_not_in_current_episode`).

7. **Grand Toothcomb Branching Synthesis**:
   `grand_permanent_high_toothcomb_branching_synthesis`: unites the `AASA` branching dichotomy, summit requirement for `AASAA`, forced `AASAS` toothcomb initiation, and unit decrement law.

Lean formal declarations in `Recaman/PermanentHighToothcombDescent.lean`:
- `Recaman.toothcomb_unit_decrement_candidate`
- `Recaman.toothcomb_subtraction_landing_value`
- `Recaman.aasa_subtraction_candidate`
- `Recaman.aasa_candidate_not_in_current_episode`
- `Recaman.aasa_fifth_addition_requires_prior_summit`
- `Recaman.aasa_forced_subtraction_under_summit_bound`
- `Recaman.aasa_forced_subtraction_landing_value`
- `Recaman.aasas_step7_subtraction_candidate`
- `Recaman.aasas_step7_candidate_not_in_current_episode`
- `Recaman.grand_permanent_high_toothcomb_branching_synthesis`

## Evidence and Audit
- Lean check: `Recaman/Audit.lean` audited and verified with `lake build Recaman.Audit`.
- Kernel axioms: `{propext, Quot.sound}` only (0 sorry, 0 admit, 0 native_decide).
- Evidence ID: `E-331` in `docs/EVIDENCE_REGISTRY.tsv`.
