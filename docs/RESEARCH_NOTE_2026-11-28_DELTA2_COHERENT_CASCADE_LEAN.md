# Research Note — Lean 4 Formalization of the `Δ = 2` Coherent Greedy Cascade (`E-805 PROVED-LEAN`)

- **Evidence Row**: `E-805` (`PROVED-LEAN`, upgrading `E-799 PROVED-PAPER`)
- **Module**: `Recaman/DeltaTwoCoherentCascade.lean` (4,650+ lines, 0 warnings, 0 sorry, standard axioms only)
- **Audit Script**: `docs/data/depth_general_20261128/delta2_lean_cascade_audit.py`

## 1. Main Mathematical Result

Upgrades `E-799` to an unconditional Lean 4 theorem establishing **`ρ_greedy ≥ √(7/3) ≈ 1.527525`** directly on actual coherent finite-state greedy continuations `SeededReplay.run b st` (`st.value ∈ st.seen`):

- **Exact linear-in-`M` per-stage amplification (`delta2_coherent_cascade_word_ratio` & `delta2_coherent_cascade_replay_stage`)**:
  For every scale parameter `M ≥ 200` and stage `k ≥ 1`, there exists an explicit coherent replay `(b, st)` (`st.value ∈ st.seen`) and balanced prefix `L ≥ 1` confined to relative height band `[-1, 2k + 3]` with
  `(2 * (21 * M - 1)) ^ (k - 1) * free (replaySign b st) 0 L ≤ (3 * (6 * M + 1)) ^ (k - 1) * additions (replaySign b st) 0 L`.
  The per-stage ratio `(42 * M - 2) / (18 * M + 3)` converges monotonically to `42 / 18 = 7 / 3` across height step `Δ = 2`.
- **Asymptotic exponential theorem (`seeded_replay_delta2_exponential_lower_bound`)**:
  For every rational base `P / Q < √(7/3)` (`1 ≤ Q`, `3 * P^2 < 7 * Q^2`) and every constant `C : Nat`, choosing `M = 10 * (P^2 + Q^2) + 200` and applying Bernoulli power amplification yields `k ≥ 1`, `b`, coherent `st`, and balanced `L ≥ 1` in band `[-1, 2k + 3]` with
  `C * P ^ (2 * k + 4) * free (replaySign b st) 0 L < Q ^ (2 * k + 4) * additions (replaySign b st) 0 L`.

## 2. Proof Architecture

1. **Compositional freshness algebra (`FreshWord`, `KeyAt`, `SLandAt`, `fresh_append`, `fresh_repeatWord`)**:
   Reduces `TypeIFresh ∧ TypeIIFresh` of concatenated and `R`-repeated balanced words to disjointness between suffix `SLandAt` potentials and prefix `KeyAt` potentials shifted by `dphiW`.
2. **Closed-form stage blocks**:
   - Ordered prefix `asRep q ++ saRep p` (`fresh_asRep_append_saRep`, avoiding the height-`0` collision of reversed `(SA)^p ++ (AS)^q`).
   - Elevated arch `archWord h' a = A^{h'} (AS)^a S^{h'}` with `dphiW V (h' - 1) = +1`.
   - Closed-form bank `v0Word h' a = A^{h'-1} (SA)^{3a-1} A (AS)^a S^{h'}` (`lift = a`, `bank = 3a - 1`, `dphiW V0 (h' - 1) = 2 - (h' - 1)^2`).
3. **Self-extending `S`-landing conveyor belt (`free_conveyor_arch_le_one`, `free_stage_lift_le`)**:
   Across all `0 ≤ m < R` copies of `V` in `V_0 ++ V^R`, the `a` candidates of `(AS)^a` at height `h' - 1` sit at `P_top + m - 3*(a - 1 - j)`. Those `≤ P_top` are supplied by `V_0`'s `(SA)^{3a-1}` bank; those `≥ P_top + 2` are supplied by `V_0`'s `S^{h'}` (`P_top + 2`) and copies `0..m-1`'s `S^{h'}` (`P_top + 3 .. P_top + m + 2`). Hence at most **1** index `j < a` per copy (`m = 3*(a - 1 - j) + 1`) can be free, giving
   `free B' ≤ (h' + 4a - 1) + R * (q + p + free B + h' + 1)`.
4. **Uniform `R_k = bank_k` stage invariant (`StageInv`, `stageInv_base`, `stageInv_step`)**:
   - Base stage `k = 1` (`h = 4`): takes `B_0 = asRep (6 * M)`, `q = 0, p = 0`, `a = 10 * M + 3`, `bank_1 = 30 * M + 8`, which makes `dphiW V_1 3 = 1` identically and satisfies `StageInv 1 B_1 bank_1` and `6 * M * bank_1 ≤ F_1 ≤ A_1`.
   - Inductive step `k → k + 1`: `exists_stepData_aux` selects `(q, p, a)` with `3 * a - 1 ∈ [2*|B| - bank - 2, 2*|B| + 5*bank]`; modular lemmas `step_V_core`, `step_repV_fresh`, `step_B'_fresh`, and `step_B'_stageInv` preserve all 15 `StageInv` clauses for `R = bank' = 3a - 1`, while `stageInv_step` combines `b'*(21M-1)*A ≤ 9M*A'` and `6M*F' ≤ b'*(6M+1)*F` to cancel `3M` and obtain `2*(21M-1)*A*F' ≤ 3*(6M+1)*F*A'`.
5. **Coherent replay lift**:
   Connects `FreshWord B` directly to `SeededReplay.run b st` (`st.value ∈ st.seen`) via `E-801`'s `seeded_replay_realizes_of_fresh`.

## 3. Reproducible Audit Output & Non-Claims

- Command: `python3 docs/data/depth_general_20261128/delta2_lean_cascade_audit.py` → `ALL E-805 AUDITS PASSED.`
- Lean audit: `lake build Recaman.DeltaTwoCoherentCascade Recaman.Audit` (0 errors, 0 warnings), `harness_gate.py --lint-module` (`90/101 substantive`), `harness_lean.py --vacuity-row E-805` (`0 flagged, 0 unknown, 6 theorems`).
- **Non-claims**: Combined with `E-797` (`PROVED-LEAN`), `ρ_greedy` is now unconditionally pinned in **`[√(7/3), 5/3]` (`[1.527525, 1.666667]`)** in Lean 4 on coherent finite-state greedy continuations, leaving canonical clock-`0` reachability (`Recaman.Basic.a`), the exact base inside `[√(7/3), 5/3]`, `C1`, and protected claims (`E-001`, `E-067`, `E-070`, `E-179`) open.
