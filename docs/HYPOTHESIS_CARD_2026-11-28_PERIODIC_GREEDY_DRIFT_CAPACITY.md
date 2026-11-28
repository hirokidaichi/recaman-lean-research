# Hypothesis Card: Periodic Drift Dichotomy, `TypeIIFresh` Residue-Order Obstruction, and Golden-Ratio Capacity (`E-806`)

- **Card ID**: `HC-2026-11-28-02`
- **Date**: `2026-11-28`
- **Status**: `PROVED-LEAN` (`E-806`)
- **Primary Lean module**: [`Recaman/PeriodicGreedyDriftCapacity.lean`](../Recaman/PeriodicGreedyDriftCapacity.lean)
- **Statement audit**: [`docs/statement_audits/E-806.md`](statement_audits/E-806.md)
- **Audit script**: [`docs/data/depth_general_20261128/periodic_greedy_drift_audit.py`](data/depth_general_20261128/periodic_greedy_drift_audit.py)

## 1. Bounded Research Question

In `E-798` (`Recaman/CoherentGreedyFreshness.lean`), `TypeIFresh` (`E-759 (I)`) ruled out zero-drift periodic cycles (`d = 0`) and forced unit-drift (`|d| = 1`) periodic coherent towers to skip height `H - 1` (`Δ ≥ 2`, realized at base `√(7/3)` in `E-805`). Can **arbitrary** periodic drift `d = wordPotDrift V r ∈ ℤ` (positive or negative, arbitrarily large) evade `E-798` to approach `5/3` (e.g., via a negative-drift `Δ = 1` cascade at base `φ = (1 + √5)/2 ≈ 1.618034`, or a large-positive-drift `Δ = 1` cascade), or do `TypeIFresh`, `TypeIIFresh`, and `E-797` unconditionally impose a strictly `< 5/3` capacity law and explicit drift-dependent obstructions at **arbitrary excursion depth `H`** on every coherent `SeededReplay.run b st` and on `Recaman.Basic.a`?

## 2. Exact Quantifiers & Formal Claims (`PROVED-LEAN`)

For every `b s R : Nat`, `st : State` (`hs : st.value ∈ st.seen`), balanced word `V : List Bool` (`mass V = 0`), relative height `r : Int` or ceiling `H : Int`, with `MatchesAt (replaySign b st) s (repeatWord R V)` (and unconditionally specialized to `canonicalOrbitSign` of `Recaman.Basic.a` at `b = 0, st = initial`):

1. **Exact Balanced Word Duality**:
   - `wordSLandings V r = wordLevelAdditions V r`,
   - `wordLowWeights V r + wordPotDrift V r = A_r(V) + 3 * A_{r+1}(V) + wordUpperExcess V r`.
2. **Negative-Drift Exact Golden-Ratio Capacity (`d ≤ 0`)**:
   - Whenever `wordPotDrift V r ≤ 0` and `R ≥ wordPotSpan V r + |wordPotDrift V r| + 2`:
     `3 * A_{r+1}(V) + 2 * A_r(V) + wordUpperExcess V r ≤ wordLowWeights V r`
     (zero additive error; characteristic root `φ = (1 + √5)/2 ≈ 1.618034 < 5/3`, and zero exponential growth above the unique sign-flip height `r*`).
3. **`TypeIIFresh` Periodic Residue-Order Obstruction & Negative-Drift `(AS)^a S` Ceiling**:
   - For every `SeededReplay.run b st` (no coherence needed), `d = wordPotDrift V r ≠ 0`, `R ≥ wordPotSpan V r + 1`:
     if `|d| ∣ (Φ_r(t + 1) - Φ_r(u))` for an `S`-landing `t` at height `r` and `A`-step `u` at height `r + 1`, then `d < 0 → Φ_r(t + 1) ≤ Φ_r(u)`, `0 < d → Φ_r(u) ≤ Φ_r(t + 1)`, and `t < u` on equality.
   - Consequently, for `d < 0`, every `(AS)^a S` top-arch run at height `r + 1` inside `V` satisfies `∀ k ∈ [1, a], ¬(|d| ∣ 3 * k)`, hence `a < |d|` and `(3 ∣ d) → 3 * a < |d|`.
4. **Positive-Drift Arbitrary-`d` Top-Level Collapse (`d ≥ 0`)**:
   - With zero `BlockWord` prefix hypothesis, whenever all additions of `V` have height `≤ H` and `0 ≤ wordPotDrift V (H - 1)` (arbitrary `d ≥ 0`, not only `|d| = 1`):
     `E_{H-1}(V^R) ≤ 3 * F_H(V^R) + 3 * AA_{H-2}(V^R) + span + |d| + 1 + prefixBudgetSlack`.
5. **Sign-Free Top-Level Golden-Ratio Capacity (all `d : Int`)**:
   - With zero `BlockWord` prefix hypothesis and no sign restriction on `wordPotDrift V (H - 1)`:
     `3 * E_H(V^R) + 2 * E_{H-1}(V^R) ≤ W(H - 1)(V^R) + 6 * AA_{H-2}(V^R) + 3 * F_H(V^R) + span + |d| + 1 + 2 * prefixBudgetSlack`.

## 3. Falsification & Evidence

- **Discovery/Holdout Audit (`COMPUTED`)**: `python3 docs/data/depth_general_20261128/periodic_greedy_drift_audit.py`
  - T1 exact duality: `2,735` discovery + `4,119` holdout `(word, r)` pairs verified.
  - T2–T4: `4,427` discovery / `6,702` holdout T2 checks (`357`/`435` exact threshold), `215`/`266` T3 checks (`31`/`39` `(AS)^a S` runs), `1,369`/`2,117` T4 positive-drift checks, `1,607`/`2,447` T4 sign-free checks.
  - Canonical orbit holdout: `Recaman.Basic.a` on `0..15000` (`fresh=True`, `35,460` repeated balanced subwords verified).
  - Genuine separation baseline (`E-786`, raw non-fresh `d = 0`): `3*A_3 + 2*A_2 = 629 > W(2) = 568` (`+61/copy`), and on `bank + V_2^10`, `3*E_3 + 2*E_2 = 6290 > W(2) + 6*AA_1 + 3*F_3 = 6100` (`+190`, growing linearly to `+∞` in `R`).
- **Adversarial construction attempts that failed (`OBSERVED`)**:
  - Positive-drift `Δ = 1` self-replenishing banks (`V = B_1 ++ (AS)^p ++ arch(5, a_5)`, nested arches): either hit `TypeIIFresh` (`t2={4: 427}`) or had `E_4` collapse to `O(F_5 + AA_3)` (proved unconditionally by T4a).
  - Negative-drift `Δ = 1` jump-over cascades (`V = (AS)^p + A^4(AS)^{a_4} AA(AS)^j S (AS)^{a_5} S^5`): achieved `92.2%` supplied `E_5` when ignoring `TypeIIFresh`, but EVERY `(AS)^{a_5} S` run with `a_5 ≥ |d|` was killed by `TypeIIFresh` at height `4` (proved unconditionally by T3b), while attempting a mod-3 `AASS` exit shift triggered height-6 `TypeIFresh` collisions (`t1={6: R}`).
- **Lean 4 Verification (`PROVED-LEAN`)**:
  - `lake build Recaman.PeriodicGreedyDriftCapacity Recaman.Audit`: 0 errors, 0 warnings, 0 sorry.
  - `python3 scripts/harness_gate.py --lint-module Recaman/PeriodicGreedyDriftCapacity.lean`: `38/45` substantive theorems.
  - `python3 scripts/harness_lean.py --vacuity-row E-806`: `0 flagged, 0 unknown, 9 theorems`.
  - Standard axioms only (`[propext, Classical.choice, Quot.sound]`).

## 4. Boundaries & Remaining Uncertainty

- Proves arbitrary-depth strictly-`< 5/3` capacity and drift-sign obstructions for **periodic** balanced repetitions `V^R` inside any coherent `SeededReplay.run` and `Recaman.Basic.a`.
- Does **not** yet prove a global `< 5/3` bound for arbitrary **non-periodic** `TypeIFresh ∧ TypeIIFresh` words (determining exact `ρ_greedy ∈ [√(7/3), 5/3]`), nor does it prove `C1`, `Q`, `H`, `SL`, surjectivity, or any protected claim (`E-001`, `E-067`, `E-070`, `E-179`).
