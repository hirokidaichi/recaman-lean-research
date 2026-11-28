# Hypothesis Card — Optimal `Δ = 2` Coherent Greedy Cascade in Lean 4 (`E-805`)

- **ID**: `H-20261128-07` (`E-805`)
- **Date**: 2026-11-28 (`R-20261128-02`)
- **Status**: `PROVED-LEAN` (upgrades `E-799 PROVED-PAPER`)
- **Module**: `Recaman/DeltaTwoCoherentCascade.lean`

## 1. Bounded Research Question

Can the `E-799` optimal unit-drift `Δ = 2` coherent greedy cascade (`ρ_greedy ≥ √(7/3) ≈ 1.527525`) be formalized unconditionally in pure Lean 4 directly on actual coherent finite-state greedy continuations `SeededReplay.run b st` (`st.value ∈ st.seen`), with zero `sorry`/custom axioms and `0 flagged / 0 unknown` vacuity?

## 2. Exact Statement

1. **Compositional freshness algebra**: `fresh_append`, `fresh_repeatWord`, and `fresh_asRep_append_saRep` prove `TypeIFresh ∧ TypeIIFresh` from height-by-height `KeyAt`/`SLandAt` separation.
2. **Stage-by-stage `Δ = 2` word cascade (`delta2_coherent_cascade_word_ratio`)**: for every `M ≥ 200` and `k ≥ 1`, there exists a balanced `FreshWord` `B` (`mass B = 0`, `1 ≤ B.length`, height band `[-1, 2k + 3]`) satisfying
   `(2 * (21 * M - 1)) ^ (k - 1) * free (wordSign B) 0 B.length ≤ (3 * (6 * M + 1)) ^ (k - 1) * additions (wordSign B) 0 B.length`.
3. **Coherent `SeededReplay.run` stage realization (`delta2_coherent_cascade_replay_stage`)**: realizes every `(M, k)` stage directly on an actual coherent finite-state greedy replay `(b, st)` (`st.value ∈ st.seen`).
4. **Unconditional `ρ_greedy ≥ √(7/3)` lower bound (`seeded_replay_delta2_exponential_lower_bound`)**: for every `P Q C : Nat` with `1 ≤ Q` and `3 * P * P < 7 * Q * Q`, there exist `k ≥ 1`, `b`, coherent `st` (`st.value ∈ st.seen`), and balanced `L ≥ 1` confined to relative height band `[-1, 2k + 3]` satisfying
   `C * P ^ (2 * k + 4) * free (replaySign b st) 0 L < Q ^ (2 * k + 4) * additions (replaySign b st) 0 L`.

## 3. Falsifier / Negative Controls

- Verified via `python3 docs/data/depth_general_20261128/delta2_lean_cascade_audit.py` (`ALL E-805 AUDITS PASSED`):
  - Discovery (`K0 = 6..10`) and holdout (`K0 = 11..15`) through `k = 3`: `E-759 = (0, 0)` across all 10 initial scales, all 15 `StageInv` clauses satisfied.
  - Full repetition `R = bank = 38` at `k = 1`: `E-759 = (0, 0)`, exact `F = 397 ≤ F_ub = 473`, `A / F = 2.3401`.
  - Exact symbolic tower `M ∈ {10, 50, 200}` at `k = 12` (`h = 26`): `stage_mult = 2.333333333 == 7/3`.
  - Negative control (a): reversed prefix `(SA)^p ++ (AS)^q` at `q = 1` triggers `c1 = 4 > 0` Type-I collisions.
  - Negative control (b): dropping the `(SA)^p` buffer (`p = 0`) at `k = 2` triggers `(4, 0)` collisions.

## 4. Verification & Audit

- `lake build Recaman.DeltaTwoCoherentCascade Recaman.Audit`: **0 errors, 0 warnings**, standard axioms `[propext, Classical.choice, Quot.sound]` only.
- `python3 scripts/harness_gate.py --lint-module Recaman/DeltaTwoCoherentCascade.lean`: `90/101 substantive theorems`.
- `python3 scripts/harness_lean.py --vacuity-row E-805`: `0 flagged, 0 unknown, 6 theorems`.
- Statement audit: `docs/statement_audits/E-805.md`.

## 5. Non-Claims

Does not prove reachability from canonical clock `0` (`Recaman.Basic.a`), does not determine the exact value of `ρ_greedy` inside `[√(7/3), 5/3]`, and does not prove `C1`, `Q`, `H`, `SL`, surjectivity, or any protected claim (`E-001`, `E-067`, `E-070`, `E-179`).
