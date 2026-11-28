# Hypothesis Card: Coherent Greedy Freshness Obstruction & Optimal Δ = 2 Cascade (`E-798`, `E-799`)

- **Card ID**: `H-20261128-01`
- **Date**: 2026-11-28
- **Status**: `PROVED-LEAN` (`E-798`) + `PROVED-PAPER` (`E-799`)
- **Registry rows**: `E-798` (`PROVED-LEAN`), `E-799` (`PROVED-PAPER`)
- **Research scope**: Arbitrary-depth (`∀ N, ∀ R, ∀ k ≥ 1, ∀ V : List Bool, ∀ r : Int`)

## 1. Bounded Research Question

Following `E-797` (exact actual-`EndN` exponential growth base `= 5/3`), two linked arbitrary-depth questions arose:
1. **(Lean formalization & obstruction)** Can we unconditionally bridge `SeededReplay.run b s` and `Recaman.Basic.a` to `floorPotential` in Lean 4, prove `E-759 (I)/(II)` freshness with zero unproven `Prop` hypotheses, and prove why `E-786`'s zero-drift `5/3` balanced cycles cannot repeat arbitrarily in any coherent greedy replay — and what minimum height step `Δ` unit-drift coherent recursive towers must obey?
2. **(Tighter coherent lower bound)** Can a coherent (`E-759 = (0, 0)`) unit-drift exponential cascade attain the `Δ = 2` boundary forced by (1), strictly beating `E-789`'s `3^{1/3} ≈ 1.44225`?

## 2. Exact Quantifiers & Dependencies

- **E-798 (`Recaman/CoherentGreedyFreshness.lean`)**:
  - `∀ b s t`, `value b s t = (s.value : Int) + (b + 1) * Fw (replaySign b s) t - floorPotential (replaySign b s) 0 (Fw ... - 1) t`.
  - `∀ b s (hs : s.value ∈ s.seen) N`, `TypeIFresh (replaySign b s) N`.
  - `∀ b s N`, `TypeIIFresh (replaySign b s) N` (no `s.value ∈ s.seen` hypothesis needed!).
  - `∀ N`, `TypeIFresh canonicalOrbitSign N ∧ TypeIIFresh canonicalOrbitSign N ∧ ∀ t, (a t : Int) = Fw t - floorPotential 0 (Fw t - 1) t`.
  - `∀ f s R V r`, `mass V = 0 → 1 ≤ R → MatchesAt f s (repeatWord R V) → TypeIFresh f (s + R * V.length) → R * wordSLandings V r ≤ wordPotSpan V r + (R - 1) * |wordPotDrift V r| + 1`.
  - Corollaries on coherent `SeededReplay.run` and `Recaman.Basic.a`:
    - Zero drift (`wordPotDrift V r = 0`, `1 ≤ wordSLandings V r`) `⇒ R ≤ wordPotSpan V r + 1` (and `¬ MatchesAt canonicalOrbitSign s (repeatWord (wordPotSpan V r + 2) V)`).
    - Unit drift (`|wordPotDrift V r| = 1`, `wordPotSpan V r + 2 ≤ R`) `⇒ wordSLandings V r ≤ 1` (`Δ ≥ 2` necessity for unit-drift coherent towers).
- **E-799 (`docs/RESEARCH_NOTE_2026-11-28_DELTA2_COHERENT_CASCADE.md`)**:
  - `∀ k ≥ 1, ∀ ε > 0`, explicit `Δ = 2` cascade `B_k` on height band `[-1, 2k + 3]` (`h_k = 2k + 2`, `H = 2k + 4`) with `V_k = (AS)^{q_k} ++ (SA)^{p_k} ++ B_{k-1} ++ A^{h_k} (AS)^{a_k} S^{h_k}` (`q_k ∈ {0, 1, 2}` BEFORE `(SA)^{p_k}`) satisfying `E-759 (I)/(II) = (0, 0)` and `A(B_k) / F(B_k) ≥ (1 - ε) * c * (7/3)^k = Ω((7/3)^{H/2}) = Ω(1.527525^H)`.

## 3. Falsifier / Negative Controls

- **Coherence necessity for `TypeIFresh`**: `b = 0, s.value = 3, s.seen = {1}` (`3 ∉ s.seen`) produces `vals = [3, 2, 4, 7, 3]` with `E-759 = (1, 0)` (Type-I fails at `t = 3`, Type-II still holds). Confirms `hs : s.value ∈ s.seen` in `seeded_replay_typeIFresh` is sharp and its omission in `seeded_replay_typeIIFresh` is genuinely stronger.
- **Ordering necessity in `Δ = 2` cascade**: placing `(SA)^p` before `(AS)^q` (`q > 0`) causes `4 * q` Type-I collisions at height `0` (verified: `q = 2 ⇒ 8` Type-I collisions). Placing `(AS)^q` BEFORE `(SA)^p` moves its height-0 `S`-landings to `+1..+q > 0`, completely avoiding `(SA)^p`'s height-0 `A`-outputs (`E-759 = (0, 0)` across all `q ∈ {0, 1, 2}`).

## 4. Evidence & Reproducible Commands

- Lean 4 build & audit: `lake build Recaman Recaman.Audit` (1055 jobs, 0 errors, 0 warnings in `CoherentGreedyFreshness.lean`).
- Gate & vacuity: `python3 scripts/harness_gate.py --lint-module Recaman/CoherentGreedyFreshness.lean` (`21/24` substantive) and `python3 scripts/harness_lean.py --vacuity-row E-798` (`0 flagged, 0 unknown, 8 theorems`).
- Python audits:
  - `python3 docs/data/depth_general_20261128/coherent_greedy_freshness_audit.py` (`ALL E-798 AUDITS PASSED`)
  - `python3 docs/data/depth_general_20261128/delta2_coherent_cascade_audit.py` (`ALL E-799 AUDITS PASSED`, including `K_0 ∈ {6, 9, 12}` through `k = 3`, all `q_3 ∈ {0, 1, 2}`, `R=[12,12,12]` `A/F = 4.3679`, `k = 4` `len = 2,618,760`, and 8-filter greedy replay on `B_1`).

## 5. Non-Claims & Stopping Conditions

- Does NOT determine the exact value of `ρ_greedy ∈ [√(7/3), 5/3] = [1.527525, 1.666667]` for non-periodic or large-drift `E-759 = (0, 0)` words.
- Does NOT construct a clock-0 canonical prehistory for `B_k` and is NOT a counterexample to `C1`, `Q`, `H`, `SL`, surjectivity, or `E-001`/`E-067`/`E-070`/`E-179`.
