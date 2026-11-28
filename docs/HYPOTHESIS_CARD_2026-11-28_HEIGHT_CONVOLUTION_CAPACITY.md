# Hypothesis Card: Exponentially-Decaying Height Convolution Capacity, Sharp `18/25` Strip Bound, and `D = 7, 8` Compression (`E-800`)

- **Card ID**: `H-20261128-02`
- **Date**: 2026-11-28
- **Status**: `PROVED-LEAN` (`E-800`)
- **Registry row**: `E-800` (`PROVED-LEAN`, `Recaman/HeightConvolutionCapacity.lean`)
- **Research scope**: Arbitrary-depth (`∀ H, ∀ d, ∀ s, ∀ K`) + local `D = 7, 8` sharpening

## 1. Bounded Research Question

In `E-797`, bounding `triAdditions(H + 1) ≤ 3 * (5/3)^H * free` threw away two independent sources of slack:
1. Every free addition `F_{m + h}` at height `m + h` was given the same worst-case floor weight `27 * 5^H` instead of its exact relative-height convolution weight `O(3^h * 5^{H - h})`.
2. Bounding total strip additions `S(H) ≤ T(H)` and low-addition weights `W(m + d) ≤ 2 * T(d - 1)` inflated the leading prefactors (`9/5 = 1.80` on `S(H)` and `54/25 = 2.16` on `W(m + d)`), leaving a `4.5×` gap to `E-786`'s `(2/5) * (5/3)^H` lower bound and failing to beat `E-787` at finite depth `D = 7`.

Can we keep the exact exponentially-decaying height convolution kernel `convFree`, prove quantitative `LOW-free` vs `HIGH-free` separation, derive exact zero-remainder identities for `S(H)` and `W(m + d)` directly from `T(H)`, slash the `5/3` strip constant below `1` (within `< 2×` of `E-786`), and tighten both `D = 7` and `D = 8` counterexample profiles in Lean 4?

## 2. Exact Quantifiers & Dependencies

For EVERY `f : Nat → Bool`, padded `BlockWord` prefix `seg f 0 n = w ++ replicate a true`, interval length `K`, and floor `m ≤ Fw f i` (`n ≤ i ≤ n + K`):
- `∀ H`, `5 * 3^(H + 2) * triAdditionsH(H + 1) ≤ convFree2(levelFree, H)`.
- `∀ H, ∀ s (1 ≤ s ≤ H + 1)`, `5 * 3^(H + 2) * triAdditionsH(H + 1) ≤ 135 * 5^H * lowFree(s) + 28 * 3^s * 5^(H + 1 - s) * highFree(s)`.
- `∀ H ≥ 1`, on strip `[m, m + H]`: `25 * 3^H * additions ≤ 18 * 5^H * free` (`0.72 * (5/3)^H`, ratio `1.80×` to `E-786`'s `0.40 * (5/3)^H`).
- `∀ d ≥ 0, ∀ r ≤ m + d`: `(625 * 3^d) * lowAdditionWeights f n r K ≤ (1008 * 5^d) * free` (`1.6128 * (5/3)^d`), and `(625 * 3^d) * (j + 1)^2 ≤ (1008 * 5^d) * free` without `hpos` or height ceiling.
- `D = 7`: `3 * W(m + 5) ≤ 56 * free`, positive-deficit profile `4 ≤ free ≤ j ≤ 16`.
- `D = 8`: `W(m + 6) ≤ 32 * free`, positive-deficit profile `4 ≤ free ≤ j ≤ 29`.

## 3. Falsifier / Negative Controls

- **Exact rational LP check**: confirmed the exact dual combinations `(5, 3, 1)` for `D = 7` (`56/3`), `(400, 213, 27, 120, 45)` for `D = 8` (`32`), and that the LP asymptotic limit for `W(m + d) / (5/3)^d` is `≈ 1.56` (our proved `1008/625 = 1.6128` is within `3.5%`).
- **`H = 0` sharpness**: on single `"A"` (`H = 0`), `A = F = 1`, `25 * 1 > 18 * 1`, proving `1 ≤ H` in `sharp_five_thirds_strip_capacity` is sharp.
- **`BlockWord` prefix necessity**: non-`BlockWord` prefix `"AS"` supplies `E_1 > 0` and violates `convFree2` at `H = 0` (`225 > 219`).
- **Random & adversarial sweep**: 6 adversarial + 10,000 random padded `BlockWord`-prefixed words (5,000 discovery + 5,000 holdout): 0 violations.

## 4. Evidence & Reproducible Commands

- `lake build Recaman Recaman.Audit` (1056 jobs, 0 errors, 0 warnings in `HeightConvolutionCapacity.lean`).
- `python3 scripts/harness_gate.py --lint-module Recaman/HeightConvolutionCapacity.lean` (`39/45` substantive, all 10 public theorems `SUBSTANTIVE`).
- `python3 scripts/harness_lean.py --vacuity-row E-800` (`0 flagged, 0 unknown, 10 theorems`).
- `python3 docs/data/depth_general_20261128/height_convolution_capacity_audit.py` (`ALL E-800 AUDITS PASSED`).

## 5. Non-Claims & Limitations

- Does NOT eliminate the residual finite bands `4 ≤ free ≤ j ≤ 16` (`D = 7`) or `4 ≤ free ≤ j ≤ 29` (`D = 8`).
- Does NOT prove `C1`, `Q`, `H`, `SL`, surjectivity, or `E-001`/`E-067`/`E-070`/`E-179`.
