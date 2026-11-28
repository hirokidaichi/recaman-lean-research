# Hypothesis Card: H-20261127-06 — Sharp Rational 3-Spacing Capacity Across `[1/2, κ)`

- **ID**: `H-20261127-06`
- **Parent Cycle**: `R-20261127-02` (Track 2B: narrowing `[5/3, 2]` on actual `EndN` in Lean 4)
- **Status**: `PROVED-LEAN` (`E-788`, `Recaman/SharpThreeSpacingCapacity.lean`)
- **Depth-general classification**: `depth_general_progress` (uniform over ALL heights `H, h, d : Nat` and ALL rational weights `P / Q ∈ [1/2, κ)`, narrowing the PROVED-LEAN actual-`EndN` exponential growth upper base from `2` (`E-785`) down to `199/110 ≈ 1.8091`, within `0.13%` of the exact 3-spacing cone root `1.8067`).

## Bounded Research Question

Can the dyadic (`q = 1/2`) telescoping invariant of `E-785` be generalized to an exact zero-slack polynomial telescoping identity for EVERY rational weight `q = P / Q` inside the 3-spacing cone (`1/2 ≤ P / Q < κ ≈ 0.55350`, `coneM P Q ≤ 3 * coneK P Q`), yielding BOTH uniform rational weighted capacity AND a prefactor-blowup-free arbitrary-depth low-addition weight bound `W_d ≤ (coneM / (Q^3(Q-P))) * (Q/P)^d * free` directly on actual `EndN`?

## Exact Quantifiers & Formal Claims

For every `P Q : Nat` with `P < Q`, `Q ≤ 2 * P`, `coneM P Q ≤ 3 * coneK P Q` (where `coneK P Q = Q^2 (Q - P)^2` and `coneM P Q = P^2 (3 Q^2 + 2 P^2 - 3 P Q)`), every sign function `f : Nat → Bool`, padded `BlockWord` prefix `seg f 0 n = w ++ List.replicate a true`, floor `m : Int` (`∀ i ∈ [n, n + K], m ≤ Fw f i`), and arbitrary `H, h, d : Nat`:

1. `rational_height_weighted_capacity`: `(3 * coneK P Q - coneM P Q) * ratAdditions P Q ≤ 3 * coneK P Q * ratFree P Q`.
2. `rational_height_exp_bound`: `(3 * coneK P Q - coneM P Q) * P^h * levelAdditions(m + h) ≤ 3 * coneK P Q * Q^h * free`.
3. `rational_low_weights_bound`: `r ≤ m + d → P^d * Q^3 * (Q - P) * lowAdditionWeights(r) ≤ coneM P Q * Q^d * free`.
4. `rational_arbitrary_target_free_gap_square` (no `hpos`, no height ceiling): `Fw(b + j) ≤ m + d + 1 → P^d * Q^3 * (Q - P) * (j + 1)^2 ≤ coneM P Q * Q^d * free`.
5. Unconditional specializations at `(11, 20)` (`base = 20/11 ≈ 1.8182`) and `(110, 199)` (`base = 199/110 ≈ 1.8091`): `actual_height_exp_twenty_elevenths`, `actual_height_exp_199_110`, `low_weights_exp_199_110`.

## Falsifier & Evidence

- Script: `docs/data/depth_general_20261127/sharp_three_spacing_audit.py`
- Discovery: exhaustive length `1..12` (`8,190` binary words) across `(1,2), (6,11), (11,20), (110,199)`.
- Holdout: `2,000` random `BlockWord ++ A^a ++ tail` instances (`seed = 2026112706`, `len ≤ 70`): `282,444` capacity checks, `282,444` exponential checks, `323,204` low-weight checks, `0` violations.
- Negative control: `(P, Q) = (5, 9)` (`q = 0.55556 > κ`) gives `3*K - M = -62 < 0`, verifying the sharp boundary of the 3-spacing cone.
- Lean 4 verification: `Recaman/SharpThreeSpacingCapacity.lean`, `lake build Recaman Recaman.Audit` (`1049` jobs, 0 errors, 0 warnings), `--lint-module` (`19/22` substantive, `7/7` public theorems substantive), `--vacuity-row E-788` (`0 flagged, 0 unknown, 7 theorems`), standard axioms only.

## Boundaries & Non-Claims

- Tightens the PROVED-LEAN actual-`EndN` exponential growth bracket from `[5/3, 2]` to `[5/3, 199/110]` (and all rational `Q/P > 1.80669`), but does NOT surpass the 3-spacing cone root `1.80669` or resolve the true optimal base inside `[5/3, 1.8067]`.
- Does NOT prove height-independent capacity or `C1` / `E-001` / `E-067` / `E-070`.
