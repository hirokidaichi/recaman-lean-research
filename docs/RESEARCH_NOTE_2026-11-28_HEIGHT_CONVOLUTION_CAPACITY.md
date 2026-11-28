# Exponentially-Decaying Height Convolution Capacity, Sharp `18/25` Strip Bound, and `D = 7, 8` Compression (`E-800`)

- **Date**: 2026-11-28
- **Evidence row**: `E-800` (`PROVED-LEAN`, `Recaman/HeightConvolutionCapacity.lean`)
- **Audit script**: `docs/data/depth_general_20261128/height_convolution_capacity_audit.py`

## 1. Summary of Results

Building on `E-797` (`actual_double_ascent_spacing_budget` for `δ ≤ 5`, `actual_eight_slot_double_ascent_budget` at `δ = 5`) and `E-792` (`floor_plus_two_aa_budget`, `same_height_supply_aa_spacing_budget`), we establish four arbitrary-depth tightenings and two sharp finite-depth compressions in Lean 4 (10 audited theorems, vacuity `0 flagged / 0 unknown`):

1. **Exact exponentially-decaying height convolution (`convFree_triangular_capacity`)**:
   With the exact `H = 1` base from `E-792` (`E_2 ≤ F_0`),
   $$5 \cdot 3^{H+2} \cdot T(H + 1) \le \mathrm{convFree}_2(F, H) = 630 \cdot 5^{H-1} F_0 + 405 \cdot 5^{H-1} F_1 + 252 \cdot 5^{H-1} F_2 + \sum_{h=3}^{H+1} 28 \cdot 3^h \cdot 5^{H+1-h} F_h \quad (H \ge 1).$$
   Free additions at height `m + h` decay exponentially as `(3/5)^h`, and free additions strictly above `m + H + 1` carry weight `0`.
2. **Quantitative `LOW-free` vs `HIGH-free` separation (`low_high_free_split_triangular_capacity`)**:
   For every cutoff `1 ≤ s ≤ H + 1`,
   $$5 \cdot 3^{H+2} \cdot T(H + 1) \le 135 \cdot 5^H \sum_{h=0}^{s-1} F_{m+h} + 28 \cdot 3^s \cdot 5^{H+1-s} \sum_{h=s}^{H+1} F_{m+h}.$$
3. **Zero-remainder identities for `S(H)` and `W(m + d)`**:
   For every `g : Nat → Nat` and `H : Nat`,
   $$2\,T(H + 1) + 3\,g(H + 2) + g(H + 1) = 3\,S(H + 2) + W(H),$$
   $$8\,T(H + 1) + 3\,g(H + 2) + g(H + 1) = 3\,W(H + 2) + W(H).$$
   - Pairing the strip identity with `δ = 3` (6-slot) convolution invariant `convFree3` (`α = 8` on `AA_H` so `2 * 8 = 16 ≥ 15` cancels the `δ = 0` top step's `3 * AA_H`) proves for **every `H ≥ 1`** on strip `[m, m + H]`:
     $$25 \cdot 3^H \cdot \mathrm{additions} \le 18 \cdot 5^H \cdot \mathrm{free} \qquad \left(\frac{A}{F} \le 0.72 \cdot \left(\frac{5}{3}\right)^H\right),$$
     slashing `E-797`'s `9/5 = 1.80` by `2.5×` and narrowing the ratio to `E-786`'s `(2/5) * (5/3)^H` lower bound from `4.5×` down to **`9/5 = 1.80×`** for every `H ≥ 1` (`H = 0` is sharp: `25 > 18`).
   - Pairing the weight identity with `8 * convFree2` proves for **every `d : Nat`** and `r ≤ m + d`:
     $$(625 \cdot 3^d)\,W(r) \le (1008 \cdot 5^d)\,\mathrm{free} \qquad \left(\frac{W(m+d)}{F} \le 1.6128 \cdot \left(\frac{5}{3}\right)^d\right),$$
     a `25%` global improvement over `E-797`'s `54/25 = 2.16` (within `3.5%` of the exact LP limit `≈ 1.56`), yielding `(625 * 3^d) * (j + 1)^2 ≤ (1008 * 5^d) * free` without `hpos` or height ceiling.
4. **LP-optimal finite-depth `D = 7` and `D = 8` compressions**:
   - **`D = 7`**: The exact `(5, 3, 1)` dual combination of `E_2 ≤ F_0`, `E-794` at `m + 2`, and `E-792` at `m + 3` yields `3 * W(m + 5) ≤ 56 * free` (improving `E-787`'s `59`), compressing depth-7 positive-deficit counterexamples to **`4 ≤ free ≤ j ≤ 16`** (`3 * 18^2 = 972 > 56 * 17 = 952`, eliminating `j = 17`).
   - **`D = 8`**: The exact `(400, 213, 27, 120, 45)` dual combination (explicitly using `E-797`'s `δ = 5` 8-slot budget at `m + 2` with weight `27` to cancel `45 * 3 = 135 = 27 * 5` on `AA_3`!) yields **`W(m + 6) ≤ 32 * free`**, compressing depth-8 positive-deficit counterexamples to **`4 ≤ free ≤ j ≤ 29`** (`31^2 = 961 > 32 * 30 = 960`, cutting `E-787`'s `j ≤ 61` in half).

## 2. Verification & Non-Claims

- Lean 4: `Recaman/HeightConvolutionCapacity.lean`, 10 audited theorems in `Recaman/Audit.lean`, `39/45` substantive, `0` warnings, `Vacuity lint (E-800; report-only): 0 flagged, 0 unknown, 10 theorems`.
- Python audit (`height_convolution_capacity_audit.py`): passed on 6 adversarial + 10,000 random padded `BlockWord`-prefixed words (5,000 discovery + 5,000 holdout), with negative controls at `H = 0` and on non-`BlockWord` prefix `"AS"`.
- Does NOT resolve `D = 7, 8` residual finite bands (`j ≤ 16`, `j ≤ 29`), `C1`, `Q`, `H`, `SL`, surjectivity, or `E-001`/`E-067`/`E-070`/`E-179`.
