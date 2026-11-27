# Research Note: Coupled Two-Height Excursion Spacing and Breaking the `1.8067` Cone Barrier (`E-794`)

**Date**: 2026-11-27  
**Parent cycle**: `R-20261127-02`  
**Lean module**: [`Recaman/JointHeightSpacingCapacity.lean`](../Recaman/JointHeightSpacingCapacity.lean) (`E-794 PROVED-LEAN`)  
**Audit script**: [`docs/data/depth_general_20261127/joint_height_spacing_audit.py`](data/depth_general_20261127/joint_height_spacing_audit.py)  
**Evidence row**: `E-794` (`PROVED-LEAN`)

## 1. Breakthrough Summary

The single-height excursion 3-spacing budget (`E-785`, `3 * E_{r+1} ≤ W(r) + 2 * A_{r-1}`) and its sharp rational cone (`E-788`) had an exact cone barrier at `κ_3 ≈ 0.55350`, `1 / κ_3 ≈ 1.80669` (making `P/Q = 5/9`, base `1.8000`, provably unattainable inside the `E-785` cone).

In `E-794` (`Recaman/JointHeightSpacingCapacity.lean`), we discover and unconditionally prove in Lean 4 that the **SAME** source-level potential `p = floorPotential f n (r - 1)` simultaneously controls **TWO adjacent supplied heights** (`E_{r+1}` at weight `3` and `E_r` at weight `1`):
$$3 \cdot E_{r+1} + E_r \le (\mathrm{descentSlots}\ f\ n\ r\ K).\mathrm{length} + 3 \cdot \mathrm{doubleAscent}\ f\ n\ K\ (r - 1),$$
$$3 \cdot E_{r+1} + E_r \le \mathrm{lowAdditionWeights}\ f\ n\ r\ K + 3 \cdot \mathrm{doubleAscent}\ f\ n\ K\ (r - 1).$$
Using a zero-slack rational polynomial telescoping invariant across the new joint cone
$$1/2 \le P/Q < \kappa_{\mathrm{joint}} \approx 0.563708 \qquad (1 / \kappa_{\mathrm{joint}} \approx 1.773969),$$
we unconditionally prove in Lean 4:
- **`actual_height_exp_nine_fifths`** (`P/Q = 5/9`, **base `9/5 = 1.8000`**, breaking `E-785`/`E-788`'s `1.8067` cone barrier — `5/9` was `E-788`'s negative control!),
- **`actual_height_exp_sixteen_ninths`** (`P/Q = 9/16`, **base `16/9 ≈ 1.7778`**),
- **`actual_height_exp_190_107`** (`P/Q = 107/190`, **base `190/107 ≈ 1.7757`**, within **`0.10%`** of the exact joint cone root `1.77397`),
- **`joint_rational_low_weights_bound`** (arbitrary-depth low-weight bound `P^(d+1) Q^2 (Q - P) * W(r) ≤ jointM P Q * Q^d * free` with zero `1 / (L - M)` prefactor blowup).

This directly satisfies **Track B** of `H-20261128-01` and narrows the `PROVED-LEAN` actual-`EndN` exponential growth bracket from `[5/3, 199/110] = [1.6667, 1.8091]` (`E-786`/`E-788`) down to **`[5/3, 190/107] = [1.6667, 1.7757]`**.

## 2. Mechanism: Joint 3+1 Potential-Slot Injection

Let `p := floorPotential f n (r - 1)`. Recall `p(i + 1) = p(i) + Fw(i + 1) - r`.

1. **Why every height-`r` supplied addition `u` (`Fw(u) = r, EndN f 0 u`) crosses `p` downward**:
   Let `s < u` be the `EndN` anchor of `u`, so `Fw(s) = r - 1` and `Ar(s, u - s) = 0`.
   - If `s ≥ n`, then
     $$p(u) - p(s) = \sum_{i = s + 1}^{u} \big(Fw(i) - r\big) = \mathrm{Ar}(s, u - s) - (u - s) = -(u - s) \le -1.$$
   - If `s < n`, then `block_suffix_positive_walk` gives `Ar(s, n - s) > 0`, and splitting `0 = Ar(s, u - s)` at `n` yields `p(u) = -Ar(s, n - s) - (u - n) ≤ -1 = p(n) - 1`.
   - In BOTH cases, `p(u) < p(u) + 1 ≤ p(s')` for an anchor `s' ∈ [n, u)`. Thus `u` has a latest downward crossing `q(u) ∈ (n, u)` of `p` at level `p(u) + 1`, with `Fw(q(u)) < r`.
   - Because `f(u) = true`, `Fw(u + 1) = r + 1`. Hence the extended excursion below `r + 1` exits at `d'(u) ∈ (q(u), u]` with `Fw(d' - 1) = r - 1`, `f(d' - 1) = true`, `f(d') = true`, and `d' ≤ u < n + K`, so `d₁ = d' - 1` is counted in `doubleAscent f n K (r - 1)`.

2. **Pairwise disjointness of `{p(t), p(t)+1, p(t)+2}` (for `t` at `r + 1`) and `{p(u)}` (for `u` at `r`) sharing an exit `d'`**:
   - `t₁ < t₂`: `p(t₁) + 3 ≤ p(t₂)` (`supply_potential_spacing_after_last_crossing`).
   - `u₁ < u₂`: since `Fw(u₁ + 1) = r + 1`, `p(u₁ + 1) = p(u₁) + 1` and `u₁ + 1 < u₂`; no crossing of `p(u₂) + 1` in `(u₁ + 1, u₂]` forces `p(u₁) + 1 ≤ p(u₂)`.
   - `u < t`: if `u + 1 = t` then `p(t) = p(u) + 1 > p(u)`; if `u + 1 < t`, no crossing of `p(t)` in `(u + 1, t - 1]` forces `p(u) + 1 < p(t)`.
   - `t < u`: since `Fw(t + 1) = r + 2`, `p(t + 1) = p(t) + 2`, and `Fw(t + 2) ≥ r + 1` gives `p(t + 2) ≥ p(t) + 3` with `t + 2 < u`; no crossing of `p(u) + 1` in `(t + 2, u]` forces `p(t) + 3 ≤ p(u)`.

3. **Target placement**:
   - Each `(t, k)` (`k ∈ {0, 1, 2}`) maps into `descentSlots f n r K` if `p(t) + k ≤ p(a₀)`, else into overflow `(d' - 1, j)` with `j ∈ {0, 1}`.
   - Each `u` satisfies `p(d') ≤ p(u) < p(a₀)`; it maps into `descentSlots f n r K` if `p(d') < p(u)`, else (when `p(u) = p(d')`, at most once per `d'`) into the third overflow slot `(d' - 1, 2)`.
   - Truncating to the last mark `d` of `((Fw = r + 1 ∨ Fw = r) ∧ EndN)` still satisfies `r ≤ Fw(n + d)`, making `belowTriangle r (Fw(n + d)) = 0` and yielding `3 * E_{r+1} + E_r ≤ lowAdditionWeights(r) + 3 * AA_{r-1}`.

## 3. Zero-Slack Joint Polynomial Telescoping

Define for `P < Q` and `Q ≤ 2 * P`:
- `jointK P Q = Q * (Q - P)^2`,
- `jointL P Q = (3 * Q + P) * jointK P Q`,
- `jointM P Q = P^2 * (4 * Q^2 + 3 * P^2 - 5 * P * Q)`,
- `cW = P * Q^2 * (Q - P)`, `cU = 2 * P^2 * Q^2`, `cPrev = 3 * P * Q * (Q - P)^2`.

The exact invariant at horizon `H + 1` is:
$$\mathrm{jointL} \cdot S_E(H + 1) + P^{H+1} \big( c_W W_H + c_U U_H + c_{\mathrm{prev}} A_H + \mathrm{jointM} \cdot A_{H+1} \big) \le \mathrm{jointM} \cdot S_A(H + 1) + P \cdot \mathrm{jointK} \cdot P^{H+1} E_{H+1}.$$
Both the base case `H = 0` (`E_0 = E_1 = 0`, `P(c_W + c_U + c_{\mathrm{prev}}) = Q \cdot \mathrm{jointM}`) and the induction step `H → H + 1` (where `Q * P * jointK * P^{H+1} * E_{H+1}` cancels identically!) hold with **zero algebraic slack**. Finally, `Q ≤ 2 * P` implies `P * jointK ≤ jointM`, so `P * jointK * E_{H+1} ≤ jointM * A_{H+1}` cancels cleanly from both sides.

## 4. Reproducible Audit Summary

Command: `python3 docs/data/depth_general_20261127/joint_height_spacing_audit.py`
- Exhaustive `L = 1..15`: `65,534` words, `463,252` joint-spacing checks, `795,436` rational-cone checks, `0` violations.
- Holdout `BlockWord + A^a` (`3,500` random tails across `1/2, 5/9, 9/16, 107/190`): `35,580` spacing + `128,320` cone checks, `0` violations.
- Zero-slack sharpness: `pref = "SAAA"`, `r = 0`, `3 * E_1 + E_0 = 7 == W(0) + 3 * AA_{-1} = 7`.
- Negative controls: non-`BlockWord` prefix `"AASASSAAAA"` gives `+2`; `P/Q = 564/1000` has `M > L`.
- Lean 4: `Recaman/JointHeightSpacingCapacity.lean` builds cleanly with `0` warnings and `0 flagged / 0 unknown` vacuity lint.
