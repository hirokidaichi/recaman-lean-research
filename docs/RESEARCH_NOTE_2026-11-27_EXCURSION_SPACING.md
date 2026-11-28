# Research Note — Excursion 3-Spacing Budget and Dyadic Capacity on Actual `EndN` (`E-785`)

- **Date**: 2026-11-27
- **Hypothesis Card**: [`docs/HYPOTHESIS_CARD_2026-11-27_EXCURSION_SPACING.md`](HYPOTHESIS_CARD_2026-11-27_EXCURSION_SPACING.md)
- **Lean 4 Formalization**: [`Recaman/SupplyExcursionSpacing.lean`](../Recaman/SupplyExcursionSpacing.lean) (**`E-785 PROVED-LEAN`**)
- **Reproducible Verification Script**: [`docs/data/depth_general_20261127/excursion_spacing_audit.py`](data/depth_general_20261127/excursion_spacing_audit.py)

## 1. Executive Summary

`E-674` (`Recaman/SupplyHeightWeightBudget.lean`, `PROVED-LEAN`) established the arbitrary-height original supply budget
$$E_{r+1} \;\le\; \mathrm{lowAdditionWeights}(f, n, r, K) = \sum_{j \le r-1} (2(r - j) - 1)\, A_j,$$
by injecting each supplied addition `t` at `Fw f t = r + 1` into a single downward area slot `(q(t), p(t)) ∈ descentSlots f n r K`. `E-775` (`PROVED-PAPER`) then proved that within the relaxed height-kernel cone defined by `E-674` alone (and in declared-mark walks), a geometric capacity $\sum q^h A_h \le C \sum q^h F_h$ holds if and only if $q^3 + 2q < 1$ ($q < \kappa_{\mathrm{old}} \approx 0.453398$, spectral growth $\rho_{\mathrm{old}} = 1/\kappa_{\mathrm{old}} \approx 2.205569$; in particular $q = 1/2$ fails with gain $9/8 > 1$).

Meanwhile, our `E-783` (`PROVED-LEAN`) multi-block reuse family at height $H = 3k$ achieved per-block $E_H = a = k(3k-2) = \frac{(H-1)^2 - 1}{3}$, leaving an apparent factor-of-$3$ gap against `E-674`'s $E_H \le (H-1)^2$.

We close this exact factor-of-$3$ gap on **actual `EndN`** at **arbitrary height `r : Int`** (`E-785`, `PROVED-LEAN`):
1. **Arbitrary-height excursion 3-spacing (`same_height_supply_three_spacing_budget`)**:
   $$3 \cdot E_{r+1} \;\le\; \mathrm{lowAdditionWeights}(f, n, r, K) + 2 \cdot A_{r-1}.$$
2. **Floor-plus-four improvement (`actual_floor_plus_four_three_spacing`)**:
   $$3 \cdot E_{m+4} \;\le\; 8 \cdot \mathrm{free}(f, n, K)$$
   (strictly improving `E-674`'s $E_{m+4} \le 6 \cdot \mathrm{free}$).
3. **Uniform dyadic (`q = 1/2`) capacity on actual `EndN` (`dyadic_height_weighted_capacity` & `actual_height_exp_two_bound`)**:
   $$\sum_{h=0}^{H} 2^{H-h} A_{m+h} \;\le\; 3 \sum_{h=0}^{H} 2^{H-h} F_{m+h}, \qquad A_{m+h} \;\le\; 3 \cdot 2^h \cdot \mathrm{free}(f, n, K).$$

This **strictly separates actual `EndN` from the `E-674`/`E-775` relaxed height-kernel cone**, breaking the `E-775` barrier $q < 0.4534$ directly at $q = 1/2$ in Lean 4 without any ceiling or run-count restriction.

## 2. Mechanism: 3-for-1 Injection via Downward Excursion Exits

For any `t ∈ [n, n + K)` with `Fw f t = r + 1` and `EndN f 0 t`, `latest_actual_supply_area_crossing` (`E-664`) yields the latest downward crossing `q(t)` of `p := floorPotential f n (r - 1)` through `p(t)` with `n < q(t) < t` and `Fw f (q t) < r`.

`E-672` / `E-674` previously used `supply_potential_spacing_after_last_crossing` only for injectivity (`p t ≠ p u`), discarding the full `+3` separation. Here we retain the excursion structure:

1. **Unique excursion exit `d(t)` (`exists_excursion_exit`, `excursion_exit_unique`)**: Let `e` be the first index `> q(t)` with `r ≤ Fw f e`. Because `Fw f (q t) < r`, `Fw f t = r + 1`, and `Fw` moves by `±1`, setting `d(t) := e - 1` yields:
   - `q(t) ≤ d(t) < t`,
   - `Fw f (d t) = r - 1` and `f (d t) = true`,
   - `Fw f (d t + 1) = r`, and `Fw f i < r` for all `i ∈ [q(t), d(t)]`.
2. **Canonical excursion entry `a(d)` (`lastAbove`)**: Define `a(d) := lastAbove f n r (d - n)` (the largest index in `[n, d]` with `r ≤ Fw f i`, or `n` if none exists). It depends **only** on `d`, satisfies `n ≤ a(d) < q(t) ≤ d`, and `Fw f i < r` on `(a(d), d]`. Because `p` decreases strictly on `[a(d), d]` (`potential_mono_below`),
   $$p(d) \le p(q(t)) < p(t) \le p(q(t) - 1) \le p(a(d)).$$
3. **3-for-1 slot map (`actual_same_height_supply_three_slots`)**: For each supplied `t` and offset `k ∈ {0, 1, 2}`, let `v := p(t) + k`:
   - If `v ≤ p(a(d(t)))`, since `p(d(t)) < p(t) ≤ v ≤ p(a(d(t)))`, `downcross_from_end_values` supplies `q' ∈ (a(d(t)), d(t)]` with `areaCrossesDown p v q'`. Map `(t, k) ↦ Sum.inl (q', v) ∈ descentSlots f n r K`. Because `q' ∈ (a(d(t)), d(t)]`, `excursion_exit_unique` recovers `d(t)` uniquely from `q'`.
   - If `p(a(d(t))) < v`, then `1 ≤ v - p(a(d(t))) ≤ k ≤ 2`. Map `(t, k) ↦ Sum.inr (d(t), (v - p(a(d(t))) - 1).toNat)` into two overflow slots indexed by `d(t)`.
4. **Injectivity**: Any collision `φ (t₁, k₁) = φ (t₂, k₂)` forces both `d(t₁) = d(t₂)` and `p(t₁) + k₁ = p(t₂) + k₂` (in the `inr` branch because `a(d)` depends only on `d`). If `t₁ < t₂`, then `q(t₂) ≤ d(t₂) = d(t₁) < t₁`, so `supply_potential_spacing_after_last_crossing` yields `p(t₁) + 3 ≤ p(t₂)`, contradicting `p(t₁) + k₁ = p(t₂) + k₂` with `k₁ ≤ 2`. Thus `t₁ = t₂` and `k₁ = k₂`, giving
   $$3 \cdot E_{r+1} \;\le\; (\mathrm{descentSlots}\, f\, n\, r\, K).\mathrm{length} + 2 \cdot A_{r-1}.$$
5. **Prefix trimming (`same_height_supply_three_spacing_budget`)**: Trimming `[n, n + K)` to the last supplied addition `n + d` ensures `r ≤ Fw f (n + d)`, zeroing `belowTriangle r (Fw f (n + d))` in `descent_slots_exact_weight` and yielding `3 * E_{r+1} ≤ lowAdditionWeights f n r K + 2 * A_{r-1}` without any endpoint height restriction.

## 3. Dyadic Capacity Induction and Exact Spectral Threshold

For any floor `m ≤ Fw f i` on `[n, n + K]`, write $A_h, F_h, E_h$ for additions, free additions, and supplied additions at height $m + h$. Define
$$U_H := \sum_{j=0}^{H} A_j, \qquad V_H := \sum_{j=0}^{H} (2(H - j) + 1) A_j = \mathrm{lowAdditionWeights}(f, n, m + H + 1, K),$$
and `dyadicSum g H := ∑_{h=0}^H 2^{H - h} g(h)`. Because $V_{H+1} = V_H + 2 U_H + A_{H+1}$ and $3 E_{H+2} \le V_H + 2 A_H$, induction on $H \ge 0$ establishes the exact invariant (`dyadic_supplied_invariant`):
$$3 \cdot \mathrm{dyadicSupplied}(H + 1) + V_{H+1} + A_{H+1} + A_H \;\le\; 2 \cdot \mathrm{dyadicAdditions}(H + 1),$$
with **exact equality at the base case $H = 0$** (since $E_0 = E_1 = 0$ and $V_1 + A_1 + A_0 = 4 A_0 + 2 A_1 = 2\,\mathrm{dyadicAdditions}(1)$) and **zero algebraic slack in the inductive step** (since $2(V_H + A_H + A_{H-1}) - (V_{H-1} + 2 A_{H-1}) = V_{H+1} + A_{H+1} + A_H - 2 A_{H+1}$ identically). Dropping the nonnegative slack terms gives `dyadicAdditions ≤ 3 * dyadicFree` (`dyadic_height_weighted_capacity`).

### Exact Cone Threshold Comparison (`E-674`/`E-775` vs `E-785`)

The general geometric generating inequality of the new 3-spacing cone $3 E_h \le 3 A_{h-2} + \sum_{t \le h-3} (2(h-t) - 3) A_t$ is
$$G_{\mathrm{new}}(q) := q^2 + q^3 + \frac{5}{3} q^4 + \frac{7}{3} q^5 + \cdots = \frac{3 q^2 - 3 q^3 + 2 q^4}{3(1 - q)^2} < 1 \iff 2 q^4 - 3 q^3 + 6 q - 3 < 0.$$

| Cone | Characteristic Equation | Threshold $\kappa$ | Growth $\rho = 1/\kappa$ | Gain at $q = 1/2$ | $q=1/2$ Capacity |
| --- | --- | --- | --- | --- | --- |
| `E-674` / `E-775` (relaxed) | $q^3 + 2q = 1$ | $0.4533976515$ | $2.2055694304$ | $9/8 = 1.125$ (**FAILS**) | Impossible |
| **`E-785` (actual `EndN` 3-spacing)** | $2q^4 - 3q^3 + 6q = 3$ | $0.5534997521$ | $1.8066855428$ | $2/3 = 0.6667$ (**PASSES**) | **$C = 3$ (`PROVED-LEAN`)** |

## 4. Sharpness and Reproducible Computation (`COMPUTED`)

Running `python3 docs/data/depth_general_20261127/excursion_spacing_audit.py` (CPU `4.50s`) verifies:
- **Discovery (`n = 0`, all `32,766` words of length `1..14`)**: `0` violations of `same_height_supply_three_spacing_budget`, `dyadic_height_weighted_capacity`, `actual_floor_plus_four_three_spacing`, and `actual_height_exp_two_bound`.
- **Frozen holdout 1 (`10,000` random `BlockWord ++ A^a ++ tail`, `len ≤ 140`, seed `2026112703`)**: `0` violations.
- **Exact small-height sharpness**:
  - `h = 1 (r = 0)`: `(SAAASS)^10` achieves `3 * E_1 = 30 = W_0 + 2 * A_{-1}` (`ratio = 1.000000`, exact equality).
  - `h = 2 (r = 1)`: `(AAASSS)^10` achieves marginal equality `3 * E_2 = W_1 + 2 * A_0` per copy (`27/30` over 10 copies).
  - `h = 3 (r = 2)`: `(AAAASASSSS)^20` achieves marginal equality `3 * E_3 = 6 = W_2 + 2 * A_1` per copy (`111/120` over 20 copies, `E_3 = F_0 + F_1` sharp).
- **Arbitrary-height asymptotic sharpness (`Holdout 2`, `E-783` family `H = 3k, k = 1..6, R = 30`)**:
  Every copy of the zero-shift block `V` achieves `3 * E_H = (H - 1)^2 - 1` against `W_{H-1} + 2 * A_{H-2} = (H - 1)^2 + 2`, leaving an additive gap of literally **`3`** at every height `H = 3k`:
  - `k = 2 (H = 6)`: `24 / 27 = 0.888889`
  - `k = 4 (H = 12)`: `120 / 123 = 0.975610`
  - `k = 6 (H = 18)`: `288 / 291 = 0.989691 → 1` as `H → ∞`.
- **Negative controls**: Dropping `+ 2 * A_{r-1}` fails on `SAAASS` (`3 > 1`); dropping the `BlockWord` prefix fails on non-`BlockWord` prefixes.

## 5. Remaining Uncertainty & Next Frontier Question

While `E-785` establishes that the single-height 3-spacing inequality `3 * E_{r+1} ≤ W_r + 2 * A_{r-1}` is **asymptotically sharp at every height `H`** (matching `E-783` up to `+3`) and lowers the proven exponential upper bound on actual `EndN` from `2.2056^h` to `< 2^h` (cone radius `1.8067^h`), a fundamental arbitrary-depth gap remains open:
- **Lower bound on actual `EndN` (`E-783`/`E-784`)**: `sup_{Fw ∈ [0, H]} A / F = Ω(H)` (single bank reuse, linear in `H`).
- **Upper bound on actual `EndN` (`E-785`)**: `sup_{Fw ∈ [0, H]} A / F ≤ O(2^H)` (cone bound `O(1.8067^H)`).
- **Open Question (`H-20261128-01`)**: Can multi-level coupling on actual `EndN` achieve super-linear (`ω(H)`) or exponential (`c^H`) growth of `A / F` across height `[0, H]`, OR does cross-height conservation of `\Phi_r` prevent simultaneously saturating `E-785` across multiple heights (forcing a polynomial-in-`H` upper bound on actual `EndN`)?
