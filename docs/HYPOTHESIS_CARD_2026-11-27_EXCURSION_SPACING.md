# Hypothesis Card — `H-20261127-03` (Excursion 3-Spacing Budget and Dyadic Height-Weighted Capacity on Actual `EndN`)

- **ID**: `H-20261127-03`
- **Date**: 2026-11-27
- **Parent Cycle**: `R-20261127-01`
- **Track**: Depth-general actual-`EndN` height capacity (strictly strengthening `E-674` and separating actual `EndN` from the `E-775` relaxed height-kernel cone)
- **Status**: **`PROVED-LEAN`** (`E-785`, `Recaman/SupplyExcursionSpacing.lean`, 0 vacuity flags, 0 unknowns)

## 1. Exact Mathematical Claim

Let `f : Nat → Bool`, `n a K : Nat`, and `w : List Bool` satisfy `BlockWord w` and `seg f 0 n = w ++ List.replicate a true` (arbitrary `BlockWord` prehistory, arbitrary run count, arbitrary interval length `K`, no endpoint height restriction).

1. **Arbitrary-height 3-spacing excursion budget (`same_height_supply_three_spacing_budget`)**:
   For every `r : Int`,
   $$3 \cdot E_{r+1} \;\le\; W_r + 2 \cdot A_{r-1},$$
   where
   - `E_{r+1} := cN (fun t => Fw f t = r + 1 ∧ EndN f 0 t) n K` (actual original supplied additions at height `r + 1`),
   - `W_r := lowAdditionWeights f n r K = ∑_{t ∈ [n, n+K), f t = true, Fw f t < r} (2(r - Fw f t) - 1)`,
   - `A_{r-1} := cN (fun t => Fw f t = r - 1 ∧ f t = true) n K` (actual additions at height `r - 1`).
   Equivalently, setting `h = r + 1`:
   $$3 \cdot E_h \;\le\; 3 \cdot A_{h-2} + \sum_{j \le h-3} \big(2(h - j) - 3\big)\, A_j.$$

2. **Floor-plus-four improvement (`actual_floor_plus_four_three_spacing`)**:
   If `∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i`, then
   $$3 \cdot E_{m+4} \;\le\; 8 \cdot \mathrm{free}(f, n, K)$$
   (strictly improving `E-674`'s `E_{m+4} ≤ 6 * free f n K` by more than `2.25×`).

3. **Uniform dyadic (`q = 1/2`) height-weighted capacity (`dyadic_height_weighted_capacity`)**:
   Under the same floor hypothesis `m ≤ Fw f i` on `[n, n+K]`, for every height horizon `H : Nat`,
   $$\sum_{h=0}^{H} 2^{H - h} A_{m+h} \;\le\; 3 \sum_{h=0}^{H} 2^{H - h} F_{m+h},$$
   where `A_{m+h} = levelAdditions f n K (m + h)` and `F_{m+h} = levelFree f n K (m + h)`.
   In particular (`actual_height_exp_two_bound`), for every `h : Nat`,
   $$A_{m+h} \;\le\; 3 \cdot 2^h \cdot \mathrm{free}(f, n, K).$$

## 2. Falsification & Boundary Checks (Executed Before Formalization)

- **Negative control 1 (dropping `+ 2 * A_{r-1}`)**: Naive `3 * E_{r+1} ≤ W_r` is **REFUTED** on `SAAASS` at `r = 0` (`3 * E_1 = 3 > 1 = W_0`) and on `(SAAASS)^R` (`3 R > R`).
- **Negative control 2 (dropping `BlockWord` prefix)**: Arbitrary non-`BlockWord` prefix `SASASASSSSAAAASASASA` + `A` + `SASSAAAAAAAAASSAAAAASAAAASASAAAAASSSAAAAAASAA` violates `3 * E_{r+1} ≤ W_r + 2 * A_{r-1}` at `r = -1` (`E = 1, W = 0, A_{-2} = 0`).
- **Discovery range (`n = 0`, exhaustive `L = 1..14`, `32,766` words)**: `0` violations of all four inequalities.
- **Frozen holdout 1 (`10,000` random `BlockWord ++ A^a ++ tail`, `len ≤ 140`, seed `2026112703`)**: `0` violations.
- **Frozen holdout 2 (`E-783` arbitrary-height family `H = 3k, k = 1..6, R = 30`)**: `0` violations, and per-block `3 * E_H / (W_{H-1} + 2 * A_{H-2}) = ((H-1)^2 - 1)/((H-1)^2 + 2) → 1` (`0.989691` at `H = 18`), proving asymptotic sharpness of the 3-spacing coefficient at arbitrary height.

## 3. Dependencies & Non-Claims

- **Lean dependencies**: Only `Recaman.SupplyHeightWeightBudget` (transitively `SupplyDescentWeight`, `SupplyDescentSlots`, `SupplyAreaCrossings`, `FloorSupplyPotential`, `FloorSupplyFreeBudget`, `LowTargetWeightedGap`). Standard axioms `[propext, Classical.choice, Quot.sound]` only.
- **What this proves**: Strictly improves `E-674` at every height `r` on actual `EndN`, strictly separates actual `EndN` from the `E-775` relaxed height-kernel cone (`q < 0.4534`, `ρ ≈ 2.2056`) by proving uniform capacity at `q = 1/2` (`C = 3`, cone spectral radius `ρ_new ≈ 1.8067 < 2`).
- **What this does NOT prove**: Does **NOT** prove an unweighted `H`-independent capacity `A ≤ C * F`, does **NOT** determine whether actual `EndN` achieves exponential `c^H` (`1 < c ≤ 1.8067`) vs polynomial `O(H^d)` growth in `H`, and does **NOT** resolve `E-001`, `E-067`, `E-070`, or `C1`.

## 4. Acceptance Test & Stopping Condition

- **Acceptance test**: Compile `Recaman/SupplyExcursionSpacing.lean`, pass `harness_gate.py --lint-module` and `harness_lean.py --vacuity-module` with 0 flags / 0 unknowns, pass `Recaman/Audit.lean` and G1–G6 checks, and pass frozen Python discovery/holdout script `docs/data/depth_general_20261127/excursion_spacing_audit.py`.
- **Outcome**: **PASSED** (`E-785 PROVED-LEAN`). Next open question: whether actual `EndN` achieves super-linear/exponential growth `A / F = ω(H)` in bounded height `[m, m + H]` or obeys a polynomial-in-`H` upper bound.
