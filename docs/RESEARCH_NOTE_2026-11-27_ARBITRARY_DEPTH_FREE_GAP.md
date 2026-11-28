# Research Note: Arbitrary-Depth Low-Weight Bounds & Free-Gap Counterexample Profiles (`E-787`)

- **Date**: 2026-11-27 (`R-20261127-02`, Track 1)
- **Registry entry**: `E-787 PROVED-LEAN` (`Recaman/ArbitraryDepthFreeGap.lean`)
- **Statement audit**: `docs/statement_audits/E-787.md` (`0 flagged, 0 unknown, 7 theorems`)
- **Hypothesis card**: `docs/HYPOTHESIS_CARD_2026-11-27_ARBITRARY_DEPTH_FREE_GAP.md`
- **Reproducible audit script**: `docs/data/depth_general_20261127/arbitrary_depth_free_gap_audit.py`

## 1. Mathematical Summary

Previously, free-gap bounds for positive-deficit suffixes after a padded `BlockWord` prefix were
available only at fixed small depths (`D = 5` in `E-663` / `Recaman/LowTargetWeightedGap.lean` and
`D = 6` in `E-666` / `Recaman/DepthSixGapResidual.lean`, yielding `j ≤ 8`), with no general theorem
for `D ≥ 7`.

Using the arbitrary-height excursion 3-spacing budget (`E-785`, `same_height_supply_three_spacing_budget`)
and level-weight decomposition `lowAdditionWeights f n (m + d + 1) K = levelWeightSum A d`, we
establish in `Recaman/ArbitraryDepthFreeGap.lean`:

1. **Arbitrary-height dyadic low-weight bound** (`low_weights_le_two_dyadic_free`):
   for every `d : Nat`,
   $$\text{lowAdditionWeights}(n, m + d + 1, K) \le 2 \cdot \text{dyadicFree}(n, K, m, d).$$
2. **Arbitrary-depth exponential-two weight bound** (`low_weights_le_pow_two_free`):
   for every `d : Nat` and `r ≤ m + d`,
   $$\text{lowAdditionWeights}(n, r, K) \le 2^d \cdot \text{free}(n, K).$$
3. **Sharp depth-5 3-spacing weight bound** (`low_weights_five_three_spacing`):
   for `r ≤ m + 5`,
   $$3 \cdot \text{lowAdditionWeights}(n, r, K) \le 59 \cdot \text{free}(n, K),$$
   strictly strengthening `E-674`'s `25 * free` down to `59/3 ≈ 19.667` (and improving over `2^5 = 32`).
4. **Unconditional arbitrary-height free-gap cutoff without `hpos` or upper height ceiling**
   (`arbitrary_target_height_free_gap_square`, `arbitrary_target_height_free_gap`):
   for every `d : Nat` with `Fw f (b + j) ≤ m + d + 1`,
   $$(j + 1)^2 \le 2^d \cdot \text{free}(n, b - n),$$
   and hence `2^d ≤ j + 2` unconditionally forces `j + 1 ≤ free f n (b - n)`.
5. **Arbitrary-depth positive-deficit counterexample profile** (`positive_arbitrary_depth_free_gap_profile`):
   for EVERY `D ≥ 2` and `hfloor : ∀ i ∈ [n, b], Fw f n - D ≤ Fw f i` (with no upper walk bound),
   any positive-deficit counterexample (`free ≤ j`) is compressed to the finite band
   $$4 \le \text{free} \le j \le 2^{D - 2} - 3, \quad \text{Fw}(b + j) \le \text{Fw}(n) - 1, \quad (j + 1)^2 \le 2^{D - 2} \cdot \text{free}.$$
6. **Sharp depth-7 counterexample profile** (`positive_depth_seven_counter_profile`):
   at `D = 7`, any positive-deficit counterexample obeys `4 ≤ free ≤ j ≤ 17`, `Fw(b + j) ≤ Fw(n) - 1`,
   and `3 * (j + 1)^2 ≤ 59 * free`.

## 2. Falsifier & Verification Record

Command:
```bash
python3 docs/data/depth_general_20261127/arbitrary_depth_free_gap_audit.py
```
Exact result:
- Discovery (exhaustive `L = 1..13`, `16,382` words): `0` violations across all 7 claims.
- Holdout (`4,000` random `BlockWord ++ A^a ++ tail`, `seed = 2026112702` + `E-786` cascade words `H = 2, 3, 4` + boundary cases): `161,407` weight checks, `1,792` supplied-gap checks, `746` `hpos` hits, `0` violations; max observed `W(m+5)/free = 10.5000 ≤ 59/3 = 19.6667`.
- Minimal negative control: non-`BlockWord` prefix `"SAA"` + tail `"A"` (`m = 1, free = 0, W(2) = 1 > 2^1 · 0`).

Lean verification:
- `lake build Recaman Recaman.Audit`: succeeded (`1048` jobs, 0 errors, 0 warnings).
- `python3 scripts/harness_gate.py --lint-module Recaman/ArbitraryDepthFreeGap.lean`: `16/20` substantive, all 7 public theorems `concrete / proof=work / SUBSTANTIVE`.
- `python3 scripts/harness_lean.py --vacuity-row E-787`: `0 flagged, 0 unknown, 7 theorems`.

## 3. Limitations & Next Frontier

- By `E-786`, `lowAdditionWeights(m + d) / free` genuinely grows at least like `(5/3)^d` on raw sign
  words, so any free-gap proof relying solely on `lowAdditionWeights / free` necessarily leaves an
  exponentially growing finite band `4 ≤ free ≤ j ≤ O(rho^D)` as `D → ∞`.
- Eliminating that band at arbitrary depth requires either (a) narrowing the actual-`EndN` exponent
  (Track 2B: `2 -> 20/11 ≈ 1.8182`), (b) testing whether coherent greedy (`E-759 = (0,0)`) eliminates
  the `E-786` exponential cascade (Track 2A), or (c) exploiting genuine clock-0 canonical invariants
  on `Recaman.Basic.a` (Track 3).
