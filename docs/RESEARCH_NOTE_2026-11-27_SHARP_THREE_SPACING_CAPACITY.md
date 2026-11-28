# Research Note: Sharp Rational 3-Spacing Capacity Across the Entire Cone `[1/2, κ)` (`E-788`)

- **Date**: 2026-11-27 (`R-20261127-02`, Track 2B)
- **Registry entry**: `E-788 PROVED-LEAN` (`Recaman/SharpThreeSpacingCapacity.lean`)
- **Statement audit**: `docs/statement_audits/E-788.md` (`0 flagged, 0 unknown, 7 theorems`)
- **Hypothesis card**: `docs/HYPOTHESIS_CARD_2026-11-27_SHARP_THREE_SPACING_CAPACITY.md`
- **Reproducible audit script**: `docs/data/depth_general_20261127/sharp_three_spacing_audit.py`

## 1. Mathematical Summary

In `E-785` (`Recaman/SupplyExcursionSpacing.lean`), the arbitrary-height excursion 3-spacing
budget `3 * E_{r+1} ≤ lowAdditionWeights(r) + 2 * A_{r-1}` was integrated at `q = 1/2`, giving
the PROVED-LEAN exponential upper bound `A_{m+h} ≤ 3 * 2^h * free` while noting numerically that
the 3-spacing cone extends up to the root `κ ≈ 0.55350` (`1/κ ≈ 1.80669`) of
`2 q^4 - 3 q^3 + 6 q = 3`.

Here we derive an exact, zero-slack polynomial telescoping invariant parameterized by EVERY
rational `q = P / Q` satisfying `P < Q`, `Q ≤ 2 * P`, and `coneM P Q ≤ 3 * coneK P Q`:
$$K = Q^2 (Q - P)^2, \qquad M = P^2 (3 Q^2 + 2 P^2 - 3 P Q),$$
$$c_V = P Q^2 (Q - P), \quad c_U = P Q^2 (4 P - 2 Q), \quad c_{A_0} = 2 P Q (Q - P)^2, \quad c_{A_1} = P (Q - P)^2 (Q + 2 P).$$
For `ratSum P Q g H = ∑_{j=0}^H Q^{H - j} P^j g(j)`, induction on `H` from
`same_height_supply_three_spacing_budget` proves:
$$3 K \cdot \mathrm{ratSupplied}(H + 1) + P^{H + 1} (c_V V_{H + 1} + c_U U_{H + 1} + c_{A_1} A_{H + 1} + c_{A_0} A_H) \le M \cdot \mathrm{ratAdditions}(H + 1)$$
with **zero slack** at both the base case (`H = 0`) and every induction step (`H → H + 1`, where
the exact remainder equals `P^{H + 2} K (V_H + 2 A_H - 3 E_{H + 2}) ≥ 0`).

### Consequences proved unconditionally in Lean 4

1. **Full-cone weighted capacity** (`rational_height_weighted_capacity`):
   `(3 K - M) * ratAdditions P Q ≤ 3 K * ratFree P Q`.
2. **Full-cone exponential level bound** (`rational_height_exp_bound`):
   `(3 K - M) * P^h * levelAdditions(m + h) ≤ 3 K * Q^h * free`.
3. **Blowup-free arbitrary-depth low-addition weight bound** (`rational_low_weights_bound`):
   Cancelling `M * ratSupplied ≤ 3 K * ratSupplied` directly retains the `c_V V_{H+1}` term
   WITHOUT dividing by `3 K - M`, yielding for ALL `d : Nat` and `r ≤ m + d`:
   $$P^d Q^3 (Q - P) \cdot \mathrm{lowAdditionWeights}(r) \le M \cdot Q^d \cdot \mathrm{free}.$$
   Even at `q = 110 / 199` (`base = 199 / 110 ≈ 1.8091`), the prefactor `M / (Q^3 (Q - P))` stays
   bounded by `1.3341`!
4. **Arbitrary-height free-gap square sharpening** (`rational_arbitrary_target_free_gap_square`):
   without `hpos` or any upper height ceiling, `Fw(b + j) ≤ m + d + 1` forces
   `P^d Q^3 (Q - P) * (j + 1)^2 ≤ M * Q^d * free`.
5. **Concrete specializations**:
   - `(11, 20)` (`base = 20 / 11 ≈ 1.8182`): `1289 * 11^h * A_{m+h} ≤ 48600 * 20^h * free` (`actual_height_exp_twenty_elevenths`).
   - `(110, 199)` (`base = 199 / 110 ≈ 1.8091`, within `0.13%` of the cone root `1.80669`):
     `5309263 * 110^h * A_{m+h} ≤ 941038563 * 199^h * free` (`actual_height_exp_199_110`) and
     `110^d * 701373311 * lowAdditionWeights(r) ≤ 935729300 * 199^d * free` (`low_weights_exp_199_110`).

Together with `E-786`, the **PROVED-LEAN** bracket for the actual-`EndN` exponential growth base
is now narrowed from `[5/3, 2]` to **`[5/3, 199/110] = [1.6667, 1.8091]`** (and every rational
upper bound `> 1.80669` is covered by the general parameterized theorem).

## 2. Falsifier & Verification Record

Command:
```bash
python3 docs/data/depth_general_20261127/sharp_three_spacing_audit.py
```
Exact result:
- Discovery (exhaustive `L = 1..12`, `8,190` words) + Holdout (`2,000` random `BlockWord ++ A^a ++ tail`, `seed = 2026112706`) across `(1,2), (6,11), (11,20), (110,199)`: `282,444` capacity checks, `282,444` exponential checks, `323,204` low-weight checks, `0` violations.
- Negative control: `(5, 9)` gives `3 K - M = -62 < 0` (outside the 3-spacing cone).

Lean verification:
- `lake build Recaman Recaman.Audit`: succeeded (`1049` jobs, 0 errors, 0 warnings).
- `python3 scripts/harness_gate.py --lint-module Recaman/SharpThreeSpacingCapacity.lean`: `19/22` substantive, `7/7` public theorems substantive.
- `python3 scripts/harness_lean.py --vacuity-row E-788`: `0 flagged, 0 unknown, 7 theorems`.
