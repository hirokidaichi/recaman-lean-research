# Hypothesis Card: Purely Numeric Departure `A` Stock Strip & `34/15` Floor Potential (E-803)

- **Date**: 2026-11-28
- **Status**: `PROVED-LEAN` (`E-803`, `Recaman/NumericStockStripPotential.lean`)
- **Branch / Frontier**: General-principle arbitrary-depth branch — second genuinely different purely numeric mechanism (upgrading `E-772 PROVED-PAPER` to `PROVED-LEAN` directly on `Recaman.SeededReplay` and `Recaman.Basic.a`)

## 1. Precise Statement & Quantifiers

For arbitrary `b : Nat`, `s : State`, define distinct seen stock count `seenCountIn b s t lo hi := |V_t ∩ [lo, hi]|`, `stockBelow b s t := |V_t ∩ [1, X(t) - 1]|`, `floorP b s t := (b + t) + 2*X(t)`, `floorW b s t := 12*(b + t) + 15*X(t) - 10*K(t)`, and `floorT b s t := 13*(b + t) + 20*X(t) - 15*K(t)`.

1. **Primitive excursion lower bound (`primitive_excursion_area_lower_bound`)**: Every nonempty primitive nonnegative balanced walk of length `w - u` has `2 ∣ (w - u)` and `3 * ((w - u) / 2) - 2 ≤ Ar f u (w - u)`.
2. **Single-cut old-stock discount (`floor_cut_stock_discount`)**: At any coherent last floor visit `IsLastFloorVisit b s c v Q` (`X(c) ≥ 1`, `X(c) ∈ seen(c)`, `c ≤ v < Q`, `Fw v = Fw c`, `Fw ≥ Fw c` on `[c, Q]`, `Fw > Fw c` on `(v, Q]`):
   - `3 * (v - c) + 6 * X(v) + 4 * N ≤ 6 * X(c)`,
   - `floorP b s (v + 1) + 4 * K + 1 ≤ 3 * floorP b s c`,
   - `3 * (v - c) + 2 * X(v) + 4 * K + 4 ≤ 6 * X(c)`.
3. **Departure `A` upcrossing strip & clipped transport (`departure_strip_stock_transport`)**: Consecutive floor-departure `A` outputs rise by at most `+1`, so every integer in `[X(c + 1), X(v + 1) - 1]` occurs in `(run b s (v + 1)).seen` and is disjoint from `[1, X(c)]`, yielding:
   `(min x (y - 1) - (x - 1 - m - K)) + (y - (x + (b + c) + 1)) ≤ stockBelow b s (v + 1)`.
4. **Main paid potential recurrences & sharpness (`floor_potential_W_recurrence`, `floor_potential_T_recurrence`, `floor_potential_T_sharp`)**:
   - `15 * floorW b s (v + 1) ≤ 34 * floorW b s c - 30` (`34/15 < 3`),
   - `13 * floorT b s (v + 1) ≤ 33 * floorT b s c - 166`, exact equality at `sharpTState = {value := 1, seen := [0, 1]}` for EVERY base `a : Nat`.
5. **Iterated arbitrary-depth envelope beating `3^j` from `j ≥ 7` (`iterated_floorW_envelope_beats_three_pow`)**:
   - Along any `j`-step chain of coherent floor cuts, `19 * 15^j * W_j ≤ 34^j * (19 * W_0 - 30) + 30 * 15^j`, `5 * P_j + 20 ≤ 2 * W_j`, and whenever `7 ≤ j`, `2 ≤ P0`, `W_0 ≤ 12 * P0`:
     `190 * 15^j * P_j < 95 * 45^j * (2 * P0 - 1) + 95 * 15^j` (strictly beating the classical `3^j * (P0 - 1/2) + 1/2` horizon for EVERY `j ≥ 7` and `P0 ≥ 2`!).
6. **Canonical orbit specialization (`canonical_orbit_floor_potentials`)**: Specializes all cut bounds, `15 * W' ≤ 34 * W - 30`, and `13 * T' ≤ 33 * T - 166` directly to `Recaman.Basic.a`.

## 2. Dependencies

- `Recaman.Basic`, `Recaman.SeededReplay`, `Recaman.CoherentGreedyFreshness` (`E-798`).

## 3. Falsifier / Discovery-Holdout Computation

- Script: `docs/data/depth_general_20261128/numeric_stock_strip_audit.py`
- Command: `python3 docs/data/depth_general_20261128/numeric_stock_strip_audit.py`
- Results:
  - Exact sharpness `13 * T' == 33 * T - 166` verified for `a = 0..50`; exact two-cut `P' == 3*P - 1 - 4*K` sharpness verified on `A(AS)^b A`.
  - Genuine clipped-cut control (`AAASSSA`, `b=0, x=10, seen={0,9,10}` → `z=1, y=8 < x=10`): `4` cuts, `1` clipped, all inequalities pass.
  - Uniform horizon `N_j < B_j` verified in exact `Fraction` arithmetic for all `j = 7..30, P_0 = 2..100`.
  - Discovery (`a[0..800]` + 60 random states: `2,779` cuts, `1,978` positive strips) and Holdout (`a[0..2000]` + 60 random states: `3,334` cuts, `2,427` positive strips): `ALL E-803 AUDITS PASSED`.

## 4. Lean Verification & Independent Audit

- Module: `Recaman/NumericStockStripPotential.lean` (`8` public theorems in `Recaman/Audit.lean`, `0` warnings, `0` `sorry`/`admit`/`native_decide`/custom axioms).
- `python3 scripts/harness_gate.py --lint-module Recaman/NumericStockStripPotential.lean`: `24/26` substantive theorems (`8/8` public `SUBSTANTIVE`).
- `python3 scripts/harness_lean.py --vacuity-row E-803`: `0 flagged, 0 unknown, 8 theorems`.
- Statement audit: `docs/statement_audits/E-803.md`.

## 5. Explicit Non-Claims & Next Decision

- Initial numeric `value`/`base`/old stock remain paid inputs; does NOT convert numerical stock into original `LOW-free` or prove `C1`, `Q`, `H`, `SL`, surjectivity, or `E-001`/`E-067`/`E-070`/`E-179`.
- Next decision: formalize `Recaman/FreshSourceHitSpacing.lean` (`E-804`, upgrading `E-760` + `E-761` unified source-clock capacity), followed by `Recaman/DeltaTwoCoherentCascade.lean` (`E-805`, upgrading `E-799` `√(7/3)` coherent cascade to `PROVED-LEAN` on `SeededReplay.run`).
