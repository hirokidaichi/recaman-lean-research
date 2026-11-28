# Research Note: Purely Numeric Departure `A` Stock Strip & `34/15` Floor Potential in Lean 4 (E-803)

- **Date**: 2026-11-28
- **Evidence**: `E-803 PROVED-LEAN` (`Recaman/NumericStockStripPotential.lean`)
- **Upgrades**: `E-772` (`PROVED-PAPER`, `docs/RESEARCH_NOTE_2026-11-23_STOCK_FLOOR_POTENTIAL.md` & `docs/RESEARCH_NOTE_2026-11-23_DEPARTURE_STOCK_STRIP.md`)
- **Audit script**: `docs/data/depth_general_20261128/numeric_stock_strip_audit.py`
- **Statement audit**: `docs/statement_audits/E-803.md`

## 1. Overview (Independent Purely Numeric Stock-Strip Mechanism)

`Recaman/NumericStockStripPotential.lean` formalizes a second genuinely distinct arbitrary-depth purely numeric mechanism directly on coherent finite-state greedy continuations `SeededReplay.run b s` and on `Recaman.Basic.a`: instead of sign-word height spacing (`E-797`/`E-800`) or candidate-band rank (`E-802`), it tracks **distinct numerical stock below the current value** `K_t = |V_t ∩ [1, X(t) - 1]|` across successive last floor visits, combining fresh floor-return values with a **departure-`A` output upcrossing strip** to reduce the arbitrary-depth floor-potential multiplier from `3` (`E-764`) down to **`34/15 ≈ 2.2667`**.

## 2. Formalized Proof Architecture (`8` Public Theorems, `0` Warnings, `0` Vacuity Flags)

1. **Duplicate-proof distinct stock counting (`seenCountIn`, `missingCountIn`, `stockBelow`)**:
   Defined by filtering `List.range (hi + 1 - lo)` on `lo + d ∈ (run b s t).seen`, automatically counting *distinct* integers in `[lo, hi]` regardless of duplicates in `s.seen` (matching `E-772`'s duplicate-list negative control).
2. **`primitive_excursion_area_lower_bound`**:
   Proves walk parity `fw_parity` and bounds the post-step relative area of any primitive nonnegative balanced walk of length `2 * l` below by `3 * l - 2` (odd post-step heights `≥ 1`, interior even post-step heights `≥ 2`, terminal `0`).
3. **Unified inductive excursion chain (`floor_visit_chain_induction`)**:
   In a single structural induction on `v - c`, extracts the primitive return count `m` and a `Nodup` list `R` of `m` fresh return values strictly below `x` and disjoint from `seen(c)`, proves `3 * (v - c) ≤ 2 * (x - z) + 4 * m`, AND proves that consecutive departure `A` outputs satisfy `Z_{i + 1} - Z_i = 2*l_i - A_i ≤ 1`, which inductively fills **every integer `w ∈ [X(c + 1), X(v + 1) - 1]`** inside `(run b s (v + 1)).seen`.
4. **`floor_cut_stock_discount` & `departure_strip_stock_transport`**:
   - Derives `3*t + 6*z + 4*N ≤ 6*x`, `P' + 4*K + 1 ≤ 3*P`, and `3*t + 2*z + 4*K + 4 ≤ 6*x`.
   - Proves the missing count in `[1, x]` at `v + 1` is `≤ M := x - 1 - m - K`, yielding the clipped bound `L - M ≤ seenCountIn b s (v + 1) 1 L` for `L = min x (y - 1)`. When `y > Z_0 = x + (b + c) + 1`, `[1, x]` and `[Z_0, y - 1]` are disjoint subsets of `[1, y - 1]`, giving `(min x (y - 1) - M) + (y - Z_0) ≤ stockBelow b s (v + 1)` uniformly across both clipped (`y ≤ x`) and positive-strip (`y > Z_0`) regimes.
5. **`floor_potential_W_recurrence`, `floor_potential_T_recurrence`, & `floor_potential_T_sharp`**:
   - Proves `15 * floorW b s (v + 1) ≤ 34 * floorW b s c - 30` and `13 * floorT b s (v + 1) ≤ 33 * floorT b s c - 166`.
   - Proves exact sharpness `13 * floorT a sharpTState 1 = 33 * floorT a sharpTState 0 - 166` at `sharpTState = {value := 1, seen := [0, 1]}` for EVERY base `a : Nat`.
6. **`iterated_floorW_envelope_beats_three_pow` & `canonical_orbit_floor_potentials`**:
   - Iterates `floor_potential_W_recurrence` across any `j`-step chain of coherent floor cuts to get `19 * 15^j * W_j ≤ 34^j * (19 * W_0 - 30) + 30 * 15^j`.
   - Proves `6 * 34^j < 45^j` for all `j ≥ 7`, showing that the `(34/15)^j` floor-`W` horizon strictly beats `3^j * (P_0 - 1/2) + 1/2` for EVERY `j ≥ 7` and EVERY initial `P_0 ≥ 2`.
   - Specializes all cut bounds directly to `Recaman.Basic.a`.

## 3. Verification & Audit

- `lake build Recaman Recaman.Audit`: exit `0`, `0` warnings in `NumericStockStripPotential.lean`, standard axioms only.
- `python3 scripts/harness_gate.py --lint-module Recaman/NumericStockStripPotential.lean`: `24/26` substantive theorems (`8/8` public `SUBSTANTIVE`).
- `python3 scripts/harness_lean.py --vacuity-row E-803`: `0 flagged, 0 unknown, 8 theorems`.
- `python3 docs/data/depth_general_20261128/numeric_stock_strip_audit.py`: `ALL E-803 AUDITS PASSED` (including genuine clipped-cut `AAASSSA` control and exact `Fraction` verification of `N_j < B_j` for `j = 7..30, P_0 = 2..100`).
