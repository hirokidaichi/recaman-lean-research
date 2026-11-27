# Research Note: Double-Ascent Excursion Spacing (`E-792`) and Refutation of Free-Only Overflow `C2` (`E-793`)

**Date**: 2026-11-27  
**Parent cycle**: `R-20261127-02`  
**Lean module**: [`Recaman/ExcursionClimbSpacing.lean`](../Recaman/ExcursionClimbSpacing.lean) (`E-792 PROVED-LEAN`)  
**Audit script**: [`docs/data/depth_general_20261127/excursion_climb_spacing_audit.py`](data/depth_general_20261127/excursion_climb_spacing_audit.py)  
**Evidence rows**: `E-792` (`PROVED-LEAN`), `E-793` (`REFUTED`)

## 1. Summary

1. **`E-792` (`PROVED-LEAN`)**: By extending the downward excursion in `E-785` (`Recaman/SupplyExcursionSpacing.lean`) from height `< r` to height `≤ r` (exiting to `r + 1`), we prove that `floorPotential f n (r - 1)` remains non-increasing on the entire extended excursion and that the penultimate step before exit is forced to be an in-window double-ascent (`AA`) transition `r - 1 → r → r + 1`. Consequently, for every padded `BlockWord` prehistory, arbitrary interval `[n, n + K)`, and arbitrary height `r`:
   - `3 * E_{r+1} ≤ (descentSlots f n r K).length + 2 * doubleAscent f n K (r - 1)` (`actual_same_height_supply_aa_slots`),
   - `3 * E_{r+1} ≤ lowAdditionWeights f n r K + 2 * doubleAscent f n K (r - 1)` (`same_height_supply_aa_spacing_budget`),
   - `3 * E_{r+1} ≤ lowAdditionWeights f n r K + 2 * min(A_{r-1}, A_r)` (`same_height_supply_min_level_budget`),
   - `doubleAscent f n K (r - 1) = 0 → 3 * E_{r+1} ≤ lowAdditionWeights f n r K` (`as_plateau_no_overflow_budget`),
   - Under floor `m`: `3 * E_{m+2} ≤ F_m + 2 * AA_m` (`floor_plus_two_aa_budget`, strictly sharpening `E-653`'s `E_{m+2} ≤ F_m` by `2/3` per floor `(AS)` bounce) and `3 * E_{m+4} ≤ 6 * free + 2 * AA_{m+2}` (`actual_floor_plus_four_aa_budget`, strictly sharpening `E-785`'s `3 * E_{m+4} ≤ 8 * free`).

2. **`E-793` (`REFUTED`)**: The stronger free-only overflow conjecture `C2` (`3 * E_{r+1} ≤ W(r) + 2 * F_{r-1}`), which had `0` violations across `65,534` exhaustive words (`L ≤ 15`) and `270,000` random hill-climbing steps and would have halved the `[5/3, 1.8067]` exponential growth gap down to `1.7256`, is **refuted** by an explicit potential-mod-3 construction using supplied `AA_{r-1}` exits:
   - Minimal padded-prefix witness (`pref = "AAA"`, `len(tail) = 62`, `r = 3`): `3 * E_4 = 21 > 19 + 2 * 0 = W(3) + 2 * F_2` (`+2` violation), while `E-792` attains **exact equality** `21 = 19 + 2 * 1 = W(3) + 2 * AA_2`.
   - Unbounded empty-prefix family (`pref = ""`, `n = 0`, `tail_k = "AAA" ++ (gadget ++ "SS")^k`, `r = 3`): `F_2 = 1` stays constant while `3 * E_4 - (W(3) + 2 * F_2) = 2k - 11 → +∞` (`+1` at `k = 6`, length `387`; `+29` at `k = 20`, length `1283`), refuting `3 * E_{r+1} ≤ W(r) + C * F_{r-1}` for every constant `C`.

## 2. Mechanism of `E-792` (`Recaman/ExcursionClimbSpacing.lean`)

Recall `floor_potential_step`: for `n ≤ i`,
$$p(i + 1) = p(i) + Fw(i + 1) - r, \qquad p := \mathrm{floorPotential}\ f\ n\ (r - 1).$$
In `E-785`, excursions were terminated upon first reaching height `r`, which allowed any addition at `r - 1` (including `(AS)` bounces `r - 1 → r → r - 1`) to carry two overflow slots. However, `Fw(i + 1) = r` changes `p` by `0`, so `p` stays monotone non-increasing throughout the entire extended excursion where `Fw ≤ r`.

Given `t ∈ [n, n + K)` with `Fw(t) = r + 1` and `EndN f 0 t`, let `q = q(t) < t` be its latest downward crossing of `p(t)` (`Fw(q) < r`), and let `d'` be the first index after `q` with `Fw(d' + 1) = r + 1`. Then:
- `q < d' < t < n + K`, `Fw(d') = r`, `f(d') = true`, and `Fw(i) ≤ r` for all `i ∈ [q, d']`.
- Because `q ≤ d' - 1 ≤ d'`, `Fw(d' - 1) ≤ r`, forcing `Fw(d' - 1) = r - 1` and `f(d' - 1) = true`.
- Hence `d₁ := d' - 1` satisfies `Fw(d₁) = r - 1 ∧ f(d₁) = true ∧ f(d₁ + 1) = true ∧ d₁ + 1 < n + K`, i.e., `d₁` is counted by `doubleAscent f n K (r - 1)`.
- Taking `a₀ := lastAbove f n (r + 1) (d' - n)`, `p` is non-increasing on `[a₀, d']`, yielding `p(d') < p(t) ≤ p(a₀)`. The same 3-for-1 slot injection of `(t, 0), (t, 1), (t, 2)` into `descentSlots f n r K ⊕ (AA_{r-1} × {0, 1})` succeeds with uniqueness of `d'` via `extended_exit_unique` and spacing `p(t₁) + 3 ≤ p(t₂)` via `supply_potential_spacing_after_last_crossing`.

Finally, `t ↦ t + 1` injects `doubleAscent f n K (r - 1)` into `levelAdditions f n K r` (`doubleAscent_le_levelAdditions_right`), giving the symmetric bound `doubleAscent(r - 1) ≤ min(A_{r-1}, A_r)`.

## 3. Mechanism of `E-793` Refutation (Mod-3 Potential Arithmetic)

To force a **supplied** `AA` exit `d` at height `r - 1` (`EndN f 0 d`, `F_{r-1} = 0`) to overflow `W(r)` by `+2`, we need an extended excursion `(a₀, d']` below `r + 1` whose potential drop satisfies `p(a₀) - p(d') ≡ 1 (mod 3)` while `d` is supplied from height `r - 2`.

- A minimal supplied dip `r → r-1 → r-2 → r-3 → r-2 → r-1` (`SSSA A`) has `p`-drop `1 + 2 + 3 + 2 + 1 = 9 ≡ 0 (mod 3)`.
- Each additional `(SA)` oscillation at height `r - 2 ↔ r - 3` contributes `Δp = -(3 + 2) = -5 ≡ +1 (mod 3)` while touching **zero** additions at `r - 1` (`F_{r-1} = 0`).
- Two such oscillations before the final `SAA` give a supplied exit `d` at `r - 1` (`r = 3`, `d` at height `2`) with exact potential drop `9 + 2 * 5 = 19 ≡ 1 (mod 3)` and exact `W(3) = 3 * 5 + 1 * 3 + 1 * 1 = 19`.
- Prepending `(AS)^19` at height `r = 3` (adding `0` to `W(3)` and `0` to `F_2`) supplies all `7` additions at height `4` emitted by `AA ++ (AS)^6 ++ A` (`p = 1, 4, 7, 10, 13, 16, 19`), yielding `E_4 = 7`, `3 * E_4 = 21 = W(3) + 2`, `F_2 = 0`, `AA_2 = 1`.
- Appending `"SS"` returns to height `3` without lowering below `0`, so repeating `gadget ++ "SS"` `k` times after `"AAA"` yields an empty-prefix (`n = 0`) family with `F_2 = 1`, `E_4 = 7k`, `W(3) = 9 + 19k`, and `3 * E_4 - (W(3) + 2 * F_2) = 2k - 11 → +∞`.

## 4. Reproducible Verification Output

Command:
```bash
python3 docs/data/depth_general_20261127/excursion_climb_spacing_audit.py
```
Exact output:
- Exhaustive `L = 1..15` (`pref = ""`): `65,534` words, `463,252` height-checks, `0` violations.
- Holdout `BlockWord + A^a` random tails (`4,000` words): `51,081` height-checks, `0` violations (`5,633` strict `AA < A` gains, `4,061` `min < A_{r-1}` gains, `672` `floor + 2` gains).
- Negative control (non-`BlockWord` prefix `"AASASSAAAA"`, `r = 2`): `3 * E_3 - (W(2) + 2 * AA_1) = +3`.
- `E-793` minimal (`pref = "AAA"`, `len(tail) = 62`, `r = 3`): `E_4 = 7, W(3) = 19, F_2 = 0, AA_2 = 1`, `C2` violation `+2`, `E-792` equality `21 = 19 + 2 * 1`.
- `E-793` unbounded empty-prefix family (`pref = ""`, `r = 3`): `k = 6` (`len = 387`, `+1`), `k = 10` (`len = 643`, `+9`), `k = 20` (`len = 1283`, `+29`).
- Lean 4: `lake build Recaman Recaman.Audit` (`1051` jobs, 0 warnings), `harness_gate.py --lint-module` (`19/23` substantive, 6/6 public), `harness_lean.py --vacuity-row E-792` (`0 flagged, 0 unknown, 6 theorems`).

## 5. Open Boundary

`E-793` shows why pointwise free-only overflow fails: the counterexample pays `19` free additions at height `r` (`F_r`) to harvest `+2` overflow slots at height `r + 1` from a single supplied `AA_{r-1}` exit. Determining whether the **global** multi-height exponential growth base on actual `EndN` (currently bracketed by `[5/3, 199/110]` from `E-786` and `E-788`) lies below `1.8067` therefore requires a cross-height charging inequality that couples `F_r` with the `r + 1` overflow, not a pointwise replacement of `AA_{r-1}` by `F_{r-1}`.
