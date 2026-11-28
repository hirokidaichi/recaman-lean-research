# Hypothesis Card: H-20261127-05 — Arbitrary-Depth Low-Weight & Free-Gap Profile

- **ID**: `H-20261127-05`
- **Parent Cycle**: `R-20261127-02` (Track 1: arbitrary-depth free-gap consequence of `E-785`)
- **Status**: `PROVED-LEAN` (`E-787`, `Recaman/ArbitraryDepthFreeGap.lean`)
- **Depth-general classification**: `depth_general_progress` (holds for ALL `d, D : Nat` with no upper walk ceiling; removes the fixed-depth `D ≤ 6` ceiling of `E-663`/`E-666`, though the finite residual band `4 ≤ free ≤ j ≤ 2^(D-2) - 3` remains open for `D ≥ 6`).

## Bounded Research Question

Does the arbitrary-height 3-spacing excursion invariant (`E-785`, `Recaman/SupplyExcursionSpacing.lean`) combine with the supplied gap-square inequality (`E-662`, `Recaman/GapSquareLowAdditions.lean`) to yield unconditional arbitrary-depth low-addition weight bounds (`W(m+d) ≤ 2^d · free`) and an unconditional arbitrary-depth positive-deficit counterexample profile (`4 ≤ free ≤ j ≤ 2^(D-2) - 3`) for every `D ≥ 2`, plus a sharp `3 · W(m+5) ≤ 59 · free` (`j ≤ 17`) profile at `D = 7`?

## Exact Quantifiers & Formal Claims

For every sign function `f : Nat → Bool`, block prefix `seg f 0 n = w ++ List.replicate a true` (`BlockWord w`), floor `m : Int` (`∀ i ∈ [n, n+K], m ≤ Fw f i`), and arbitrary height offset `d : Nat` / depth `D ≥ 2`:

1. `low_weights_le_two_dyadic_free`: `lowAdditionWeights f n (m + d + 1) K ≤ 2 * dyadicFree f n K m d`.
2. `low_weights_le_pow_two_free`: `r ≤ m + d → lowAdditionWeights f n r K ≤ 2^d * free f n K`.
3. `low_weights_five_three_spacing`: `r ≤ m + 5 → 3 * lowAdditionWeights f n r K ≤ 59 * free f n K`.
4. `arbitrary_target_height_free_gap_square` (no `hpos`, no ceiling): `Fw f (b + j) ≤ m + d + 1 → (j + 1)^2 ≤ 2^d * free f n (b - n)`.
5. `arbitrary_target_height_free_gap` (no `hpos`, no ceiling): `Fw f (b + j) ≤ m + d + 1 ∧ 2^d ≤ j + 2 → j + 1 ≤ free f n (b - n)`.
6. `positive_arbitrary_depth_free_gap_profile`: `2 ≤ D ∧ hfloor(Fw f n - D) ∧ hpos ∧ free ≤ j → 4 ≤ free ∧ j + 3 ≤ 2^(D - 2) ∧ Fw f (b + j) ≤ Fw f n - 1 ∧ (j + 1)^2 ≤ 2^(D - 2) * free`.
7. `positive_depth_seven_counter_profile`: `D = 7 ∧ hpos ∧ free ≤ j → 4 ≤ free ∧ j ≤ 17 ∧ Fw f (b + j) ≤ Fw f n - 1 ∧ 3 * (j + 1)^2 ≤ 59 * free`.

## Falsifier & Evidence

- Script: `docs/data/depth_general_20261127/arbitrary_depth_free_gap_audit.py`
- Discovery: exhaustive length `1..13` (`16,382` binary words, `n = 0`): `0` violations across all 7 theorems.
- Holdout: `4,000` random `BlockWord ++ A^a ++ tail` instances (`seed = 2026112702`, `len ≤ 80`) + adversarial `E-786` cascade words (`H = 2, 3, 4`): `161,407` weight checks, `1,792` supplied-gap checks, `746` `hpos` hits, `0` violations; max observed `W(m+5)/free = 10.5000 ≤ 59/3 = 19.6667`.
- Negative control: non-`BlockWord` prefix `"SAA"` + tail `"A"` gives `m = 1, free = 0, W(2) = 1 > 2^1 · 0 = 0`, confirming `BlockWord` is load-bearing.
- Lean 4 verification: `Recaman/ArbitraryDepthFreeGap.lean`, `lake build Recaman Recaman.Audit` (0 errors, 0 warnings), `--lint-module` (`16/20` substantive, all `7/7` public theorems `concrete/work/SUBSTANTIVE`), `--vacuity-row E-787` (`0 flagged, 0 unknown, 7 theorems`), standard axioms only.

## Boundaries & Non-Claims

- Does NOT close the residual finite gap band `4 ≤ free ≤ j ≤ 2^(D - 2) - 3` (or `j ≤ 17` at `D = 7`).
- Does NOT prove height-independent `j + 1 ≤ free` or `C1` / `E-001` / `E-067` / `E-070`.
- By `E-786`, an exponential growth factor `≥ (5/3)^d` in `lowAdditionWeights / free` is unavoidable on raw sign words, so further tightening of the base (`2 -> 11/6` or `20/11`, Track 2B) improves constants/base but cannot make the band `D`-independent via low-addition weights alone.
