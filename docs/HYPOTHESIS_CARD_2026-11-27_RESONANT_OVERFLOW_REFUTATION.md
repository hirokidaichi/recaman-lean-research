# Hypothesis Card: `H-20261127-14` (`E-796` — Refutation of Upper-Free-Only Overflow `F_{≥ r-1}` and Asymptotic Constant-1 Sharpness of `E-794`)

- **ID**: `H-20261127-14`
- **Date**: 2026-11-27
- **Parent cycle**: `R-20261127-02` (30-min extension)
- **Track**: Depth-general actual-`EndN` `[5/3, 1.77397]` boundary (testing whether replacing `AA_{r-1}` in `E-794` by `C * F_{≥ r-1}` — which survived all exhaustive `L ≤ 14` and 25,000 hill-climbing trials — collapses the actual-`EndN` upper bound to `5/3`)
- **Status**: `REFUTED` (`E-796`, `docs/RESEARCH_NOTE_2026-11-27_RESONANT_OVERFLOW_REFUTATION.md`)

## 1. Refuted Conjectures

Both pointwise upper-free-only overflow conjectures on actual `EndN` (for ANY constant `C`):
- `(A)`: `3 * E_{r+1} ≤ lowAdditionWeights f n r K + C * ∑_{h ≥ r - 1} F_h`,
- `(B)`: `3 * E_{r+1} + E_r ≤ lowAdditionWeights f n r K + C * ∑_{h ≥ r - 1} F_h`,
are **REFUTED** for every constant `C`, both on padded `BlockWord ++ A^16` prefixes and on empty prefix `n = 0`.

## 2. Exact Two-Potential Resonance Construction (`D = 13, L = 1`)

Define the 30-letter dip and 166-letter resonant period unit at height `r = 16`:
- `dip = S^{13} ++ A S ++ A^{11} ++ S A A ++ A` (`len = 30`, `W(16) = 199`, `Δp_{15}(dip) = -199`, `drop_{14}(dip) = 169`),
- `unit = dip ++ A ++ (A S)^{66} ++ A ++ S S` (`len = 166`, `Δp_{15}(unit) = +3`, `Δp_{14}(unit) = +169 = drop_{14}(dip)`).

Because `drop_{14}(dip) == Δp_{14}(unit) == 169` (exact `m_lag = 1` two-potential resonance):
1. On `pref = A^{16}`, `tail_k = (AS)^{204} ++ unit^k` (`r = 16`, every `k ≥ 1`):
   - `E_{17} = 67 k`, `E_{16} = k - 1`, `W(16) = 199 k`, `AA_{15} = k`,
   - **`∑_{h ≥ 15} F_h = 205` (strictly constant for all `k ≥ 1`, with `F_{15} = 0` and `F_{16} = 205`)**,
   - `3 * E_{17} - W(16) = +2 k → +∞` and `3 * E_{17} + E_{16} - W(16) = +3 k - 1 → +∞`,
   - **Asymptotic constant-1 sharpness of `E-794`**: `(W(16) + 3 * AA_{15}) - (3 * E_{17} + E_{16}) == 1` for EVERY `k ≥ 1`!
2. On empty prefix `pref = ""`, `tail_k = A^{16} ++ (AS)^{204} ++ unit^k` (`n = 0`, `r = 16`):
   - **`∑_{h ≥ 15} F_h = 206` (strictly constant for all `k ≥ 1`)**,
   - `3 * E_{17} + E_{16} - W(16) = 3 k - 257 → +∞` (`+1` at `k = 86`, `+1243` at `k = 500`),
   - `3 * E_{17} - W(16) = 2 k - 256 → +∞` (`+2` at `k = 129`, `+744` at `k = 500`).
3. Negative control (`D = 12` off-resonance): `∑_{h ≥ r-1} F_h` grows linearly (`+1/copy`), confirming exact resonance `169 == 169` is essential.

## 3. Stopping Decision & Non-Claims

Pointwise replacement of `3 * AA_{r-1}` by ANY upper-free term `C * F_{≥ r-1}` is **`REFUTED` / `STOPPED`**. Note that `unit` spends linear lower-height free additions `F_{< r-1}` inside `dip` (specifically at depths `3..15`), so `E-796` does not refute a global bound coupling `F_{< r-1}` (or `5/3` as the global exponential base), and is not a counterexample to `C1`, `E-001`, `E-067`, or `E-070`.
