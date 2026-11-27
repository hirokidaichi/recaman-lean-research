# Research Note: Two-Potential Resonance Refuting All Upper-Free Overflow Bounds and Proving Asymptotic Constant-1 Sharpness of `E-794` (`E-796`)

**Date**: 2026-11-27  
**Parent cycle**: `R-20261127-02` (30-min extension)  
**Audit script**: [`docs/data/depth_general_20261127/resonant_overflow_refutation_audit.py`](data/depth_general_20261127/resonant_overflow_refutation_audit.py)  
**Evidence row**: `E-796` (`REFUTED`)

## 1. Motivation & Result

After `E-794` (`3 * E_{r+1} + E_r ≤ W(r) + 3 * AA_{r-1}`, cone root `1.77397`) narrowed the actual-`EndN` exponential bracket to `[5/3, 190/107]`, we observed that `5/3` is the exact cone root of `3 * E_{r+1} + E_r ≤ W(r)` (with zero `AA_{r-1}` overflow), and that the `E-793` counterexample (`3 * E_4 = 21 > 19 = W(3)`) spent `F_3 ≥ 19` free additions at height `r`. Furthermore, across all `32,766` exhaustive words (`L ≤ 14`) and `25,000` hill-climbing evaluations, BOTH `3 * E_{r+1} ≤ W(r) + 2 * F_{≥ r-1}` and `3 * E_{r+1} + E_r ≤ W(r) + 3 * F_{≥ r-1}` had **0 violations**.

In `E-796`, we construct an explicit **exact two-potential resonant periodic unit** (`D = 13, L = 1`, length `166`) that simultaneously:
1. **Refutes** `3 * E_{r+1} ≤ W(r) + C * F_{≥ r-1}` and `3 * E_{r+1} + E_r ≤ W(r) + C * F_{≥ r-1}` for **EVERY constant `C`** (on both `pref = A^{16}` and empty prefix `n = 0`), with `F_{≥ r-1}` strictly **constant** (`205` resp. `206`) while the overflow grows as `+2k` resp. `+3k → +∞`.
2. **Proves asymptotic constant-1 sharpness of `E-794`**: for EVERY `k ≥ 1`, on `pref = A^{16}`, `tail_k = (AS)^{204} ++ unit^k` at `r = 16`,
   $$3 E_{17} + E_{16} = 202 k - 1, \qquad W(16) + 3 \cdot AA_{15} = 202 k,$$
   so `E-794`'s slack is identically **`1` for all `k = 1, 2, ..., ∞`** — proving that the coefficient `3` on `AA_{r-1}` in `E-794` is asymptotically exact even when `F_{≥ r-1} = O(1)`!

## 2. Complete All-`k` Proof (`PROVED-PAPER`)

Set `r = 16`, `p_1(i) := floorPotential f n 15 i` (`Δp_1 = Fw - 16`, controlling height `17`), and `p_0(i) := floorPotential f n 14 i` (`Δp_0 = Fw - 15 = Δp_1 + 1`, controlling height `16`). Define:
- `dip := S^{13} ++ A S ++ A^{11} ++ S A A ++ A` (length `30`, starting and ending at height `16`, staying in `[3, 16]`),
- `unit := dip ++ A ++ (A S)^{66} ++ A ++ S S` (length `166`, starting and ending at height `16`, staying in `[3, 18]`).

Direct arithmetic on `dip` and `unit`:
1. Inside `dip` (from `a_{0,j}` at height `16` to `d'_j` at height `16`):
   - `W(16)` of `dip` is `1 * 25 + 1 * 25 + ∑_{h=4}^{14} (31 - 2h) + 27 + 25 + 1 = 199` (verified exactly in audit script: `W(16) = 199 ≡ 1 (mod 3)`).
   - `Δp_1(dip) = -199`, and `Δp_0(dip) = Δp_1(dip) + |dip| = -199 + 30 = -169`.
   - Since the first step `S` of `dip` goes `16 → 15` (`Δp_0 = 0`), the `p_0`-drop from `a_{0,j} + 1` (height `15`) to `d'_j` (height `16`) is **`drop_0 = 169`**.
2. Inside the climbing/harvesting tail `A ++ (A S)^{66} ++ A ++ S S` (length `136`):
   - `Δp_1 = +1 + 66 * 3 + 2 + 1 + 0 = +202`, so **`Δp_1(unit) = -199 + 202 = +3`**.
   - Hence **`Δp_0(unit) = Δp_1(unit) + |unit| = 3 + 166 = +169 == drop_0`** (exact lag-1 two-potential resonance!).
3. **Exact supply verification for all copies `j = 1, 2, ..., k`** after bank `(AS)^{204}` (which visits height `16` at every `p_1 ∈ [0, 204]`):
   - **Start of copy `j`**: `Fw = 16`, `p_1(start_j) = 204 + 3(j - 1)`, `p_0(start_j) = p_0(start_1) + 169(j - 1)`.
   - **Height-`15` exit `d_{1,j} = d'_j - 1`**: preceded immediately by `S A A` from height `14` (`Ar = (-1) + 0 + 1 = 0`), hence **`EndN` holds for `d_{1,j}` on every copy `j ≥ 1`** (`F_{15} = 0`).
   - **Height-`16` exit `d'_j`**: at copy `j ≥ 2`, `p_0(d'_j) = p_0(a_{0,j} + 1) - 169 = p_0(a_{0,j-1} + 1)` with `Fw(a_{0,j-1} + 1) = 15`, so `Ar(a_{0,j-1} + 1, d'_j - (a_{0,j-1} + 1)) = 0`. Hence **`EndN` holds for `d'_j` on EVERY copy `j ≥ 2`** (`E_{16} = k - 1`, `F_{16} = 205` constant!).
   - **All `67` height-`17` additions of copy `j`**: sit at `p_1 = 204 + 3(j - 1) - 199 + 1 + 3 i = 6 + 3(j - 1) + 3 i` for `i = 0, ..., 66`. Every value `≤ 204` is supplied by `(AS)^{204}`, and every value `204 + 3 m` (`1 ≤ m ≤ j - 1`) is supplied by the trailing `S S` landing `start_{m+1}` (height `16`, `p_1 = 204 + 3 m`) of copy `m`! Hence **`E_{17} = 67 k`** and `F_{17} = 0`!
4. Summing over `k` copies on `pref = A^{16}` (`n = 16`):
   `E_{17} = 67 k`, `E_{16} = k - 1`, `W(16) = 199 k`, `AA_{15} = k`, `F_{≥ 15} = 205` (constant), giving `3 E_{17} + E_{16} = 202 k - 1`, `W(16) + 3 AA_{15} = 202 k` (constant slack `1`), and `3 E_{17} - W(16) = 2 k → +∞`. Prepending `A^{16}` inside the tail (`pref = ""`, `n = 0`) adds `W(16) += 256`, `F_{15} += 1`, `AA_{15} += 1`, keeping `F_{≥ 15} = 206` constant while `3 E_{17} + E_{16} - W(16) = 3 k - 257 → +∞`.

## 3. Reproducible Audit Output

Command: `PYTHONDONTWRITEBYTECODE=1 python3 docs/data/depth_general_20261127/resonant_overflow_refutation_audit.py`
- Padded `pref = A^{16}`: verified `k = 1, 5, 30, 100, 300, 500` (`len = 83,424`, `3*E_{17} + E_{16} - W(16) = +1499`, `F_{≥ 15} = 205`, `E-794` slack `= 1`).
- Empty `pref = ""`: verified `k = 86` (`+1`), `k = 129` (`3*E_{17} - W(16) = +2`), `k = 500` (`+1243`, `F_{≥ 15} = 206`).
- Negative control (`D = 12` off-resonance): `F_{≥ r-1}` grows linearly (`+40` from `k = 10` to `k = 50`).

## 4. Open Boundary

`E-796` shows that `E-794`'s `3 * AA_{r-1}` term cannot be dropped or replaced by any upper-free term `C * F_{≥ r-1}` pointwise. Because `dip` consumes `14` lower-height free additions (`F_{< r-1}`) per copy, the global multi-height question — whether the exponential growth base on actual `EndN` inside `[5/3, 190/107]` equals `5/3` or exceeds `5/3` — remains open.
