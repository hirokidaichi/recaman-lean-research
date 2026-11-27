# Hypothesis Card — `H-20261128-01` (Exact Actual-`EndN` Exponential Base in `[5/3, 190/107]` and Coherent Greedy Exponential Cascade)

- **ID**: `H-20261128-01`
- **Date**: 2026-11-28 (drafted at end of `R-20261127-01`, **BOTH Track A & Track B resolved in `R-20261127-02`**; refined residual question remains `CONJECTURED`)
- **Track**: Depth-general actual-`EndN` height capacity & greedy S-novelty separation
- **Status**: **Track A `PROVED-PAPER` (`E-789`)**, **Track B `PROVED-LEAN` (`E-794`, plus `E-788`/`E-792`/`E-793`)**, residual exact base inside `[5/3, 1.77397]` remains **`CONJECTURED`**

## 1. Outcomes Achieved in `R-20261127-02`

1. **Track A (`E-789 PROVED-PAPER`) — RESOLVED**:
   - Explicitly constructs all-`k` `Δ = 3` (`h_k = 3k + 1`, height band `[-1, 3k + 2]`, span `H = 3k + 3`) unit-shift (`ΔΦ_{h_k - 1}(V_k) = +1`) balanced cascades `B_k = V0_k ++ V_k^{R_k}` using a height-`0 ↔ -1` `(SA)^{p_k}` buffer separating `V0_{k-1}`'s negative bank valley from `V_{k-1}`'s positive `S`-landings.
   - Proves `E-759 (I)/(II) = (0, 0)` (hence 8-filter coherent finite-State greedy realizable by `E-782`) AND `A(B_k) / F(B_k) ≥ (1 - ε) · 3^k = Ω(3^{H/3}) = Ω(1.44225^H)`. Verified up to `k = 3` (`len = 15,023,282`, `A/F = 5.2650`) plus exact 8-filter greedy replay on `B_1`.
   - **Conclusion**: Greedy `S`-novelty (`E-759 = (0, 0)`) does **NOT** force sub-exponential fixed-height capacity.

2. **Track B (`E-788`, `E-792`, `E-793`, `E-794`) — RESOLVED**:
   - `E-788 PROVED-LEAN` (`Recaman/SharpThreeSpacingCapacity.lean`): formalizes the full `E-785` 3-spacing rational cone `1/2 ≤ P/Q < κ_3 ≈ 0.55350`, lowering the Lean upper base from `2` to `199/110 ≈ 1.8091`.
   - `E-792 PROVED-LEAN` (`Recaman/ExcursionClimbSpacing.lean`): tightens `2 * A_{r-1}` overflow to `2 * doubleAscent(r - 1)` (`AA` climbs only) at every height, sharpening `E-653` and `E-785`.
   - `E-793 REFUTED`: refutes pointwise free-only overflow `C2` (`3 * E_{r+1} ≤ W(r) + 2 * F_{r-1}`, cone root `1.7256`) via an explicit mod-3 potential gadget (`3 * 7 = 21 > 19 + 0`, zero slack in `E-792`) and an unbounded empty-prefix family (`F_2 = 1`, `3 * E_4 - W(3) = 2k - 9 → +∞`).
   - **`E-794 PROVED-LEAN` (`Recaman/JointHeightSpacingCapacity.lean`)**: couples TWO adjacent heights (`3 * E_{r+1} + E_r ≤ W(r) + 3 * AA_{r-1}`) on the same `floorPotential f n (r - 1)` and proves a zero-slack rational telescoping invariant across the new joint cone `1/2 ≤ P/Q < κ_joint ≈ 0.563708` (`1 / κ_joint ≈ 1.77397`). Unconditionally proves `P/Q = 5/9` (`base = 9/5 = 1.8000`, strictly breaking `E-785`/`E-788`'s `1.8067` cone barrier!), `P/Q = 9/16` (`base = 16/9 ≈ 1.7778`), and `P/Q = 107/190` (`base = 190/107 ≈ 1.7757`), narrowing the **PROVED-LEAN** actual-`EndN` exponential growth bracket to **`[5/3, 190/107] = [1.6667, 1.7757]`**.

## 2. Next Open Residual Question (`CONJECTURED`)

1. **Closing `[5/3, 1.77397]`**: Does any actual-`EndN` family achieve exponential growth strictly above `5/3` (e.g., via multi-level `AA` overflow cascades), OR does a global cross-height inequality coupling height-`r` free oscillations `F_r` (which `E-793` had to pay in bulk) with `r + 1` overflow lower the upper bound further toward `5/3`?
2. **Beyond static seen-set filters (`E-791 STOPPED`)**: Formalize genuinely global clock-0 ledger/Eulerian-trail invariants on `Recaman.Basic.a` (such as the unconditional quadratic distinct-seen cardinality bound `2 * upperTri(b + 1 - |V|) ≤ upperTri(b) + a b`, exact mod-4 even/odd visit capacities, and disjoint multi-point cluster clock budgets).
3. **Non-claims**: Neither `C1` nor protected claims (`E-001`, `E-067`, `E-070`, `E-179`) are proved.
