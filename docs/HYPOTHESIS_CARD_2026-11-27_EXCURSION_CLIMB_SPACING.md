# Hypothesis Card: Double-Ascent Excursion Spacing (`E-792`) and Free-Only Overflow Refutation (`E-793`)

## Card A — `H-20261127-10` (`E-792`)

- **ID**: `H-20261127-10`
- **Status**: `PROVED-LEAN` (`E-792`, `Recaman/ExcursionClimbSpacing.lean`)
- **Research question**: Can the `2 * A_{r-1}` overflow term in `E-785` (`3 * E_{r+1} ≤ W(r) + 2 * A_{r-1}`) be tightened at arbitrary height `r` and arbitrary interval `[n, n + K)` to charge overflows solely to in-window double-ascent (`AA`) exits `r - 1 → r → r + 1`, and does this simultaneously sharpen `E-653` (`E_{m+2} ≤ F_m`) and `E-785` (`3 * E_{m+4} ≤ 8 * free`)?
- **Exact quantifiers**: For all `f : Nat → Bool`, `n a K : Nat`, `r m : Int`, `{w : List Bool}` with `hw : BlockWord w` and `hpre : seg f 0 n = w ++ List.replicate a true`:
  1. `3 * E_{r+1} ≤ (descentSlots f n r K).length + 2 * doubleAscent f n K (r - 1)`
  2. `3 * E_{r+1} ≤ lowAdditionWeights f n r K + 2 * doubleAscent f n K (r - 1)`
  3. `3 * E_{r+1} ≤ lowAdditionWeights f n r K + 2 * min(A_{r-1}, A_r)`
  4. `doubleAscent f n K (r - 1) = 0 → 3 * E_{r+1} ≤ lowAdditionWeights f n r K`
  5. Under `hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i`:
     `3 * E_{m+2} ≤ F_m + 2 * doubleAscent f n K m` and `3 * E_{m+4} ≤ 6 * free f n K + 2 * doubleAscent f n K (m + 2)`.
- **Dependencies**: `Recaman.SupplyExcursionSpacing` (`E-785`), `Recaman.SupplyHeightWeightBudget`, `Recaman.FloorSupplyPotential`, `Recaman.BlockSuffixPositivity`.
- **Evidence**:
  - Falsifier/audit script `docs/data/depth_general_20261127/excursion_climb_spacing_audit.py`: `65,534` exhaustive words (`L = 1..15`, `463,252` checks, `0` violations) + `4,000` holdout `BlockWord + A^a` random tails (`51,081` checks, `0` violations) + negative control (`"AASASSAAAA"` gives `+3` violation) + exact sharpness (`21 = 19 + 2 * 1`).
  - Lean 4 build (`1051` jobs, 0 warnings), `--lint-module` (`19/23` substantive, 6/6 public substantive), `--vacuity-row E-792` (`0 flagged, 0 unknown, 6 theorems`).
- **Scope / non-claims**: Does not lower the `199/110` exponential upper bound of `E-788` by itself (since `AA_{r-1}` can equal `A_{r-1}` in cascades) and does not prove `C1`, `E-001`, `E-067`, or `E-070`.

## Card B — `H-20261127-11` (`E-793`)

- **ID**: `H-20261127-11`
- **Status**: `REFUTED` (`E-793`, `docs/RESEARCH_NOTE_2026-11-27_EXCURSION_CLIMB_SPACING.md`)
- **Research question**: Does the free-only overflow inequality `C2`: `3 * E_{r+1} ≤ W(r) + 2 * F_{r-1}` hold for all padded `BlockWord` prehistories and arbitrary heights `r` (which would reduce the actual-`EndN` exponential upper bound from `1.8067` to `1.7256`)?
- **Exact counterexamples**:
  1. Minimal padded-prefix witness (`pref = "AAA"`, `n = 3`, `tail = (AS)^19 ++ SS ++ (SA)^2 ++ SAA ++ AA ++ (AS)^6 ++ A`, `len(tail) = 62`, `r = 3`): `E_4 = 7`, `3 * E_4 = 21`, `W(3) = 19`, `F_2 = 0`, `E_2 = 1`, `AA_2 = 1`, giving `3 * E_4 - (W(3) + 2 * F_2) = +2` (while `E-792` holds with exact equality `21 = 19 + 2 * 1`).
  2. Unbounded empty-prefix family (`pref = ""`, `n = 0`, `tail_k = "AAA" ++ (gadget ++ "SS")^k`, `r = 3`): for every `k ≥ 1`, `F_2 = 1`, `E_4 = 7k`, `W(3) = 9 + 19k`, `AA_2 = 1 + k`, so `3 * E_4 - (W(3) + 2 * F_2) = 2k - 11 → +∞` (first violation `+1` at `k = 6`, length `387`), refuting `3 * E_{r+1} ≤ W(r) + C * F_{r-1}` for every constant `C`.
- **Stopping decision**: Pointwise free-only overflow `C2` (`3 * E_{r+1} ≤ W(r) + 2 * F_{r-1}`) is `REFUTED`. Any narrowing of the `[5/3, 199/110]` growth bracket must couple heights globally (e.g., accounting for the height-`r` free additions `F_r` consumed to supply the overflow) rather than dropping supplied `AA_{r-1}` exits pointwise.
