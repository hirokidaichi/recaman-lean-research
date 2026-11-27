# Hypothesis card: Exact `5/3` actual-`EndN` exponential capacity via 8-slot double-ascent spacing (`E-797`)

- **ID**: `H-20261127-E797`
- **Status**: `PROVED-LEAN` (`E-797`, `Recaman/ExactFiveThirdsCapacity.lean`)
- **Date**: 2026-11-27
- **Scope**: Arbitrary-depth, arbitrary-height, arbitrary-interval actual `EndN` with any padded `BlockWord` prehistory `seg f 0 n = w ++ List.replicate a true` and floor `∀ i ∈ [n, n + K], m ≤ Fw f i`.

## Bounded research question

Given that `E-796` proved the `3 * AA_{r-1}` overflow in `E-794` (`3 * E_{r+1} + E_r ≤ W(r) + 3 * AA_{r-1}`) cannot be dropped at a single height, can charging the `AA_{r+1}` double ascents at height `r + 1` via their 4-step `+8` potential jump on `p = floorPotential f n (r - 1)` cancel the `AA` overflow across heights and close the `[5/3, 190/107]` actual-`EndN` exponential growth bracket to the **exact** rational base `5/3`?

## Exact statements

1. **Parameterized `(3 + δ)`-slot double-ascent excursion budget (`δ ≤ 5`, sharp at `δ = 5`)**:
   For every `f : Nat → Bool`, `n a K δ : Nat` (`δ ≤ 5`), `r : Int`, `hw : BlockWord w`, `hpre : seg f 0 n = w ++ List.replicate a true`:
   - `3 * E_{r+1} + δ * EAA_{r+1} + E_r ≤ (descentSlots f n r K).length + (3 + δ) * AA_{r-1}`,
   - `3 * E_{r+1} + δ * EAA_{r+1} + E_r ≤ lowAdditionWeights f n r K + (3 + δ) * AA_{r-1}`.
2. **Exact `5/3` triangular, single-level, total-strip, low-weights, and free-gap capacities**:
   Under `hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i`:
   - `3 ^ (H + 1) * triAdditions f n K m (H + 1) ≤ 9 * 5 ^ H * free f n K` (`∀ H : Nat`),
   - `5 * 3 ^ h * levelAdditions f n K (m + h) ≤ 9 * 5 ^ h * free f n K` (`∀ h : Nat`),
   - `5 * 3 ^ H * additions f n K ≤ 9 * 5 ^ H * free f n K` whenever `∀ i ∈ [n, n + K), Fw f i ≤ m + H`,
   - `(25 * 3 ^ d : Int) * lowAdditionWeights f n r K ≤ (54 * 5 ^ d : Int) * free f n K` (`r ≤ m + d`),
   - `(25 * 3 ^ d : Int) * (j + 1)^2 ≤ (54 * 5 ^ d : Int) * free f n (b - n)` (`Fw f (b + j) ≤ m + d + 1`, no `hpos`, no height ceiling).

## Falsifier & negative controls

- **Negative control (`δ = 6`)**: `w = A^20 (AS)^420 S^20 A^20 A (AASS)^50` (`n = 20, r = 20`) has `W(20) = 400`, `E_{21} = EAA_{21} = 50`, `AA_{19} = 1`; `δ = 5` passes (`400 ≤ 408`), while `δ = 6` **fails by `-41`** (`450 > 409`).
- **Sharpness of `δ = 5`**: `w = A^20 (AS)^120 (S^9 A^9 (SA)^16) A (AASS)^13` (`W(20) = 97`) hits slack `+1` at `δ = 5` (`104 ≤ 105`) and fails at `δ = 6` (`117 > 106`).
- **Corpus audit**: `docs/data/depth_general_20261127/exact_five_thirds_capacity_audit.py` — `0` violations across `6` adversarial families + `10,000` random padded-`BlockWord` words.

## Non-claims & stopping conditions

- Does NOT determine the exact exponential base under coherent finite-state greedy chronology (`E-759 = (0, 0)`, currently `[3^{1/3}, 5/3]`) or under canonical clock-0 reachability.
- Does NOT prove height-independent capacity, `C1`, `Q`, `H`, `SL`, surjectivity, or protected claims (`E-001`, `E-067`, `E-070`, `E-179`).
