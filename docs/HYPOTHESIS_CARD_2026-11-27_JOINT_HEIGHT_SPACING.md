# Hypothesis Card: `H-20261127-12` (`E-794` — Coupled Two-Height Excursion Spacing & Joint Rational Cone `< 1.8067`)

- **ID**: `H-20261127-12`
- **Date**: 2026-11-27
- **Parent cycle**: `R-20261127-02`
- **Track**: Depth-general actual-`EndN` exponential growth bracket (`H-20261128-01` Track B acceptance test: breaking `E-785`/`E-788`'s `1.8067` 3-spacing cone barrier directly on actual `EndN`)
- **Status**: `PROVED-LEAN` (`E-794`, `Recaman/JointHeightSpacingCapacity.lean`)

## 1. Bounded Research Question

Can two adjacent supplied heights (`E_{r+1}` and `E_r`) be coupled inside the SAME potential `p = floorPotential f n (r - 1)` via a joint 3+1 slot injection into `descentSlots f n r K ⊕ (AA_{r-1} × {0, 1, 2})`, proving:
$$3 \cdot E_{r+1} + E_r \le \mathrm{lowAdditionWeights}\ f\ n\ r\ K + 3 \cdot \mathrm{doubleAscent}\ f\ n\ K\ (r - 1)$$
at arbitrary height `r` and arbitrary interval `[n, n + K)`, and does the resulting joint rational polynomial telescoping invariant break the `E-785`/`E-788` 3-spacing cone barrier (`ρ_3 ≈ 1.80669`) unconditionally in Lean 4?

## 2. Exact Quantifiers

For all `f : Nat → Bool`, `n a K : Nat`, `r m : Int`, `{w : List Bool}` with `hw : BlockWord w` and `hpre : seg f 0 n = w ++ List.replicate a true`:
1. `3 * levelSupplied f n K (r + 1) + levelSupplied f n K r ≤ (descentSlots f n r K).length + 3 * doubleAscent f n K (r - 1)`.
2. `3 * (levelSupplied f n K (r + 1) : Int) + (levelSupplied f n K r : Int) ≤ lowAdditionWeights f n r K + 3 * (doubleAscent f n K (r - 1) : Int)`.
3. For every rational `P / Q` with `P < Q`, `Q ≤ 2 * P`, `jointM P Q ≤ jointL P Q` (i.e. `1/2 ≤ P/Q < κ_joint ≈ 0.563708`, `1/κ_joint ≈ 1.773969`, where `jointL P Q = (3*Q + P)*Q*(Q - P)^2`, `jointM P Q = P^2*(4*Q^2 + 3*P^2 - 5*P*Q)`) and interval floor `hfloor : ∀ i, n ≤ i → i ≤ n + K → m ≤ Fw f i`:
   - `(jointL P Q - jointM P Q) * ratAdditions P Q f n K m H ≤ jointL P Q * ratFree P Q f n K m H`,
   - `(jointL P Q - jointM P Q) * P ^ h * levelAdditions f n K (m + h) ≤ jointL P Q * Q ^ h * free f n K`,
   - For `r ≤ m + d`: `P ^ (d + 1) * Q ^ 2 * (Q - P) * lowAdditionWeights f n r K ≤ jointM P Q * Q ^ d * free f n K` (no `1 / (L - M)` prefactor blowup).
4. Concrete unconditional specializations:
   - `P/Q = 5/9` (`base = 9/5 = 1.8000`, strictly breaking `E-788`'s `1.8067` cone barrier — which was `E-788`'s negative control!),
   - `P/Q = 9/16` (`base = 16/9 ≈ 1.7778`),
   - `P/Q = 107/190` (`base = 190/107 ≈ 1.7757`, within `0.10%` of the exact joint cone root `1.77397`).

## 3. Evidence & Falsification

- Script `docs/data/depth_general_20261127/joint_height_spacing_audit.py`:
  - Exhaustive `L = 1..15` (`65,534` words): `463,252` joint-spacing checks + `795,436` rational-cone checks, `0` violations.
  - Holdout `BlockWord + A^a` (`3,500` random tails across `1/2, 5/9, 9/16, 107/190`): `35,580` spacing + `128,320` cone checks, `0` violations.
  - Direct simulation of Lean's exact injection `phi` across `2,500` random `BlockWord + A^a` words: `0` collisions.
  - Exact zero-slack sharpness (`pref = "SAAA"`, `r = 0`): `3*E_1 + E_0 = 7 == W(0) + 3*AA_{-1} = 7`.
  - Negative controls: non-`BlockWord` prefix `"AASASSAAAA"` violates by `+2`; `P/Q = 564/1000` (`base = 1.77305`) lies outside joint cone (`M > L`).
- Lean 4: `Recaman/JointHeightSpacingCapacity.lean` (`0` warnings, `0 flagged / 0 unknown` vacuity lint, standard axioms only).

## 4. Scope & Non-Claims

Narrows the **PROVED-LEAN** actual-`EndN` exponential growth bracket from `[5/3, 199/110] = [1.6667, 1.8091]` (`E-786`/`E-788`) to **`[5/3, 190/107] = [1.6667, 1.7757]`** (breaking `E-785`'s `1.8067` cone barrier and cutting `> 23%` of the remaining exponential gap). Does not resolve the exact base inside `[5/3, 1.77397]`, height-independent capacity, `C1`, `E-001`, `E-067`, or `E-070`.
