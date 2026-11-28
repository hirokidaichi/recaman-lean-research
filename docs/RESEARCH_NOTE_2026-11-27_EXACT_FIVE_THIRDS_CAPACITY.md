# Research note: Exact `5/3` actual-`EndN` exponential capacity via 8-slot double-ascent excursion spacing (`E-797`)

## Summary

This note records the resolution of the actual-`EndN` exponential growth bracket `[5/3, 190/107]` (`E-786` vs `E-794`) to the **exact rational base `5/3`**, proved unconditionally in Lean 4 in [`Recaman/ExactFiveThirdsCapacity.lean`](../Recaman/ExactFiveThirdsCapacity.lean) (`E-797 PROVED-LEAN`, 8 audited theorems, 0 vacuity flags, 0 warnings, standard axioms only).

Combined with `E-786` (`Recaman/ExponentialHeightCascade.lean`), the maximum `additions / free` ratio on actual `EndN` inside any height strip `[m, m + H]` is now pinned from both sides in Lean 4 to within a **uniform constant factor `9/2 = 4.5`** for every `H ≥ 2`:
- **Lower bound (`E-786 PROVED-LEAN`)**: `(2/5) · (5/3)^H ≤ max(additions / (free + O_c))`
- **Upper bound (`E-797 PROVED-LEAN`)**: `max(additions / free) ≤ (9/5) · (5/3)^H`

## Mechanism: 4-step `+8` potential jump for supplied double ascents

Let `p = floorPotential f n (r - 1)`. In `E-794`, every supplied addition `t ∈ E_{r+1}` received 3 slots `{p(t), p(t)+1, p(t)+2}` and every `u ∈ E_r` received 1 slot `{p(u)}`, yielding `3 E_{r+1} + E_r ≤ W(r) + 3 AA_{r-1}` (root `1.77397`). As `E-796` showed, the `3 AA_{r-1}` overflow term cannot be dropped at a single height (constant slack `1`).

The key new observation is that whenever `t ∈ E_{r+1}` is **also an in-window double ascent** (`f t = true ∧ f (t + 1) = true`, i.e., `t ∈ EAA_{r+1}`):
1. `Fw f (t + 1) = r + 2` ⇒ `p(t + 1) = p(t) + 2`,
2. `Fw f (t + 2) = r + 3` ⇒ `p(t + 2) = p(t) + 5`,
3. `Fw f (t + 3) ≥ r + 2` ⇒ `p(t + 3) ≥ p(t) + 7`,
4. `Fw f (t + 4) ≥ r + 1` ⇒ `p(t + 4) ≥ p(t) + 8`.

Since `Fw` stays `≥ r + 2` at `t + 1, t + 2, t + 3`, every later supplied addition `x ∈ E_{r+1} ∪ E_r` sharing the same extended excursion exit satisfies `x ≥ t + 4` and `p(x) ≥ p(t) + 8` (`spacing_aa_rp1_rp1`, `spacing_aa_rp1_r`). Injecting `3 + δ` slots (`δ ≤ 5`, sharp at `δ = 5` / 8 slots) for each `t ∈ EAA_{r+1}`, `3` slots for remaining `t ∈ E_{r+1}`, and `1` slot for `u ∈ E_r` into `descentSlots f n r K ⊕ (AA_{r-1} × {0, ..., 2 + δ})` proves unconditionally:
$$3 E_{r+1} + \delta \cdot EAA_{r+1} + E_r \le W(r) + (3 + \delta) \cdot AA_{r-1} \qquad (\forall \delta \le 5).$$

## Exact critical telescoping at `δ = 2` and `q = 3/5`

At `δ = 2` (5 slots) and critical ratio `q = 3/5`:
1. **Cross-height cancellation of `AA`**: `AA_h` enters the LHS with weight `2 · (3/5)^h` and the RHS (at `r = h + 1`) with weight `5 · (3/5)^{h+2} = (9/5) · (3/5)^h < 2 · (3/5)^h` (leaving strictly positive margin `(1/5) · (3/5)^h`!).
2. **Exact triangular identity**: for `T(H) = ∑_{h=0}^H (H - h + 1) A_{m+h}` and `W(H) = ∑_{h=0}^{H-1} (2(H - h) - 1) A_{m+h}`,
   $$5 \cdot T(H) + 3 \cdot A_{H+1} + A_H = 3 \cdot T(H + 1) + W(H)$$
   holds identically for every sequence `A`.
3. **Two-term induction (`exact_five_thirds_invariant`)**: using `E_m = E_{m+1} = 0` (`block_prefix_low_clock_not_endable`),
   $$3 \cdot 3^{H+1} T(H+1) + 3^{H+2} AA_H + 2 \cdot 3^{H+1} AA_{H+1} + 3^{H+2} F_{H+1} \le 27 \cdot 5^H \sum_{h=0}^{H+1} F_{m+h}$$
   for every `H : Nat`, immediately yielding:
   - `3^(H+1) * triAdditions(H+1) ≤ 9 * 5^H * free`,
   - `5 * 3^h * levelAdditions(m + h) ≤ 9 * 5^h * free` (`∀ h : Nat`),
   - `5 * 3^H * additions ≤ 9 * 5^H * free` on every strip `[m, m + H]`,
   - `(25 * 3^d) * lowAdditionWeights(r) ≤ (54 * 5^d) * free` (`r ≤ m + d`),
   - `(25 * 3^d) * (j + 1)^2 ≤ (54 * 5^d) * free` (`Fw(b + j) ≤ m + d + 1`, no `hpos`, no height ceiling).

## Reproducible verification & falsifier controls

Command: `python3 docs/data/depth_general_20261127/exact_five_thirds_capacity_audit.py`
- `5 * T(H) + 3 * A_{H+1} + A_H == 3 * T(H+1) + W(H)` verified for `H = 1..25`.
- Negative control (`δ = 6`): `w = A^20 (AS)^420 S^20 A^20 A (AASS)^50` (`W(20) = 400`, `E_{21} = EAA_{21} = 50`, `AA_{19} = 1`): `δ = 5` passes (`400 ≤ 408`), `δ = 6` fails (`450 > 409`, slack `-41`).
- Sharpness of `δ = 5`: `w = A^20 (AS)^120 (S^9 A^9 (SA)^16) A (AASS)^13` (`W(20) = 97`): `δ = 5` hits slack `+1` (`104 ≤ 105`), `δ = 6` fails (`117 > 106`, slack `-11`).
- Corpus test: `0` violations across `6` adversarial families (including `E-796` and `E-793`) + `10,000` random `BlockWord`-prefixed words.

## Explicit non-claims

This closes the actual-`EndN` exponential growth base to exact `5/3`, but does NOT determine the growth base under coherent finite-state greedy (`E-759 = (0, 0)`) or canonical clock-0 reachability, and does NOT prove height-independent capacity, `C1`, `Q`, `H`, `SL`, surjectivity, or protected central claims (`E-001`, `E-067`, `E-070`, `E-179`).
