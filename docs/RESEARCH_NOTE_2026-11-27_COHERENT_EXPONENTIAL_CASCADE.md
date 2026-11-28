# Research Note: Coherent Greedy (`E-759 = (0, 0)`) Exponential Height Cascade (`E-789`)

- **Date**: 2026-11-27 (`R-20261127-02`, Track 2A)
- **Registry entry**: `E-789 PROVED-PAPER`
- **Hypothesis card**: `docs/HYPOTHESIS_CARD_2026-11-27_COHERENT_EXPONENTIAL_CASCADE.md`
- **Reproducible audit script**: `docs/data/depth_general_20261127/coherent_exponential_cascade_audit.py`

## 1. Main Theorem (`PROVED-PAPER`)

**Theorem (`E-789`).** For every integer `k ≥ 1` and every `ε > 0`, there exists an explicit
balanced sign word `B_k` confined to relative height band `[-1, 3k + 2]` (total span `H = 3k + 3`)
such that:
1. `B_k` satisfies `E-759 (I)/(II) = (0, 0)` (zero Type-I and zero Type-II subtraction collisions,
   hence realizable by coherent finite-State greedy replay passing all 8 canonical filters of `E-782`),
2. `A(B_k) / F(B_k) ≥ (1 - ε) · 3^k = Ω(3^{H / 3}) = Ω(1.44225^H)`.

In particular, imposing `E-759 = (0, 0)` and the 8 static canonical filters of `E-782` does **not**
collapse the actual-`EndN` exponential height growth of `E-786` to a polynomial bound: the
coherent-greedy exponential growth base lies in `[3^{1/3}, 1.8067]` (`[1.4422, 1.8067]`), while the
raw-sign-word base lies in `[5/3, 1.8067]` (`[1.6667, 1.8067]`).

## 2. Explicit Construction (`Δ = 3`, `h_k = 3k + 1`)

Fix `K_0 = 6 N` (`N ≥ 1`) and set `B_0 = (AS)^{K_0}` (confined to `[0, 1]`, `A(B_0) = F(B_0) = K_0`,
`E-759(B_0) = (0, 0)`). For `k = 1, 2, ...`, set `h_k = 3k + 1` (so `h_{k-1} = 3k - 2` and
`ΔΦ_{h_k - 1}(SA) = -(2 h_k - 1) = -(6k + 1) ≡ -1 (mod 3)`, coprime to `3` for EVERY `k ≥ 1`):

1. **Height-`-1` buffer length `p_k`**:
   Set `p_lo(1) = 0`, and for `k ≥ 2`,
   $$p_{\mathrm{lo}}(k) = \left\lfloor \frac{3 \cdot \mathrm{bank}_{k-1}}{2 (2 h_{k-1} - 3)} \right\rfloor + 2.$$
   Choose the unique `p_k ∈ {p_lo(k), p_lo(k) + 1, p_lo(k) + 2}` such that
   $$3 a_k := 1 + (2 h_k - 1) p_k - \Delta\Phi_{h_k - 1}(B_{k-1}) - \Delta\Phi_{h_k - 1}(A^{h_k} S^{h_k}) \equiv 0 \pmod{3}.$$
2. **Unit-shift cycle word `V_k` (`ΔΦ_{h_k - 1}(V_k) = +1`)**:
   $$V_k := (SA)^{p_k} \mathbin{+\!+} B_{k-1} \mathbin{+\!+} A^{h_k} (AS)^{a_k} S^{h_k}.$$
   By construction `ΔΦ_{h_k - 1}(V_k) = +1`, and every `A` of `(AS)^{a_k}` lies at height `h_k`
   with candidate `Φ_{h_k - 1}` values stepping by `+3` across `[c_min, c_max]`.
3. **Bank initializer `V0_k` and repetition `R_k`**:
   Let `P_bank_top = -(h_k - 1)(h_k - 2) / 2` and `dp_0 = ΔΦ_{h_k - 1}(A^{h_k} S^{h_k})`. Set
   $$\mathrm{lift}_k = \left\lceil \frac{P_{\mathrm{bank,top}} - dp_0 - c_{\min}}{3} \right\rceil + 1, \qquad
     \mathrm{bank}_k = dp_0 + 3 \cdot \mathrm{lift}_k - P_{\mathrm{bank,top}} + c_{\max},$$
   $$V_{0,k} := A^{h_k - 1} (SA)^{\mathrm{bank}_k} A (AS)^{\mathrm{lift}_k} S^{h_k}, \qquad
     B_k := V_{0,k} \mathbin{+\!+} V_k^{R_k} \quad (1 \le R_k \le \mathrm{bank}_k).$$

## 3. Complete All-Height Proof of `E-759(B_k) = (0, 0)`

We prove by induction on `k` that `E-759(B_k) = (0, 0)` (with `B_k` confined to `[-1, h_k + 1]`):

- **Top band `r ∈ {h_k - 1, h_k, h_k + 1}`**: `B_{k-1}` is confined to `[-1, h_{k-1} + 1] = [-1, h_k - 2]`,
  so `B_{k-1}` and `(SA)^{p_k}` never reach height `≥ h_k - 1`.
  - At `r = h_k + 1`: zero `S`-landings occur.
  - At `r = h_k`: `ΔΦ_{h_k}(V_k) = 1 - |V_k| < 0`, while the `Φ_{h_k}` span of `(AS)^{a_k}` is `a_k < |V_k| / 2`,
    so `V_{0,k}` and all `R_k` cycles of `V_k` occupy pairwise disjoint descending intervals of `Φ_{h_k}`.
  - At `r = h_k - 1`: `V_{0,k}`'s bank peaks cover `[P_bank_top - bank_k, P_bank_top]`; `V_{0,k}`'s own
    `S`-landing at `h_k - 1` lies at `P_bank_top - bank_k + 1 + 3·lift_k = P_bank_top + 2 > P_bank_top`;
    and in cycle `j` (`0 ≤ j < R_k`), the unique `S`-landing at `h_k - 1` lies at
    `P_bank_top + 3 + j` (since the last target candidate of cycle `0` is `P_bank_top` and the first
    `S` of `S^{h_k}` shifts `Φ_{h_k - 1}` by `+3`). Every `S`-landing at `h_k - 1` is therefore
    strictly above all prior outputs and candidates at `h_k - 1` (zero Type-I and zero Type-II
    collisions; moreover for `j ≥ 3`, the last target `P_bank_top + j` is supplied by cycle `j - 3`'s
    `S`-landing!).
- **Lower corridor `r ∈ {-1, 0, ..., h_k - 2}`**:
  Relative to the end of `V_{0,k}` (and identically relative to the end of each preceding cycle `V_k`),
  `(AS)^{lift_k}` (resp. `(AS)^{a_k}`) boosts `Φ_r` by `+(2(h_k - r) + 1) · lift_k ≥ 5 · a_k ≈ 5 |B_{k-1}|`.
  Therefore, EVERY output and candidate of `V_{0,k}` (or of any earlier cycle `V_k`) at height
  `r ∈ {-1, ..., h_k - 2}` lies `≤ -3 |B_{k-1}|` EXCEPT for the single final `S^{h_k}` landing
  (for `r ≥ 0`) at `rel_end = +r(r + 1) / 2`.
  Now check the `S`-landings of `(SA)^{p_k} ++ B_{k-1}` relative to that boundary `0`:
  1. **At `r = -1`**: `S^{h_k}` never visits `-1`; `(SA)^{p_k}` has `S`-landings stepping monotonically
     up `+1, +2, ..., +p_k > 0`, and `B_{k-1}`'s `S`-landings at `-1` start at `≥ 4 · bank_{k-1} + p_k > p_k`,
     all strictly above `-5 |B_{k-1}|`.
  2. **At `r ∈ {0, 1, ..., h_{k-1} - 3}`**: `B_{k-1}` begins with `V_{0, k-1}` whose first `S`-landing
     at `r ≤ h_{k-1} - 3` occurs only in its final `S^{h_{k-1}}`, AFTER `(SA)^{bank_{k-1}}` and
     `(AS)^{lift_{k-1}}`, giving `min_Sland_r(B_{k-1}) ≥ 4 · bank_{k-1}`. Subtracting
     `(2r + 1) · p_k < (3/2) · bank_{k-1}` leaves every `S`-landing `≥ (5/2) · bank_{k-1} ≫ r(r+1)/2`.
  3. **At `r = h_{k-1} - 2` (`V_{0,k-1}`'s `SA`-bank valley)**: `B_{k-1}` has an empty `S`-landing gap
     between `V_{0,k-1}`'s bank (`≤ bank_{k-1}`) and `V_{k-1}`'s cycles (`≥ (8/3) · bank_{k-1}` because
     `(AS)^{lift_{k-1}}` adds `5 · lift_{k-1} ≈ (5/3) · bank_{k-1}`). Because
     `(2 h_{k-1} - 3) · p_k ≈ (3/2) · bank_{k-1}` lies dead center in `(bank_{k-1}, (8/3) · bank_{k-1})`,
     `V_{0,k-1}`'s bank shifts strictly below `0` (while staying `> -2 · bank_{k-1} ≫ -3 |B_{k-1}|`),
     and ALL `V_{k-1}` `S`-landings shift strictly above `+(7/6) · bank_{k-1} ≫ r(r+1)/2`, missing
     `+r(r+1)/2` cleanly!
  4. **At `r = h_{k-1} - 1`**: `B_{k-1}`'s `S`-landings lie in `[-h^2, R_{k-1} + 3]`. Because
     `R_{k-1} ≤ bank_{k-1}` and `(2 h_{k-1} - 1) · p_k > (3/2) · bank_{k-1} > R_{k-1} + 3`,
     ALL `S`-landings of `B_{k-1}` shift strictly below `0` (and strictly above `-3 |B_{k-1}|`).
  5. **At `r = h_{k-1}`**: `B_{k-1}`'s `S`-landings are already strictly negative (`≤ -|B_{k-1}|/6`),
     and stay in `(-2 |B_{k-1}|, 0)`, strictly inside `(-6 |B_{k-1}|, +r(r+1)/2)`.
  6. **At `r = h_{k-1} + 1 = h_k - 2`**: `B_{k-1}` has ZERO `S`-landings.
  Finally, within `V_k`, `A^{h_k}(AS)^{a_k}S^{h_k}` lifts `Φ_r` by `≥ 5 a_k` before its `S^{h_k}`
  landings, so those `S^{h_k}` landings lie strictly above every earlier output/candidate in `V_k`.
  By the induction hypothesis `E-759(B_{k-1}) = (0, 0)`, every internal `S` inside `B_{k-1}` is
  also collision-free. Thus `E-759(B_k) = (0, 0)`.

## 4. Exact Exponential Ratio `A(B_k) / F(B_k) ≥ (1 - ε) · 3^k`

Setting `R_k = bank_k` for each `k ≥ 1`:
- `ΔΦ_{h_k - 1}(B_{k-1}) = -3 |B_{k-1}| + O(R_{k-1}) = -6 A(B_{k-1}) + O(bank_{k-1})`, hence
  `a_k ≥ 2 A(B_{k-1}) - O(h_k^2 + bank_{k-1})`, so `A(V_k) = A(B_{k-1}) + a_k + p_k + h_k ≥ 3 A(B_{k-1}) - O(bank_{k-1})`.
- Every `A` of `(AS)^{a_k}` in `V_k` is supplied by `V_{0,k}` (or by a prior cycle's `S`-landing at
  `h_k - 1` for `j ≥ 3`), except at most `O(1)` targets, so `F(V_k) ≤ F(B_{k-1}) + p_k + h_k + 1`.
- Since `F(V_{0,k}) ≤ (4/3) · bank_k + h_k`, `R_k = bank_k`, and `p_{k+1} ≤ bank_k / 2`, both
  `F(V_{0,k}) / (R_k · F(V_k))` and `p_{k+1} / F(B_k)` are `O(1 / F(B_{k-1})) ≤ O(1 / K_0)`.
- Choosing `K_0 = Θ(k / ε)` gives `A(B_k) / F(B_k) ≥ (1 - ε) · 3^k = Ω(3^{H / 3})`.

## 5. Verification Record

Command:
```bash
python3 docs/data/depth_general_20261127/coherent_exponential_cascade_audit.py
```
- Discovery (`K_0 = 6`): `k = 1` (`len=808, A/F=2.1838`), `k = 2` (`len=46,134, A/F=4.0625`), `k = 3` (`len=1,825,686, A/F=4.4346`) — ALL `E-759 = (0, 0)`, all separation invariants verified.
- Holdout (`K_0 = 12`): `k = 1` (`len=3,318, A/F=2.4113`), `k = 2` (`len=334,184, A/F=5.2697`), `k = 3` (`len=15,023,282, A/F=5.2650`) — ALL `E-759 = (0, 0)`, all separation invariants verified.
- Exact `E-782` 8-filter greedy replay on `B_1` (`len=578, A/F=2.0942`): `True`.
- Symbolic recurrence (`K_0 = 600, R_k = bank_k`): `A/F / 3^k = 0.99228` steady across `k = 1..6` (`A/F >= 723.37` at `k = 6, H = 21`).
