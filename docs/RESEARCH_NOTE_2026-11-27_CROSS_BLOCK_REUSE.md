# Unbounded cross-block reuse of a lower-stage source bank

This note records two arbitrary-depth refutation theorems from Track 1 (`H-20261127-01`, executing `H-20261126-01`):

1. **`E-783` (`PROVED-LEAN`, `Recaman/CrossBlockReuseUnbounded.lean`)**: Refutes `H-20261126-01` (`2 A_after_cut ≤ 3(F + O_c) - 3`) at `R = 2, H = 3` and proves that **no linear cross-block capacity `A_after_cut ≤ C(F + O_c) + K` holds for any constants `C, K`**, simultaneously for **every** finite original prehistory `U` (keeping origin at `0` and retaining all old co-suppliers).
2. **`E-784` (`PROVED-PAPER`, human review pending, not yet Lean-checked)**: Proves that even under **full actual greedy S-freshness (`E-759` I & II = 0)** — and hence by `E-782` executable from a coherent finite `State` whose exact distinct seen set satisfies all 8 canonical scalar+spatial filters — **no linear cross-block capacity `A_after_cut ≤ C(F + O_c) + K` holds** (`A / (F + O_c) = 2k - O(1) → ∞` for all `k ≥ 3`).

**Scope boundary**: Neither `E-783` nor `E-784` refutes C1 or constructs a canonical orbit from `a 0 = 0`. In both families the extra depth below the initial head `m` is `D_depth = 0`, and original free additions `F` grow far faster than `m`. What is refuted is extending `E-776`'s single-block linear `A/(F + O_c)` capacity across multiple balanced staged blocks (`R ≥ 2`).

## 1. Exact post-cut partition and the `R = 2` counterexamples

For any sign sequence `f : Nat → Bool`, cut `c`, and post-cut length `L`, define:
- `InternalSupplied f c q`: `f q = true ∧ ∃ u k, c ≤ u ∧ u + k = q ∧ Win f u k`;
- `ExclusiveOldSupplied f c q`: `EndN f 0 q ∧ ¬ InternalSupplied f c q` (counting `O_c`);
- `free f c L`: `cN (fun q => f q = true ∧ ¬ EndN f 0 q) c L` (counting `F`).

Because `c ≤ u` implies `0 ≤ u`, every internally supplied addition is automatically `EndN f 0 q`, and targets possessing both an old supplier (`u < c`) and an internal supplier (`u ≥ c`) stay in `internalSuppliedCount` rather than `exclusiveOldCount`. Thus `additions_partition_after_cut` (`PROVED-LEAN`) gives the exact identity
$$A_{\text{after cut}} = L_{\text{int}} + (F + O_c),$$
so `2 A ≤ 3(F + O_c) - 3` is equivalent to `3 L_int + 3 ≤ A`.

### Minimal 2-block refutations

1. **Lean-certified 2-block counter (`h20261126_two_block_counter`, `E-783`)**:
   `V_1 = stagedBlock [1, 2, 1, 1]`, `V_2 = stagedBlock [1, 1, 1, 2]` (`H_1 = H_2 = 3`, `m = 5`, 27 letters `S^5 AASAAASSSS AAAASASSSS AA` after any `U` of length `n`).
   Post-cut additions: `A = 12`. Four explicit internal supplies (`c+2 → c+5` via `SAA`; `c+9 → c+12` via cross-boundary `SAA`; **`c+2 → c+13` via length-11 window reusing bank peak `c+2` across blocks**; `c+8 → c+15` via length-7 window from descent clock `c+8`) force `L_int ≥ 4`, hence `F + O_c ≤ 8` and
   $$3(F + O_c) - 3 \le 21 < 24 = 2 A$$
   for **every** arbitrary old prehistory `U`. Note that this 27-letter word has one E-759 (I) collision (`fI = 1, fII = 0`).
2. **Coherent greedy-realizable 2-block counter (`E-784`)**:
   `V_1 = stagedBlock [2, 1, 1]`, `V_2 = stagedBlock [1, 1, 1, 2]` (25 letters `S^5 ASAASSS AAAASASSSS AA`, empty `U`) has `A = 11`, `L_int = 3`, `F = 8`, `O_c = 0`, `2A = 22 > 21 = 3(F + O_c) - 3`, AND passes **E-759 `(0, 0)`** plus literal exact greedy replay through the `E-782` 8-filter spatial bridge grid.

## 2. Raw-sign unbounded ratio family (`E-783`, `PROVED-LEAN`)

For any `k ≥ 1`, define:
$$H = 3k,\qquad a = k(3k - 2),\qquad \text{bank} = 3a + 2,\qquad \text{lift} = a + 1.$$
Note the exact identity `3 a = H(H - 2)`. Form the staged blocks:
- `V_0 = stagedBlock ([1]^(H-2) ++ [bank, 1, lift])` (length `2H + 2·bank + 2·lift - 2`, additions `4a + H + 2`),
- `V = stagedBlock ([1]^H ++ [a])` (length `2H + 2a`, additions `H + a`),
- `familyWord k R = S^(H+2) ++ V_0 ++ V^R ++ AA`.

Relative to cut height `0`, the area of `V` satisfies
$$\mathrm{Fw}(V) = 0,\qquad \mathrm{Ar}(V) = |V| \cdot (H - 1).$$
Indeed, `2 Ar(V) - 2 |V|(H - 1) = (-H^2 + 3H) + (6a - 6) + 4 + (-H^2 + H + 2) = 2(3a - H(H - 2)) = 0`.
Therefore the window invariant `Φ_{H-1}(t) = B(t) - t(H - 1)` is **strictly invariant across every copy of `V`**.

Inside `V_0`, stage `H - 2` has `bank = 3a + 2` peaks at relative height `H - 1`, at clocks `u(i) = c + (H - 2) + 2i + 1` (`0 ≤ i < bank`). Setting `d = bank - 1 - i`, direct summation of the 5 segments `(SA)^d`, `[A]`, `(AS)^(lift-1)`, `[A]`, `S^(H+1)` plus the ascent `A^H (AS)^j` of copy `r` of `V` yields
$$2\,\mathrm{Ar}\big(u(i) \to q_{r,j}\big) = (-2d + H^2 - 3H + 8) + (-H^2 + 3H) + 6j = -2d + 8 + 6j,$$
which vanishes identically at `d = 4 + 3j`, i.e., `i_j = 3(a - 1 - j) ∈ [0, bank - 5]`. Hence every one of the `R · a` stage-`H` additions `q_{r,j}` (`0 ≤ r < R, 0 ≤ j < a`) satisfies `InternalSupplied f c q_{r,j}` (`bank_to_copy_zero_win`), giving (`cross_block_reuse_counts`):
$$A = (4a + H + 4) + R(H + a),\qquad L_{\text{int}} \ge R a,\qquad F + O_c \le (4a + H + 4) + R H.$$
Given any `C, K : Nat`, choosing `k = C + 1` makes `(H + a) - C H = 4(C + 1) ≥ 4`, and `R = C(4a + H + 4) + K + 1` yields `C(F + O_c) + K < A` (`no_linear_cross_block_capacity`), uniformly for every `f : Nat → Bool` and every prehistory length `n`.

*Remark*: Because `ΔΦ_{H-1}(V) = 0`, `V` has integer mean `H - 1`, so `V ++ V` violates E-759 (I) (`V` is not greedily repeatable). The next section removes this obstruction completely.

## 3. Coherent-greedy-realizable unbounded ratio family (`E-784`, `PROVED-PAPER`)

For every integer `k ≥ 3`, define:
$$u = 6k + 2,\quad h = 2u = 12k + 4,\quad K = 3u = 18k + 6,\quad m = K + 2 = 18k + 8,$$
$$a = 36k^2 + 8k - 1,\quad R = (3k + 1)^2 = 9k^2 + 6k + 1,\quad \text{lift} = 9k + 4,\quad \text{bank} = 117k^2 + 105k + 29.$$
Define the staged blocks:
- `V_0 = stagedBlock ([1]^(h-2) ++ [bank] ++ [1]^(u+1) ++ [lift])`, length `L_0 = 2(K + bank + lift - 1) = 234k^2 + 264k + 76`;
- `V = stagedBlock ([1]^h ++ [a] ++ [1]^u)`, length `L_V = 2(K + a) = 72k^2 + 52k + 10`;
- `W_k = S^m ++ V_0 ++ V^R ++ AA` (empty old prehistory `U = ε`).

Write relative height `y = H_0(t) + m ∈ [0, K + 1]` (so `y = m` at `t = 0` and `y = 0` at cut `c = m`) and `Ψ_y(t) := (B_{\text{rel}}(t) - t y) - (B_{\text{rel}}(m) - m y)` (differing from the origin-0 invariant `B_0(t) - t(y - m)` only by a `t`-independent constant).

### 3.1 Unit `Φ_{h-1}` shift and unbounded cross-block ratio

For `V = [1]^h ++ [a] ++ [1]^u`:
$$\mathrm{Area}_0(V) = (K + 1)^2 + (a - 1)(2h + 1) = (3u + 1)^2 + (a - 1)(4u + 1).$$
At source height `y = h - 1 = 2u - 1`:
$$\Delta \Psi_{h-1}(V) = \mathrm{Area}_0(V) - L_V(h - 1) = 3a - 3u^2 + 8u = 3(36k^2 + 8k - 1) - 3(36k^2 + 24k + 4) + (48k + 16) = \mathbf{+1}.$$
Consequently, for **every** relative height `y ∈ [0, K + 1]`:
$$\Delta \Psi_y(V) = 1 + L_V (h - 1 - y). \tag{1}$$
In `V_0`, stage `h - 2` has `bank` peaks at height `h - 1` whose `Ψ_{h-1}` values form the unbroken integer interval `[P_{\min}, P_{\max}]` with
$$P_{\max} = -72k^2 - 30k - 3,\qquad P_{\min} = P_{\max} - (\text{bank} - 1) = -189k^2 - 135k - 31.$$
In copy `r` (`1 ≤ r ≤ R`) of `V`, the `a` additions of stage `h` (`0 ≤ j < a`) lie at height `h` and require source height `h - 1` with invariant
$$\Psi_{h-1}(q_{r,j}) = t_0 + (r - 1) + 3j,\qquad t_0 = -189k^2 - 60k - 2 = P_{\min} + (75k + 29).$$
Since `t_0 > P_{\min}` and the maximum target value is
$$t_0 + (R - 1) + 3(a - 1) = (-189k^2 - 60k - 2) + (9k^2 + 6k) + (108k^2 + 24k - 6) = -72k^2 - 30k - 8 = P_{\max} - 5 < P_{\max},$$
**every** one of the `R · a` targets `q_{r,j}` matches a peak in `V_0`'s stage-`(h - 2)` bank! (Each bank peak is reused up to `~3k^2` times across copies; repeating blocked `A` candidates is legal in Recamán.)
Therefore `L_{\text{int}} ≥ R · a`, while post-cut additions are `A = (K + bank + lift - 1) + R(K + a) + 2`, so
$$F + O_c = A - L_{\text{int}} \le (K + \text{bank} + \text{lift} + 1) + R K = (117k^2 + 132k + 40) + (9k^2 + 6k + 1)(18k + 6) = 162k^3 + 279k^2 + 186k + 46,$$
whereas `A ≥ R · a = (9k^2 + 6k + 1)(36k^2 + 8k - 1) = 324k^4 + 288k^3 + 75k^2 + 2k - 1`. Hence
$$\frac{A_{\text{after cut}}}{F + O_c} \ge 2k - O(1) \longrightarrow +\infty.$$

### 3.2 Complete all-`k ≥ 3` proof of E-759 (I) & (II) = 0 across all six height regimes

We must show that for every `S` landing `v` in `W_k` (at relative height `y = H_{\text{rel}}(v)`), `Ψ_y(v)` never equals `Ψ_y(u)` for any earlier clock `u < v` with height `y` (condition I) nor `Ψ_y(q)` for any earlier `A`-clock `q < v` with height `y + 1` (condition II). Trailing `AA` has no `S` landings and creates no collisions. In `S^m`, each height `y ∈ [0, m - 1]` is landed on once at clock `t_{\text{head}}(y) = m - y` with `Ψ_y(t_{\text{head}}(y)) = y(y + 1)/2`, and no earlier clock has height `y` (or `A`-candidate height `y`).

Direct summation over `V_0` yields the exact closed form
$$\mathrm{Area}_0(V_0) - L_0(h - 2) = 117k^2 + 234k + 76 > 0, \qquad \mathrm{Area}_0(V_0) - L_0(h - 1) = -117k^2 - 30k. \tag{2}$$

We verify all six height regimes for every `k ≥ 3`:

- **Regime 1 (`0 ≤ y ≤ h - 3`)**:
  The `S` landings after the head are the unique descent clocks of `V_0` and `V_1, ..., V_R` at height `y`. Since `f(y) = \mathrm{Area}_0(V_0) - L_0 y - y(y + 1)/2` is strictly decreasing in `y ≥ 0` and at `y = h - 3 = 12k + 1`:
  $$f(h - 3) = \big(\mathrm{Area}_0(V_0) - L_0(h - 2)\big) + L_0 - \frac{(12k + 1)(12k + 2)}{2} = 279k^2 + 480k + 151 > 0,$$
  we have `Ψ_y(m + L_0) > y(y + 1)/2` for all `0 ≤ y ≤ h - 3` (and `> 1` at `y = 0`). At `V_0`'s descent `S` (`Ψ_y = Ψ_y(m + L_0) + y(y + 1)/2`), this strictly exceeds `Head S = y(y+1)/2`, `V_0`'s ascent output (`-y(y-1)/2`), and `V_0`'s ascent `A`-candidate (`-y(y-1)/2 + 1`). By (1), `ΔΨ_y(V) = 1 + L_V(h - 1 - y) ≥ 2 L_V + 1 > 0`, so every subsequent `V_r` descent `S` strictly exceeds all prior outputs/candidates at height `y` (inside `V_r`, the ascent output/candidate satisfy `Ψ_y ≤ Ψ_y(s_r) - y(y-1)/2 + 1 < Ψ_y(s_r) + ΔΨ_y(V) + y(y+1)/2 = Ψ_y(V_r\text{ desc }S)`).

- **Regime 2 (`y = h - 2`)**:
  The `S` landings after the head are `V_0`'s `bank - 1` bank valleys (stepping by `+1` from `-(h - 2)(h - 3)/2 + 1` up to `-(h - 2)(h - 3)/2 + bank - 1`), `V_0`'s descent `S`, and `V_r`'s descent `S` (`1 ≤ r ≤ R`). The bank valleys are strictly increasing (hence pairwise distinct and strictly above `V_0`'s initial stage-`h-2` arrival `-(h-2)(h-3)/2`) and remain strictly below `Head S = (h - 2)(h - 1)/2` because
  $$(h - 2)^2 - \text{bank} = (12k + 2)^2 - (117k^2 + 105k + 29) = 27k^2 - 57k - 25 > 0 \qquad (\forall k \ge 3).$$
  (No `A` at height `h - 1` occurs before the bank valleys end.) By (2), `Ψ_{h-2}(m + L_0) = 117k^2 + 234k + 76 > 0`, so `V_0`'s descent `S` (`Ψ_{h-2}(m + L_0) + (h - 2)(h - 1)/2`) strictly exceeds `Head S` and `V_0`'s stage-`h-1` `A`-candidate (`Ψ_{h-2}(s_{\text{mid}}) = -(h-2)(h-3)/2 + bank - 1 < Head S`). Thereafter `ΔΨ_{h-2}(V) = L_V + 1 > 0` strictly separates every `V_r` descent `S` above all earlier outputs and candidates.

- **Regime 3 (`y = h - 1`, critical source height)**:
  Here `ΔΨ_{h-1}(V) = +1`. From (2), `V_0`'s descent `S` sits at
  $$\text{desc}_0 = \big(\mathrm{Area}_0(V_0) - L_0(h - 1)\big) + \frac{(h - 1)h}{2} = (-117k^2 - 30k) + (72k^2 + 42k + 6) = -45k^2 + 12k + 6,$$
  and `V_r`'s descent `S` sits at `desc_r = desc_0 + r` (`1 ≤ r ≤ R`), which are strictly increasing. Their range `[desc_0, desc_R]` lies strictly inside `(P_{\max}, \text{Head }S)` for all `k ≥ 3`:
  $$\text{desc}_0 - P_{\max} = (-45k^2 + 12k + 6) - (-72k^2 - 30k - 3) = 27k^2 + 42k + 9 > 0,$$
  $$\text{Head }S - \text{desc}_R = (72k^2 + 42k + 6) - (-36k^2 + 18k + 7) = 108k^2 + 24k - 1 > 0.$$
  Meanwhile EVERY non-descent output and `A`-candidate at height `h - 1` — namely `V_0`'s bank peaks (`[P_{\min}, P_{\max}]`), all `V_r` stage-`h` target candidates (`[t_0, P_{\max} - 5]`), and all `V_r` ascent arrivals at height `h - 1` (`t_0 + (r - 1) - 1 ∈ [P_{\min}, P_{\max}]`) — lies in `[P_{\min}, P_{\max}]`, strictly below `desc_0`. Hence zero (I) or (II) collisions occur at `y = h - 1`.

- **Regime 4 (`y = h`, critical valley height)**:
  Here `ΔΨ_h(V) = -(L_V - 1) < 0`. In `V_r`, the `a - 1` stage-`h` valleys occupy `[X_r + 1, X_r + a - 1]` (strictly increasing by `+1`, with arrival output `X_r`) and `V_r`'s descent `S` sits at `D_r = X_r + (a - 1) + (u + 1)^2` (with `X_r = X_1 - (r - 1)(L_V - 1)`). Notice the exact separation between `D_r` and `X_{r-1}`:
  $$(L_V - 1) - (D_r - X_r) = (2K + 2a - 1) - (a - 1 + (u + 1)^2) = a + 4u - u^2 - 1 = 8k + 2 > 0.$$
  Thus the copy intervals `[X_r, D_r]` (`r = 1, ..., R`) are pairwise strictly disjoint and strictly decreasing!
  Moreover, `V_0`'s descent `S` satisfies `D_1 < \text{desc}_0 < \text{Head }S` (since `V_1` drops by `L_V - 1` below `desc_0`), while `V_0`'s ascent output `v_{0,\text{asc}}` and ascent `A`-candidate `v_{0,\text{cand}} = v_{0,\text{asc}} + 1` satisfy the exact identity
  $$X_1 - v_{0,\text{cand}} = 21k + 7 > 8k + 2 = X_1 - D_2.$$
  Hence `D_2 - v_{0,\text{cand}} = 13k + 5 > 0`, while `v_{0,\text{asc}} - (X_2 + a - 1) = (L_V - 1 - a + 1) - (21k + 8) = 36k^2 + 23k + 3 > 0`. Thus `v_{0,\text{asc}} < v_{0,\text{cand}}` sit strictly inside the empty gap `(X_2 + a - 1, D_2)` between `V_2`'s valleys and `V_2`'s descent `S`, avoiding every `S` landing of `V_1, ..., V_R` (and `V_r`'s own ascent `A`-candidate at height `h` from stage `h + 1` has `Ψ_h = X_r + a < D_r`). Hence zero collisions at `y = h`.

- **Regime 5 (`y = h + 1`, stage-`h` peaks)**:
  Here `ΔΨ_{h+1}(V) = -(2 L_V - 1) < 0`. In `V_1`, the peaks span `[p_{\min}, p_{\max}]` (width `a - 1`), and `V_1`'s descent `S` sits at `D_1^{(5)} = p_{\max} + u^2 - (a - 1) > p_{\max}` (since `u^2 - (a - 1) = 16k + 6 > 0`), with total copy span `D_1^{(5)} - p_{\min} = u^2 < 2 L_V - 1`. Directly computing at `y = h + 1`:
  $$v_{0,\text{asc}}^{(5)} - D_1^{(5)} = 17k + 6 > 0,$$
  and `v_{0,\text{asc}}^{(5)} < v_{0,\text{cand}}^{(5)} = v_{0,\text{asc}}^{(5)} + 1 < \text{desc}_0^{(5)} < \text{Head }S`. Hence `V_1, ..., V_R` occupy pairwise disjoint strictly decreasing intervals all strictly below `v_{0,\text{asc}}^{(5)}`, giving zero collisions.

- **Regime 6 (`h + 2 ≤ y ≤ K + 1`)**:
  At `y = K + 1` there are no `S` landings at all. For `h + 2 ≤ y ≤ K`, let `t_0(y) = s_{\text{mid}} + (y - (h - 1))` be `V_0`'s ascent arrival at height `y` (the start of `lift` when `y = K`) and `t_1(y) = m + L_0 + L_V - y` be `V_1`'s descent `S` clock at height `y`. Because `t_0(y + 1) = t_0(y) + 1` is an `A` step (`H` goes `y → y + 1`) and `t_1(y + 1) = t_1(y) - 1` is reversed across an `S` step (`H` goes `y + 1 → y`),
  $$\big(\Psi_{y+1}(t_0(y+1)) - \Psi_{y+1}(t_1(y+1))\big) - \big(\Psi_y(t_0(y)) - \Psi_y(t_1(y))\big) = t_1(y) - t_0(y) - 1 \ge L_V + 2\,\text{lift} - 1 > 0.$$
  Starting from Regime 5 (`y = h + 1`, where `Ψ(t_0) - Ψ(t_1) = 17k + 6 > 0`), induction on `y` proves `Ψ_y(t_1(y)) < Ψ_y(t_0(y))` for **every** `h + 1 ≤ y ≤ K`!
  Inside `V_0`, for `y < K`, `v_{0,\text{asc}} < v_{0,\text{cand}} < \text{desc}_0 < \text{Head }S`; at `y = K`, the `lift - 1` lift valleys step by `+1` from `Ψ_K(t_0(K)) + 1` up to `Ψ_K(t_0(K)) + lift - 1 = \text{desc}_0 - 1 < \text{desc}_0 < \text{Head }S`.
  Across `V_1, ..., V_R`, `ΔΨ_y(V) = -(y - (h - 1)) L_V + 1 ≤ -(3 L_V - 1)`, while the internal span of `V_r` at height `y` is `(K + 1 - y)^2 ≤ u^2 < 3 L_V - 1`, so all copies `V_1, ..., V_R` are pairwise strictly disjoint and lie strictly below `Ψ_y(t_0(y))`. Hence zero collisions in Regime 6.

Combining Regimes 1–6 proves `E-759 (I) & (II) = 0` for all `k ≥ 3`. By `E-782`, every `W_k` (`k ≥ 3`) is executed greedily by a coherent finite `State` whose exact seen set passes all 8 canonical scalar+spatial filters, while achieving `A / (F + O_c) = 2k - O(1) → ∞`.

## 4. Reproducible verification

- Lean module (`E-783`): `Recaman/CrossBlockReuseUnbounded.lean` (`26/28` substantive via `harness_gate.py --lint-module`; `0` flagged / `0` unknown via `harness_lean.py --vacuity-module`).
- Discovery & holdout checks (`E-783` & `E-784`):
  - `python3 docs/data/depth_general_20261127/cross_block_discovery.py` (CPU 0.49s): exhaustive `R = 2` (1,241 cases, 6 counters, best `[(1,2,1,1),(1,1,1,2)]` with `slack = -3`) + 5,000 random multi-block words.
  - `python3 docs/data/depth_general_20261127/cross_block_holdout.py` (CPU 4.68s): independent `O(Q^2)` check on `[(1,2,1,1),(1,1,1,2)]` with 6 prehistories `U`; coherent 2-block `[(2,1,1),(1,1,1,2)]` passing E-759 `(0, 0)` + literal `E-782` 8-filter greedy replay; Family A `k = 1..5` cross-check; Family B discovery (`k = 3, 4`) & frozen holdout (`k = 5, 6, 7`, up to `Q = 1,902,094`, `fI = fII = 0`, `ratio = 13.6604`); literal 8-filter greedy replay on `u = 6, h = 13, R = 6` (`ratio = 1.5269`).
