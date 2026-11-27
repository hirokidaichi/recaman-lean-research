# Spatial gap capacity of canonical Recamán states and the eight-filter language boundary

This note records two paired arbitrary-depth results from Track 2 (`H-20261127-02`, executing and strengthening `H-20261126-02`):

1. **`E-781` (`PROVED-LEAN`, `Recaman/CanonicalGapCapacity.lean`)**: Four new arbitrary-time spatial visited-inventory inequalities for the actual canonical Recamán sequence `a : Nat → Nat` and `valuesThrough b` (`Recaman.Basic`), strictly strengthening the adjacent-gap-`≤ b` condition of `H-20261126-02`.
2. **`E-782` (`PROVED-PAPER`, human review pending, not yet Lean-checked)**: Even when all four new spatial inequalities are combined with the four scalar canonical filters of `E-778` (eight filters total, enforced on the *exact* distinct seen set `V`, not merely a cover), the resulting filter suite still excludes **zero** coherent finite sign words. We also record an immediate corollary of `E-779` showing that every coherent-admissible nonpositive-height word (in particular every C1 positive-deficit word) admits an arbitrarily long coherent executed predecessor `S^L ++ w`.

## 1. Canonical spatial gap capacity (`E-781`, `PROVED-LEAN`)

Let `a n = (stateAt n).value`, `valuesThrough b = (stateAt b).seen`, and `upperTri n = n * (n + 1) / 2`. Because `a 0 = 0` and every step `k ∈ {1, ..., b}` changes `a` by exactly `±k`, the following hold unconditionally for every `b : Nat`:

1. **Walk-length peak bound (`walk_peak_le_upperTri`)**:
   $$\forall t \le b,\qquad 2\,a_t \le a_b + \mathrm{upperTri}(b).$$
   *Proof*: Combine `a_le_upperTri t` (`a t ≤ upperTri t`) with downward drift `a t + upperTri t ≤ a b + upperTri b` (`a_add_upperTri_mono`), proved by induction on `b ≥ t` using `recurrence`. Equality holds at `b = 1, 2, 3, 4` (e.g. `b = 4, t = 3`: `2·6 = 2 + 10`).

2. **Prefix trapping across an empty band (`empty_gap_prefix_trapped`)**:
   If `(lo, hi)` is empty in `valuesThrough b` (`∀ v ∈ valuesThrough b, v ≤ lo ∨ hi ≤ v`), then
   $$\forall t \le b,\quad t < hi - lo \implies a_t \le lo.$$
   *Proof*: Induction on `t`. Base `t = 0`: `a 0 = 0 ≤ lo`. Step `t → t + 1 < hi - lo`: by IH `a t ≤ lo`, so `a (t + 1) ≤ a t + (t + 1) < lo + (hi - lo) = hi`. Since `a (t + 1) ∈ valuesThrough b`, emptiness forces `a (t + 1) ≤ lo`.
   *Immediate corollary (`no_empty_gap_gt_clock`)*: if `b < hi - lo`, then `∀ v ∈ valuesThrough b, v ≤ lo`. Thus no adjacent gap inside `[0, max(valuesThrough b)]` exceeds `b`, proving the necessity half of `H-20261126-02`.

3. **Distinct tail cardinality above a gap (`empty_gap_distinct_tail_count_le`)**:
   If `lo < hi` and `(lo, hi)` is empty in `valuesThrough b`, then every duplicate-free list `L : List Nat` with `∀ v ∈ L, v ∈ valuesThrough b ∧ hi ≤ v` satisfies
   $$|L| \le b + 1 - (hi - lo).$$
   *Proof*: Every `v ∈ L` equals `a t` for some `t ≤ b`; by `empty_gap_prefix_trapped` we must have `hi - lo ≤ t ≤ b`. Hence `L` is a `Nodup` subset of `[a (hi - lo), ..., a b]`, which has length `b + 1 - (hi - lo)`. Sharpness persists beyond `b = 1000` (16 sharp hits in `b ∈ [0, 1000]`, 3 in `[1001, 5000]`).

4. **Tail peak bound above a gap (`empty_gap_tail_peak_le`)**:
   If `t ≤ b`, `lo < hi`, `hi ≤ a t`, and `(lo, hi)` is empty in `valuesThrough b`, then
   $$2\,a_t + \mathrm{upperTri}(hi - lo - 1) \le a_b + lo + \mathrm{upperTri}(b).$$
   *Proof*: By prefix trapping, `g := hi - lo ≤ t` and `a (g - 1) ≤ lo`. Combining upward drift `a t + upperTri (g - 1) ≤ a (g - 1) + upperTri t` with downward drift `a t + upperTri t ≤ a b + upperTri b` cancels `upperTri t`.
   *Boundary audit*: The hypothesis `hi ≤ a t` is essential; at `b = 4` (`a = [0,1,3,6,2]`), `(lo, hi) = (6, 11)` is vacuously empty (`g = 5`), yet `t = 3` has `2·6 + upperTri 4 = 22 > 18 = 2 + 6 + upperTri 4`.

5. **Descending gap-rank capacity (`multi_gap_rank_bound`)**:
   For any threshold `θ : Nat` and any `GapChain` of strictly separated empty bands `(lo_0, hi_0), ..., (lo_{m-1}, hi_{m-1})` (`lo_i < hi_i`, `hi_i ≤ lo_{i+1}`) in `valuesThrough b` such that each band has width `hi_i - lo_i > θ` and `hi_i ∈ valuesThrough b`:
   $$m \le b - \theta.$$
   Equivalently, the `k`-th largest adjacent gap `g_(k)` in sorted `valuesThrough b` satisfies `g_(k) ≤ b + 1 - k` for all `k ≥ 1`.
   *Proof*: The upper endpoints `hi_0 < hi_1 < ... < hi_{m-1}` form a `Nodup` list of length `m` in `valuesThrough b`, all `≥ hi_0`. Applying `empty_gap_distinct_tail_count_le` to the first band `(lo_0, hi_0)` gives `m ≤ b + 1 - (hi_0 - lo_0) ≤ b - θ`.

### Audit: exact seen set vs. visited cover

For an arbitrary visited cover (superset `V ⊇ V_b = {a_0, ..., a_b}`), adding extra elements inside `[0, a_b]` only splits gaps, so `g ≤ b` inside `[0, a_b]` still holds for covers. However, `walk_peak_le_upperTri`, `empty_gap_distinct_tail_count_le`, and `multi_gap_rank_bound` are strictly **exact-seen-set** invariants: adding `100` to `V_3 = {0,1,3,6}` violates `g ≤ 3` and `2 max V ≤ x + upperTri 3`, and adding extra points above a gap or splitting wide gaps can violate `tail_count` and `multi_gap_rank_bound`.

## 2. Falsification of the literal step-`b` grid and the eight-filter no-go (`E-782`, `PROVED-PAPER`)

### 2.1 The literal step-`b` grid in `H-20261126-02` fails `E-781`

In `H-20261126-02`, the proposed bridge grid `G = {b + δ + j b : j ≥ 0, ≤ M}` has `~101 N` consecutive gaps of exact width `b`. While every individual gap is `≤ b`, `E-781`'s `empty_gap_distinct_tail_count_le` allows at most `b + 1 - b = 1` element of `V` above any gap of width `b`, and `multi_gap_rank_bound` allows at most `1` gap of width `b` (`g_(2) ≤ b - 1`). Thus the literal step-`b` grid fails Filters 7, 8a, and 8b on every finite word, including the empty word `Q = 0`.

### 2.2 Margin-buffered step-`d` bridge grid passes all eight filters for every coherent word

Let `w` be any finite sign word of length `Q ≥ 0`, `N = Q + 1 ≥ 1`. Set
$$b = 1000 N^2,\qquad x = 100(b + N)N,\qquad d = b - 200 N.$$
Let `X_0, ..., X_Q` and `C_q` be the prescribed affine trajectory and subtraction candidates starting at `(b, x)` (E-759). Let `T_0 = {x} ∪ {C_q : q < Q \text{ is original free A}}` and `M = max T_0`.

1. **Affine bounds**: Every `X_i` and `C_q` has the form `x + b h + c` with `|h| ≤ N`, `|c| ≤ 2 N^2`, so every element of `T_0` and every prescribed `S` landing lies in `[99 b N + 98 N^2, 101 b N + 102 N^2]`. In particular `M ≤ 101 b N + 102 N^2`.
2. **Residue-avoiding bridge grid**: Since there are at most `Q = N - 1` prescribed `S` landings and `d = 1000 N^2 - 200 N ≥ 800 N > N`, by pigeonhole there exists `δ ∈ {1, ..., N}` such that `b + δ ≢ X_v (mod d)` for every `S` landing `X_v`. Define
   $$G_d = \{b + \delta + j d : j \ge 0,\ b + \delta + j d \le M\},\qquad T = T_0 \cup G_d,\qquad L = \frac{b}{2} - |T|,\qquad V = [0, L] \cup T.$$
3. **Uniform cardinality & gap bounds for all `N ≥ 1`**:
   - Since `d = 800 N^2 + 200 N(N - 1) ≥ 800 N^2`,
     $$|G_d| \le 1 + \left\lfloor \frac{101000 N^3 + 102 N^2 - 1000 N^2}{800 N^2} \right\rfloor \le 1 + 126 N + 1 \le 128 N,$$
     and `|T_0| ≤ N`, so `|T| ≤ 129 N < 200 N`.
   - Hence `L = 500 N^2 - |T| ≥ 500 N^2 - 129 N ≥ 371 N > N ≥ δ`, and `min T = b + δ > L`, so `[0, L]` and `T` are disjoint and `|V| = (L + 1) + |T| = b/2 + 1`.
   - The first non-unit gap `(L, b + δ)` has width `g_0 = b/2 + |T| + δ ≤ 500 N^2 + 130 N < 1000 N^2 - 200 N = d` (difference `≥ 500 N^2 - 330 N ≥ 170 N^2 > 0`). Every gap inside `T = G_d ∪ T_0` has width `≤ d` (inserting `T_0` only splits gaps of `G_d`, and `M - max G_d < d`). Thus **every adjacent gap `g` of `V` satisfies `g ≤ d = b - 200 N`**.
4. **Verification of all eight canonical filters for all `N ≥ 1`**:
   - *(F1)* `|V| = b/2 + 1 ≤ b + 1`.
   - *(F2)* `4 ∣ b` gives even `upperTri(b)`, and `x = 100(b+N)N` is even.
   - *(F3)* `max V = M ≤ 101 b N + 102 N^2 < 500 b N^2 + b/2 = upperTri(b)`.
   - *(F4)* With `s = |V| - 1 = b/2`, `x + s(2b - s + 1) - upperTri(b) = x + b^2/4 > 0`.
   - *(F5, walk-length peak)* `2 M - x ≤ 102 b N + 104 N^2 < 500 b N^2 < upperTri(b)`.
   - *(F6, adjacent gap)* Every gap `g ≤ d < b`.
   - *(F7, descending gap-rank)* For `θ ≥ d`, `#{gaps > θ} = 0 ≤ b - θ`. For `1 ≤ θ < d`, every gap `> 1` ends at an element of `T`, so `#{gaps > θ} ≤ |T| ≤ 129 N < 200 N = b - d < b - θ`. For `θ = 0`, `#{gaps > 0} = b/2 ≤ b`.
   - *(F8a, tail cardinality above every gap)* For `g = 1`, `#{v ∈ V : v ≥ hi} ≤ b/2 ≤ b`. For `g ≥ 2`, `hi ∈ T`, so `#{v ∈ V : v ≥ hi} ≤ |T| ≤ 129 N < 200 N + 1 = b - d + 1 ≤ b - g + 1`.
   - *(F8b, tail peak above every gap)* Since `g ≤ d = b - 200 N`,
     $$\mathrm{upperTri}(b) - \mathrm{upperTri}(g - 1) \ge \sum_{k=b-200N}^{b} k \ge 200 N(b - 200 N) = 200 b N - 40000 N^2,$$
     and `(200 b N - 40000 N^2) - (102 b N + 104 N^2) = 98000 N^3 - 40104 N^2 > 0` for all `N ≥ 1`. Hence `2 M + upperTri(g - 1) ≤ x + lo + upperTri(b)` even with `lo = 0`.
5. **Exact greedy replay**: Every prescribed `S` landing `X_v` satisfies `X_v ≥ 99 b N + 98 N^2 > L` (so `X_v ∉ [0, L]`), avoids `G_d` by the residue choice of `δ mod d`, and avoids `T_0` and prior outputs `X_u` iff `w` satisfies E-759 (I)/(II) (since `b = 1000 N^2 > 4 N^2` separates distinct slopes). Every prescribed `A` is forced either by its internal `Win` source or by its seeded candidate in `T_0 ⊆ V`.

Therefore the eight-filter spatial hierarchy adds **zero** finite-word exclusions beyond E-759 (I)/(II). As in E-778, this constructs a coherent finite `State`, **not** a canonical execution from `a 0 = 0`, and never replaces original `free` counts by seed cardinality.

## 3. Supporting corollary to E-779: `S^L`-predecessor closure on the C1 positive-deficit domain

By E-779 §1, for any coherent-admissible finite sign word `w`, `S ++ w` fails E-759 iff some `S`-clock `q` in `w` has preheight `H_w(q) = 2` and `B_w(q) = q + 1`. In particular, if `H_w(t) ≤ 1` for every `0 ≤ t ≤ |w|` (which holds for every word in the C1 positive-deficit initial-`S` domain, where `H_w(0) = 0` and `H_w(t) ≤ -1` for all `t ≥ 1`), then no clock reaches height `2`, so `S ++ w` is automatically coherent-admissible and satisfies `H_{S++w}(t) ≤ 0` everywhere. By induction on `L`, **`S^L ++ w` is coherent-admissible for every `L ≥ 0`**. Thus one-step (or arbitrary finite `L`-step) coherent predecessor existence alone cannot exclude any C1 positive-deficit word (whereas reaching canonical clock `0` requires starting with `AAA`, not `S^L`).

## 4. Reproducible verification

- Lean module (`E-781`): `Recaman/CanonicalGapCapacity.lean` (`9/10` substantive via `harness_gate.py --lint-module`; `0` flagged / `0` unknown via `harness_lean.py --vacuity-module`).
- Discovery & holdout checks (`E-782`):
  - `python3 docs/data/depth_general_20261127/spatial_inventory_audit.py` (CPU 4.31s): verifies `E-781` on canonical `a(0..1000)` and holdout `a(1001..5000)`; confirms literal `step_b` fails `f7/f8`; verifies `step_d` passes all 8 filters and matches exact greedy replay on all 63 discovery words (`Q = 0..5`) and 192 holdout words (`Q = 6..7`).
  - `python3 docs/data/depth_general_20261127/spatial_inventory_holdout.py` (CPU 0.13s): independent `O(Q^2)` window-sum check verifying all 256 length-8 words, E-777 `W_1..W_4`, all 197 coherent `H ≤ 1` words (`Q = 1..8`) under `S^L ++ w` (`L = 1, 2, 5`), and the `H = 2` negative control `AAS` (`S ++ AAS = SAAS` rejected).
