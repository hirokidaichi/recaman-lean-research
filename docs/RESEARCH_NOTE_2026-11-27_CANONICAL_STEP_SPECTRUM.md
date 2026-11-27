# Research Note: Canonical Step-Spectrum, Consecutive-Step Degree & 12-Filter Variable-Step Bridge No-Go (`E-790` / `E-791`)

- **Date**: 2026-11-27 (`R-20261127-02`, Track 3 — genuinely distinct general mechanism on `Recaman.Basic.a`)
- **Registry entries**:
  - `E-790 PROVED-LEAN` (`Recaman/CanonicalStepSpectrum.lean`, `docs/statement_audits/E-790.md`)
  - `E-791 PROVED-PAPER` (12-filter variable-step bridge language no-go)
- **Hypothesis card**: `docs/HYPOTHESIS_CARD_2026-11-27_CANONICAL_STEP_SPECTRUM.md`
- **Reproducible audit script**: `docs/data/depth_general_20261127/canonical_step_spectrum_audit.py`

## 1. Canonical Clock-0 Theorems (`E-790 PROVED-LEAN`)

In `Recaman/CanonicalStepSpectrum.lean`, we prove unconditionally for every canonical clock `b : Nat`
of the actual Recamán orbit `a = Recaman.Basic.a` and its visited set `valuesThrough b`:

1. **Realized Step Spectrum (`f9`, `canonical_step_difference_realized`)**:
   for every `1 ≤ k ≤ b`, there exist `u, v ∈ valuesThrough b` with `|u - v| = k`
   (witnessed by `u = a (k - 1)` and `v = a k`).
2. **Consecutive Incident Steps (`f10`, `canonical_consecutive_incident_steps`)**:
   for every interior visited value `v ∈ valuesThrough b` with `v ≠ 0` and `v ≠ a b`,
   there exist a clock `1 ≤ t < b` and `u₁, u₂ ∈ valuesThrough b` with `|v - u₁| = t` and
   `|v - u₂| = t + 1`.
3. **Odd & Even Neighbor Parity (`canonical_odd_even_neighbor`)**:
   every `v ∈ valuesThrough b \ {0, a b}` has BOTH an even-distance neighbor and an odd-distance
   neighbor in `valuesThrough b` within distance `b`.
4. **Separated-Set `2x` Clock Budget (`f11`, `canonical_separated_set_clock_budget`)**:
   for any `1 ≤ θ ≤ b` and any `Nodup` list `L` of elements in `valuesThrough b \ {0, a b}` with
   pairwise separation `|v - w| > b` and nearest-neighbor distance `≥ θ` in `valuesThrough b`,
   the map `v ↦ [t(v), t(v) + 1]` yields pairwise disjoint pairs in `{θ, ..., b}`, forcing
   $$2 \cdot |L| \le b + 1 - \theta$$
   (strictly `2x` tighter than `E-781`'s `|L| ≤ b + 1 - θ` on isolated peaks).
5. **First-Moment Sum Capacity (`f12`, `canonical_distinct_sum_le_upperTri_top`)**:
   for any `Nodup` list `L` of elements in `valuesThrough b`,
   $$\sum_{v \in L} v \le \sum_{j = 0}^{|L| - 1} \mathrm{upperTri}(b - j)$$
   (exact equality at `b = 1, 3`).

### Disqualification of `E-782`'s Constant-Step Bridge `G_d`

In `E-782`, the 8-filter witness used `L = b / 2` and a constant-step bridge `G_d` with even step
`d = b - 200 N`. Both `f9` and `f10` immediately disqualify `G_d`:
- Every step size `k ∈ (b / 2, d)` (for example `k = b / 2 + 1`) is **missing** from `G_d` (fails `f9`).
- Every interior bridge point `g_j = L + j · d` (`j ≥ 2`, strictly above `L + b`) has ONLY ONE
  distance `≤ b` (`d`, even only) to any other element of `G_d` (fails `f10` and `canonical_odd_even_neighbor`).

## 2. 12-Filter Variable-Step Bridge Language No-Go (`E-791 PROVED-PAPER`)

**Theorem (`E-791`).** Even when ALL 12 canonical seen-set filters (`f1..f4` of `E-778`, `f5..f8` of
`E-781`, and `f9..f12` of `E-790`) are enforced simultaneously on the exact distinct seen-set `V`
together with exact greedy replay, **zero** `E-759`-admissible finite words are excluded.

**Explicit construction for any `E-759`-admissible word `W` of length `N`:**
- Choose even `b = 2 · max(1000, 100 (N + 2)^3)`, `L = b / 2`, `M_off = 3 (N + 2)^2`, and
  initial bridge step `d_0 = b - 17 (N + 2)^2`.
- Place `a_b` with parity matching `upperTri(b)` at height `h_0 = max(3, -H_min(W) + 4)` so the
  downward **variable-step bridge** `g_0 = a_b`, `g_{j+1} = g_j - (d_0 - j)` lands its last point
  inside `[1, L]`, and extend an analogous upward variable-step bridge above `a_b` whenever
  `max(ext_seeds) > a_b + b`.
- Include the single anchor point `{b}`: together with `[0, L]`, `{b}` realizes EVERY step
  `L, L + 1, ..., b` (completing `{1, ..., b}` for `f9`) and itself has consecutive steps `(b - 1, b)`
  to `{1, 0} ⊆ [0, L]`.
- For every required external seed `c ∈ ext_seeds` (and the top upward bridge point if present),
  attach the 4-point shifted cluster `{c + M_off + r : r ∈ {0, 1, 2, 3}}`:
  - `c` acquires consecutive incident steps `(M_off, M_off + 1)`;
  - each of the 4 cluster points acquires consecutive incident steps `(1, 2)`;
  - since all bridge residues (`±17 j (N + 2)^2 + O(j^2)`) and cluster offsets (`+3 (N + 2)^2 + r`)
    are strictly disjoint from the trajectory window `[-N^2, +N^2] (mod b)` for `j ≤ 2 N`, greedy
    replay of `W` is completely unaffected!
- All 12 filters hold: `|V| = b/2 + O(N) ≤ b + 1` (`f1`), exact parity (`f2`),
  `max(V) = O(N b) ≪ upperTri(b) = b^2 / 2` (`f3, f4, f5, f12`), every adjacent gap `≤ b` (`f6`),
  tail distinct counts `O(N) ≪ 17 (N + 2)^2` (`f7, f8`), full step spectrum `{1..b}` (`f9`),
  consecutive incident steps `(t, t + 1)` at every `v ∈ V \ {0, a_b}` (`f10`), and every separated
  point has a neighbor within `max(d_0, M_off)` giving `2 |L_sep| = O(N) ≪ b + 1 - θ` (`f11`).

## 3. Verification Record & Stopping Decision

Command:
```bash
python3 docs/data/depth_general_20261127/canonical_step_spectrum_audit.py
```
- Real Recamán `a(0..600)` (Discovery `b = 0..250`, Holdout `b = 251..600`): `0` violations across `f9..f12` (`1,797` separated-set checks).
- `E-782` `G_d` (`b = 10000, d = 9800`): `k = 5001` missing (`f9` fail), `g_2` unique distance `[9800]` (`f10` fail).
- `E-791` 12-filter bridge: `180/180` all length-8 `E-759`-admissible words + `E-777 W_1..W_4` + `E-784` counterexample PASS all 12 filters + exact greedy replay.
- Lean 4: `Recaman/CanonicalStepSpectrum.lean` built (`1050` jobs, 0 warnings), `--vacuity-row E-790` (`0 flagged, 0 unknown, 5 theorems`).

**Stopping decision**: Static seen-set filtering by local distances, step spectrum, local degrees,
and first-moment bounds is **`STOPPED`**. Separating canonical Recamán from `E-759` requires
**global clock-0 dynamical / Eulerian-trail reachability** (not local properties of `V`).
