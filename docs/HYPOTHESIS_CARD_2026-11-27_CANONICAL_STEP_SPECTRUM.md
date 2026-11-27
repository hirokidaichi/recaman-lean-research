# Hypothesis Card: H-20261127-08 — Canonical Step-Spectrum, Consecutive-Step Degree & 12-Filter Bridge Boundary

- **ID**: `H-20261127-08`
- **Parent Cycle**: `R-20261127-02` (Track 3: genuinely distinct general mechanism on clock-0 `Recaman.Basic.a`)
- **Status**:
  - Canonical orbit invariants: **`PROVED-LEAN`** (`E-790`, `Recaman/CanonicalStepSpectrum.lean`)
  - 12-filter static seen-set word selection: **`PROVED-PAPER` (no-go / `STOPPED`)** (`E-791`, `docs/RESEARCH_NOTE_2026-11-27_CANONICAL_STEP_SPECTRUM.md`)
- **Depth-general classification**: `depth_general_progress` (arbitrary clock `b : Nat` on `Recaman.Basic.a` / `valuesThrough b`, plus all-word `N` no-go for 12 static seen-set filters).

## Bounded Research Question

Do the step-size realization (`{1..b}`), consecutive-incident-step degree `(t, t + 1)`, separated-set `2x` clock budget (`2 * |L| ≤ b + 1 - θ`), and exact first-moment sum bound (`L.sum ≤ topUpperTriSum b L.length`) on the actual canonical Recamán set `valuesThrough b` disqualify `E-782`'s constant-step bridge `G_d` — and if so, do all 12 static canonical filters (`f1..f12`) narrow the `E-759` coherent finite-word language, or does a variable-step bridge still realize every `E-759`-admissible word?

## Exact Claims & Outcomes

1. **`E-790 PROVED-LEAN`** (`Recaman/CanonicalStepSpectrum.lean`, 5 audited theorems, vacuity `0 flagged / 0 unknown`):
   - `canonical_step_difference_realized`: every `k ∈ [1, b]` appears as `|u - v|` in `valuesThrough b` (directly disqualifies `E-782`'s `G_d` at `k = b/2 + 1`).
   - `canonical_consecutive_incident_steps` & `canonical_odd_even_neighbor`: every `v ∈ valuesThrough b \ {0, a b}` has consecutive incident step sizes `(t, t + 1)` (`1 ≤ t < b`), hence both even- and odd-distance neighbors `≤ b` (directly disqualifies `E-782`'s `G_d` at `g_2 = L + 2d`).
   - `canonical_separated_set_clock_budget`: any `> b`-separated `Nodup` subset `L ⊆ valuesThrough b \ {0, a b}` with nearest neighbor `≥ θ` (`1 ≤ θ ≤ b`) obeys `2 * L.length ≤ b + 1 - θ` (strictly `2x` stronger than `E-781`).
   - `canonical_distinct_sum_le_upperTri_top`: any `Nodup` subset `L ⊆ valuesThrough b` obeys `L.sum ≤ ∑_{j=0}^{L.length-1} upperTri (b - j)` (sharp at `b = 1, 3`).
2. **`E-791 PROVED-PAPER` (12-filter no-go / `STOPPED`)**:
   - Replacing `G_d` by a **variable-step bridge** (`d_0 = b - 17(N+2)^2, d_0 - 1, d_0 - 2, ...`, anchor `{b}`, and 4-point shifted clusters `{c + 3(N+2)^2 + r : r = 0..3}` for each external seed) satisfies ALL 12 static filters (`f1..f12`) AND exact greedy replay for EVERY `E-759`-admissible finite word!

## Falsifier & Evidence

- Script: `docs/data/depth_general_20261127/canonical_step_spectrum_audit.py`
- Real Recamán `a(0..600)` (Discovery `b = 0..250`, Holdout `b = 251..600`): `0` violations across `f9, f10, f11, f12` (`1,797` separated-set tests).
- `E-782` `G_d` falsification (`b = 10000, d = 9800`): step `5001` missing (`f9` fail) and `g_2 = 24600` has unique incident distance `[9800]` (`f10` and parity fail).
- `E-791` 12-filter bridge verification: exhaustive length `8` (`180/180` all `E-759`-admissible words PASS all 12 filters + exact greedy), holdout `E-777 W_1..W_4` and `E-784` counterexample all PASS all 12 filters + exact greedy.
- Lean verification: `Recaman/CanonicalStepSpectrum.lean`, `lake build Recaman Recaman.Audit` (`1050` jobs, 0 errors, 0 warnings), `--vacuity-row E-790` (`0 flagged, 0 unknown, 5 theorems`).

## Stopping Decision

- Static local-metric / step-spectrum / local-degree / first-moment filtering of seen-sets `V` is **`STOPPED`** (`E-791`). Any future canonical-vs-`E-759` language separation must exploit **global path-existence / Eulerian-trail / clock-0 dynamical reachability** from `a 0 = 0`.
