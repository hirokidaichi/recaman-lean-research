# Hypothesis card: `spatial-gap-inventory`

- ID: `H-20261127-02` (executes and strengthens `H-20261126-02`)
- Owner: Antigravity (proposer / falsifier / formalizer / separate audit pass)
- Created: 2026-11-27
- Status: `PROVED-LEAN` (`E-781`, canonical necessity) + `PROVED-PAPER` (`E-782`, 8-filter spatial language no-go)
- Research branch: `spatial-visited-inventory` (distinct general mechanism)
- Work state: completed (Lean checked for `E-781`; all-word proof on paper + discovery/holdout verified for `E-782`)
- Parent card / allocation cycle: `R-20261127-01` (distinct general mechanism, ≥25 min allocation)

## Exact statement

Two coupled arbitrary-time / arbitrary-word claims:

1. **Canonical necessity (`E-781`, `PROVED-LEAN` in `Recaman/CanonicalGapCapacity.lean`)**:
   For the actual standard Recamán sequence `a : Nat → Nat` and `valuesThrough : Nat → List Nat` at every canonical clock `b : Nat` (no depth or cutoff bound):
   - Walk-length peak bound (`walk_peak_le_upperTri`): `∀ b t, t ≤ b → 2 * a t ≤ a b + upperTri b`.
   - Prefix trapping (`empty_gap_prefix_trapped`): if `∀ v ∈ valuesThrough b, v ≤ lo ∨ hi ≤ v`, then `∀ t ≤ b, t < hi - lo → a t ≤ lo`.
   - Adjacent-gap necessity (`no_empty_gap_gt_clock`): if `b < hi - lo` and `(lo, hi)` is empty in `valuesThrough b`, then `∀ v ∈ valuesThrough b, v ≤ lo`.
   - Tail peak bound (`empty_gap_tail_peak_le`): for `t ≤ b`, `lo < hi`, `hi ≤ a t`, `2 * a t + upperTri (hi - lo - 1) ≤ a b + lo + upperTri b`.
   - Distinct tail cardinality (`empty_gap_distinct_tail_count_le`): for any `Nodup` list `L` of visited values in `valuesThrough b` with all `v ≥ hi` (`lo < hi`), `L.length ≤ b + 1 - (hi - lo)`.
   - Descending gap-rank capacity (`multi_gap_rank_bound`): for any threshold `θ : Nat` and strictly ordered `GapChain gaps` of empty bands in `valuesThrough b` of width `> θ` whose upper endpoints lie in `valuesThrough b`, `gaps.length ≤ b - θ`.

2. **All-word 8-filter spatial language no-go (`E-782`, `PROVED-PAPER`)**:
   For every finite sign word `w` of length `Q ≥ 0` (including the empty word), `w` satisfies E-759 (I)/(II) if and only if there exist `b : Nat`, `x : Nat`, and a coherent finite `State ⟨x, seen⟩` whose exact distinct seen set `V` executes `w` greedily and simultaneously satisfies all 8 canonical necessary conditions:
   - the 4 scalar conditions of E-778 (`|V| ≤ b + 1`, `x ≡ upperTri b (mod 2)`, `V ⊆ [0, upperTri b]`, `upperTri b ≤ x + s(2b - s + 1)` with `s = |V| - 1`);
   - walk-length peak bound `2 * max V ≤ x + upperTri b`;
   - adjacent-gap bound `g ≤ b` (H-20261126-02);
   - descending gap-rank hierarchy `#{gaps > θ} ≤ b - θ` for every `θ ∈ [0, b]`;
   - tail cardinality `#{v ∈ V : v ≥ hi} ≤ b + 1 - g` and tail peak `2 * max V + upperTri (g - 1) ≤ x + lo + upperTri b` for every adjacent gap `(lo, hi)` of width `g = hi - lo` in `V`.

   **Supporting audit findings**:
   - The literal step-`b` bridge grid proposed in `H-20261126-02` passes `g ≤ b` but **fails** the sharper tail-cardinality, tail-peak, and descending gap-rank invariants on every word (including `Q = 0`). Replacing `d = b` with the margin-buffered step `d = b - 200 * N` (`N = Q + 1`) repairs the grid and satisfies all 8 filters simultaneously.
   - Cover vs. exact seen set: `g ≤ b` (inside `[0, a b]`) holds for any visited cover `V ⊇ V_b`, whereas `walk_peak_le_upperTri`, `empty_gap_distinct_tail_count_le`, and `multi_gap_rank_bound` are exact-seen-set (`V = V_b`) invariants and can fail on strict supersets with spurious entries.
   - Supporting E-779 corollary: every coherent-admissible finite word `w` with prefix height `H(t) ≤ 1` for all `t` (in particular every C1 positive-deficit word) admits an arbitrarily long coherent executed predecessor `S^L ++ w` for every `L ≥ 0`.

## Why it would matter

- Frontier obligation discharged: proves arbitrary-time spatial visited-inventory invariants on the real canonical Recamán orbit (`Recaman.Basic`) in Lean 4, and resolves `H-20261126-02` by proving that even this strictly stronger 8-filter spatial hierarchy excludes zero coherent finite words.
- Stronger than an existing identity or equivalent reformulation because: `E-755`/`E-778` track only scalar counts/cover sums; `E-781` extracts exact spatial trapping and rank-ordered gap capacities from the monotonic step sizes `1, 2, ..., b` of `Recaman.Basic.stateAt`.
- Smallest useful consequence: closes the spatial gap-hierarchy filter route as a finite-word language selector and isolates what remains genuinely missing (global executed past connecting to `a 0 = 0`, not static snapshots of `V`).

## Connection to arbitrary depth

- Assessment axis: `depth_general_progress` (new arbitrary-time canonical spatial inequalities in Lean 4 + new all-word 8-filter language no-go).
- Quantifiers and dependence on depth D, length, height and run count: `E-781` quantifies over all `b, t, lo, hi, θ : Nat` and arbitrary lists `L`, `gaps` with zero depth/cutoff assumption; `E-782` quantifies over all finite sign words `w` of arbitrary length/depth.
- Original actual-supply/free assumptions and their producers: `E-781` uses only `Recaman.Basic.a`, `valuesThrough`, `upperTri` directly; `E-782` retains all original `Win`/free sets from origin `0` without resetting or deleting future free candidates.
- Repeated use of the same free position, maximum load and boundary correction: not applicable to `E-781`; `E-782` does not conflate seed cardinality `|V|` with original free count `F`.
- Depth-dependent cost and its proved payment/cancellation: in `E-782`, `b = 1000 N^2` and `d = b - 200 N` yield `|T| ≤ 129 N < 200 N = b - d` uniformly for all `N ≥ 1`, paying every gap-rank and tail-peak margin explicitly.
- Concrete next inequality or history-preserving induction step consuming this result: redirects provenance filters away from static `V`-snapshot inequalities toward actual executed-history connectivity back to clock `0` (or direct nonlinear LOW-free/class charging).
- Existing generic input and the genuinely new edge beyond it: E-759 and E-778 are inputs; the new edges are (i) the Lean-proved spatial canonical invariants (`E-781`) that strictly separate literal step-`b` grids from canonical states, and (ii) the step-`d` margin-buffered bridge grid (`E-782`) showing all 8 filters still preserve the full coherent word language.
- Countermodel/no-go test for this mechanism, with reachability scope: `E-782` explicitly constructs coherent finite-State seeds, NOT canonical prehistories from `a 0 = 0`; it does not refute C1 or prove canonical reachability.

## Allocation and decision value

- Mode: global exploration + Lean formalization of canonical necessity.
- Competing units and shared bottlenecks: runs alongside Track 1 (`H-20261127-01`, cross-block charging) as the ≥25-minute distinct mechanism required by Protocol §1.8.
- Why this unit now: `H-20261126-02` was the designated distinct-mechanism follow-up after E-778; checking its spatial gap filter revealed both a sharper Lean-provable orbit invariant and its exact language-level boundary.
- If successful, which dependency edge changes?: proves `E-781` in Lean 4 on `Recaman.Basic` and eliminates all 8 static scalar+spatial gap filters as coherent-word selectors (`E-782`).
- If unsuccessful, which candidate family is excluded and how does the next choice change?: if any spatial gap filter had excluded a coherent word, it would have provided a new canonical filter; instead `E-782` closes static gap-rank filtering.

| Budget dimension | Cycle total | This unit planned | This unit actual | Cap / accounting rule |
|---|---|---|---|---|
| Agent work minutes | ~115 min | 30 min (distinct general mechanism) | ~25 min (10:18–10:43 JST, incl. Lean module + audit) | Tracked separately from Track 1 |
| Python CPU seconds | — | ≤10s | 4.44s (`spatial_inventory_audit.py` 4.31s + `spatial_inventory_holdout.py` 0.13s) | Single-process exact checks |

- Audit reservation and who performs the separate audit pass: independent semantic audit pass + `harness_gate.py` + `harness_lean.py --vacuity-module` + `./scripts/check.sh`.
- First checkpoint: 10:25 JST (Lean build + vacuity clean + discovery/holdout pass).

## Provenance and dependencies

- Definitions used: `Recaman.a`, `Recaman.valuesThrough`, `Recaman.upperTri`, `Recaman.CanonicalGapCapacity.GapChain`, E-759 (I)/(II), `SeededReplay.run`.
- Lean theorems used: `Recaman.recurrence`, `Recaman.mem_valuesThrough_iff`, `Recaman.a_le_upperTri`.
- Unverified mathematical assumptions: none for `E-781`; `E-782` is `PROVED-PAPER` (human review pending, not yet formalized in Lean).
- Literature source or analogy: E-755 / E-759 / E-778 / E-779.

## Falsification plan

- Small and boundary cases: `b = 0..4` (sharpness of `walk_peak_le_upperTri`), `Q = 0, 1` (`N = 1, 2`), empty-band edge cases (`hi ≤ lo`, `hi - lo > b`), `t < hi - lo` counterexample to unconditional `empty_gap_tail_peak_le` caught and fixed by requiring `hi ≤ a t`.
- Adversarial or weakened-history model: literal step-`b` grid (`H-20261126-02`) tested and killed by `f7_gap_rank`/`f8_tail_cnt`/`f8_tail_peak`; strict superset cover vs. exact seen set audited; negative control `AAS` (`max H = 2`) verified to fail `S ++ AAS = SAAS`.
- Discovery range: canonical `a(0..1000)` for `E-781`; all 63 words of lengths `0..5` for `E-782`.
- Frozen holdout range: canonical `a(1001..5000)` for `E-781`; all 192 words of lengths `6..7` + all 256 words of length `8` + E-777 `W_1..W_4` + 197 nonpositive-height words (`H ≤ 1`, lengths `1..8`) for `E-782`.
- Maximum one permitted repair: 1 design repair on `empty_gap_tail_peak_le` (requiring `hi ≤ a t` after falsifying `t < hi - lo` at `b = 4, g = 5`) before Lean formalization; 0 repairs after script freeze.
- Stop condition: stop static spatial gap-filter search once `E-782` closes the full 8-filter hierarchy.

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-11-27 | `COMPUTED` | `python3 docs/data/depth_general_20261127/spatial_inventory_audit.py` | 0 violations on `a(0..1000)` & `a(1001..5000)`; literal `step_b` fails `f7/f8`; `step_d` passes all 8 filters & exact replay on 63 discovery + 192 holdout words |
| 2026-11-27 | `COMPUTED` | `python3 docs/data/depth_general_20261127/spatial_inventory_holdout.py` | 256/256 length-8 holdout + E-777 `W_1..W_4` + 197/197 `H ≤ 1` `S^L`-predecessor checks pass; `AAS` negative control fails `S++AAS` |
| 2026-11-27 | `PROVED-LEAN` | `lake build Recaman.CanonicalGapCapacity && harness_gate.py --lint-module && harness_lean.py --vacuity-module` | 9/10 substantive, 0 flagged, 0 unknown across 8 elaborated theorems (`E-781`) |
| 2026-11-27 | `PROVED-PAPER` | `docs/RESEARCH_NOTE_2026-11-27_SPATIAL_GAP_INVENTORY.md` | All-word proof of 8-filter spatial bridge-grid equivalence (`E-782`) + `S^L`-predecessor closure for `H ≤ 1` |

## Semantic audit

- Informal statement implies formal statement: Yes — `a`, `valuesThrough`, `upperTri` directly represent the canonical orbit at arbitrary time `b`; `Nodup` subset and `GapChain` avoid any list-ordering or multiplicity loophole.
- Formal statement implies intended consequence: Yes — `no_empty_gap_gt_clock`, `empty_gap_distinct_tail_count_le`, and `multi_gap_rank_bound` enforce exact canonical spatial gap constraints on `valuesThrough b`, and `E-782` constructs an exact finite `State` passing all 8 filters for every E-759 word.
- Counterfactual examples that should make the statement false: `b = 4`, `(lo, hi) = (6, 11)` refutes `empty_gap_tail_peak_le` without `hi ≤ a t`; literal step-`b` grid fails `f7/f8`; strict superset cover `V = {0,1,3,6,100}` fails `no_empty_gap_gt_clock` at `b = 3`; `AAS` fails `S ++ AAS`.
- Could the theorem be proved from weaker or vacuous assumptions?: No (`harness_lean.py --vacuity-module`: 0 flagged, 0 unknown).
- Are reachability, freshness, time order, or actual-orbit provenance accidentally omitted?: No — `E-781` is proved on actual canonical `stateAt b`; `E-782` explicitly separates coherent finite-State seeds from canonical prehistory.

## Decision

- Continue / formalize / refute / stop: `E-781` formalized (`PROVED-LEAN`); `E-782` proved on paper (`PROVED-PAPER`); static scalar+spatial gap-filter approach **STOPPED** as a coherent finite-word selector.
- Depth-general assessment: **yes** (both `E-781` arbitrary-time canonical spatial theorems in Lean 4 and `E-782` all-word 8-filter language no-go satisfy Protocol §1.8 criteria 1 & 3).
- Reopen static spatial filtering only if: a genuinely new non-gap canonical invariant (e.g., exact distinct-step-subset-sum / full walk realization to clock `0`) is proposed with an explicit word that fails it.
