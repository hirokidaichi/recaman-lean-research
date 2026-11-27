# Research Handoff — 2026-11-27 Session 2 (`R-20261127-02`)

**Date**: 2026-11-27  
**Parent cycle**: `R-20261127-02` (continuing from `R-20261127-01` / [`RESEARCH_HANDOFF_2026-11-27_DAILY.md`](RESEARCH_HANDOFF_2026-11-27_DAILY.md))  
**Branch / PR**: `hirokidaichi/research-progress-pr` ([PR #92](https://github.com/hirokidaichi/recaman-lean-research/pull/92))

## 1. Conclusion First

Session 2 (`R-20261127-02`, including the 30-min extension) resolved **both** tracks of `H-20261128-01` and delivered **6 new `PROVED-LEAN` modules** (41 newly audited theorems, **0 vacuity flags**, **0 warnings**, standard axioms only, all commits naturally spaced `≥ 30 min` without `RECAMAN_ALLOW_BURST=1`), **2 `PROVED-PAPER` results**, and **2 `REFUTED` conjectures** (`E-787`..`E-796`):

1. **Narrowed the `PROVED-LEAN` actual-`EndN` exponential growth bracket from `[5/3, 2]` → `[5/3, 199/110]` (`E-788`) → `[5/3, 190/107] = [1.6667, 1.7757]` (`E-794`)**, strictly breaking the `E-785`/`E-788` 3-spacing cone barrier (`1.8067`) directly on actual `EndN` via a new **coupled two-height 3+1 slot injection** (`3 * E_{r+1} + E_r ≤ W(r) + 3 * AA_{r-1}`) and zero-slack rational telescoping across `[1/2, κ_joint ≈ 0.563708)`.
2. **Resolved `H-20261128-01` Track A (`E-789 PROVED-PAPER`)**: proved that `E-759 = (0, 0)` coherent finite-State greedy realizability (passing all 8 filters of `E-782`) still permits fixed-height-strip exponential growth `Ω(3^{H/3}) = Ω(1.44225^H)` via a `Δ = 3` unit-shift cascade with height-`-1` `(SA)^{p_k}` buffers.
3. **Extended fixed-depth `D ≤ 6` free-gap bounds to arbitrary depth `D ≥ 2` (`E-787 PROVED-LEAN`)**: proved `4 ≤ free ≤ j ≤ 2^(D-2) - 3` for all `D ≥ 2` and sharp depth-7 compression `3 * W(m + 5) ≤ 59 * free, j ≤ 17`, without `hpos` or height ceiling.
4. **Sharpened `E-785` and `E-653` to double-ascent (`AA`) exits only (`E-792 PROVED-LEAN`) and refuted free-only overflow `C2` (`E-793 REFUTED`)**: proved `3 * E_{r+1} ≤ W(r) + 2 * AA_{r-1}` (and `3 * E_{m+2} ≤ F_m + 2 * AA_m`, `3 * E_{m+4} ≤ 6 * free + 2 * AA_{m+2}`), while constructing a mod-3 potential counterexample (`3 * 7 = 21 > 19 + 0`, zero slack in `E-792`) and an unbounded empty-prefix family (`F_2 = 1`, `3 * E_4 - W(3) = 2k - 9 → +∞`) refuting `3 * E_{r+1} ≤ W(r) + C * F_{r-1}` for every constant `C`.
5. **Closed static seen-set filtering on `Recaman.Basic.a` (`E-790 PROVED-LEAN` + `E-791 PROVED-PAPER`, `STOPPED`)**: proved canonical step-spectrum (`f9`), consecutive incident steps & odd/even neighbors (`f10`), `2x`-stronger separated clock budget (`f11`), and exact first-moment capacity (`f12`) on `valuesThrough b` (directly disqualifying `E-782`'s constant-step bridge `G_d`), then proved via a variable-step bridge + `{b}` anchor + 4-point shifted seed clusters that even all 12 static seen-set filters (`f1..f12`) still exclude **zero** `E-759`-admissible finite words.

**Strict non-claims**: Neither `C1`, `Q`, `H`, `SL`, surjectivity, nor any protected central claim (`E-001`, `E-067`, `E-070`, `E-179`) is proved.

## 2. Hypothesis-Card & Evidence Status (`E-787`..`E-794`)

| Row | Label | Module / Note | Audited Theorems | Vacuity | Summary |
|---|---|---|---|---|---|
| `E-787` | `PROVED-LEAN` | `Recaman/ArbitraryDepthFreeGap.lean` | 7 | `0 flagged / 0 unknown` | Arbitrary-depth `W(r) ≤ 2^d * free`, `3*W(m+5) ≤ 59*free`, `4 ≤ free ≤ j ≤ 2^(D-2)-3`, sharp `D = 7` (`j ≤ 17`) |
| `E-788` | `PROVED-LEAN` | `Recaman/SharpThreeSpacingCapacity.lean` | 7 | `0 flagged / 0 unknown` | Full 3-spacing rational cone `[1/2, κ₃)` telescoping, no-blowup low-weights bound, `20/11` & `199/110` (`1.8091`) |
| `E-789` | `PROVED-PAPER` | `docs/RESEARCH_NOTE_2026-11-27_COHERENT_EXPONENTIAL_CASCADE.md` | — | — | Coherent greedy `E-759=(0,0)` `Ω(3^{H/3})` cascade (`k=1..3` verified up to len `15,023,282`, 8-filter greedy replay on `B_1`) |
| `E-790` | `PROVED-LEAN` | `Recaman/CanonicalStepSpectrum.lean` | 5 | `0 flagged / 0 unknown` | Canonical `valuesThrough b` step-spectrum (`f9`), consecutive steps (`f10`), `2x` separated clock (`f11`), first-moment (`f12`) |
| `E-791` | `PROVED-PAPER` | `docs/RESEARCH_NOTE_2026-11-27_CANONICAL_STEP_SPECTRUM.md` | — | — | All 12 static filters (`f1..f12`) exclude 0 `E-759` words (variable-step bridge + 4-pt clusters); static filtering `STOPPED` |
| `E-792` | `PROVED-LEAN` | `Recaman/ExcursionClimbSpacing.lean` | 6 | `0 flagged / 0 unknown` | `3*E_{r+1} ≤ W(r) + 2*AA_{r-1}`, `min(A_{r-1}, A_r)`, `3*E_{m+2} ≤ F_m + 2*AA_m`, `3*E_{m+4} ≤ 6*free + 2*AA_{m+2}` |
| `E-793` | `REFUTED` | `docs/RESEARCH_NOTE_2026-11-27_EXCURSION_CLIMB_SPACING.md` | — | — | Free-only overflow `C2` refuted (`21 > 19 + 0` minimal; `2k - 9 → +∞` empty-prefix family refutes all `C * F_{r-1}`) |
| `E-794` | `PROVED-LEAN` | `Recaman/JointHeightSpacingCapacity.lean` | 8 | `0 flagged / 0 unknown` | Coupled `3*E_{r+1}+E_r ≤ W(r)+3*AA_{r-1}` + joint cone `[1/2, κ_joint)` breaking `1.8067`: `9/5`, `16/9`, `190/107` (`1.7757`) |
| `E-795` | `PROVED-LEAN` | `Recaman/CanonicalPathInvariants.lean` | 8 | `0 flagged / 0 unknown` | Unconditional clock-0 `subSum` complement, quadratic distinct-seen lower bound `2*upperTri(b+1-|V|) ≤ upperTri b + a b`, mod-4 parity cap, cut connectivity, and multi-point cluster clock budget `m + ∑|C_i| ≤ b + 1 - θ` |
| `E-796` | `REFUTED` | `docs/RESEARCH_NOTE_2026-11-27_RESONANT_OVERFLOW_REFUTATION.md` | — | — | Exact `D=13` two-potential resonance (`Δp_{14} == drop_{14} == 169`) refutes ALL upper-free overflow bounds `C*F_{≥ r-1}` (`F_{≥ 15} = 205` const while `3*E_{17}+E_{16}-W = 3k-1 → +∞`) and proves asymptotic constant-1 sharpness of `E-794` |

Across **both** sprints (`R-20261127-01` + `R-20261127-02`, `E-781`..`E-796`): **10 new `PROVED-LEAN` modules, 60 audited theorems, 0 flagged / 0 unknown vacuity lint, 0 warnings, 0 `RECAMAN_ALLOW_BURST=1`**.

## 3. Changed Files (Session 2)

- **Lean modules**:
  - `Recaman/ArbitraryDepthFreeGap.lean`
  - `Recaman/SharpThreeSpacingCapacity.lean`
  - `Recaman/CanonicalStepSpectrum.lean`
  - `Recaman/ExcursionClimbSpacing.lean`
  - `Recaman/JointHeightSpacingCapacity.lean`
  - `Recaman.lean`, `Recaman/Audit.lean`
- **Statement audits (G5)**:
  - `docs/statement_audits/E-787.md`, `E-788.md`, `E-790.md`, `E-792.md`, `E-794.md`
- **Research notes & hypothesis cards**:
  - `docs/RESEARCH_NOTE_2026-11-27_ARBITRARY_DEPTH_FREE_GAP.md` / `docs/HYPOTHESIS_CARD_2026-11-27_ARBITRARY_DEPTH_FREE_GAP.md`
  - `docs/RESEARCH_NOTE_2026-11-27_SHARP_THREE_SPACING_CAPACITY.md` / `docs/HYPOTHESIS_CARD_2026-11-27_SHARP_THREE_SPACING_CAPACITY.md`
  - `docs/RESEARCH_NOTE_2026-11-27_COHERENT_EXPONENTIAL_CASCADE.md` / `docs/HYPOTHESIS_CARD_2026-11-27_COHERENT_EXPONENTIAL_CASCADE.md`
  - `docs/RESEARCH_NOTE_2026-11-27_CANONICAL_STEP_SPECTRUM.md` / `docs/HYPOTHESIS_CARD_2026-11-27_CANONICAL_STEP_SPECTRUM.md`
  - `docs/RESEARCH_NOTE_2026-11-27_EXCURSION_CLIMB_SPACING.md` / `docs/HYPOTHESIS_CARD_2026-11-27_EXCURSION_CLIMB_SPACING.md`
  - `docs/RESEARCH_NOTE_2026-11-27_JOINT_HEIGHT_SPACING.md` / `docs/HYPOTHESIS_CARD_2026-11-27_JOINT_HEIGHT_SPACING.md`
- **Reproducible falsifier & audit scripts**:
  - `docs/data/depth_general_20261127/arbitrary_depth_free_gap_audit.py`
  - `docs/data/depth_general_20261127/sharp_three_spacing_audit.py`
  - `docs/data/depth_general_20261127/coherent_exponential_cascade_audit.py`
  - `docs/data/depth_general_20261127/canonical_step_spectrum_audit.py`
  - `docs/data/depth_general_20261127/excursion_climb_spacing_audit.py`
  - `docs/data/depth_general_20261127/joint_height_spacing_audit.py`
- **Registry, trackers, manifest**:
  - `docs/EVIDENCE_REGISTRY.tsv`, `docs/CURRENT_FRONTIER.md`, `docs/RESEARCH_GENERALIZATION_TRACKER.md`, `docs/HYPOTHESIS_CARD_2026-11-28_CROSS_HEIGHT_CAPACITY.md`, `docs/RESEARCH_HANDOFF_2026-11-27_SESSION2.md`, `viewer/manifest.json`.
- **Protected files untouched**: `git diff origin/main -- docs/PROTECTED_CLAIMS.tsv docs/protected_pins/` is empty (0 lines).

## 4. Commands Run & Verification

- `lake build Recaman Recaman.Audit`: succeeded (`1052` jobs, 0 warnings in all new modules).
- `python3 scripts/harness_gate.py --lint-module <file>` on all 5 Session 2 Lean modules: 100% public substantive.
- `python3 scripts/harness_lean.py --vacuity-row <row>` across all 9 new Lean rows (`E-781`, `E-783`, `E-785`, `E-786`, `E-787`, `E-788`, `E-790`, `E-792`, `E-794`): **0 flagged, 0 unknown across all 52 theorems**.
- All 6 Session 2 Python audit scripts exited 0 with 0 violations and exact negative controls.
- Full `./scripts/check.sh` (including G1–G6 pin verification, module graph, import contract, registry audit, and manifest check): passes cleanly with exit code 0.

## 5. Failed Attempts, Counterexamples & Stopped Branches

- `3 * E_{r+1} ≤ W(r) + 2 * A_{r-2}`: immediately refuted by `AAASSS*5` (`r = 1`: `12 > 5`).
- Moving `(AS)` bank at height `H - 1` to beat `5/3`: algebraically cancels (`+b_{H-1} - b_{H-1} = 0`).
- Free-only overflow `C2` (`3 * E_{r+1} ≤ W(r) + 2 * F_{r-1}`): survived 65,534 exhaustive words and 270,000 hill-climbing steps, then **refuted** by mod-3 potential construction (`E-793`), proving supplied `AA_{r-1}` exits cannot be dropped pointwise.
- Static 12-filter seen-set selection (`f1..f12`): **STOPPED** (`E-791`).

## 6. Remaining Uncertainty & Next Decision

- **Residual exponential bracket**: `[5/3, 190/107] = [1.6667, 1.7757]` (joint cone root `1.77397`). Next high-leverage question: either break `5/3` from below using recursive `AA`-overflow cascades, or break `1.77397` from above via a cross-height charging inequality accounting for the height-`r` free oscillations `F_r` consumed in `E-793`.
- **Distinct clock-0 canonical mechanism**: formalize global ledger/path invariants on `Recaman.Basic.a` beyond static seen-set filters (e.g., exact complement triangular bound `subSum b + upperTri (b - subCount b) ≤ upperTri b`, unconditional quadratic distinct-seen lower bound `2 * upperTri (b + 1 - |V|) ≤ upperTri b + a b`, mod-4 parity partition capacity, and disjoint multi-point cluster clock budgets `m + ∑ |C_i| ≤ b + 1 - θ`).
- **Tracker verdict**: `local_progress = yes`, `depth_general_progress = yes`, consecutive no-general-progress streak `0`, next allocation `30/60/10` (`≥ 25 min` distinct mechanism). All prior `STOPPED` constraints remain intact.
