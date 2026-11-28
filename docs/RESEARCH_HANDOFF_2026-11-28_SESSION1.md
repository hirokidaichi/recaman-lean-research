# Research Handoff — 2026-11-28 Session 1 (`R-20261128-01`, `E-797..E-804`)

## 1. Conclusion

Completed and fully verified **7 new arbitrary-depth Lean 4 modules (`E-797`, `E-798`, `E-800`, `E-801`, `E-802`, `E-803`, `E-804`, all `PROVED-LEAN`, 61 audited theorems, `0 flagged / 0 unknown` vacuity, standard axioms `{propext, Classical.choice, Quot.sound}` only)** plus **1 new `PROVED-PAPER` construction (`E-799`)**, across 7 module-adding commits spaced `>= 30 min` apart (**zero `RECAMAN_ALLOW_BURST=1`**, **zero edits to `docs/PROTECTED_CLAIMS.tsv` or `docs/protected_pins/`**):

1. **`E-797 PROVED-LEAN`** (`Recaman/ExactFiveThirdsCapacity.lean`): closes the exact exponential growth base of actual `EndN` height capacity to **`5/3`** (`5 * 3^H * additions <= 9 * 5^H * free`, matching `E-786`'s `(2/5)*(5/3)^H` lower bound).
2. **`E-798 PROVED-LEAN`** (`Recaman/CoherentGreedyFreshness.lean`): formalizes `E-759` chronological `S`-freshness, periodic pigeonhole law, unconditional zero-drift repetition prohibition (blocking `E-786` periodic words on all coherent `SeededReplay.run` and `Recaman.Basic.a`), and unit-drift `Delta >= 2` necessity.
3. **`E-799 PROVED-PAPER`**: constructs the optimal unit-drift `Delta = 2` coherent greedy exponential cascade (`h_k = 2k + 2`), improving the coherent greedy lower bound from `3^(1/3) ~ 1.4422` (`E-789`) to **`sqrt(7/3) ~ 1.527525`** and narrowing `rho_greedy in [sqrt(7/3), 5/3]`. (Lean 4 formalization remains WIP and was deliberately excluded from this push.)
4. **`E-800 PROVED-LEAN`** (`Recaman/HeightConvolutionCapacity.lean`): exponentially-decaying height convolution capacity tightening full-band actual-`EndN` capacity to **`25 * 3^H * additions <= 18 * 5^H * free`** (`0.72 * (5/3)^H`, ratio `9/5` to `E-786`), `625 * 3^d * W(r) <= 1008 * 5^d * free` (`1.6128 * (5/3)^d`), and sharp `D = 7` (`j <= 16`) / `D = 8` (`W(m+6) <= 32*free, j <= 29`) compressions.
5. **`E-801 PROVED-LEAN`** (`Recaman/DynamicPredecessorObstruction.lean`): proves the full bidirectional `E-759` characterization **`seeded_replay_realizes_iff_fresh`** plus arbitrary-depth 1-step predecessor separation (`e779Word k` at depth `-(3k+5)`, initial-`S` Type-I witness, initial-`SS` Type-II witness).
6. **`E-802 PROVED-LEAN`** (`Recaman/NumericCandidateRankPotential.lean`): formalizes `E-761` purely numeric candidate-band rank potential `Phi_Y`, sharp `+6` permanent sign floor, all-time fresh-value wallet `<= max(1, y - 2)`, fixed original `Win` source finite capacity, and finite-horizon count on all `SeededReplay.run` and `Recaman.Basic.a`.
7. **`E-803 PROVED-LEAN`** (`Recaman/NumericStockStripPotential.lean`): formalizes `E-772` purely numeric departure-`A` stock strip with clipping + output-strip transport, **`15 * W' <= 34 * W - 30`**, sharp **`13 * T' <= 33 * T - 166`**, and strict domination over the classical `3^j` horizon for all `j >= 7`, `P_0 >= 2`.
8. **`E-804 PROVED-LEAN`** (`Recaman/FreshSourceHitSpacing.lean`): formalizes `E-760` unique `Z = ASSSSAAA` bridge, `Z ++ Z` replay prohibition, 2-step common-source gap `>= 20`, arbitrary-length span `8*n + 4*(n/2)`, and unified `E-761` source-clock capacity `(b + u) + 11 + 8*(M - 2) + 4*((M - 2)/2) <= X(u)` on all `SeededReplay.run` and `Recaman.Basic.a`.

**Explicit non-claims**: `C1`, `Q`, `H`, `SL`, surjectivity, and all protected claims (`E-001`, `E-067`, `E-070`, `E-179`) remain UNPROVED / unchanged.

## 2. Hypothesis-Card & Evidence Status

| Row | Status | Module / Artifact | Audited Theorems | Vacuity (`flagged/unknown`) |
|---|---|---|---|---|
| `E-797` | `PROVED-LEAN` | `Recaman/ExactFiveThirdsCapacity.lean` ([card](HYPOTHESIS_CARD_2026-11-27_EXACT_FIVE_THIRDS_CAPACITY.md), [audit](statement_audits/E-797.md)) | 8 | `0 / 0` |
| `E-798` | `PROVED-LEAN` | `Recaman/CoherentGreedyFreshness.lean` ([card](HYPOTHESIS_CARD_2026-11-28_COHERENT_GREEDY_FRESHNESS.md), [audit](statement_audits/E-798.md)) | 8 | `0 / 0` |
| `E-799` | `PROVED-PAPER` | [note](RESEARCH_NOTE_2026-11-28_DELTA2_COHERENT_CASCADE.md), `docs/data/depth_general_20261128/delta2_coherent_cascade_audit.py` | — | N/A (`PROVED-PAPER`) |
| `E-800` | `PROVED-LEAN` | `Recaman/HeightConvolutionCapacity.lean` ([card](HYPOTHESIS_CARD_2026-11-28_HEIGHT_CONVOLUTION_CAPACITY.md), [audit](statement_audits/E-800.md)) | 10 | `0 / 0` |
| `E-801` | `PROVED-LEAN` | `Recaman/DynamicPredecessorObstruction.lean` ([card](HYPOTHESIS_CARD_2026-11-28_DYNAMIC_PREDECESSOR_OBSTRUCTION.md), [audit](statement_audits/E-801.md)) | 9 | `0 / 0` |
| `E-802` | `PROVED-LEAN` | `Recaman/NumericCandidateRankPotential.lean` ([card](HYPOTHESIS_CARD_2026-11-28_NUMERIC_CANDIDATE_RANK_POTENTIAL.md), [audit](statement_audits/E-802.md)) | 11 | `0 / 0` |
| `E-803` | `PROVED-LEAN` | `Recaman/NumericStockStripPotential.lean` ([card](HYPOTHESIS_CARD_2026-11-28_NUMERIC_STOCK_STRIP_POTENTIAL.md), [audit](statement_audits/E-803.md)) | 8 | `0 / 0` |
| `E-804` | `PROVED-LEAN` | `Recaman/FreshSourceHitSpacing.lean` ([card](HYPOTHESIS_CARD_2026-11-28_FRESH_SOURCE_HIT_SPACING.md), [audit](statement_audits/E-804.md)) | 7 | `0 / 0` |

## 3. Excluded Unvalidated Work (Not Committed / Not Pushed)

- An in-progress Lean 4 formalization draft for `E-799` (`DeltaTwoCoherentCascade.lean`, targeting `PROVED-LEAN` for `rho_greedy >= sqrt(7/3)` on `SeededReplay.run`) and its companion audit script (`delta2_lean_cascade_audit.py`) were deliberately excluded from this commit and moved out of the repository tree to session scratch because compilation and G1–G5 / vacuity verification were not yet finished at session stop.

## 4. Changed Files (Commits `63bc402`..HEAD)

- Lean library: `Recaman.lean`, `Recaman/Audit.lean`, `Recaman/ExactFiveThirdsCapacity.lean`, `Recaman/CoherentGreedyFreshness.lean`, `Recaman/HeightConvolutionCapacity.lean`, `Recaman/DynamicPredecessorObstruction.lean`, `Recaman/NumericCandidateRankPotential.lean`, `Recaman/NumericStockStripPotential.lean`, `Recaman/FreshSourceHitSpacing.lean`.
- Registry & audits: `docs/EVIDENCE_REGISTRY.tsv`, `docs/statement_audits/E-797.md`, `E-798.md`, `E-800.md`..`E-804.md`.
- Cards, notes, tracker, handoff, & manifest: `docs/CURRENT_FRONTIER.md`, `docs/RESEARCH_GENERALIZATION_TRACKER.md`, `docs/RESEARCH_HANDOFF_2026-11-28_SESSION1.md`, `docs/HYPOTHESIS_CARD_2026-11-27_EXACT_FIVE_THIRDS_CAPACITY.md`, `docs/HYPOTHESIS_CARD_2026-11-28_*.md`, `docs/RESEARCH_NOTE_2026-11-27_EXACT_FIVE_THIRDS_CAPACITY.md`, `docs/RESEARCH_NOTE_2026-11-28_*.md`, `docs/data/depth_general_20261127/exact_five_thirds_capacity_audit.py`, `docs/data/depth_general_20261128/*.py`, `viewer/manifest.json`.

## 5. Verification Commands & Strongest Evidence

- Full repository check `./scripts/check.sh` run on final `HEAD` (module architecture closure, G1–G5 registry checks, full `lake build`, `Recaman/Audit.lean` standard-axiom verification, zero `sorry`/`admit`/`native_decide`/`axiom`, G6 protected-pin verification, and vacuity lint).
- Per-row `python3 scripts/harness_lean.py --vacuity-row E-NNN` verified `0 flagged, 0 unknown` for every one of `E-797`, `E-798`, `E-800`, `E-801`, `E-802`, `E-803`, `E-804`.
- Exact negative controls formalized in Lean 4 alongside positive theorems: `E-797` `delta = 6` counterexample (`50 x AASS`, excess `-41`); `E-798` non-coherent `TypeIFresh` failure (`s.value = 3, s.seen = {1}`); `E-801` `e779Word k` / `initialSWitnessI` / `initialSWitnessII` (showing Type-II `A`-obstruction is genuinely necessary); `E-802` `ASSS` proving `+6` floor sharpness and `(AS)^(Y/3)A` proving `Y/3 + 1` sharpness; `E-803` `13*T' = 33*T - 166` exact equality family; `E-804` non-fresh `SSAA ++ Z ++ Z ++ A` achieving span `16 < 20`.

## 6. Remaining Uncertainty & Next Decision

- **Uncertainty**: `rho_greedy` is currently pinned in `[sqrt(7/3), 5/3]` (`[1.527525, 1.666667]`), with the lower bound `E-799` at `PROVED-PAPER` only; all numeric/source capacities (`E-802`, `E-803`, `E-804`) bound individual candidate bands, single `Win` sources, or departure-`A` stock strips rather than closing global multi-source `C1`.
- **Recommended next step**:
  1. Finish the remaining mechanical Lean 4 proof fixes in the saved `DeltaTwoCoherentCascade.lean` draft to upgrade `E-799` (`rho_greedy >= sqrt(7/3)`) to `PROVED-LEAN` (`E-805`).
  2. In parallel (`>= 25 min` distinct mechanism per protocol §1.8), test whether `E-759` chronological `S`-freshness forces a strict upper bound `< 5/3` on `rho_greedy`, or whether multi-source coupling of `E-802`–`E-804` yields an arbitrary-depth global budget on `Recaman.Basic.a`.
