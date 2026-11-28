# Hypothesis Card: Complete Bi-Directional E-759 Realization & Arbitrary-Depth Dynamic Predecessor Separation (E-801)

- **Date**: 2026-11-28
- **Status**: `PROVED-LEAN` (`E-801`, `Recaman/DynamicPredecessorObstruction.lean`)
- **Branch / Frontier**: General-principle arbitrary-depth branch (Front 3A — bi-directional coherent greedy characterization + dynamic predecessor obstruction on `Recaman.SeededReplay` and `Recaman.Basic.a`)

## 1. Precise Statement & Quantifiers

1. **Bi-directional `E-759` realization (`seeded_replay_realizes_iff_fresh`)**:
   For every finite sign word `w : List Bool`:
   ```lean
   (∃ b st, st.value ∈ st.seen ∧ MatchesAt (replaySign b st) 0 w)
     ↔ (TypeIFresh (wordSign w) w.length ∧ TypeIIFresh (wordSign w) w.length)
   ```
2. **Dynamic 1-step predecessor obstruction (`no_predecessor_forbids_nonzero_clock_replay`, `no_predecessor_forbids_all_canonical_clocks`)**:
   For any `w : List Bool` satisfying `BlocksSPredecessor w` (there is a subtraction step `w[q] = false` with `wordHeight w (q+1) = 1` and `areaW (w.take (q+1)) = q + 2`) and `BlocksAPredecessorI w ∨ BlocksAPredecessorII w` (a subtraction step `w[q] = false` with either `wordHeight w (q+1) = -1, areaW = -(q+2)` [Type-I collision with clock `s - 1` value] or `wordHeight w (q+1) = -2, areaW = -2*(q+2)` [Type-II collision with the rejected candidate of the prepended `A` at clock `s - 1`]):
   - No coherent `SeededReplay` (`st.value ∈ st.seen`) can realize `w` at ANY clock `s ≥ 1`.
   - If `w` starts with `S` (`w[0] = false`) or has `w[2] = false` (e.g. `AAS...`), then `w` NEVER occurs at ANY clock `s : Nat` of the canonical Recamán orbit `Recaman.Basic.a`.
3. **Arbitrary-depth dynamic separation (`e779Word_arbitrary_depth_dynamic_separation`)**:
   For EVERY `k : Nat`, the word `e779Word k = AAS ++ S^(3k+6) ++ A^(3k+6) ++ (SA)^(3k^2+8k+1) ++ SS` satisfies:
   - coherent `SeededReplay` realizable at clock `0` (hence passes ALL static prefix/freshness filters, including `E-759` and all 12 static filters of `E-791`),
   - NEVER occurs at ANY clock `s ≥ 1` of ANY coherent `SeededReplay`,
   - NEVER occurs at ANY clock `s : Nat` of `Recaman.Basic.a`,
   - reaches arbitrary negative excursion depth `-(3k + 5)` at step `3k + 9`.
4. **Initial-`S` and initial-`SS` dynamic separation (`initial_S_dynamic_separation_witnesses`)**:
   Both `initialSWitnessI` (`SAAAASS ++ S^8 A^8 (SA)^5 SS`, len `35`, Type-I `A`-block) and `initialSWitnessII` (`SSA^6SSS ++ S^{10} A^9 (SA)^2 SS`, len `36`, Type-II `A`-block) are clock-`0` coherent-greedy realizable, have no coherent 1-step predecessor (`s ≥ 1`), and NEVER occur at ANY clock `s : Nat` of `Recaman.Basic.a`.

## 2. Dependencies

- `Recaman.Basic` (`a`, `stateAt`, `State`)
- `Recaman.SeededReplay` (`run`, `value`, `seen`, `base`)
- `Recaman.CoherentGreedyFreshness` (`E-798`: `Fw`, `Ar`, `TypeIFresh`, `TypeIIFresh`, `seeded_replay_typeIFresh`, `seeded_replay_typeIIFresh`, `canonicalOrbitSign`, `canonicalOrbitSign_eq_replaySign`)

## 3. Falsifier / Discovery-Holdout Computation

- Script: `docs/data/depth_general_20261128/dynamic_predecessor_obstruction_audit.py`
- Command: `python3 docs/data/depth_general_20261128/dynamic_predecessor_obstruction_audit.py`
- Results:
  - Exhaustive len `1..8` (`386` fresh words out of `510`): exact Lean large-base constructor `(M, b, v₀, freeBlockers)` and 1-step predecessor criteria (`BlocksSPredecessor`, `BlocksAPredecessorI`, `BlocksAPredecessorII`) match `100%`.
  - Discovery `k = 0..10` and Holdout `k = 11..20` for `e779Word k`: `E-759 = (0, 0)`, exact clock-0 replay verified, both `S`- and `A`-predecessors blocked, `0` occurrences in `a[0..5000]`.
  - `initialSWitnessI` (len `35`, Type-I) and `initialSWitnessII` (len `36`, Type-II): `E-759 = (0, 0)`, exact clock-0 replay verified, `0` occurrences in `a[0..5000]`.
  - Negative control (`"AAS"`): blocks `S`-predecessor only (`(True, False, False)`); `"A" ++ "AAS"` is `E-759 = (0, 0)` and realizable at `s ≥ 1`.
  - Structural falsifier discovery: for `SSA`-headed words, `SSA` already visits `(Fw, Ar) = (-1, -1)`, so `TypeIFresh` FORBIDS any later subtraction landing at `(-1, 0)` (Type-I `A`-blocking is impossible on `SSA...`!); therefore `initialSWitnessII` genuinely requires **Type-II `(-2, 0)`** blocking!

## 4. Lean Verification & Independent Audit

- Module: `Recaman/DynamicPredecessorObstruction.lean` (`9` public theorems in `Recaman/Audit.lean`, `0` warnings, `0` `sorry`/`admit`/`native_decide`/custom axioms).
- `python3 scripts/harness_gate.py --lint-module Recaman/DynamicPredecessorObstruction.lean`: `27/28` substantive theorems (all `9` public theorems `SUBSTANTIVE`).
- `python3 scripts/harness_lean.py --vacuity-row E-801`: `0 flagged, 0 unknown, 9 theorems`.
- Statement audit: `docs/statement_audits/E-801.md`.

## 5. Explicit Non-Claims & Next Decision

- Does **NOT** prove surjectivity (`E-001`), finite excursion (`E-067`), `C1`, `Q`, `H`, `SL`, or that `E-799`'s `Δ = 2` coherent cascade is excluded by 1-step predecessor checks (in fact `E-799`'s `B_1` passes 1-step predecessor checks for BOTH `S` and `A`).
- Next decision: formalize genuinely different arbitrary-depth numeric / fresh-source mechanisms directly on `SeededReplay` and `Recaman.Basic.a` (such as `E-761` candidate-band rank potential and `E-760` fresh same-source hit spacing), and test whether multi-drift or non-periodic coherent cascades can improve `ρ_greedy ∈ [√(7/3), 5/3]`.
