# Research Note: Complete Bi-Directional E-759 Characterization & Arbitrary-Depth Dynamic Predecessor Separation (E-801)

- **Date**: 2026-11-28
- **Evidence**: `E-801 PROVED-LEAN` (`Recaman/DynamicPredecessorObstruction.lean`)
- **Audit script**: `docs/data/depth_general_20261128/dynamic_predecessor_obstruction_audit.py`
- **Statement audit**: `docs/statement_audits/E-801.md`

## 1. Motivation & Context

In `E-798` (`Recaman/CoherentGreedyFreshness.lean`), we proved the **necessity** direction of `E-759` unconditionally in Lean 4: every coherent `SeededReplay` (with `st.value ∈ st.seen`) and every clock window of the canonical Recamán orbit `Recaman.Basic.a` satisfies both `TypeIFresh` and `TypeIIFresh`.

Three critical open questions remained at the paper level:
1. **Sufficiency of `E-759` in Lean 4**: Is `(TypeIFresh ∧ TypeIIFresh)` ALSO **sufficient** for clock-`0` realization by an actual coherent `SeededReplay` (with `st.value ∈ st.seen`), making `E-759` an exact bi-directional characterization of static coherent-greedy realizability?
2. **Arbitrary-depth dynamic separation in Lean 4 (`E-779` upgrade)**: `E-779` (`PROVED-PAPER`) exhibited an infinite family `e779Word k` of arbitrary negative depth `-(3k + 5)` that is `E-759 = (0, 0)` (hence passes ALL static prefix/freshness filters) yet has NO coherent 1-step predecessor and hence NEVER occurs at ANY clock of `Recaman.Basic.a`. Upgrading this to `PROVED-LEAN` establishes in Lean 4 that static greedy filters alone cannot capture the canonical orbit, and that dynamic lookbehind strictly strengthens them at arbitrary excursion depth.
3. **Initial-`S` / initial-`SS` words (`E-779` open question)**: Can an initial-`S` or initial-`SS` word (matching the excursion head of a negative-depth block) exhibit the exact same dynamic separation?

## 2. Main Formalized Results (`E-801 PROVED-LEAN`)

### 2.1 Explicit Large-Base Constructor & Complete `E-759` Equivalence

For any `w : List Bool` of length `N = w.length`, set:
- `M := 2 * (N + 1) ^ 2 + 2`,
- `b := 2 * M + N + 2`,
- `v₀ := (N + 2) * (b + 1) + M`,
- `freeBlockers w := { v₀ + (Fw t - 2) * (b + 1) + Ar t | t < N, w[t] = true }` (converted to `Nat`).

Because `|Ar t| ≤ N(N + 1) / 2 < M` and `b + 1 > 2M + N + 2`, the affine map `(h, a) ↦ v₀ + h * (b + 1) + a` is strictly injective on `[-N-2, N+2] × [-M, M]`. Therefore:
- Every addition step `w[t] = true` has its rejected subtraction candidate `v_t - (b + t + 1) = v₀ + (Fw t - 2)(b + 1) + Ar t` placed in `freeBlockers w` (so `st.seen` forces an addition).
- Every subtraction step `w[t] = false` lands at `v_{t+1} = v₀ + (Fw t - 1)(b + 1) + Ar t`, which is positive (since `Fw t - 1 ≥ -(N + 1)` and `v₀ = (N + 2)(b + 1) + M`), distinct from every earlier visited value `v_i` (`i ≤ t`) by `TypeIFresh`, and distinct from every element of `freeBlockers w` by `TypeIIFresh`.

This yields **`seeded_replay_realizes_of_fresh`** and, combined with `E-798`, the exact equivalence **`seeded_replay_realizes_iff_fresh`**:
```lean
(∃ b st, st.value ∈ st.seen ∧ MatchesAt (replaySign b st) 0 w)
  ↔ (TypeIFresh (wordSign w) w.length ∧ TypeIIFresh (wordSign w) w.length)
```

### 2.2 Dynamic 1-Step Predecessor Obstructions

Prepending a single step `p ∈ {S, A}` at clock `s - 1` shifts every subsequent subtraction landing `(wordHeight w (q + 1), areaW (w.take (q + 1)))` in `w` according to `shift_fw_and_pot`:
- **Prepending `S` (`f (s - 1) = false`, `BlocksSPredecessor`)**: a subtraction step `w[q] = false` with `wordHeight w (q + 1) = 1` and `areaW (w.take (q + 1)) = q + 2` shifts to `Fw f (s + q + 1) = Fw f (s - 1)` with equal `floorPotential`, colliding with the visited value at clock `s - 1` and violating `TypeIFresh` (`blocksSPredecessor_forbids_S_before`).
- **Prepending `A` (`f (s - 1) = true`)**:
  - **Type-I `A`-block (`BlocksAPredecessorI`)**: a subtraction step `w[q] = false` with `wordHeight w (q + 1) = -1` and `areaW (w.take (q + 1)) = -(q + 2)` shifts to `Fw f (s + q + 1) = Fw f (s - 1)` with equal `floorPotential`, colliding with the visited value at clock `s - 1` and violating `TypeIFresh`.
  - **Type-II `A`-block (`BlocksAPredecessorII`)**: a subtraction step `w[q] = false` with `wordHeight w (q + 1) = -2` and `areaW (w.take (q + 1)) = -2 * (q + 2)` shifts to `Fw f (s + q + 1) = Fw f (s - 1) - 1` with equal `floorPotential`, colliding with the **rejected subtraction candidate of the prepended `A` at clock `s - 1`** and violating `TypeIIFresh` (`blocksAPredecessor_forbids_A_before`).

Combining both obstructions yields:
- **`no_predecessor_forbids_nonzero_clock_replay`**: no coherent `SeededReplay` can match `w` at ANY clock `s ≥ 1`.
- **`no_predecessor_forbids_all_canonical_clocks`**: since `Recaman.Basic.a` begins `A, A, A` (`a 0 = 0, a 1 = 1, a 2 = 3, a 3 = 6`), any word with `w[0] = false` OR `w[2] = false` cannot match at `s = 0` either, and hence NEVER occurs at ANY clock `s : Nat` of `Recaman.Basic.a`.

### 2.3 Arbitrary-Depth `e779Word k` Family & Initial-`S`/`SS` Witnesses

1. **`e779Word k = AAS ++ S^(3k+6) ++ A^(3k+6) ++ (SA)^(3k^2+8k+1) ++ SS`** (for ALL `k : Nat`):
   - `e779Word_fresh` proves `TypeIFresh ∧ TypeIIFresh` analytically across all 5 phases for arbitrary `k : Nat`.
   - `t = 2` (`S` at end of `AAS`) gives `(Fw, Ar) = (1, 0)` (`BlocksSPredecessor`).
   - `t = L - 1` (final `S` of `SS`) gives `(Fw, Ar) = (-1, 0)` (`BlocksAPredecessorI`).
   - At `t = 3k + 9`, `wordHeight (e779Word k) (3k + 9) = -(3k + 5)`, proving arbitrary negative depth.
2. **Initial-`S` and Initial-`SS` Witnesses (`initial_S_dynamic_separation_witnesses`)**:
   - `initialSWitnessI` = `SAAAASS ++ S^8 A^8 (SA)^5 SS` (length `35`): starts with `S`, `E-759 = (0, 0)`, blocks `S`-pred at `t = 6` (`(1, 0)`) and `A`-pred via **Type-I** at `t = 34` (`(-1, 0)`).
   - `initialSWitnessII` = `SSA^6SSS ++ S^{10} A^9 (SA)^2 SS` (length `36`): starts with `SS`, `E-759 = (0, 0)`, blocks `S`-pred at `t = 10` (`(1, 0)`) and `A`-pred via **Type-II** (`(-2, 0)`). Notably, because `SSA` already visits `(-1, -1)`, `TypeIFresh` makes Type-I `A`-blocking impossible for every `SSA`-headed word — proving that **Type-II blocking is genuinely necessary** for initial-`SS` dynamic separation.

## 3. Audit & Verification

- `lake build Recaman.DynamicPredecessorObstruction Recaman.Audit`: exit `0`, `0` warnings in `DynamicPredecessorObstruction.lean`, standard axioms `[propext, Classical.choice, Quot.sound]` only.
- `python3 scripts/harness_gate.py --lint-module Recaman/DynamicPredecessorObstruction.lean`: `27/28` substantive theorems (`9/9` public theorems `SUBSTANTIVE`).
- `python3 scripts/harness_lean.py --vacuity-row E-801`: `0 flagged, 0 unknown, 9 theorems`.
- `python3 docs/data/depth_general_20261128/dynamic_predecessor_obstruction_audit.py`: `ALL E-801 AUDITS PASSED`.
