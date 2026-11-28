# Hypothesis Card: `H-20261127-13` (`E-795` — Global Clock-0 Ledger, Parity-Partition, Cut-Connectivity, and Multi-Point Cluster Invariants on `Recaman.Basic.a`)

- **ID**: `H-20261127-13`
- **Date**: 2026-11-27
- **Parent cycle**: `R-20261127-02` (30-min extension)
- **Track**: Genuinely distinct global clock-0 invariants on the canonical Recamán trajectory `Recaman.Basic.a` / `valuesThrough b` (beyond the 12 static seen-set filters stopped by `E-791`)
- **Status**: `PROVED-LEAN` (`E-795`, `Recaman/CanonicalPathInvariants.lean`)

## 1. Bounded Research Question

Can we unconditionally prove in Lean 4 on the canonical Recamán sequence `Recaman.Basic.a` (at arbitrary clock `b : Nat`, with zero corridor hypotheses):
1. Exact top-triangular subtraction complement bound `subSum b + upperTri (b - subCount b) ≤ upperTri b` and subtraction-freshness cover bound `subCount b + 1 ≤ V.length`, yielding the first unconditional quadratic lower bound on distinct visited values `2 * upperTri (b + 1 - V.length) ≤ upperTri b + a b` (forcing `|V| ≥ (1 - 1/√2) b` whenever `a b = o(b^2)`)?
2. Exact mod-4 parity-partition capacity (`L.length ≤ evenClockCount b` and `L.length ≤ oddClockCount b`)?
3. Global cut-crossing connectivity across arbitrary subsets `S : Nat → Prop` separating `0` from `valuesThrough b`?
4. Interior cluster entry-exit span (`θ + L.length ≤ b`) and unified disjoint multi-point cluster clock capacity `Cs.length + (Cs.map List.length).sum ≤ b + 1 - θ`, strictly generalizing both `E-781` and `E-790`?

## 2. Evidence & Falsification

- Script `docs/data/depth_general_20261127/canonical_path_invariants_audit.py`:
  - Real Recamán `b = 0..1500`: all 8 theorems verified (`55,131` cut checks, `696` cluster checks, `0` violations).
  - Exact zero-slack sharpness: `b = 4` (`subSum 4 + upperTri 3 = 4 + 6 = 10 == upperTri 4`); `b = 10` (`even = 5/5`, `odd = 6/6`).
  - Negative controls: `|V| = 25` at `b = 100, a_b = 50` passes `|V| ≤ b + 1` & parity but fails quadratic bound (`5852 > 5100`); `7` evens at `b = 10` fails mod-4 cap (`7 > 5`); two 4-point clusters at `b = 20, θ = 15` pass `E-790` (`4 ≤ 6`) but fail multi-point cluster budget (`10 > 6`).
- Lean 4: `Recaman/CanonicalPathInvariants.lean` builds cleanly (`1053` jobs, `0` warnings), `21/23` substantive (`8/8` public substantive), `0 flagged / 0 unknown` vacuity lint, standard axioms only.

## 3. Scope & Non-Claims

Proves genuine unconditional global laws of `Recaman.Basic.a` at every clock `b`. Explicitly notes that `E-791`'s variable-step bridge (`|V| ≈ b/2`, balanced `[0..b/2]`, `O(N)` clusters) still passes these invariants, so `E-791`'s `STOPPED` verdict on static seen-set filtering of `E-759` finite words stands unchanged. Does not prove `C1`, `E-001`, `E-067`, `E-070`, or surjectivity.
