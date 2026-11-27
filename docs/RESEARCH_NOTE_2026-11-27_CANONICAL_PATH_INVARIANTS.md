# Research Note: Global Clock-0 Ledger, Parity-Partition, Cut-Connectivity, and Multi-Point Cluster Invariants (`E-795`)

**Date**: 2026-11-27  
**Parent cycle**: `R-20261127-02`  
**Lean module**: [`Recaman/CanonicalPathInvariants.lean`](../Recaman/CanonicalPathInvariants.lean) (`E-795 PROVED-LEAN`)  
**Audit script**: [`docs/data/depth_general_20261127/canonical_path_invariants_audit.py`](data/depth_general_20261127/canonical_path_invariants_audit.py)  
**Evidence row**: `E-795` (`PROVED-LEAN`)

## 1. Summary

Following the `E-791` stop verdict on static local seen-set filtering (`f1..f12`), we formalize eight unconditional global clock-0 structural laws of the canonical Recamán trajectory `Recaman.Basic.a` and `valuesThrough b` in [`Recaman/CanonicalPathInvariants.lean`](../Recaman/CanonicalPathInvariants.lean) (0 warnings, `0 flagged / 0 unknown` vacuity lint):

1. **Exact top-triangular subtraction complement (`subSum_add_upperTri_complement_le`)**:
   $$\mathrm{subSum}(b) + \mathrm{upperTri}\big(b - \mathrm{subCount}(b)\big) \le \mathrm{upperTri}(b),$$
   strictly sharpening `SubtractionLedger.subSum_le_mul_subCount` (`subSum b ≤ b * subCount b`) and sharp with equality at `b = 4` (`4 + 6 = 10`).
2. **Subtraction freshness cover bound (`subCount_succ_le_cover_length`)**:
   Every subtraction step `t` lands on a strictly unseen value (`a t ∉ valuesThrough (t - 1)`), and `a 0 = 0`, so every cover `V` of `valuesThrough b` satisfies `subCount b + 1 ≤ V.length`.
3. **Unconditional quadratic distinct-seen cardinality bound (`canonical_distinct_cover_quadratic_bound`)**:
   Combining (1), (2), and `ledger_identity` (`a b + 2 * subSum b = upperTri b`) yields, for EVERY `b : Nat` and EVERY cover `V` of `valuesThrough b` (with zero corridor assumptions):
   $$2 \cdot \mathrm{upperTri}\big(b + 1 - |V|\big) \le \mathrm{upperTri}(b) + a(b),$$
   forcing $|V| \ge (1 - 1/\sqrt{2}) b \approx 0.2929 b$ whenever $a(b) = o(b^2)$.
4. **Exact mod-4 parity-partition capacity (`canonical_even_visit_count_le`, `canonical_odd_visit_count_le`)**:
   Every `Nodup` list `L ⊆ valuesThrough b` of even (resp. odd) visited values has length at most `evenClockCount b` (clocks `≡ 0, 3 mod 4`) resp. `oddClockCount b` (clocks `≡ 1, 2 mod 4`), attaining exact equality at `b = 10` (`5/5` evens, `6/6` odds).
5. **Global cut-crossing connectivity (`canonical_cut_crossing_step`)**:
   For any predicate `S : Nat → Prop` with `S 0` and `∃ v ∈ valuesThrough b, ¬ S v`, there exists a clock `1 ≤ t ≤ b` crossing `S` (`S (a (t - 1)) ∧ ¬ S (a t)`) with `stepDist (a (t - 1)) (a t) = t`.
6. **Interior cluster entry-exit span (`canonical_interior_cluster_entry_exit_span`)**:
   For any interior cluster `S` (`¬ S 0`, `¬ S (a b)`) containing a nonempty `Nodup` `L ⊆ valuesThrough b` at boundary separation `≥ θ`, there exist `1 ≤ t₁ < t₂ ≤ b` entering/exiting `S` with `θ ≤ t₁`, `θ ≤ t₂`, and `θ + L.length ≤ b`.
7. **Unified disjoint multi-point cluster clock budget (`canonical_disjoint_clusters_clock_budget`)**:
   For any list `Cs : List (List Nat)` of nonempty `Nodup` interior clusters inside `valuesThrough b` with boundary distance `≥ θ` and mutual distance `> b`,
   $$\mathrm{Cs.length} + \sum_{C \in \mathrm{Cs}} |C| \le b + 1 - \theta,$$
   strictly unifying and generalizing both `E-781`'s single-tail capacity and `E-790`'s isolated-vertex `2 * m ≤ b + 1 - θ` to arbitrary multi-point clusters (with zero redundant `1 ≤ θ` or `θ ≤ b` side hypotheses).

## 2. Reproducible Audit Summary

Command: `PYTHONDONTWRITEBYTECODE=1 python3 docs/data/depth_general_20261127/canonical_path_invariants_audit.py`
- Real Recamán `b = 0..1500`: `55,131` cut checks, `696` cluster checks, `0` violations across all 8 theorems.
- Sharpness: `b = 4` (`4 + 6 = 10 == upperTri 4`); `b = 10` (`even = 5/5, odd = 6/6`).
- Negative controls: `|V| = 25` at `b = 100, a_b = 50` fails quadratic bound (`5852 > 5100`); `7` evens at `b = 10` fails mod-4 cap (`7 > 5`); two 4-point clusters at `b = 20, θ = 15` pass `E-790` (`4 ≤ 6`) but fail multi-point cluster budget (`10 > 6`).
- Lean 4: `lake build Recaman Recaman.Audit` (`1053` jobs, `0` warnings), `harness_gate.py --lint-module` (`21/23` substantive, `8/8` public), `harness_lean.py --vacuity-row E-795` (`0 flagged, 0 unknown, 8 theorems`).

## 3. Scope Boundary

These are unconditional structural theorems of the actual clock-0 canonical sequence `Recaman.Basic.a`. Because `E-791`'s variable-step bridge (`|V| ≈ b/2`, balanced `[0..b/2]`, `O(N)` clusters) also satisfies them, `E-791`'s `STOPPED` status for static seen-set filtering of `E-759` words remains intact; separating canonical Recamán from `E-759` still requires genuine clock-0 dynamical / deterministic-recurrence reachability.
