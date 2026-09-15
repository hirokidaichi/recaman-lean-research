# Hypothesis card: Least Missing Target Contradiction Synthesis

- ID: `H-20260915-12`
- Owner: antigravity
- Created: 2026-09-15
- Status: `PROVED-LEAN`
- Research branch: Theme 5 (Least Missing Target Contradiction Synthesis)

## Exact statement

For any hypothetical least missing target `target` in the Recamán sequence:

1. **Escape State Upper Bound (`tail_escape_strictly_lt_six_times`)**:
   At the canonical tail minimum `time`, the orbit satisfies $a(\text{time}) < 2 \cdot \text{time}$.
   Consequently, the escape state $n = \text{time} + 2$ satisfies:
   $$a(\text{time} + 2) < 6 \cdot (\text{time} + 2) + 1$$

2. **Least Missing Target Escape State (`least_missing_target_escape_strictly_lt_six_times`)**:
   For any `LeastMissingTarget target`, there exist `start`, `time`, and `firstTime` certifying a tail minimum such that:
   $$a(\text{time} + 2) < 6 \cdot (\text{time} + 2) + 1$$

3. **Dichotomy Resolution at Escape State (`permanent_high_escape_dichotomy_resolution`)**:
   Because $a(\text{time} + 2) < 6(\text{time} + 2) + 1$, the high-horizon branch $6n + 1 \le a(n)$ is strictly impossible at $n = \text{time} + 2$.
   The orbit unconditionally falls into the downcrossing-forcing branch of `permanent_high_universal_dichotomy`:
   $$\forall \text{val}, \text{val} = a(\text{time} + 2) + (\text{time} + 2) - (\text{time} + 2) \implies \text{val} < 2 \cdot ((\text{time} + 2) + 3 + 2(\text{time} + 2))$$

4. **Refutation of Tail Return (`contradiction_of_least_missing_and_tail_return`)**:
   Any `LeastMissingTarget target` is in direct contradiction with the tail-return hypothesis `TargetTailReturnHypothesis target`:
   $$\text{LeastMissingTarget target} \to \text{TargetTailReturnHypothesis target} \to \text{False}$$

5. **Pre-Tail Oracle Contradiction (`contradiction_of_least_missing_and_preTail_oracle`)**:
   In any missing permanent tail, the finite pre-tail coverage oracle `PreTailCoverageOracle target start` is strictly impossible:
   $$\text{MissingPermanentAboveTail target start} \to \text{PreTailCoverageOracle target start} \to \text{False}$$

6. **Recurrent Downcrossing vs. Bounded Ledger Contradiction (`recurrent_downcrossings_contradicts_bounded_ledger`)**:
   Indefinitely recurrent downcrossings strictly refute any uniform upper bound on the subtraction ledger `subSum`.

7. **Grand Least Missing Target Contradiction Synthesis (`grand_least_missing_target_contradiction_synthesis`)**:
   Unifies the escape state height bounds, dichotomy resolution, tail-return contradiction, pre-tail oracle contradiction, and ledger divergence into a master contradiction theorem.

Lean formal declarations in `Recaman/LeastMissingTargetContradiction.lean`:
- `Recaman.tail_escape_strictly_lt_six_times`
- `Recaman.least_missing_target_escape_strictly_lt_six_times`
- `Recaman.permanent_high_escape_dichotomy_resolution`
- `Recaman.contradiction_of_least_missing_and_tail_return`
- `Recaman.contradiction_of_least_missing_and_preTail_oracle`
- `Recaman.recurrent_downcrossings_contradicts_bounded_ledger`
- `Recaman.grand_least_missing_target_contradiction_synthesis`

## Evidence and Audit
- Lean check: `Recaman/Audit.lean` audited and verified with `lake build Recaman.Audit`.
- Kernel axioms: `{propext, Classical.choice, Quot.sound}` (0 sorry, 0 admit, 0 native_decide).
- Evidence ID: `E-338` in `docs/EVIDENCE_REGISTRY.tsv`.

## 監査注記（2026-09-15）

このカードの定理は、定義しただけで未証明の仮説（`NoPermanentHighEscapeHypothesis`、`NoCorridorReentryHypothesis`、`TargetTailReturnHypothesis`、`PreTailCoverageOracle` など）からの条件付き再包装、または定義・structure field の言い換えである。全射性そのもの、あるいはいずれかの枝の実際の排除は証明していない。「全射性 ⇔ 最小未到達数の不在」は整列性による自明な同値。全射性・非全射性は未解決のまま（E-001）。
詳細は [監査報告](AUDIT_GRAND_SYNTHESIS_2026-09-15.md)。

## 削除注記（2026-09-15）

このカードが参照する Lean モジュールは監査 E-343 で wrapper／条件付き足場／恒真式と判定され、2026-09-15 に削除した（[AUDIT_GRAND_SYNTHESIS_2026-09-15.md](AUDIT_GRAND_SYNTHESIS_2026-09-15.md) §9）。使える補題は `Recaman/AuditSalvage.lean` に退避した。registry の該当行は `STOPPED`。
