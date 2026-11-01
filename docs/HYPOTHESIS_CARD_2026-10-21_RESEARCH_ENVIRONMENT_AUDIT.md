# Hypothesis card: Research environment audit

- ID: `H-20261021-01`
- Owner: Codex, environment audit session
- Created: 2026-10-21 JST
- Status: `REFUTED`
- Research branch: engineering audit; no mathematical frontier claim

## Exact statement

対象revision `5606b64d27290a9959e1dbf19d5e7c58840a0a85` の G5 について、
実在する実内容定理を引用する新規 `PROVED-LEAN` 行 r の全てに対し、
監査ファイルが定理文のみ、または三項目と reviewer が未記入なら
`harness_gate.py --check-registry` は非ゼロで終了する、と仮定して検査する。
対象は有限のソフトウェア検査であり、Recamán 数列上の予想ではない。

## Why it would matter

- Frontier obligation discharged: なし。意味監査の完了を機械的に強制できるかを判定する。
- Stronger than an existing identity or equivalent reformulation because: 該当なし。
- Smallest useful consequence: 不完全な監査を受理するなら、研究自動化の前に G5 を補強する。

## Provenance and dependencies

- Definitions used: AGENTS.md、AI_RESEARCH_PROTOCOL.md の G1–G5、既存 gate の exit code。
- Lean theorems used: 新証明には使用しない。fixture の既存 symbol は reproducible script を参照。
- Unverified mathematical assumptions: なし。
- Literature source or analogy: [ShadowBench](https://arxiv.org/abs/2608.29270v3) の意味整合検査。

## Falsification plan

- Small and boundary cases: 正常な registry、既存負例テスト、未記入テンプレート、定理文のみ。
- Adversarial or weakened-history model: 意味監査の記入条件を除いた fixture。履歴モデルは扱わない。
- Discovery range: 上記二つの不完全 G5 fixture。
- Frozen holdout range: なし。今回は有限再現による反証であり、一般的な検出性能は推定しない。
- Maximum one permitted repair: 今回は修理しない。改善案のみを報告する。
- Acceptance: fixture、command、revision、exact output を保存し、受理／拒否を特定する。
- Stop condition: 一つの不完全 fixture が exit 0 なら仮説を `REFUTED` として監査を終える。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-10-21 | `COMPUTED` | `python3 docs/data/environment_audit_20261021/reproduce.py` | 未記入テンプレートと定理文のみ、いずれも exit 0。exact output は `reproduction.json` |
| 2026-10-21 | `REFUTED` | 同上 | G5 が監査記入完了を要求するという上記仮説は偽 |
| 2026-10-21 | `COMPUTED` | `./scripts/check.sh` | 404 jobs、2,652 公理監査、全通過。`validation.txt` に要約 |

## Semantic audit

- Informal statement implies formal statement: gate の終了コードという直接観測に一致する。Lean 化なし。
- Formal statement implies intended consequence: 二つの fixture で受理されたことだけを結論する。
- Counterfactual examples that should make the statement false: 定理文を引用しているが監査の回答がないファイル。
- Could the theorem be proved from weaker or vacuous assumptions?: 定理の証明は行っていない。
- Are reachability, freshness, time order, or actual-orbit provenance accidentally omitted?: 対象外。
- Roles: proposer は G5 の強制範囲を設定、falsifier は隔離 fixture、formalizer は Lean 化不要と判断、auditor は実装と exit code を照合。同一セッションであり独立査読済みとは扱わない。

## Decision

- Continue / formalize / refute / stop: 上記仮説を refute、数学研究枝の追加は stop。
- Reason: G5 は署名の引用を照合するが三回答・reviewer の記入を検査していない。
- Reopen only if: gate 修正時、正常例と今回の反例を固定した回帰試験で再判定する。
- Handoff: [監査報告](RESEARCH_ENVIRONMENT_AUDIT_2026-10-21.md)。数学の台帳・proof map の更新は不要。
