# Hypothesis card: Brief freshness and harness regression repairs

- ID: `H-20261021-02`
- Owner: Codex, environment implementation session
- Created: 2026-10-21 JST
- Status: `COMPUTED`
- Research branch: engineering maintenance; no new mathematical claim

## Exact statement

対象は revision `5606b64d27290a9959e1dbf19d5e7c58840a0a85` に対する今回の作業木差分。
固定した次の有限検査を満たすことを実装の受入条件とする。

1. brief の正本の研究単位・証拠ラベル・宣言件数を変えた各fixtureで、次回呼出しが変更を表示する。
2. G5 の未記入テンプレート、定理文のみ、G2 の仮定を結論の連言成分に含む定理＋実内容定理の混合行を、それぞれ G5・G5・G2 で拒否する。
3. 既存台帳・中心ラベルと、名前付き仮説を持つ条件付き定理の正常例を通す。
4. 回帰検査は実台帳・実監査ファイルを書き換えず、`make test` と CI の実行経路に入る。

これは有限のソフトウェア検査であり、意味整合性を全て決定できるという量化ではない。

## Why it would matter

- Frontier obligation discharged: なし。古い研究課題の固定表示と、監査未完了の受理経路を修正する。
- Stronger than an existing identity or equivalent reformulation because: 該当なし。
- Smallest useful consequence: 今回の受理漏れ3件を、将来の検査器変更でも自動検出できる。

## Provenance and dependencies

- Definitions used: `CURRENT_FRONTIER.md` の `Research brief` 節、証拠台帳、中心ラベル pin、G2/G5。
- Lean theorems used: 回帰fixtureは既存の実在symbolを参照。新しいLean定理は追加しない。
- Unverified mathematical assumptions: なし。条件付き結果の仮説を自動的に排除したとは扱わない。
- Literature source or analogy: [先行監査](RESEARCH_ENVIRONMENT_AUDIT_2026-10-21.md)。今回の実装は記入完了と既知の空虚性パターンの検査であり、ShadowBench の双方向意味検査を実装したものではない。

## Falsification plan

- Small and boundary cases: 未記入・部分記入・重複回答・署名改変・別節の引用・code block内だけの回答・reviewer未記入／日付欠落。
- Adversarial or weakened-history model: G3を満たす別定理とG2違反定理の混合。数学的historyモデルは対象外。
- Discovery range: 先行監査の3件。
- Frozen holdout range: なし。固定した回帰集合の検証であり、未知の誤仕様に対する検出率は推定しない。
- Maximum one permitted repair: 数学の予想修理は行わない。実装の互換性問題は正常例を追加して修正する。
- Stop condition: 固定回帰・既存台帳・全体検証の通過で今回の変更を止める。研究moduleの追加へ進まない。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-10-21 | `COMPUTED` | `make test` | brief 5 tests・harness 18 tests、404 build jobs、2,652公理監査、計算回帰3本、manifest全通過。exit 0 |
| 2026-10-21 | `COMPUTED` | `python3 docs/data/harness_repairs_20261021/compare_regressions.py` | 旧gateでは3件とも回帰assertionが失敗、現gateでは3件とも通過 |
| 2026-10-21 | `COMPUTED` | `bash scripts/test_harness_gates.sh` を2本同時実行 | 両方exit 0、実監査ファイル全件と台帳のhash不変 |
| 2026-10-21 | `COMPUTED` | `ruby -e 'require "yaml"; YAML.parse_file(".github/workflows/ci.yml")'`、`bash -n scripts/test_harness_gates.sh`、`git diff --check` | 構文・差分検査通過。GitHub上のjob実行ではない |

exact output と source hash は [検証データ](data/harness_repairs_20261021/validation.json)、
[make test の全出力](data/harness_repairs_20261021/make_test.log)、
[旧版との比較出力](data/harness_repairs_20261021/regression_comparison.txt) を参照。

## Semantic audit

- Informal statement implies formal statement: CLIの終了コードと出力を直接検査する。Lean化なし。
- Formal statement implies intended consequence: 今回の固定例の拒否、現在の正常例の受理を示す範囲に限定する。
- Counterfactual examples that should make the statement false: 先行監査の三つの受理漏れ。旧版で実際にテスト失敗を確認した。
- Could the theorem be proved from weaker or vacuous assumptions?: 数学的定理は証明していない。G5のyes/noの真偽やreviewer本人性は引き続き監査対象。
- Are reachability, freshness, time order, or actual-orbit provenance accidentally omitted?: 数学的statementを変更していない。
- Roles: proposerは有限受入条件を固定、falsifierは正常例と敵対的fixture、formalizerはCLI実装と回帰、auditorは旧版比較・並行実行・全体検証を担当。同一セッションの検査。

## Decision

- Continue / formalize / refute / stop: 今回の実装範囲を完了して stop。
- Changed files: `scripts/dev_tool.py`、`scripts/harness_gate.py`、`scripts/test_harness_gates.sh`、新しいPythonテスト2本、`Makefile`、CI workflow、frontierのbrief節、再現手順、監査4件の回答欄、本カードと検証データ。
- Failed attempts / compatibility: 既存監査4件の定理別選択肢が未記入だったため、既存総括・署名・証明との照合を記録して回答を整理。日付が次行にある既存reviewer欄も正常例として維持した。
- Remaining uncertainty: GitHubのUbuntu/macOS matrixは設定済みだがリモート実行は未確認。G2/G5の構文heuristicは未知の意味のすり替えを網羅しない。
- Next decision: 将来の研究単位の変更時は正本の `Research brief` 節を同期する。未知の受理漏れを発見したら最小fixtureを追加し、正当な条件付き結果を通す検査も維持する。
- Reopen only if: 新しい受理漏れ・誤拒否、またはCI実行上の不具合が見つかった場合。
