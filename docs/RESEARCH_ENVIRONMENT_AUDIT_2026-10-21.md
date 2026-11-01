# 数学自動研究環境の監査と改善案

2026-10-21 JST。対象 revision: `5606b64d27290a9959e1dbf19d5e7c58840a0a85` と作業開始時の未コミット変更。

結論は、**Lean の検証基盤は動いているが、研究課題の鮮度と意味監査の完了を強制する経路に不備がある**。
最初に brief とゲートを修正し、既知反例を検索・実行する仕組みを整える。その後に探索速度を上げる順序を推奨する。
研究手順の原則は既存の [AI研究プロトコル](AI_RESEARCH_PROTOCOL.md) に既に揃っている。以下はその実装上の不足と、文献から追加できる仕組みである。

## 実際に確認した状態

`./scripts/check.sh`、`bash scripts/test_harness_gates.sh`、`make test-probes check-manifest` は全て exit 0。
404 build jobs、401 library modules の root 到達性、110 import contracts、378 evidence rows、2,652 宣言の公理監査が通過した。
402 という viewer の module 数は Audit を含む。167 行が `PROVED-LEAN`。
これは現在の作業木に対する検査であり、commit 単独のクリーンビルドではない。
出力要約は [validation.txt](data/environment_audit_20261021/validation.txt)、追加の反例試験は
[reproduce.py](data/environment_audit_20261021/reproduce.py) と [exact output](data/environment_audit_20261021/reproduction.json) に保存した。

Lean 4.33.1 の固定、外部 Lean package 不使用、禁止公理と proof escape の検出、中心命題の pin、
反証・停止を成果として保存する方針は維持する価値が高い。

## 優先して修正する不備

| 優先度 | 確認事項と影響 | 改善案と受入条件 |
|---|---|---|
| P0 | `scripts/dev_tool.py:45–85` の brief は frontier の存在だけ確認し、内容を読まず固定文を表示する。現在の SL・TS・S1 ではなく旧 T6 を次課題として出す。公理監査数も実測 2,652 に対し 1,743。E-176–178 の有限計算を established ground truth に置き、E-178 には台帳外の `CLOSED` 表示もある | 現在の work unit を一箇所で構造化し、brief はその参照・registry の label・署名・revision から生成する。正本を更新した fixture で brief も追随し、`COMPUTED` の有限範囲が消えないことを検査 |
| P0 | G5 は監査ファイル内の署名文字列だけを検査する。未記入テンプレートと定理文のみのファイルが両方受理された。未記入を落とすという仮説は `REFUTED` | 三項目の回答、条件付き仮説一覧、reviewer と対象revisionを構造化して必須化。今回の二例を拒否し、現在の正当な条件付き帰納補題は適切な説明付きで受理する。記入だけで意味の正しさが保証されるわけではない |
| P1 | G2 は `conjunct-is-hypothesis` を分類するが、個別の拒否条件に入れていない。別の実内容定理を同じ行に混ぜると、仮定を連言成分に含む定理も引用できる。隔離 fixture で exit 0 を再現 | G2 の個別違反と G3 の「少なくとも一本の実内容」を分ける。混合行の負例を追加。既存定理の数学的誤りという指摘ではなく、新規登録に対する規約と実装の不一致 |
| P1 | CI は `make test` を呼ぶが、その依存に `test_harness_gates.sh` がない。生の registry 検査は走るが、検査器の負例テストは走らない | gate tests を CI の fast job に含める。テスト内部の `sed -i ''` は macOS 形式なので Python 等へ置換して Linux でも確認する。Ubuntu での実行は今回未実施 |
| P1 | 既存 gate tests は実作業木に E-993.md を書き、終了時に `E-99[0-9].md` を一括削除する。並行実行・別作業のファイルと衝突し得る | 全fixtureを一時ディレクトリへ隔離する。二重実行しても作業木と互いのfixtureを変えないことを受入条件にする |
| P1 | `make test-probes` の自動回帰は旧 trace/certificate の三本。最新の line-capacity・SL・TS・S1 の反例群を標準テストとして呼ぶ経路はない | 既知反例の小さい corpus を追加し、候補はこれを通してから高価な全数探索へ進める。最近の研究ディレクトリにある個別の独立検算は残し、共通起動口から再利用する |
| P2 | 最新の実験群は `experiments/issue73_20261020` に163ファイル、対応 data に15ファイル。両ディレクトリ内に統一 `SHA256SUMS`・`run_metadata.json`・`commands.json`・README は見つからなかった。カードにはコマンドと結果があるため「再現不能」とまでは断定しない | 研究単位ごとに statement hash、source revision＋dirty diff hash、探索範囲、seed、実行command、exit code、出力hash、発見／holdout区分を一つの manifest に結合する |
| P2 | `register-evidence` は max ID + 1 の採番と複数ファイル書込みを行い、事前の全検証・排他・一括rollbackがない。競合の実行再現は今回は行っていない | まず変更予定を dry-run 出力し、一時コピー上で検証後に適用。採番と適用の競合を検出し、失敗時に半端な変更を残さない |

G5 の最小反例は、既存の実内容定理一つと署名だけの監査ファイルで成立する。
G2 の fixture は既存の `anchorBoundary_exitNormal_at_landing` を使用した。
その結論には仮定の `m ≤ y` と `FirstAt a y fy` が含まれ、別の実内容定理を併記すると通る。
どちらも一時ディレクトリ内の擬似 E-993 を使い、実台帳には登録していない。

中心ラベルの人間承認・30分間隔は現状ローカルhookにある。ローカルでは `core.hooksPath=.githooks` を確認した。
GitHub側の保護ブランチ・必須レビュー設定までは今回監査していない。
人間承認の強制を CI に移す際は、環境変数や自己申告の reviewer 名だけを本人性の証拠にしない。

## 最新の一次資料から取り入れる仕組み

### 1 意図した命題と形式命題の双方向チェック

[ShadowBench, 2026-08-29提出・09-05改訂](https://arxiv.org/abs/2608.29270v3) は、形式命題が意図を表す補助命題群を含意する向きと、
その連言から形式命題が従う向きを検査する SA-Pass を提案する。著者の一つの評価設定では compile 61.8% に対し SA-Pass 11.2%。
この数値は同ベンチマークの結果であり、このリポジトリの誤り率ではない。

ここへの提案は、重要な宣言で「量化範囲」「実軌道／抽象語」「必要仮定」「意図した帰結」の基準statementを先に固定し、
実装との含意を両方向で検査すること。全lagの主張を lag≤11 にすり替えた場合、逆向き・帰結の検査が失敗するようにする。
既知の反例を排除するか、削除が no-op にならないか、非空の適用例があるかも併用する。
shadow 自体の仕様が弱ければ通過するので、独立の意味監査は引き続き必要である。
補題を足すだけで難問の証明が得られるわけではなく、仕様のすり替えを検出する投資として位置付ける。

### 2 定理検索と停止枝検索を一つの研究パケットにする

[MathForm, 2026-08-14](https://arxiv.org/abs/2608.14221v1) は、関連定義・定理を集める retrieval planner と生成器を分離し、
compiler feedback と semantic consistency の両方で修正する。ここでは Mathlib 専用モデルの導入効果は未検証であり、
core Lean 中心の既存構成にそのまま適用できるとは限らない。

転用しやすいのは検索の構成である。`packet --claim ...` のような入口から、対象の正確な署名、必要定義、関連証拠label、
停止枝、最小反例、成功条件、停止条件をrevision付きで返す。既存の `search` と `decls` を基礎にできる。
宣言抽出はregexだけではなく elaborated type・参照定数を使う方式を検討する。
現在も E-378 の引用に equation-style theorem の証明枝が混入しており、署名抽出の限界が見える。

受入条件は、T6 の一般化要求から E-240 の純AAS反例と E-347 の no-op 注意を取り出せること、
現研究の H/EqClassW/SL から未証明 edge と C1/C2/TS の具体的義務を取り出せること。
巨大な履歴文書を読む負担は、初回の規約読込み後にこのパケットへ集約する。

### 3 探索器だけを改良し 評価器を固定する

[AlphaEvolve の数学研究報告, 2025-12-22改訂](https://arxiv.org/abs/2511.02864v3) は、候補programの生成と自動評価を反復し、
数理的構成の探索へ適用している。本件への適用は私たちの設計案であり、同論文が Recamán を解いたという意味ではない。

改善対象を一般的な「全射性証明生成」にせず、反例探索の分岐順序・状態圧縮・counterexample minimizer に限定する。
評価器、既知反例集合、凍結holdout、時間・メモリ予算は探索器に変更させない。
候補不等式→小さい反例→最小化→仮説の一回修理→別のholdout、という既存手順を機械的に結ぶ。
counterexample が減っただけで証拠を `PROVED-LEAN` へ上げない。

最新カードには H+ の長さ34反例、DF2 の長さ32反例、Φ′ の長さ56反例、a_y≤2 での C2′ 反例がある。
これらを候補評価の必須回帰にする。現在の受入候補は C1 の面積不等式 Q、C2 の窓位置制約、TS の個別義務であり、
どれを試すにしても [最新カード](HYPOTHESIS_CARD_2026-10-20_LINE_CAPACITY.md) の仮定を先に凍結する。
今回それらの数学的真偽は新たに判定していない。

### 4 解答生成と批判を分け 未解決を正常終了にする

[Aletheia, 2026-03-06改訂](https://arxiv.org/abs/2602.10177v3) は Generator・Verifier・Reviser を分け、試行回数上限を持つ。
自然言語で動作する研究agentであり、その verifier の承認を Lean kernel 検査と同視することはできない。
文献・計算toolの利用と人間の関与記録も重視している。

このリポジトリでは四役分離が既に規定されている。追加すべきなのは役の数より、反証passの実行証拠、
生成側の説明に依存しない監査、未解決のまま止めた理由の記録である。
別セッションの監査にはstatement・定義・既知反例を先に渡し、生成者の「解決した」という要約を判定根拠にしない。
中心ラベルの昇格は既存の人間判断を維持する。

[Station, 2026-09-14改訂](https://arxiv.org/abs/2608.23691v2) は、共有知識を蓄積する複数agentの数学探索を報告し、
対話・証明・検証コードを公開している。この研究からは再利用可能な知識記録を参考にできるが、
agent数を増やせばこの問題の進捗が増えるという結論は導けない。
独立な反例探索や文献調査だけを分離し、同じ未証明仮定の共有で見かけの合意を作らない。

### 5 往復翻訳は補助検査にとどめる

[Faithful Autoformalization via Roundtrip Verification and Repair, 2026-09-21改訂](https://arxiv.org/abs/2604.25031v3) は、
形式化→自然言語化→再形式化の同値性検査と局所修理を提案する。評価対象は法律の規則であり、数学や Lean での効果が
同じだとは確認されていない。定理を説明文へ戻して量化子・前提の脱落を見付ける補助手段としては試せるが、
二つの翻訳が同じ誤りを共有する場合に備え、前述の基準statementと反例を併用する。

## 効率化の導入順と判定

1. **brief の正本参照と gate tests の隔離・CI化。** 今回の三つの受理反例を拒否し、正当な既存結果を通すことを最初の完了条件にする。
   名前や tactic 数の規制を強くするだけでは、短い正しい証明まで落とし得る。意味の検査を追加する。
2. **研究パケットと反例corpus。** 同じ定義の再導入、停止枝の再開、有限結果の一般化を検出する小さなfixtureを固定する。
   反例は元の意図を変更した際にも再実行し、量化子・historyの変更を見えるようにする。
3. **run manifest と証明依存の接続。** カード・実験・出力・Lean signature を一つの hash chain にする。
   SAT/LP 等が出す候補certificateは、まず独立実装で確認し、数学的成果とする場合は健全性を証明した Lean checker へ渡す。
   任意のSAT結果や数値評価をそのまま証明にしない。既存 `OwnerFamilyLagEleven.check_sound` は再利用できる設計例。
4. **高速な局所形式化ループを測定する。** 作業中は対象moduleの `lake build`、区切りで既存full audit。
   CIの toolchain/build cache、時間上限、旧runの取消しを検討し、cold/warm時間を測る。今回、速度向上率は測定していない。
   [Lean REPL](https://github.com/leanprover-community/repl) はJSON経由のcommand/tactic状態操作を提供するため試験候補だが、
   Lean 4.33.1互換性と既存checkerとの整合を別環境で確かめてから採否を決める。
5. **研究成果の測定。** theorem数・commit数を報酬にせず、既知誤仕様の検出率、正当な定理の誤拒否、
   反例までの時間、同一停止枝の再提案回数、独立監査で残った未証明edgeを記録する。
   発見用課題と未使用評価課題を分け、同じ予算で旧運用と比較する。改善しなければ追加toolの導入を止める。

## 引き継ぎ

- 仮説カード: [H-20261021-01](HYPOTHESIS_CARD_2026-10-21_RESEARCH_ENVIRONMENT_AUDIT.md)、状態 `REFUTED`。
  G5 の記入強制という仮説を反証したもので、数学の予想への反証ではない。
- 追加物: 本報告、カード、再現script、exact JSON、validation要約。既存の研究コード・台帳に修正は加えていない。
- 最強の証拠: 不完全G5二例とG2混合行が隔離再現で exit 0。
- 既存検証の限界: gate tests は全通過したが今回の受理反例を検出しなかった。full build 通過は意味監査完了を示さない。
- 残る不確実性: 外部toolの4.33.1互換性、導入後の速度・研究成果、GitHub側の承認設定、未検算の紙上議論。
- 次の判断: P0・P1を先に実装し固定負例で再評価する。数学の新module追加、大規模な学習基盤や探索agentの増設は、この受入条件を満たすまで保留する。
