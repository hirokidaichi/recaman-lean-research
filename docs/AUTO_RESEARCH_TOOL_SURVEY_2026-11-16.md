# 自動研究フレームワークの調査と試行

2026-11-16 JST。基準 revision `82ad51a`。[10/21 の研究環境監査](RESEARCH_ENVIRONMENT_AUDIT_2026-10-21.md) からの差分として、
外部の自動研究ライブラリ・仕組みを調べ、導入候補の一部を実際に試した。数学的証拠は追加していない。台帳・Lean ライブラリ・ゲートは変更していない。

## 結論

1. **最優先は新しい探索器ではなく、「Lean が受理した」以上の検証を機械化すること**。このリポジトリ固有の失敗（空虚・条件付き再包装の定理）に直接効く道具が、
   2026 年後半に Lean 公式から揃った（core の `lake comparator` / `lake check`、同梱の `leanchecker`）。同じ仕組みは**依存追加なしで**今の v4.33.1 上に再現でき、
   本日の試行で動いた（T2 文の固定 12/12、T3 空虚性プローブ 固定悪例 5/5・実定理の誤検出 0）。
2. **日次研究は Codex アプリで動いている**（[DAILY_RESEARCH_SCHEDULE.md:161](DAILY_RESEARCH_SCHEDULE.md)）。Claude Code の hook・plugin 前提の仕組みは
   日次ループでは発火しない。導入物は repo の script・git hook・Lean ファイルとして置き、どのエージェントからも同じ入口で呼べる形にする。
3. **LLM による探索器進化（OpenEvolve＋Claude Code）は、固定した評価器の上では人手の基準線を明確に上回った**（T6）。
   乱択・焼きなまし・ブロック語彙の 3 戦略は長さ 34 の既知 H+ 反例を 500 万評価でも再発見できなかったが、16 反復（約 4 分、Claude 呼び出し 16 回）で
   進化した戦略は、未使用 seed で 30 万評価 5/10・100 万評価 8/10 で再発見した。既知の答えの再発見であり、新しい数学的発見ではない。
4. **lean-lsp-mcp は日次セッションの道具として有用だが、最小仮定検査には誤判定の型がある**（T5）。同じファイルの呼び出し側が壊れるだけで「必要」と数える。
   空虚性の型（結論＝仮定・矛盾・純算術）は検出しないので、T3 のプローブと併用する。
5. 自律研究ループ系（autoresearch、AI Scientist、co-scientist など）は「安くて信頼できるスカラー指標」を前提にしている。
   純粋数学の証明作業にはそれがなく、唯一の機械判定「Lean が受理」は 9/15 の空虚ループが最適化してしまった指標そのものである。
   転用するのは指標ではなく、**試行台帳・再起動用の小さな状態ファイル・別ベンダーの査読**という周辺の仕組みに限る。

## 前提（この repo での適合性を決める条件）

- Lean 4 core v4.33.1、Mathlib なし、1,027 モジュール。`sorry`/`native_decide`/独自 axiom 禁止、公理は propext・Classical.choice・Quot.sound のみ。
  → Mathlib 前提の prover・検索（DeepSeek/Goedel/Kimina-Prover、LeanSearch など）は適合しない。`bv_decide` も補助公理を足すので不可。
- 主要リスクは Lean が受理する空虚な定理（[INC-20260915-01](INCIDENT_REPORT_2026-09-15_VACUOUS_SYNTHESIS_LOOP.md)）。既存ゲート G1〜G5 は署名の文字列・構文に基づく。
- 状態ファイルが巨大：`CURRENT_FRONTIER.md` 173KB、`DEVELOPMENT_LOG.md` 289KB、`EVIDENCE_REGISTRY.tsv` 640KB（728 行）。毎日の文脈復元コストが大きい。
- 調査は 3 本のサブエージェントが一次資料（GitHub、公式 docs、arXiv）で確認した。下表のうち、本セッションで手元確認したのは
  `leanchecker`・`cadical` がツールチェーンに同梱されていること、日次実行が Codex であること、状態ファイルの大きさだけ。
  その他のバージョン・日付は調査時点の記載で、本書では再確認していない。

## 調査結果

### A. Lean の検証・信頼基盤とエージェント接続

| 名前 | 何をするか | 状態 | 適合 | 理由 |
|---|---|---|---|---|
| `leanchecker`（core 同梱） | .olean をカーネルで再検査し、`#print axioms` では見えない環境改竄を検出 | v4.33.1 に同梱（手元確認） | 高 | 依存なし。T4 で試行 |
| `lake check` / `lake comparator`（core） | check: ビルド→export→カーネル再生→標準公理のみ。comparator: 解答が課題ファイルと**同じ文**を証明するか | v4.35.0（2026-10-12）で core 化、単体 repo は archive。sandbox は Linux のみ | 高（要 upgrade） | PROTECTED_CLAIMS をカーネル水準で固定できる。T2 は同じ仕組みの v4.33 版 |
| lean-lsp-mcp | MCP で goal・診断・局所検索・`lean_verify`・`lean_minimal_hypotheses`（仮定を一つずつ外して再 elaboration） | v0.33.0（11-03）、MIT、`uvx` | 高 | Codex も MCP に対応。最小仮定は空虚性に直撃。本日は外部取得が承認待ちで未試行 |
| Lean Beam（Lean FRO） | Lean ネイティブ CLI/MCP、投機的 `runAt`、checkpoint | beta、4.34〜4.36 のみ | 中（upgrade 後に高） | 4.33 の module writer が書込み失敗を成功と報告する不具合（lean4#14204、4.34.1 で修正）の報告あり（未確認） |
| LeanInteract / repl | Python から REPL 操作 | 活発。repl は v4.33.0 タグ | 中 | Python probe→Lean の橋 |
| atp-checkers（arXiv 2606.29493） | 13 種の lint（仮定から False、未使用 binder 等） | Mathlib 前提 | 設計は高・そのままは低 | T3 は同じ考えを Mathlib なしで実装 |
| Plausible | CONJECTURED 文のランダム反例探索 | v4.33.0 タグ、batteries 依存 | 中〜高 | 外部 package 不使用の方針と要相談 |
| Loogle（ローカル）・LeanArchitect | 自 project の補題検索、`@[blueprint]` から依存グラフ | Loogle は 4.33 ビルド未確認、LeanArchitect は v4.33.1 タグ | 中〜高 | Mathlib がないので自 project 検索が重要 |
| lean4-skills（Claude Code plugin） | prove/disprove/checkpoint/review、定理見出しは不変 | MIT、活発 | 中 | Claude セッション専用。日次 Codex には効かない |
| Aristotle（Harmonic） | 自動証明サービス | 3.0（10-26）以降は C/Verilog 専用で Lean は対象外との報告 | 低 | — |
| Leanstral 1.5（Mistral） | Apache の Lean 特化モデル、lean-lsp-mcp と併用 | 119B MoE | 中 | 独立な第二エージェント候補。Mathlib 前提かは不明 |
| Archon | Claude Code 上の plan/prove/review | 既定で権限確認を無効化し Mathlib を導入 | 低 | 発想（blueprint doctor）のみ参考 |

### B. 自動発見・反例探索

| 名前 | 中身 | 状態 | 適合 | メモ |
|---|---|---|---|---|
| OpenEvolve | MAP-Elites＋島、評価器の出力を prompt へ還流 | v0.4.1（11-02）、Apache | 高 | `provider: claude_code` で API キーなしに Claude Code ログインを使える |
| ShinkaEvolve（Sakana） | novelty 棄却・モデル選択 bandit で少サンプル | v0.0.8（11-13）、Apache | 高 | `max_api_costs` の金額上限があり、事前固定予算の規則と合う |
| CodeEvolve / CORAL | 島＋CVT-MAP-Elites / Claude Code・Codex を使う多エージェント進化 | 活発、Apache | 中 | CORAL は日次セッションの形に近い |
| AlphaEvolve（Google Cloud） | 一般提供（2026-07） | 企業向け手続き・価格不明 | 低〜中 | 問題集 repo の検証器は参考 |
| PatternBoost / Wagner 交差エントロピー | 局所探索＋小型 transformer / RL | 2024/2021、ライセンスなし | 中〜高 | ±1 語はそのまま扱える。再実装が必要 |
| CaDiCaL＋LRAT、lrat-catcher `+kernel` | SAT の証明書を Lean のカーネルだけで取り込む | CaDiCaL はツールチェーンに同梱（手元確認）。lrat-catcher は v4.30 固定 | 中〜高 | 長さ 35〜50 の H を「窓 > 31 必須」付きで符号化する案。Optio（arXiv 2609.25011）が kernel-only の先例 |

既知の教訓：AlphaEvolve の 67 問報告（arXiv 2511.02864）では評価器の抜け穴を突く候補が出た。評価器・既知反例・holdout は探索器に触らせない（10/21 監査 §3 と同じ）。

### C. 自律研究ループと周辺の仕組み

| 名前 | 転用できる仕組み | 効く痛点 | 適合 |
|---|---|---|---|
| Karpathy autoresearch | 固定予算・一指標・keep/discard の ratchet、捨てた試行も `results.tsv` に残す | 進展と再包装の区別 | 中（指標は転用しない） |
| Aletheia（DeepMind） | 結果ごとに自律度（H/C/A）と重要度（0〜4）、人間関与カード | 再包装の可視化 | 高（ラベル） |
| ProofCouncil | 別ベンダーの critic 3 者、コスト記録、サブスク限定モード | 空虚化・再包装 | 高 |
| OpenProver | 10k 字以内の whiteboard＋短 ID 索引、必要時だけ本文を読む | 文脈復元コスト | 高 |
| LeanMarathon | 証明前に読み取り専用の Target-Reviewer が文を審査、編集範囲を凍結 | 空虚化 | 高 |
| Lea | formalized/verified/disproved/audited の段階を文と import の hash に結びつける | G5 監査の陳腐化 | 高（仕組み） |
| Prove2Me・Anthropic FLT | 文を不変にした文 DAG、進展＝中心命題の依存錐で閉じたノード数 | 一般化の停滞・再包装 | 高 |
| co-scientist | 近接クラスタリングで重複仮説を検出（Elo 対戦は信頼度が低い） | STOPPED 案の改名再提案 | 中 |
| Ralph loop・Claude Code hooks | 毎回新プロセス、状態はファイルだけ | 文脈復元 | 中（Codex でも動く形にする必要） |

## 試行（本日実施、`experiments/autoresearch_trial_20261116/`）

再現手順は同ディレクトリの [README](../experiments/autoresearch_trial_20261116/README.md)。どれもツールの評価で、証拠ラベルの対象ではない。

### T1 反例探索ベンチ（探索器進化の比較基準）

- 評価器 `hmargin.c`：区間容量予想 H（E-509）の max(e − s)、unclean 数（E-511）、H+ 余裕 e + u − s を 1 語 2.5µs で計算。
  長さ ≤ 14 の全語で margin ≤ 0、ランダム 300 語で独立な素朴実装と一致、E-511 の語で e = 11・S = 13・unclean = 3 を再現。
- `bench.py`：戦略ファイル（`search(n, evaluate, budget, rng)`）を評価回数で予算化し、ハード非依存に比較。
  課題 `rediscover` は長さ 34 の H+ 反例（存在が既知、E-511）を見つけられるか。
- 結果：乱択・焼きなまし・ブロック語彙（EqClass ブロック＋欠陥）の 3 戦略とも、500 万評価 × 2 seed で **0/2**。最良は全て e + u − s = 0。
  地形は「自明な等号語の広大な台地」と「針のような反例」で、文字単位の局所探索は効かない。
- 未対応：H の反例には長さ 32 以上の窓が必須（E-372）だが、`hunt` 課題の目的関数にまだ入れていない。

### T2 文の固定（Comparator の仕組みを v4.33 上で再現）

人間が散文の主張から書いた `Prop`（`Pins.lean`）を、引用された定理が証明するかを 2 方式で検査する。
`exact` は型が定義的に一致（Comparator 相当）、`implies` は binder を intro し定理を apply、残りを `assumption` だけで閉じる（より強い定理は通し、追加仮定は通さない）。

| 事例 | exact | implies |
|---|---|---|
| E-511 `clean_capacity` を固定文 E511 に | 通過 | 通過 |
| 変異：Nodup を外す／`≤` を `<` に | 拒否 | 拒否 |
| 変異：仮定 `0 < n` を追加（弱い文） | 拒否 | 通過 |
| **E-510 `periodic_capacity_of_line` を E-070 に** | 拒否 | 拒否（`⊢ LineCapacity e` が閉じない） |
| 結論を仮定に持つ定理を E-070 に | 拒否 | 拒否 |

12/12 が期待どおり、1 件 0.2〜0.3 秒、公理監査付き。9/14 の誤昇格（条件付き定理を中心命題の根拠にする）を機械的に止められる形である。
固定文自体の正しさは人間が保証する必要があり、それは現在の PROTECTED_CLAIMS の承認手続きと同じ位置に入る。

### T3 空虚性プローブ（Mathlib なしの atp-checkers 相当）

elaborate 済みの定数を直接調べる Lean メタプログラム `VacuityProbe.lean`。各定理について、証明項に現れない Prop 仮定（unused）、
結論と定義的に等しい仮定、`omega`/`simp_all`/`grind` で仮定から `False`、Recaman の対象に触れない純算術かつ自動で閉じる文、を報告する。

- 固定悪例 5 本（9/15 監査の C・T 型、削除済み E-319 `grand_capacity_inequality` の署名そのもの、未使用の定義済み仮定、矛盾仮定）：**5/5 検出**、理由も正しい。
- 現行 9 モジュール 67 定理（E-376・E-511・E-719〜E-724 等）：**2 件検出、どちらも本当に証明に使われていない仮定**。
  `TightSubsetDecomposition.tight_triple_lag7_spans_neighborhood` の `_hA3`（作者が下線で未使用を明示）と、
  `NearestInitialSourcePair.nearest_source_window`（E-720）の `hhb : h ≤ b`。後者は定理を弱めているだけで無害だが、監査時に知るべき情報。
  矛盾・結論＝仮定・純算術の誤検出は 0。実行 約 3 秒。
- 開発中の失敗も記録する：v4.33 では `ConstantInfo.value?` が定理に対して `none` を返すため初版は未使用仮定を見逃した。また heartbeat 超過は
  通常の `try` で捕まらず（`tryCatchRuntimeEx` が必要）、初版は一部モジュールで中断した。固定悪例を先に置いたことで両方を検出できた。

### T4 leanchecker

`lake env leanchecker Recaman.CleanWindowCapacity` は 0.9 秒、`--fresh`（Init からの依存も再検査）は 36 秒。
**全ライブラリ `lake env leanchecker --fresh Recaman`：exit 0、出力なし（全宣言がカーネル再検査を通過）、実時間 780 秒（user 741 秒）、
最大常駐メモリ 35.5GB**（96GB の macOS 機）。メモリが大きいので、GitHub の標準 runner（16GB 前後）では `--fresh` は通らない見込み。
CI では差分（変更モジュールだけ、`--fresh` なし）、全体はローカルか大メモリ機で週次、が現実的。

## 第 2 段：外部ツールの試行（同日、広木さんの承認後）

### T5 lean-lsp-mcp v0.33.0

`uvx lean-lsp-mcp` を MCP SDK のクライアント（`lean_lsp_mcp/client.py`）から起動し、ビルド済みの worktree に対して呼んだ。初期化 0.8 秒。
22 ツールのうち Mathlib 検索系（leansearch・loogle・leanfinder・hammer_premise）は外部サービス向けで、この repo には効かない。

| ツール | 対象 | 結果 | 時間 |
|---|---|---|---|
| `lean_file_outline` | E-720 のモジュール | import と各定理の署名を返す | 0.8 秒 |
| `lean_goal` | 同 26 行目 | 仮定一覧とゴールを正しく返す | 0.01 秒 |
| `lean_verify` | `nearest_source_window` | 公理 propext・Quot.sound、標準 | 1.0 秒 |
| `lean_local_search` | `clean_capacity` | 本体に加え `docs/data/` の凍結 snapshot の同名定理も返す（検索範囲の絞り込みが要る） | 0.3 秒 |
| `lean_minimal_hypotheses` | `nearest_source_window` | **`hhb` を load-bearing と誤判定**。理由は同じファイル 53 行目の呼び出し側が引数を位置で渡しており、仮定を外すとそこが壊れるため。定理自身の証明では未使用（T3 が正しい） | 2.2 秒 |
| `lean_minimal_hypotheses` | 固定悪例 5 本 | 未使用の定義済み仮定 `hH` を removable と検出。さらに旧 E-319 署名の `hkU` も removable と検出（T3 は omega の証明項が `hkU` を含むため見逃した）。結論＝仮定・矛盾仮定・純算術はすべて load-bearing で、**空虚性の型は検出しない** | 各 0.03〜1.1 秒 |

結論：lean-lsp-mcp は日次セッションの「Lean を見る目」として有用で、Codex にも MCP で入れられる。最小仮定検査は T3 と補完関係にある
（MCP は「証明を書き直せば外せる仮定」、T3 は「証明項に現れない仮定」と空虚性の型）。ただし同一ファイルの呼び出し側の破綻を「必要」と数えるため、
判定は呼び出し側を除いた行で読む必要がある。

### T6 OpenEvolve 0.4.1（探索器の進化、Claude Code 経由）

- 設定：`provider: claude_code`（`claude -p --model sonnet`、API キー不要）、評価器は固定（`evolve/evaluator.py`）、
  LLM が書いたコードは `sandbox-exec`（ネットワーク禁止、`/private/tmp` 以外への書込み禁止）の中で実行。家ディレクトリへの書込みを試すコードが拒否されることを事前に確認した。
- 課題：T1 の `rediscover`（長さ 34 の H+ 違反）。採点は best hplus に unclean 数の段階点を足したもの、2 seed × 30 万評価。初期戦略（焼きなまし）は 0.285。
- **1 反復目（LLM 呼び出し 1 回、23 秒）で得点 1.13**。生成コードは評価器に触れていない正当な改良で、目的関数を `2·hplus + u + 0.05·e` に変え、
  評価のキャッシュで予算を節約し、区間反転・挿入の移動とリスタート数・A 密度の多様化を加えたもの（`strategies/evolved_iter1.py`）。
  見つかった語は `SAAASSSSAAAASASSSAAASAAASSAAAASAAA` で、**E-511 の台帳にある H+ 反例そのもの**（e = 11、u = 3、S = 13）。コードに語は埋め込まれておらず、乱択からの探索で到達した。
- **16 反復の本走**（LLM 呼び出し 16 回、実時間 233 秒、うち 1 件は評価 100 秒の timeout、2 件は差分の一部が親に当たらず部分適用）で最良得点 1.645、
  発見用の 2 seed とも違反に到達。最良戦略（`strategies/evolved_run16.py`）は、全 1 文字反転とランダム交換の最急上昇によるタブー探索に、
  A/S 密度を変える多点スタートと、`hplus ≥ 0`・`≥ 1` に段差を付け unclean 数を 0.5 倍で足す目的関数を組み合わせたもの。これも評価器には触れていない。
- 発見に使っていない seed での発見率（`results/openevolve_holdout.txt`）：

  | 戦略 | 30 万評価 × 10 seed | 100 万評価 × 10 seed | 500 万評価 × 5 seed |
  |---|---|---|---|
  | 焼きなまし（基準線） | 0/10 | — | 0/5 |
  | 1 反復目の進化戦略 | 1/10 | 2/10 | 5/5 |
  | 16 反復後の進化戦略 | **5/10**（中央値 5.3 万評価目） | **8/10**（中央値 20 万評価目） | — |

- ヒットした語は全試行で同じ E-511 の語だった。長さ 34 の H+ 違反がこの語だけかは調べていない（OBSERVED、主張しない）。
- 費用：`claude -p --model sonnet` を計 17 回（疎通 1＋本走 16）、サブスクリプション内。各呼び出しに `--max-budget-usd 1.0` が付く。
- 評価：**既知の答えの再発見という課題では、LLM 進化は人手の基準線を明確に上回った**。ただし新しい数学的発見ではない。
  本命は H の反例探索（`hunt`）で、長さ 32 以上の窓を持つ endable を報酬にする指標は `bench.py` に入れたが、進化はまだ回していない。
  回すなら、発見用の長さ 35〜64・holdout 用の長さ 65〜128・seed・評価回数・CPU 上限を実行前にカードへ固定し、候補は `naive_margin` と既存 `eqcheck.c` 系で独立に再検査する。

## 本線化（同日、提案 1・2 を実装）

広木さんの「G6 と lint を本線へ」を受け、試行版を次の形でハーネスに組み込んだ。実験用の `experiments/autoresearch_trial_20261116/statement_pin/`
と `vacuity_probe/` は記録として残し、本線は以下を正本とする。

| 部品 | 置き場所 | 役割 |
|---|---|---|
| 固定文 | `docs/protected_pins/ProtectedStatements.lean` | E-001・E-067・E-070 を Lean の `Prop` で固定。用語は既証明の部分結果（E-071・E-128）と同じ |
| 固定の一覧 | `docs/protected_pins/PINS.tsv` | 保護行ごとに固定名、または `unpinned: <理由>`（E-179） |
| 定義ロック | `docs/protected_pins/definitions.lock` | 固定文が使う 22 定義（`a`・`stateAt`・`signSum`・`P2`・`subPhases` 等）の型と値の 64 ビット指紋 |
| G6 静的検査 | `harness_gate.py --check-pins-static`（`check_research_registry.sh` から） | Lean なしで、全保護行に固定か理由があること、固定名が `def … : Prop` として存在すること、ロックが空でないことを検査。CI の harness ジョブと pre-commit で走る |
| G6 Lean 検査 | `harness_lean.py --check-pins`（`check.sh` から） | 固定文の elaborate、仮定から `False` が出ないこと、定義ロックとの一致、PROVED-LEAN の固定命題を引用定理が本当に証明すること |
| 空虚性 lint | `harness_lean.py --vacuity-row/--vacuity-module/--vacuity-recent`（`check.sh` は直近 5 行を report-only で表示） | T3 のプローブ。timeout は `?` と表示し「問題なし」と区別。G5 テンプレートに貼付欄を追加 |
| 人間の所有 | `.githooks/pre-commit` | `docs/protected_pins/` の変更は `RECAMAN_HUMAN_APPROVED=1` を要求 |
| 回帰テスト | `scripts/test_lean_gates.py`（`make test-lean-gates`、`make test` に含む）と `test_harness_gates.py` の静的ケース | 正例・負例 7 件、定義の書換え・削除・追加の検出、PROVED-LEAN の誤昇格の拒否、指紋が定義値の変化を捉えること、lint の悪例 5/5 |

固定文の正例・負例（`scripts/lean/pin_cases.tsv`）：

| ケース | 期待 | 結果 |
|---|---|---|
| E-071 の定理 → E-067 を lag ≤ 7 に制限した文 | 通過 | 通過 |
| E-071 の定理 → E-067（全 lag） | 拒否 | 拒否（結論が合わない） |
| E-128 の定理 → E-070 を ssCount ≤ 1 に制限した文 | 通過 | 通過（E-128 に正の周期和の仮定がないのは、より強い定理として許される） |
| E-128 の定理 → E-070 | 拒否 | 拒否（`ssCount ≤ 1` の仮定が閉じない） |
| E-510 の定理 → E-070 | 拒否 | 拒否 |
| 結論を仮定に持つ定理 → E-070 | 拒否 | 拒否 |
| `all_targetResolvable_implies_surjective` → E-001 | 拒否 | 拒否（`∀ m, 0 < m → TargetResolvable m` が閉じない、E-338〜E-342 型） |

実測：`./scripts/check.sh` 全体 17 秒（ビルド済み）、うち G6 約 3 秒、lint 約 3 秒。`make test-lean-gates` 22 秒。
lint は直近行で、E-720 `nearest_source_window` の `hhb` と E-718 `SSAA_height_one_positive` の `hK` を「証明項に現れない仮定」として報告する
（どちらも定理を弱めているだけで、誤りではない）。

限界：固定文が意図した数学を正しく表すかは人間が保証する（ここが今回の承認対象）。指紋は Lean の toolchain を上げると変わり得るので、
upgrade 時はロックの再生成を人間が承認する。`implies` 検査は `assumption` で閉じる形だけを認めるため、仮定の順序や形が違う同値な定理は
通らないことがある（その場合は誤った拒否になり、誤った受理にはならない）。

## 導入提案（優先順）

| 順 | 提案 | 依存 | 人間の判断が要る点 | 受入条件 |
|---|---|---|---|---|
| 1 | **G6 文の固定**（本日実装済み、固定文は承認待ち）：PROTECTED_CLAIMS の各行に Lean の固定文を付け、label 変更行は `check_pins` 通過を必須にする | なし | 固定文の内容（中心命題の定義そのもの）、ゲート追加 | 9/14 型の誤昇格と空虚定理を拒否、正当な定理を通す（T2 の 12 事例を回帰テストに） |
| 2 | **空虚性プローブを report-only の lint に**（本日実装済み）：新規 PROVED-LEAN 行の引用定理に自動実行し、G5 監査に結果を貼る | なし | 強制にするか | 9/15 監査の C/T 型の再現例を全検出、直近 1 か月の行で誤検出率を測る |
| 3 | **leanchecker を週次/CI に**（CI は変更モジュールの差分、全体 `--fresh` は大メモリ機で週次） | なし | 実行場所 | 全体 `--fresh` は本日 exit 0・780 秒・35.5GB。差分版の CI 所要時間を測る |
| 4 | **lean-lsp-mcp** を Codex と Claude の両方に設定（T5 で動作確認済み） | `uvx`（外部取得） | MCP 設定の追加 | 1 cycle で goal 取得・`lean_minimal_hypotheses` を使う。最小仮定の判定は呼び出し側の破綻を除いて読み、T3 と併用 |
| 5 | **v4.35+ への upgrade 検証**（使い捨てブランチ） | toolchain 更新 | 本線の toolchain 方針 | `lake check --paranoid`・`lake comparator` が Linux で通る、全 check 緑 |
| 6 | **探索器進化**（OpenEvolve＋Claude Code、T6 で再発見課題は基準線を超えた） | pip（外部取得）、サブスク費用 | `hunt` を回すかと費用・CPU 上限 | `hunt` の発見用/holdout 長を事前固定。評価器・既知反例・holdout は探索器に触らせず、候補は独立実装で再検査。ShinkaEvolve との A/B は未実施 |
| 7 | **ループ周辺**：試行台帳（autoresearch の results.tsv＋Aletheia の重要度ラベル）、whiteboard＋索引（OpenProver）、別ベンダー査読（日次 Codex の文を Claude が読む） | なし | 日次プロンプトの変更 | 査読は 9/15 の空虚例 5 本と正当例 5 本の盲検で 4/5 以上検出したら採用 |

推奨しない：Aristotle（Lean 対象外の報告）、Mathlib 前提の prover・検索、Archon（権限確認を無効化して Mathlib を導入）、Elo 対戦による仮説選抜、ThetaEvolve（8×80GB GPU）。

## 未実施・不確実性

- 第 2 段で lean-lsp-mcp と OpenEvolve は試した。ShinkaEvolve・CORAL との比較、v4.35 への upgrade 検証（`lake check --paranoid`・`lake comparator`、
  全 1,027 モジュールの再ビルドが要る）、Lean Beam、Loogle のローカル構築は未実施。
- 調査表のバージョン・日付・機能は調査エージェントの一次資料確認に基づき、本書では再確認していない。特に Lean Beam の 4.33 不具合、
  Aristotle の Lean 対象外化、`lake comparator` の macOS での挙動は導入前に確認する。
- T2・T3 は少数事例での動作確認で、検出率・誤検出率の推定ではない。T1 は探索戦略についての OBSERVED で、H について何も言わない。

## 次の判断

1. G6（文の固定）と空虚性プローブの lint 化を本線に入れるか。どちらも依存追加なしだが、ゲート変更と固定文の内容は人間の判断。
2. lean-lsp-mcp を日次の Codex 設定に入れるか。
3. OpenEvolve の `hunt`（H の反例探索）を、事前固定した発見用/holdout 長と CPU 上限で回すか。
