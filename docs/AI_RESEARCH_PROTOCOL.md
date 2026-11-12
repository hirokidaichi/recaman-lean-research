# AI と進める数学研究プロトコル

最終更新: 2026-11-12（任意深さを優先する計画・継続判定。過去の実績は変更しない）

## 結論

このリポジトリに必要なのは、AIへ長い一発プロンプトを与えることではなく、研究を
**提案・反証・形式化・意味監査**の検証可能なループへ分解することである。現在のリポジトリは
Leanによる証明監査と個別探索ログには強い。一方、セッションをまたいで仮説の意味、証拠レベル、
棄却条件を保存する共通形式がなかった。本書と
[`HYPOTHESIS_CARD_TEMPLATE.md`](HYPOTHESIS_CARD_TEMPLATE.md)を個別研究unitの境界面とする。
repository全体の現在状態は[`CURRENT_FRONTIER.md`](CURRENT_FRONTIER.md)、frontier-changing claimは
[`EVIDENCE_REGISTRY.tsv`](EVIDENCE_REGISTRY.tsv)へ同期する。

この運用の成功条件は「生成した定理数」ではない。次のいずれかを、再現可能な証拠付きで得ることとする。

1. 既存frontierを真に前進させる新しい補題。
2. 有望な仮説を早期に棄却する反例・countermodel・no-go定理。
3. 次に必要な数学的入力を、元問題と同値でない最小の証明義務へ縮約すること。
4. 形式化されたstatementと意図した数学のずれを発見すること。

## 1. 文献から採用する設計原則

### 1.1 生成器と検証器を分ける

FunSearchはLLMを創造的なprogram生成器として使い、決定的evaluatorで候補を選別し、多様な候補群を
維持した。AlphaGeometryも補助構成を生成する言語モデルとsymbolic deduction engineを分離した。
このリポジトリでは、これを次のように翻訳する。

- 提案器: 不変量、課金則、有限状態、反例モデルを複数出す。
- 反証器: exact probe、境界例、free-history modelで候補を殺す。
- 検証器: Lean kernelと`Recaman/Audit.lean`で形式的主張を確認する。
- 人間監査: 「証明したstatementが欲しかったstatementか」を確認する。

Leanが最後の検証器であっても、意味の保存までは保証しない。型が通る弱い命題、到達不能な状態にだけ
成立する命題、仮定から結論が空虚に出る命題を別途排除しなければならない。

### 1.2 探索可能な対象と評価関数を先に作る

FunSearchの成功例は、候補を機械的に採点できる問題に集中し、既知構造をprogram skeletonとして固定し、
重要な部分だけを進化させた。このプロジェクトでは数列全域性を直接採点せず、例えば次を対象にする。

- target-relative crossing episodeへの課金関数。
- finite extension modelの状態圧縮。
- blocker provenanceを区別する重み。
- 既存ledger identityからは導けない区間不等式。

評価関数は実装前に固定する。有限rangeでの違反数だけでなく、既存定理より強いか、cutoff非依存か、
countermodelを分離するか、どの残余ケースを除くかを含める。

### 1.3 AIは直観の候補を作り、数学者は解釈可能なstatementへ戻す

Daviesらの枠組みは、データから関係を予測するだけで終わらず、attribution等を用いて人間が理解できる
関係へ戻し、予想と証明を作る反復過程である。本研究でも相関や高精度予測を成果とせず、最終的に
量化された不等式、有限分類、単調量、または構成的反例族へ蒸留する。

### 1.4 検索とpremise selectionを局所化する

LeanDojo/ReProverとLean Copilotは、巨大なライブラリから関連premiseを検索することと、proof stateから
局所的な次手を生成することを分けている。本リポジトリでも全モジュールを毎回コンテキストへ詰めず、
`PROOF_MAP`から対象義務の依存閉包を選び、関連定義・既存定理・既知反例だけをwork packetへ入れる。

### 1.5 プロンプトは手順列より成果条件を中心にする

OpenAIの公式モデルガイドは、長期・tool-heavy taskについて、目的、制約、必要証拠、成功条件、停止条件、
許可境界を明示し、同じ指示を重複させないことを勧めている。本プロトコルでは、研究依頼を
「何を順番に考えるか」ではなく「どのstatementを、何を証拠として、どこで止めるか」で指定する。

### 1.6 探索・活用を、次の判断を変える情報で配分する

研究単位の目的を次の三つに区別する。証明・反例探索・計算は**手段**であり、これとは別の軸である。

- **活用**: 選択済みの機構で、特定の未証明edgeを閉じる。反例探索による最後の適用条件確認も含む。
- **局所探索**: 同じ経路の候補・仮定・表現を比較し、どの研究単位へ進むかを決める。
- **大域探索**: 経路そのもの、対象、または証明機構を変える候補を比較する。

同じ有限表の枠数・lag・走査上限を増やすだけでは、独立した機構の探索と数えない。
同じ未証明仮定に依存する複数候補も、その依存関係を明記する。

HayらのmetareasoningとRusso・Van Royのinformation-directed samplingを参考に、各候補について
「成功したらどのedgeが閉じるか」「失敗したら何を除外でき、次の選択がどう変わるか」「費用上限」を書く。
成功確率や情報量を推定できない場合は、根拠を添えた定性的比較でよい。架空の確率や合成点数を作らない。
両論文のモデルにおける最適性・regret保証を、この数学研究へそのまま移してはならない。

### 1.7 予算と切替は実行前に固定し、判定後に更新する

1. cycleの総予算と各カードの配分を同じ単位で記録する。次回からの初期値は
   **局所完了30・任意深さの原理探索/反証60・独立監査10%**（2026-11-12利用者指示）。
   これは運用仮説であり最適比率ではない。活用60・探索30・監査10は旧配分と明記する。
2. 時間、CPU時間、token、金銭は別々に上限を持つ。並行作業なら延べ作業時間と経過時間を区別する。
   親cycleと子カードで同じ費用を二重計上せず、予定と実績を分け、未実行は未実行と書く。
3. 各unitに最初の確認点、継続・切替・停止・再開の条件を置く。反例、循環仮定、同値な言い換え、
   予算到達、同じ障害の再出現を判定材料にする。反例数ゼロだけでは延長理由にならない。
4. 局所unitの継続は、供給元を確認した新補題、反例による候補族の排除などを根拠にする。
   路線全体は1.8の一般化側でも別判定する。未証明edgeを言い換えただけの候補作成は数学的進展でない。
   未証明仮定を増やしたり監査を省いたりしない。監査超過はまず局所枠から移し、
   必要時は探索枠の未消化も明記して期限を守る。
5. 再配分は判定時点で、旧配分・新配分・証拠・次の判断を記録する。止まった枝へ余り時間を自動投入しない。
   同じ障害で2 cycle連続してedgeも候補集合も変わらなければ、次cycleの探索枠の少なくとも半分を
   別機構の評価へ移す。これは停止済み枝の無条件再開を許可する規則ではない。
6. 定理数、module数、commit数、調べた上限の増加を報酬にしない。反証・停止も、次の選択を変えるなら成果。

命題の証拠labelと作業状態は分ける。未着手・継続待ち・切替は作業状態で、追加の証拠labelではない。
強い補助命題が反証されても親命題は自動的に`REFUTED`にならない。方法だけが停止した場合は、命題を
`CONJECTURED`のまま残し、停止した方法を`STOPPED`として特定する。

### 1.8 任意深さに使える原理を別に評価する（2026-11-12利用者指示）

最新DAILYの数学的証拠と停止状態は保持する。方針変更前のhandoffにある次回配分・優先課題は、
この利用者指示と更新済み当日カードを優先する。過去の結果や実績を新方針へ書き換えない。

一日の親cycleについて、`local_progress`と`depth_general_progress`を別々に記録する。
これは配分の判断欄であり、新しい証拠labelではない。statement・仮定・依存・既定7 label・
実際に変わった未知edgeを引用する。局所側の成功で一般化側を成功扱いにしない。

- 局所側: 固定深さ/固定source枝の排除、候補削減、既存PAPERの元actual Lean接続。
- 一般化側: 次のいずれかを新しい証拠で得た場合に限り進展ありとする。
  1. 任意深さで使える元実供給/freeの課金則・ポテンシャル・不等式。深さ依存項があれば
     増加を払う補正/相殺を示し、欲しい無重み件数へ消費できる範囲を明記する。
  2. 深さを増減する操作が元履歴・actual供給・free会計を保存する接続補題。
     元prefixを新しいBlockWordと仮定し直さず、必要な輸送を証明する。
  3. 一般機構を破る正確な反例/no-go。抽象history・実orbit到達・補助命題・親C1を区別し、
     どの一般機構を候補から外すか記す。有限計算だけならCOMPUTEDの範囲に留める。

Dをbinderへ足す包装、深さ6を7へ増やす検証、既存一般式の再証明、結論を入力したadapter、
重み付き会計から無重み件数への未証明の置換は一般化側の進展でない。
既存E681/E674等は入力であり、引用だけを新進展にしない。有用な局所成果は正しく保存する。

setupで「一般化への接続契約」をカードへ固定する: 深さ/長さ/高度依存、同freeへの請求重複と
最大負荷、境界補正、元actual仮定の供給元、次に消費する具体的な不等式。
個別候補の式と全量化子は反証/実装より前に固定する。候補を選んだだけでは進展ありにしない。
最初15分は一般化側で判定し、新edge/一般機構の反証がなければ同手法の延長を止め、
確保した原理探索枠の中で別の機構へ切り替える。局所成果でこの判定を代用しない。

定刻の研究・監査100分では局所30/一般化60/監査10。一般化60分のうち25分以上は、
重複課金、無重み化、深さ輸送、必要な軌道条件の監査等から別の機構へ必ず使う。
同じ未知仮定を別名で使う候補、資源/tactic/import/splitだけの変更は別機構でない。
一般化側の進展なしが親cycleで連続2回なら、次は局所20/一般化70/監査10へ移す。
局所成功・日付変更でこの連続回数を消さず、一般化の新証拠が出た場合だけ0へ戻す。
既存局所停滞とSTOPPED jobの再開条件は独立に保持する。

新指標は[一般化tracker](RESEARCH_GENERALIZATION_TRACKER.md)へ次回から記録する。
11/12以前の一般化側は未評価とし、遡って成功/0回と分類しない。親cycleは一日一つ、
unit/CPU jobを別cycleと数えない。日次報告には両側の結果、一般化が動かない理由、連続回数と次の切替を記す。

## 2. 標準研究サイクル

### Phase A: 問いを一枚に固定する

`HYPOTHESIS_CARD_TEMPLATE.md`をコピーし、次を埋める。

- exact statementと全量化子。
- 実軌道、抽象history、finite prefixのどれを扱うか。
- 既存のどの残余を除くか。
- 一般化への接続契約と、局所側/一般化側のどちらを判定するunitか。
- 活用・局所探索・大域探索の別、cycle内の配分、費用上限、最初の確認点。
- 成功時の前進と、失敗時に得る情報・切り替える行き先。
- 発見rangeと未使用holdout range。
- 一度だけ許す修理と停止条件。

カードを作れないほど広い問いは実行単位にしない。「全域性を証明せよ」ではなく、例えば
「同一candidate再利用を許す重み付き入射評価で、seeded corridor countermodelを分離できるか」とする。

### Phase B: コンテキストpacketを作る

AIへ渡すpacketは次の順にし、セッション履歴そのものを知識ベースにしない。

1. `Goal`: 今回決める一つの問い。
2. `Known`: 使用可能なLean定理と計算事実。証拠labelを付ける。
3. `No-go`: 既知反例、停止枝、禁止された同値変形。
4. `Objects`: 必要な定義とnotation。
5. `Acceptance`: 合格する成果物と検証command。
6. `Stop`: 何が起きたら棄却するか。
7. `Allocation / Decision`: 予算、確認点、継続・切替条件と依存する別カード。
8. `Output`: hypothesis card、patch、実験logなどの形。

長い作業では、各サイクル終了時にこのpacketを更新する。会話の要約には「結論、証拠、反例、未解決義務、
次の判断」だけを残し、試行錯誤の全文はdevelopment logまたはカードへ退避する。

### Phase C: 提案と反証を分離する

提案器には多様性を要求し、同じ同値変形の言い換えを候補数に数えない。候補ごとに「なぜ既存identity
から出ないか」「最小の反例は何になりそうか」を添える。その後、別の反証passで次を行う。

1. 小さい時刻、等号、0/1、off-by-one、parityを検査する。
2. 実軌道条件を一つずつ弱め、どの条件が本質か調べる。
3. 既存countermodelへ適用する。
4. discovery rangeで候補を絞る。
5. statementを凍結してholdoutを一回だけ実行する。
6. 破れたら元の命題と反例を保存する。一回だけ原因に基づく修理版を別versionで許し、再度破れたら方法を`STOPPED`にする。

データを見た後で量化子、定数、rangeを黙って変更してはならない。既に見たrangeをholdoutと呼ばない。
修理に使ったholdoutはdiscoveryへ移し、新しい未使用holdoutを凍結する。紙上専用unitはrange欄を
「該当なし」とし、既知反例と境界条件による反証passを省略しない。

### Phase D: 紙上証明から最小Lean statementへ移す

実装前に、定義から結論までの依存chainを書き、未知edgeを一つに絞る。次を満たすまで新moduleを作らない。

- statementがtarget/cutoff-independentか、依存を明記している。
- 既存のcoverage同値命題やendpoint恒等式の単なる包装ではない。
- 仮定は実際の生成箇所から供給できる。
- 結論は次の定理が消費できる形である。
- 一般化unitは1.8の契約を満たし、既存一般式の包装を新しい原理と呼んでいない。

形式化後は`#print axioms`だけでなくsemantic auditを行う。具体的には、意図的に仮定を弱めてなお証明が
通らないか、親・子・clock・freshness・reachabilityを捏造できないか、既知反例を排除できているかを確認する。

### Phase E: 判定を保存する

各cycleは必ず次のいずれかで閉じる。

- `PROVED-LEAN`: auditへ追加し、proof mapを更新。
- `PROVED-PAPER`: Lean化する最小義務を記録。
- `COMPUTED`: command、revision、range、出力、限界を記録。
- `REFUTED`: 最小反例と破れた仮定を保存。
- `STOPPED`: 再開条件を一文で残す。

「有望そう」「さらに調べる」で閉じない。
unit終了時に予定・実績・得た情報・次配分をカードへ残す。今回の問いを判定できなければ、停止した
方法と不足入力を明示する。証拠labelを昇格させて時間切れを成功に見せない。

## 3. 指示テンプレート

```text
Goal:
  [今回決める一つの数学的問い]

Known (evidence-labelled):
  - PROVED-LEAN: [使用できる定理名と意味]
  - COMPUTED: [revision, command, range, exact observation]

No-go / do not repeat:
  - [既知反例、空虚なinterface、停止済み戦略]

Allocation / value of information:
  - [cycle ID、活用/局所探索/大域探索、総予算に対する配分、監査枠]
  - [成功時に閉じるedge、失敗時に除外する候補と次の選択]
  - [最初の確認点、各費用上限、実績の記録先]

Acceptance:
  - exactなstatement、または最小反例を返す
  - 既存結果より強い理由を示す
  - Lean変更時は ./scripts/check.sh を通す

Falsification first:
  - boundary casesと既存countermodelを先に試す
  - discovery rangeとholdout rangeを混ぜない

Stop:
  - [反例、同値変形への還元、二度目の修理など]
Continue / switch:
  - [継続を正当化する新情報、切替先、再開に必要な外部入力]

Output:
  結論、証拠label、変更、command、失敗、未確実性、次の判断。
```

悪い指示は「新しい不変量を考えて証明して」である。良い指示は、候補の形、既知no-go、合格判定、
反証順序、終了条件までを固定し、探索経路そのものには不要な拘束を加えない。

## 4. このリポジトリに固有の注意と空虚化防止策

- `Lean accepts`と`Recamán実軌道から生成される`を同一視しない。
- existentialなparent/child interfaceは、任意のrank下降を捏造できないか敵対的に検査する。
- fixed-point floorの有限掃過を大域進捗と数えない。構造的天井と再開条件を尊重する。
- deep traceは回帰試験と具体的排除には有用だが、新しい一様機構の代用にしない。
- 同じ値の再利用可能性があるため、単純なinjective chargingを仮定しない。
- 新しい型、certificate、adapterは、それ自体を数学的進捗として数えない。
- READMEの数値的現況は変化が速い。研究packetでは定理名とsource revisionを優先する。

### 4.1 ハーネス（INC-20260915-01 の教訓）

2026-09-15 の空虚定理量産インシデント（[報告書](INCIDENT_REPORT_2026-09-15_VACUOUS_SYNTHESIS_LOOP.md)）の根本原因は、
規則の不在ではなく規則が機械的に効いていなかったことである。以下は `scripts/harness_gate.py` と `.githooks/pre-commit` が強制する。

1. **G1〜G3（内容の下限）**：新規 `PROVED-LEAN` 行の audit symbol は実在する定理で、結論（またはその連言成分）が仮定そのものや `x = x` であってはならず、
   少なくとも 1 本は純算術でも wrapper でも omega/rfl 一発でもない定理を含む。`python3 scripts/harness_gate.py --lint-module <file>` で事前確認する。
   算術補助補題は許されるが、それだけのモジュールは研究成果ではない。
2. **G5（定理文の逐語引用）**：E-347 以降の `PROVED-LEAN` 行は `docs/statement_audits/E-NNN.md`（`--audit-template E-NNN` で生成）を必須とし、
   各定理の binder と結論を逐語で引用して 3 項目（実対象の binder／未証明 Prop や結論そのものの仮定／wrapper か）に答える。引用は source と照合される。
3. **定義した仮説は排除ではない**：`def FooHypothesis : Prop` から結論を導く定理は、その仮説名を claim に明記した上でのみ `PROVED-LEAN` とし、
   無条件命題は `CONJECTURED` のまま。`H → ¬P` の定義的否定を「枝 P の排除」と呼ばない。label は既存の 7 種のみを使う（`CONDITIONAL` は無い）。
4. **P（中心命題の pin）**：`docs/PROTECTED_CLAIMS.tsv` の label は registry と一致しなければならない。変更は広木さんの判断で、`RECAMAN_HUMAN_APPROVED=1` の commit でのみ行う。
   GitHub で閉じていない issue を文書で CLOSED と書かない。
5. **G4（命名）**：grand/master/universal/closure/synthesis/resolution/apex を含む定理名・モジュール名は新規行で拒否される。
6. **速度制限**：1 commit に新規モジュール 1 本、前回のモジュール追加から 30 分。`RECAMAN_ALLOW_BURST=1` は人間用。空いた時間で反証（既存の `REFUTED` 行と証明書の検索）を行う。
   **2026-11-01の明示承認**：利用者は「今回と日次保存に限り許可」と回答した。
   今回および今後の日次の検証済み研究snapshotを保存するcommitに限り、単一commandの
   `RECAMAN_ALLOW_BURST=1`で本数・間隔の制限を免除できる。環境へ常設せず、G1〜G5・
   保護claim・逐語audit・禁止事項・pre-commit内容監査は維持する。反証を省く許可ではない。
   日次commit/pushの再確認は不要。同日の追加指示で研究branchをmainへ統合するため、以降の保存先は`origin/main`。
   remote更新を取り込み、通常のfast-forward pushとref/SHA照合を行う。force pushは禁止。
7. **Git**：`git add -A` 禁止。`git commit -- <paths>`。他セッションのファイルを含めない。
8. **セマンティック監査**：`lake build` 通過は推論の正しさであって問題の解決ではない。監査は別セッションで `report_vacuity.py` → binder 読み → R/W/C/T 表の順に行う。

gate は heuristic で、`have` を含む連言合成や regime を仮定した算術は G3 を通る。それらは G5 の記入と P で止める。負例テストは `bash scripts/test_harness_gates.sh`。

## 5. 参考文献と本プロトコルへの対応

- A. Davies et al., [Advancing mathematics by guiding human intuition with AI](https://www.nature.com/articles/s41586-021-04086-x), Nature 600 (2021). データ→予測→解釈→予想→証明の反復を採用。
- B. Romera-Paredes et al., [Mathematical discoveries from program search with large language models](https://www.nature.com/articles/s41586-023-06924-6), Nature 625 (2024). 生成器とevaluator、skeleton、候補多様性、反復選抜を採用。
- T. H. Trinh et al., [Solving olympiad geometry without human demonstrations](https://www.nature.com/articles/s41586-023-06747-5), Nature 625 (2024). neural proposalとsymbolic verificationの役割分離を採用。
- K. Yang et al., [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](https://arxiv.org/abs/2306.15626), NeurIPS 2023. proof stateと関連premiseの局所retrievalを採用。
- S. Song et al., [Towards Large Language Models as Copilots for Theorem Proving in Lean](https://arxiv.org/abs/2404.12534) (2024). tactic suggestion、proof search、premise selectionの分離を採用。
- T. Tao, [Machine Assisted Proof](https://terrytao.wordpress.com/wp-content/uploads/2024/03/machine-assisted-proof-notices.pdf), Notices of the AMS (2024). 形式化による細粒度分業と検証可能な協働を採用。
- N. Hay et al., [Selecting Computations: Theory and Applications](https://arxiv.org/abs/1408.2048), UAI 2012（arXiv掲載2014）. 次の判断を改善する計算と費用を比較する考え方を採用。
- D. Russo and B. Van Roy, [Learning to Optimize via Information-Directed Sampling](https://arxiv.org/abs/1403.5556), 2014–2017. 選択に関係する情報と活用の利益をともに考慮する設計を参考にする。
- OpenAI, [Model guidance: prompting best practices](https://developers.openai.com/api/docs/guides/latest-model) (参照日 2026-09-01). outcome、証拠、成功条件、停止条件、権限境界を明示するlean prompt設計を採用。

これらの論文はRecamán全域性の新しい数学的証拠ではない。本書が導入するのは、候補生成を増やしつつ、
誤った進捗、statement drift、再現不能な実験、停止済み枝の反復を減らすための研究工程である。
