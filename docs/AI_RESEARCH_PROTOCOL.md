# AI と進める数学研究プロトコル

最終更新: 2026-09-01

## 結論

このリポジトリに必要なのは、AIへ長い一発プロンプトを与えることではなく、研究を
**提案・反証・形式化・意味監査**の検証可能なループへ分解することである。現在のリポジトリは
Leanによる証明監査と個別探索ログには強い。一方、セッションをまたいで仮説の意味、証拠レベル、
棄却条件を保存する共通形式がなかった。本書と
[`HYPOTHESIS_CARD_TEMPLATE.md`](HYPOTHESIS_CARD_TEMPLATE.md)をその境界面とする。

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
局所的な次手を生成することを分けている。本リポジトリでも全228モジュールを毎回コンテキストへ詰めず、
`PROOF_MAP`から対象義務の依存閉包を選び、関連定義・既存定理・既知反例だけをwork packetへ入れる。

### 1.5 プロンプトは手順列より成果条件を中心にする

OpenAIの公式モデルガイドは、長期・tool-heavy taskについて、目的、制約、必要証拠、成功条件、停止条件、
許可境界を明示し、同じ指示を重複させないことを勧めている。本プロトコルでは、研究依頼を
「何を順番に考えるか」ではなく「どのstatementを、何を証拠として、どこで止めるか」で指定する。

## 2. 標準研究サイクル

### Phase A: 問いを一枚に固定する

`HYPOTHESIS_CARD_TEMPLATE.md`をコピーし、次を埋める。

- exact statementと全量化子。
- 実軌道、抽象history、finite prefixのどれを扱うか。
- 既存のどの残余を除くか。
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
7. `Output`: hypothesis card、patch、実験logなどの形。

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
6. 破れたら一回だけ原因に基づく修理を許し、再度破れたら`STOPPED`にする。

データを見た後で量化子、定数、rangeを黙って変更してはならない。

### Phase D: 紙上証明から最小Lean statementへ移す

実装前に、定義から結論までの依存chainを書き、未知edgeを一つに絞る。次を満たすまで新moduleを作らない。

- statementがtarget/cutoff-independentか、依存を明記している。
- 既存のcoverage同値命題やendpoint恒等式の単なる包装ではない。
- 仮定は実際の生成箇所から供給できる。
- 結論は次の定理が消費できる形である。

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

## 3. 指示テンプレート

```text
Goal:
  [今回決める一つの数学的問い]

Known (evidence-labelled):
  - PROVED-LEAN: [使用できる定理名と意味]
  - COMPUTED: [revision, command, range, exact observation]

No-go / do not repeat:
  - [既知反例、空虚なinterface、停止済み戦略]

Acceptance:
  - exactなstatement、または最小反例を返す
  - 既存結果より強い理由を示す
  - Lean変更時は ./scripts/check.sh を通す

Falsification first:
  - boundary casesと既存countermodelを先に試す
  - discovery rangeとholdout rangeを混ぜない

Stop:
  - [反例、同値変形への還元、二度目の修理など]

Output:
  結論、証拠label、変更、command、失敗、未確実性、次の判断。
```

悪い指示は「新しい不変量を考えて証明して」である。良い指示は、候補の形、既知no-go、合格判定、
反証順序、終了条件までを固定し、探索経路そのものには不要な拘束を加えない。

## 4. このリポジトリに固有の注意

- `Lean accepts`と`Recamán実軌道から生成される`を同一視しない。
- existentialなparent/child interfaceは、任意のrank下降を捏造できないか敵対的に検査する。
- fixed-point floorの有限掃過を大域進捗と数えない。構造的天井と再開条件を尊重する。
- deep traceは回帰試験と具体的排除には有用だが、新しい一様機構の代用にしない。
- 同じ値の再利用可能性があるため、単純なinjective chargingを仮定しない。
- 新しい型、certificate、adapterは、それ自体を数学的進捗として数えない。
- READMEの数値的現況は変化が速い。研究packetでは定理名とsource revisionを優先する。

## 5. 参考文献と本プロトコルへの対応

- A. Davies et al., [Advancing mathematics by guiding human intuition with AI](https://www.nature.com/articles/s41586-021-04086-x), Nature 600 (2021). データ→予測→解釈→予想→証明の反復を採用。
- B. Romera-Paredes et al., [Mathematical discoveries from program search with large language models](https://www.nature.com/articles/s41586-023-06924-6), Nature 625 (2024). 生成器とevaluator、skeleton、候補多様性、反復選抜を採用。
- T. H. Trinh et al., [Solving olympiad geometry without human demonstrations](https://www.nature.com/articles/s41586-023-06747-5), Nature 625 (2024). neural proposalとsymbolic verificationの役割分離を採用。
- K. Yang et al., [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](https://arxiv.org/abs/2306.15626), NeurIPS 2023. proof stateと関連premiseの局所retrievalを採用。
- S. Song et al., [Towards Large Language Models as Copilots for Theorem Proving in Lean](https://arxiv.org/abs/2404.12534) (2024). tactic suggestion、proof search、premise selectionの分離を採用。
- T. Tao, [Machine Assisted Proof](https://terrytao.wordpress.com/wp-content/uploads/2024/03/machine-assisted-proof-notices.pdf), Notices of the AMS (2024). 形式化による細粒度分業と検証可能な協働を採用。
- OpenAI, [Model guidance: prompting best practices](https://developers.openai.com/api/docs/guides/latest-model) (参照日 2026-09-01). outcome、証拠、成功条件、停止条件、権限境界を明示するlean prompt設計を採用。

これらの論文はRecamán全域性の新しい数学的証拠ではない。本書が導入するのは、候補生成を増やしつつ、
誤った進捗、statement drift、再現不能な実験、停止済み枝の反復を減らすための研究工程である。
