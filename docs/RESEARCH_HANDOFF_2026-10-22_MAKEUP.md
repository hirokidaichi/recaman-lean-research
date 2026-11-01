# 2026-10-22 C1 Q追加研究の引き継ぎ

## 結論

C1 Qの**最低水準をq0以後に訪れる場合**を、元のp基点の非Endable A予算1からLeanで証明した（E-379）。
古いブロックprefixを正確に縮める補題（E-380）と、その面積の二次上下界・下界の等号形（E-381）も形式化した。
**Q/C1/H/SL全体は未解決、数学的labelはCONJECTUREDのまま。**

計算では、深さ4・a_z≤3の全71contextを語長/S数cutoffなしで完了（E-382）。
さらに任意長prefixをmass≤17の20111語へ縮め、z長1..32・a_z≤3で深さ≥5がないことを確認した（E-383）。
全125181373 nodeを別C++でも再実行し、全counts・全候補・min値まで一致した。
個別のold windowに可能な面積集合を、全massで二次境界間の整数区間として紙上分類した（E-384、存在方向は未Lean）。

E-382とE-379の二分により、a_z≤3で**zだけが深さ≤4**なら、将来のyの語長・深さを制限せずQを扱える。
z長≤32ではE-383がその深さを供給する。この結合はCOMPUTEDに依存し、PROVED-LEANではない。
次の一問はa_z≤3の一様な深さ4供給。これが通っても一般Qにはa_z≥4が残る。

## カード・cycle・実時刻

- Card: [H-20261022-01](HYPOTHESIS_CARD_2026-10-22_C1_Q_MAKEUP.md)、主目標のstatusはCONJECTURED。
- Cycle: R-20261022-MAKEUP、[C1](HYPOTHESIS_CARD_2026-10-21_C1_AREA.md)の継続。
- 利用者の「約100分を今から研究」の明示依頼による追加枠。今回は朝8時の制限を適用しない。
- **実開始08:28:14 JST、終了は10:06:27 JST、実経過98分13秒。期限10:08:14 JST。**
- 朝の18分51秒、親cycleの予定100分、並行CPUを追加実績へ二重加算しない。
- 本実経過は、資料読取・提案・反証・紙上推論・形式化・実行中の計算監視・監査・記録を含む。
  純粋な思考時間だけを計測した値ではない。clock sleepで実績を作っていない。
- 新規数学探索は09:57の組合せ監査を最後に終了。09:58:14以降は検証・再現性・引き継ぎのみ。

| 実測区間JST | 主な作業（並行CPUを別加算しない） |
|---|---|
| 08:28:14〜08:33:39 | 開始確認、仕様固定、既存sourceとの照合、Az反例を独立再計算 |
| 08:33:39〜08:42:17 | 面積結合B/R、凍結holdout、自由tag弱化モデル、固定A予算probe |
| 08:42:17〜08:49:27 | Nとfresh-low Qの形式化、予算2・境界反例、整数clockへの接続 |
| 08:49:27〜08:58:41 | statement監査・全体check、exact制約モデル校正、有限contextの形式化 |
| 08:58:41〜09:25:11 | suffix閉性、71contextの分類と独立監査、二次下界・等号二族、R/peak探索の停止 |
| 09:25:11〜09:49:39 | deep-three監視、適応mass代表、任意長prefix付きN32探索、spectrum緩和、二次上界、全体check |
| 09:49:39〜09:57:23 | N32全tree独立照合、全mass spectrumの紙上監査、brief同期の不具合修理、Qの部分領域の二分 |
| 09:57:23〜10:06:27 | source/command/hash保存、意味監査、リンク・台帳・brief・差分・終了processの確認 |

### 予定と実績の扱い

初期予定は開始5・C1活用60・局所入力20・監査15分。
二次面積という独立入力を得た後、開始5・C1活用50・局所入力30・監査15分へ再配分した。
最後は検証の比重を増やし、その分を研究枠から差し引いた。期限は延ばさない。
実績は上の実測区間で記録し、区間内の思考・反証・検証の純時間を未計測の推定値で埋めない。
新edgeと候補集合の変化があるため、同一障害で無変化のcycleとして加算しない。以前の停滞状態を日付でリセットしない。

## 強い証拠と意味監査

- **E-379 / PROVED-LEAN**: padded BlockWord prefixの後で、全tailの最低水準をq0以後に訪れる場合のZ≥0。
  2段回復には元p基点で異なる2個の非Endable Aが必要となり、予算1に反する。
  a_yを2へ緩めるSSSAAASではZ=−3。fresh条件を外した一般Qはまだ証明していない。
- **E-380 / PROVED-LEAN**: 高さ下落≤Dならold prefixを半径floor(5(D+1)/2)へ縮めてEndableを両方向に保存。
  D=4では密度とparityで11clock。suffix閉性と、全後半clockを一つのmass≤D+1の代表で保存する定理も証明。
  tail全体は保持し、有限lag化とは呼ばない。削除prefixの不足保存は別義務で、計算側の全代表で確認した。
- **E-381 / PROVED-LEAN**: m(m+1)≤2area+2、等号はB A^jまたはC A^jの二族。
  上界4area≤5m²−11m+16も証明しA Bでsharp。実際の古いP2窓なら2Z≤2−r(r+1)が必要。
  この必要条件や既知結果への接続wrapperをC1の証明に数えない。
- **E-382 / COMPUTED**: 深さ4・a_z≤3の全71代表・46674 node・19950 guard endpointでZ最小1。
  zのa_z=3はSASAAA / SSAAAA / SSAAAASA / SSSSAAAASAAAの4語（許容contextはprefixに依存）。
  独立Pythonの全始点mass/moment・直接面積和で全counts一致。NFAの13状態でも代表集合が一致。
- **E-383 / COMPUTED**: 深さcutoffを置かず、z長1..32の全tailを全20111prefix代表で調べ深さ≥5は0。
  完了木125181373 nodeを独立C++で全件照合。元と独立版はF/G式とmod4枝刈りを共有しない。
  32より先のtailや、最大観測長12より長いzの不在を証明したとはしない。
- **E-384 / PROVED-PAPER**: [全massの面積spectrum](RESEARCH_NOTE_2026-10-22_BLOCK_AREA_SPECTRUM.md)。
  m=0/1の例外、m=0..7の完全な集合、m≥8の三区間の隙間なしを含む帰納。
  各areaの語の存在方向は未Lean、人間レビュー未。複数窓を共通prefixで同時に実現する定理ではない。

同じ担当でも、提案→小例/境界/弱化historyの反証→紙上chain→形式化→別passの意味監査を分けた。
親Dからのprefix文法の供給には従来の真部分区間EqClassW依存が残る。
全区間H/Qや、それと同値な定義済み仮説を新しいLean定理の仮定へ隠していない。

## 失敗・反例・停止・計算費用

- Az≥0という独立な前半下界はSAAA|SSSSAAAASAAAでAz=−2、REFUTED。
  q0自身はF(q0)>gでQのguard外。Sを2回続けたbではY=3、Z=1。Qの反例ではない。
  Az≥1は最短z=SのAz=0でも偽。16clock例を最小反例と呼ばない。
- 自由Endable tagのS^m A^(m+1)、m≥4はNと個数条件を守ってZ<0になる。
  真のP2供給は1clockだけなので実際のdはm−1。自由tagの方法をSTOPPED、Qは未反証。
- discovery 20/32は経過0.44秒、28/64は9.78秒。後者のAz<0の241142 guardでもZ最小1。
- holdoutは2000000語・8生成群・長さ80..384、20897765 split、25344026 guard endpointで違反0。
  経過17.02秒。新しい完全語のサンプルであり、短いmotifまで未使用とはしない。guard内のEndable endpointは0。
- 固定A予算の旧探索は590.31秒で中断。1971prefix完了・1prefix中断、全体未完了。
  S上限延長を止め、証明によるprefix削減へ切替。

| exact/relaxed probe | 実solve秒 | 判定 | 範囲・判断 |
|---|---:|---|---|
| Q-old-min | 27.575 | INFEASIBLE | prefix=SAAA,q0=32,b=64の固定設定だけ |
| R-negative | 900.256 | UNKNOWN | q0=80。RはCONJECTURED、時間延長STOPPED |
| peak-five | 899.991 | UNKNOWN | q0=80。候補は未証明、同設定延長STOPPED |
| deep-three | 900.0125 | UNKNOWN | q0=80。a_z≤3の深さ供給は一様には未証明 |
| old spectrum緩和 | 3.9078 | INFEASIBLE | tail長32の個別signature緩和。全長の証明ではない |
| Y-triangle | 120.0023 | UNKNOWN | q0=32,b=64。三角評価を証明・反証したとは扱わない |

全exactモデルはE⇔Aかつ実P2窓の存在を両方向に制約。長さ8の256語、既知4例、数え落とし/偽tagの対照を校正した。
spectrum緩和ではold windowを別prefixで供給できるため、SATでも実語の反例にしない。
今回はINFEASIBLEだったのでcommon_prefix_lift.pyの持上げ探索は**未実行・該当なし**。
UNKNOWNのobjective=0は反例不在や面積下界の証拠にしない。

探索CPU上限は実行前に1200→3900秒へ再配分。各jobは単一workerで上限・argv・seedを事前固定。
`/usr/bin/time`ログのあるrunのuser+sys合計は**3425.57秒**（[集計](data/c1_q_makeup_20261022/cpu-accounting.json)）。
これは経過研究時間に加算しない。コンパイル・Lean・install・一部の小校正CPUは別途完全には測っていない。
新規探索は09:58:14までに終了し、最終の計算workerは09:50台の独立検証で完了している。

## 変更ファイルとcommands

数学: Recaman/BlockSuffixPositivity.lean、Recaman/Audit.lean、EVIDENCE_REGISTRY.tsv、statement_audits/E-379〜E-381。
記録: 本handoff、当日DAILYへの最新入口、今回/親C1カード、RESEARCH_ALLOCATION、CURRENT_FRONTIER、PROOF_MAP、
RESEARCH_PORTFOLIO、RESEARCH_NOTE_2026-10-22_C1_Q.md、BLOCK_AREA_SPECTRUM.md、[全データ](data/c1_q_makeup_20261022/)。
運用: scripts/dev_tool.py、scripts/test_dev_tool.py。既存の他セッション変更は保存し、stage/commit/pushしていない。

- `python3 scripts/harness_gate.py --lint-module Recaman/BlockSuffixPositivity.lean`: 通過。
- `./scripts/check.sh`: **404 build jobs、2685宣言**、全公理がpropext/Classical.choice/Quot.soundの範囲。
- `bash scripts/check_research_registry.sh`: 384行、170 PROVED-LEAN、対象26行のG1–G5、保護4行が通過。
- `make test-tools`: brief **7件**とgate **18件**が通過。
- `make brief`: E-379〜E-384と中心命題の現label・次の判定を同期。
- `git diff --check`: 最終保存後に確認。実験ごとの完全argvは[RUN_INDEX.tsv](data/c1_q_makeup_20261022/RUN_INDEX.tsv)。
- 最初の`./scripts/lakew`は既定のelanパス不在で失敗。PATH上のlake/Lean v4.33.1でsource checkと全checkを行った。
  wrapper修理へ数学枠を流用していない。

brief同期では、Unicodeの単語境界が「E-379で」のような日本語隣接IDを落とす不具合を発見。
ASCIIのID継続文字を除外する抽出へ修理し、日本語隣接・未知ID・ASCII連続IDを回帰テストに追加した。
これは数学的証拠ではなく、記録の同期修理として費用内に計上。

22件のsource/model hashが全て一致。appendしたPROTOCOLは、実行当初の一致するprefixを
PROTOCOL.initial.mdへ復元して保存した。419ファイルの検証時source snapshot、tool versions、正確なraw出力も保存。
他セッションのRecaman.lean / viewer/manifest.json / SS2OldestPattern.leanの3hashは開始前の値を保持。
PROTECTED_CLAIMS.tsvは差分なし。最終manifestとprocess確認は終了時の実測を添付する。
追加の基点移動・枝刈り・整数domainの監査は[FINAL_SEMANTIC_AUDIT.md](data/c1_q_makeup_20261022/FINAL_SEMANTIC_AUDIT.md)。
exportしたsource419ファイルと証拠33ファイルは、一時directoryでG5/lint/protected/briefを再検証済み。

## 次の一問と再開条件

次回はC1のQの旧minimum caseから再開し、C2/Pの入力監査を最初から繰り返さない。

**bounded question**: padded BlockWord prefix後の元p基点で、d(k1)=0、全k1<u≤q0でd(u)≥1、d(q0)=1、
a_p(k1,q0)≤3を満たす全有限語について、全k1≤u≤q0でF(u)≥g−4が従うか。
元のprefixの不足非負性も明示する。これは完成Dを弱めた補助入力であり、反例があっても親Qを自動反証しない。

- 受入: 語長に依存しない非循環な証明、または実際の全P2条件を満たす深さ5の語と全ledger。
- 最初の確認点15分: mass/momentの新しい不等式か候補集合を変える反例が出るか。
- 停止: 有限長/S数の延長、同じUNKNOWNモデルへの時間追加、定義したQの仮定化だけなら当該方法を止める。
- 継続できなければ新しいjoint-areaの機構評価へ配分し、停止したAz独立非負・自由tagへ戻らない。
- E-384の存在方向のLean化は独立した最小義務として記録済みだが、Qの供給不足を隠すための定理数増加には使わない。
- a_z≤3の深さが解決しても、一般Qにはa_z≥4、C1からS1にはC2/F、SLのd=2にはTSがなお必要。

最終保存判定: 2026-10-22T10:06:27+09:00。本追加cycleの研究・監査・記録を終了。Q全体はCONJECTURED。自分の数学workerは0、stage/commit/pushなし。
