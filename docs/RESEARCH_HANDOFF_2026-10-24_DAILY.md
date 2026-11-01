# 2026-10-24 日次研究の引き継ぎ

## 結論

**C1の全証明とr4の全分類は未完了。** 明示16rootの後半Q、無制限runの供給制約、
任意長prefixのmass3/4を同時保存する10代表など、E-390〜394/E-396〜399の9入力をPROVED-LEANにした。
第4free後の供給は高々2回という強い補助案は、既知実例の5回でE-395 REFUTED。
これは親C1/Qの反例ではない。a_z≤4から明示16語への全包含は未供給、E-388はCOMPUTEDを維持する。
次は **同じ低mass代表でmass3/4の両tagを正確化した固定代表r4モデルの候補削減評価** から再開する。

[新入力とC1への接続](RESEARCH_NOTE_2026-10-24_C1_INPUTS.md)、[証拠台帳](EVIDENCE_REGISTRY.tsv)、
[CURRENT_FRONTIER](CURRENT_FRONTIER.md)、[意味監査](data/c1_four_20261024/SEMANTIC_AUDIT.md)。
E-001/E-067/E-070 CONJECTURED、E-179 COMPUTEDの保護labelを保持。
一般a_z≥5、C1/Q/C2/F/TS/SL/H、全射性は未解決。人間レビュー未。

## 実時計の正本と最終実績

Cycle R-20261024-01、session `785c43d7-babb-4467-9063-967a228328b7`。
[journal](data/daily_research/2026-10-24.json)を正本とする。初回05:59:05.837049にwaiting開始、
06:00:14.070437にsetup、06:02:09.171827にresearchへ。waiting68.233秒を除外する。
06:00〜06:00:14の未計上分を補填せず、予定120分/open/CPU/前日実績を加算しない。

<!-- FINAL_METRICS_START -->
- 実作業開始 `2026-10-24T06:00:14.070437+09:00`、実終了 `2026-10-24T07:59:53.014163+09:00`。journal待機開始は05:59:05.837049。
- **confirmed_work_seconds=7178.944（119分38.944秒）**。120分への不足 **21.056秒**。
- 開始側の未計上14.070秒を遡及加算しない。待機等除外 `{"waiting": 68.233}`、gap 0.000秒、open0、時間外0。
- 待機68.233秒のうち約54.163秒は6時前。窓内の開始不足14.070秒と終了側余裕6.986秒が今回の不足を構成し、待機全体を重ねて加算しない。
- 前日以前の朝18分51秒・追加98分13秒・2026-10-23実績を本日へ加えていない。
- journalは担当が確認した研究・資料読取・監視・検証・記録区間で、純思考時間やCPU時間の測定ではない。CPUは別計上。

| 区分 | 当初予定（分） | closed journal実績（秒） |
| --- | ---: | ---: |
| 開始確認 | 10 | 115.101 |
| C1活用 H01/H04/H09/H13 | 60 | 2260.379 |
| 局所探索 H03/H05〜H08/H10〜H12 | 30 | 2618.381 |
| 別pass監査 | 10 | 1568.373 |
| 引き継ぎ | 10 | 616.710 |

| 実unit | JST開始〜終了 | 確認済み秒 |
| --- | --- | ---: |
| R-20261024-01/start | 06:00:14〜06:02:09 | 115.101 |
| H-20261024-01/macro-semantics | 06:02:09〜06:11:41 | 572.680 |
| H-20261024-01/macro-certificate | 06:11:41〜06:16:51 | 310.049 |
| H-20261024-01/kernel-certificate | 06:16:51〜06:22:30 | 338.634 |
| H-20261024-01/certificate-encoding | 06:22:30〜06:28:10 | 339.587 |
| H-20261024-03/terminal-finite-check | 06:28:10〜06:30:37 | 147.795 |
| H-20261024-04/sixteen-root-future | 06:30:37〜06:33:53 | 195.149 |
| H-20261024-05/odd-run-terminal | 06:33:53〜06:43:07 | 553.983 |
| H-20261024-06/common-prefix-mass3 | 06:43:07〜06:55:25 | 738.576 |
| H-20261024-07/last-free-chain | 06:55:25〜06:59:46 | 261.089 |
| H-20261024-08/symbolic-single-run | 06:59:46〜07:05:39 | 352.924 |
| H-20261024-09/zero-free-motif | 07:05:39〜07:12:15 | 395.875 |
| R-20261024-01/semantic-and-validation | 07:12:15〜07:15:09 | 173.726 |
| H-20261024-10/even-run-followup | 07:15:09〜07:20:15 | 306.671 |
| H-20261024-11/mass-four-joint | 07:20:15〜07:22:42 | 146.421 |
| R-20261024-01/final-semantic-audit | 07:22:42〜07:25:56 | 194.646 |
| H-20261024-12/joint-prefix-representative | 07:25:56〜07:27:47 | 110.922 |
| R-20261024-01/final-evidence-audit | 07:27:47〜07:42:44 | 896.908 |
| H-20261024-13/low-mass-old-iff | 07:42:44〜07:44:33 | 108.405 |
| R-20261024-01/last-connection-audit | 07:44:33〜07:49:36 | 303.093 |
| R-20261024-01/final-handoff | 07:49:36〜07:59:53 | 616.710 |

- 親cycle R-20261024-01に全てを包含。子card時間とsetup/audit/handoffを重ねて加算しない。
- [最終status](data/c1_four_20261024/final-journal-status.json)、[集計JSON](data/c1_four_20261024/final-allocation.json)、[packet manifest](data/c1_four_20261024/final-packet-manifest.json)。
- stop後の集計・manifest書込はjournalへ遡及加算していない。
<!-- FINAL_METRICS_END -->

## 予定・再配分・継続判断

当初予定はsetup10/C1活用60/局所探索30/別pass監査10/handoff10分。
06:08前に実macro接続の新edgeを供給し、最初15分gateを通過。CPU0→120秒を実行前に固定した。
06:27頃に大規模r4一括kernel法をSTOPPEDとして、一般terminal checkと明示16root Qへ切替。
その後は奇数run、共通prefix、強い2供給案の反証、三run完全式、6node motifへ進んだ。

07:12:15に全体検証成功後の別pass監査へ移った。noteの「07:15」は予定時刻の誤記で、
07:13のcheckpointに訂正を残し、実績はjournalの時刻だけを使う。
監査で新しい記号的入力を識別したため07:15:09〜07:22:42にH10/H11、
07:25:56〜07:27:47にH12へ局所探索を再配分し、それぞれ最初15/10/10分gate内に新edgeを得た。
その後の接続監査でH13を識別し07:42:44〜07:44:33に実old窓/endpoint A付きEndNの同値を供給。07:44:09までに個別検査成功、7:45前に数学sourceを最終凍結して以後は意味・出典・保存だけを監査。監査超過は未使用setup/研究枠から支払い、
8時を延長しない。親cycle/子cardの時間を二重計上しない。

前日からの連続無変化0を継承し、本日も新edgeと補助案/共通prefix候補の除去があるため0を維持。
日付resetではない。新しい10代表をr4 graphへ投入した計測はまだなく、状態数削減を主張しない。

## カードと最強の証拠

| ID | 状態 | 当日判断 |
| --- | --- | --- |
| H-20261024-01 | PROVED-LEAN E-390 | 実S-gap macroだけ完了。後続大表の方法STOPPED |
| H-20261024-02 | CONJECTURED | r4全体Qは分類未供給。別statement H04へ切り出し |
| H-20261024-03 | PROVED-LEAN E-391 | 任意具体語の有限terminal checkから全長futureへ |
| H-20261024-04 | PROVED-LEAN E-392 | 明示16語所属を残した全長/全深さfuture Qとold排除 |
| H-20261024-05 | PROVED-LEAN E-393 | 無制限奇数A-runのterminal族と一つ低い閾値の対照 |
| H-20261024-06 | PROVED-LEAN E-394 | 同じprefixのmass3 area5/7を排除 |
| H-20261024-07 | REFUTED E-395 | 2供給案を既知E-389の5供給で棄却 |
| H-20261024-08 | PROVED-LEAN E-393拡張 | 三run local/actual EndNの完全式（endpoint A/長いSを保持） |
| H-20261024-09 | PROVED-LEAN E-396 | 6node motifから任意future追加A≤5 |
| H-20261024-10 | PROVED-LEAN E-397 | k≥1,m≥4k+1の偶数runからfree0なら追加A≤1 |
| H-20261024-11 | PROVED-LEAN E-398 | mass4全6語と共通prefixの面積pair、tripの9/13併存 |
| H-20261024-12 | PROVED-LEAN E-399 | 全mass3/4 suffixを同じ10候補の一代表へ双方向保存 |
| H-20261024-13 | PROVED-LEAN E-399拡張 | 同じr/全bで低mass実old窓の同値と実endpoint A付きEndNの同値 |

各cardに全量化子/受入/停止とcounter-controlを固定してから形式化した。
提案・反証・形式化・監査は別pass。G5はE-390〜394/E-396〜399に逐語statementと仮定/wrapper監査。
Int元pのadapterや子helper/有限row数を独立の研究成果として追加計上しない。

## 失敗・反例・不確実性

- r4 A-event graphは12837状態/513480case、全A≤10/16endpoint候補を計算。独立reverse/DFSと
  928長gap対照が一致したが、全表/関数block/Nat block/state-edge分離のkernel検証は資源上限で停止。
  最初は約11GiB、その後は事前4GiB guard。自己processを終了し、未検証表は.lean.txtへ隔離。
  述語を弱めず、未供給Table仮定で全分類を包むactive theoremも除いた。r4全分類は未証明。
- 再開条件は数学的な小quotientまたは実測で資源を減らすchecker。時間/メモリ追加だけでは再開しない。
- E-395の反例はASAAA|S5 A3 S4 A4 S A3。全tail A10/free4/最小不足1/終端不足4、最後のfree後に5供給。
  既知E-389語の再解析で新語発見ではない。26候補/88実pair、後半holdoutは候補不足で0。
  一般5上限へ単に言い換える修理はしない。
- mass4は既知trip語が両極値9/13を共有する。mass3の排除を全massへ延長しない。
- E-399は低mass情報だけを保存する。旧E-380の深さ4条件付き11clock全EndN保存とは範囲が違う。
  深さやmass≥5を黙って切らず、10状態の全履歴automatonを完成扱いにしない。
- 全体check途中でgrammar対照のconstructor組立1箇所、CURRENT参照E-379/E-382/E-383の漏れを検出し修正。
  失敗logも保持。最終source/registryは成功ログと一致する。

## CPUと再現

- 探索CPU当初0。実行前に親cap120CPU秒/100wall秒と子job capを固定し、研究枠から最大2分を再配分。
- frozen argv/source/input hashはRUNS/LAST_FREE_RUN/LAST_FREE_INDEPENDENT_RUN/MOTIF_RUN。
  探索5jobの丸めtime値はuser+sys約6.66CPU秒/wall約6.73秒。validation/Lean/記録CPUは別で一部未取得、総CPU未確定。
- Q4の719状態入力は前日のCOMPUTEDデータを再利用したもので、今日の独立holdoutと呼ばない。
- [source manifest](data/c1_four_20261024/final-source-manifest.json)とdirty overlay、source snapshotに
  未追跡Three/ThreeQ/SS2を含むLean8ファイルを保存。HEADは`5606b64d27290a9959e1dbf19d5e7c58840a0a85`。
- 最終small sourceは`python3 docs/data/c1_four_20261024/generate_final_sources.py`でbyte一致を確認。
  `generate_lean.py`等は停止した大表の診断用で、現行sourceの再生成に使わない。

## 変更と検証

当日変更: Recaman/BlockSuffixPositivity.lean、Recaman/Audit.lean、新規FourNonsuppliedData/SixteenRootAreaData、
CURRENT_FRONTIER/EVIDENCE_REGISTRY/PROOF_MAP/RESEARCH_PORTFOLIO/GLOSSARY、C1親card、当日13card/翌日card、
当日note/DAILY、DAILY_RESEARCH_SCHEDULE/AUTOMATION_PROMPT、G5監査9件、当日packet/journal。
関連しない既存の追跡済みdirty差分15箇所とRecaman.lean/viewer/SS2/保護表の初期hash一致を確認。
stage/commit/pushは行っていない。他sessionの作業を保持。

- `./scripts/check.sh`: 最終399entries/183PROVED-LEAN、408jobs/2782宣言、公理監査成功。
- `python3 scripts/harness_gate.py --lint-module <new file>`: Four7/8、Sixteen29/30の実内容判定。
  BlockSuffixも147/161（補助wrapperを新結果にしない）。
- G1〜G5: E-344以降39対象pass、保護4label維持。reopen gateの完了済みr3入口も現状へ訂正。
- `make test-tools`: dev7/session12/harness18、計37テスト成功。新gate/tool実装変更はない。
- `make brief`: E-399を含む現状と次cardを反映。最終logと[RUN_INDEX](data/c1_four_20261024/RUN_INDEX.md)参照。
- 既存automation `recam-n-6-8`の入口を翌日cardへ更新。時刻/同thread/ACTIVE/作成時刻をreadbackで保持確認。
  設定更新だけで将来120分を完遂済みとはしない。

## 次の一問（翌日以降の開始点）

[H-20261025-01](HYPOTHESIS_CARD_2026-10-25_JOINT_OLD_SUPPLY.md)。E-399の同じrを最初に一つ選び、
全future clockで必要mass3/4の実EndNを正確に判定する既証明E-399を使い、固定r4モデルからどの候補/path/tagを除けるか評価する。実old窓/EndNの同値を再証明しない。
最初15分で新しい供給edge/具体な候補除去/反例がなければ、その方法をSTOPPEDとし、
残り45分をrun-family multi-run分解25分と小certificate20分へ再配分する。
CPU探索は当初0。新graphの前にfresh protocol/上限/argv/dirty hash/独立checkerとholdoutを固定する。
旧r3/深さ/Q、C2/P、大規模r4時間追加を再開しない。一unitの完了/停止だけでは一日を終えない。
