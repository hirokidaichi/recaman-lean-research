# 2026-10-25 日次研究の引き継ぎ

## 結論

新しい数学的証拠あり。E-407（PROVED-LEAN）は任意長/任意rの実供給A直前のS-gapについて、
旧 j≤2A−2 を **2j+2≤A** へ強化した（Aは先行する全A）。A=10ならj≤18からj≤4へ絞れる。
全jで等号となるlocal供給族も証明。これは一般rankの量的入力であり、free個数による一般rank自体は未供給。

**r4分類は未証明のまま。E-404 CONJECTURED、E-388 COMPUTEDを維持。**
同12837状態の証明DAGはA4〜10の11316nodeまでkernel成功したが、A3以下/初期Checkedまで届かず
07:45:00.034521の固定期限で停止した。部分層・条件付きreductionを全長分類と呼ばない。
未検証12ソースをpacketへhash付き隔離し、active sourceの全体checkは412jobs/2811宣言で成功。

## 実時計・予定と実績

親cycle R-20261025-01、session `51dc3c8d-740c-4ba1-9d72-6dae5bcab781`。
実開始06:01:21.862027 JST。起動遅れを遡及補填しない。7:45以降の新規数学探索なし。

<!-- FINAL_TIME_START -->
実開始 06:01:21.862027、実終了 07:59:10.380882 JST。`confirmed_work_seconds=7068.519`、**117分48.519秒**。
120分に対する不足 **2分11.481秒**。起動遅れ・枠内の終了余白を遡及補填しない。
待機/blocked除外 {}、未確認gap 0秒、枠外作業 0秒。
終了cursorはnull、open区間の先取りなし。journalは確認済み作業区間で純CPU/純思考の計測ではない。

| Phase | 予定 | 確認済み実績 |
| --- | --- | --- |
| setup | 10分 | 1分32.076秒 |
| research（活用+探索） | 60+30分 | 82分56.746秒 |
| audit | 10分 | 21分33.417秒 |
| handoff | 10分 | 11分46.280秒 |

実unitごとの区間（上表の内訳で追加加算しない）:

| Unit | 実績 |
| --- | --- |
| R-20261025-01/start | 1分32.076秒 |
| H-20261025-01/fixed-root-model | 3分14.657秒 |
| H-20261025-01/decision-and-small-certificate | 5分39.659秒 |
| H-20261025-02/mass-barrier-formalization | 6分44.378秒 |
| H-20261025-03/future-context-erasure | 2分33.390秒 |
| H-20261025-03/quotient-design | 3分58.069秒 |
| H-20261025-03/independent-quotient-audit | 2分23.551秒 |
| H-20261025-04/direct-proof-dag | 3分07.495秒 |
| H-20261025-04/dag-benchmark | 3分54.912秒 |
| H-20261025-04/certificate-interface-and-controls | 7分01.108秒 |
| H-20261025-05/context-sharpness | 2分46.348秒 |
| H-20261025-06/separator-barriers | 2分21.863秒 |
| H-20261025-06/two-run-family | 4分21.151秒 |
| H-20261025-07/linear-local-checker | 5分35.231秒 |
| H-20261025-07/fast-full-certificate | 1分34.645秒 |
| H-20261025-08/local-gap-extremal | 3分44.450秒 |
| H-20261025-08/gap-key-and-count | 5分26.987秒 |
| H-20261025-08/old-gap-bound | 2分58.043秒 |
| H-20261025-09/proved-gap-pruning | 8分55.810秒 |
| H-20261025-09/pruned-full-certificate | 6分35.002秒 |
| R-20261025-01/semantic-source-audit | 4分14.033秒 |
| H-20261025-10/layered-proof-validation | 7分04.522秒 |
| R-20261025-01/semantic-audit | 2分45.722秒 |
| R-20261025-01/resource-and-semantic-audit | 4分48.809秒 |
| R-20261025-01/final-validation | 2分40.332秒 |
| R-20261025-01/final-handoff | 2分43.140秒 |
| R-20261025-01/provenance-and-final-record | 3分25.173秒 |
| R-20261025-01/statement-scope-handoff | 4分32.951秒 |
| R-20261025-01/closing | 1分05.015秒 |

[確定時間のJSON](data/joint_old_20261025/final-time-summary.json)。並行CPUを足さず、前日/別sessionの時間を含めない。
<!-- FINAL_TIME_END -->

定刻予定はsetup10/活用60/局所探索30/別pass監査10/handoff10分。
H01で候補削減1件を得たが圧縮効果が小さく、同10root大表投入をSTOPPEDにして任意prefix/文脈/一般gap入力へ切替えた。
監査超過とproof-checker検証は研究枠から支払い、8時を延長しない。
活用/探索を混ぜたunitもあり、その内訳の実秒数はjournalが分離計測していない。phase/実unitの表を正確な実測として使い、
予定60/30をそのまま実績としない。複数cardは同じ親cycleのunitで、親子や並行CPUを二重加算しない。

## 安定した成果と境界

| Evidence | 水準 | 何が変わったか・仮定 |
| --- | --- | --- |
| E-400 | COMPUTED | 同じ低mass代表10rootの射影12837→12836/40024→40023、1状態/1辺のみ削減。root合計128149/最大12828、16終端候補不変。同大表方法STOPPED |
| E-401 | PROVED-LEAN | 任意前置語と明示長S/偶数A-runの形で、追加free0なら任意長future全A≤1 |
| E-402 | PROVED-LEAN | suffix最大massと明示残りA予算を使う全future local文脈消去。old用実総mass/areaは別保持 |
| E-403 | COMPUTED | 新future文脈商10106状態/35440辺（2731状態/4584辺減）、全product/辺独立照合、520長gap対照/1920future holdout。商kernel未供給 |
| E-404 | CONJECTURED | 16候補への全包含/深さ4/任意future Qが目標。初期kernel未供給、全体を昇格しない |
| E-405 | REFUTED | 無予算future消去案を任意深い負bufferの一様反例族で反証、閾値1への緩和も反証。親C1/実軌道の反例ではない |
| E-406 | PROVED-LEAN | 実総Sとsuffix最大massを分離して短いseparator条件へ。無制限二run族でも追加free0の全future全A≤1。任意tailの形供給は残る |
| E-407 | PROVED-LEAN | 実EndNのlocal/old両方で2j+2≤全A、長さ/深さ/free/r/j上限なし。全Aとfree Aの間の未知edgeは残る |

E-384の未Lean存在方向には依存しない。16候補への包含は各16語の実現定理とは異なる。
E-392は明示16root仮定のfuture Qのまま。a_z≤4からその仮定を供給したとは記述しない。

## 検証・失敗した方法・再開条件

- H04: 表lookupなし正の帰納的Checked DAG。default parallel benchはCPU上限でexit152。単workerでmembership nil分岐不足を検出・修正。
  同256nodeの成功bench72.52wall秒/peak627072KiB。A11 good/子欠落の負例は期待どおりkernel拒否。
- H07: 全wordの単一scanと元macro同値をLean証明、bench31.24wall秒へ改善。slow全jobは966.515wall秒で自分のgroupだけ停止。
  linear全jobも次のpruningへの置換で1208.844wall秒/peak3588192KiBで停止。両方とも初期proof未供給。
- H09: E407の一般半数gapと予算先判定を使う全40macro同値がLean成功。bench15.08wall秒。
  pruned全jobは560.921wall秒/4195632KiBで4GiB RSS guard STOPPED。
- H10: A数の11依存layerへ同じ全状態/全childを分割。A10/9/8の64node bench4.87wall秒/521072KiB成功後、全jobへ。
  全jobは864.548wall秒/peak3701456KiB、固定07:45期限でSTOPPED。全r4の反例ではない。
  全sourceを[data packet](data/joint_old_20261025/layered_source/)へ隔離。今日の再試行なし、同じjobの時間/メモリ追加のみで再開しない。
- pruned最初のbenchは先行assert失敗後に非errexit shellが欠落fileへ進みexit1。成功版と区別し以後set-e/exit確認へ訂正。
- E407最初の完成commentaryはBool.or分岐のcompile完了を先走り、直後に訂正。数学主張は変えず、half-gap-final-lean-2.log exit0と最終全体checkで確認。
- 最終check初回はfrontier書換時の旧Evidence参照欠落で停止。E379等の実際の適用範囲を戻し、final-check-2.logで全て成功。

## 変更ファイル

- 新規active Lean: `Recaman/PrefixMassBarrier.lean`、`FourEventProof.lean`、`FourEventFast.lean`、`FourEventPruned.lean`。
  Prefixの新不等式と一般checker同値を保持。r4の条件付きreductionを無条件の成果と数えない。
- `Recaman.lean`の担当importと`Recaman/Audit.lean`の担当宣言追加。以前からある他sessionの変更は保持。
- `EVIDENCE_REGISTRY.tsv` E400〜407、`statement_audits/E-401/E-402/E-404候補/E-406/E-407.md`、
  `CURRENT_FRONTIER.md`、`PROOF_MAP.md`、`GLOSSARY.md`、`RESEARCH_PORTFOLIO.md`。
- 今日の10枚のcard、`RESEARCH_NOTE_2026-10-25_C1_GAP.md`、本DAILY、翌日H26カード、
  `DAILY_RESEARCH_SCHEDULE.md`、`DAILY_RESEARCH_AUTOMATION_PROMPT.md`、日次journal、当日data packet。
- activeから外した12候補sourceは`data/joint_old_20261025/layered_source/*.lean.txt`へ保存。削除で反証扱いにしない。
- 既存automation `recam-n-6-8` のpromptのみ更新。ID/種別/名前/時刻/状態/threadは同じ、重複作成なし。

## Commands・証拠・CPU

[command index](data/joint_old_20261025/COMMAND_INDEX.md)、[全体check成功](data/joint_old_20261025/final-check-2.log)、
[全新moduleのlint](data/joint_old_20261025/final-module-lints.json)（12候補はstaticのみでarchive）、[最終registry/G1〜G5](data/joint_old_20261025/final-registry-2.log)、[別pass意味監査](data/joint_old_20261025/SEMANTIC_AUDIT.md)。
主な実行は各protocolのargv/dirty hash、個別Lean、`./scripts/check.sh`、各new moduleへの`harness_gate.py --lint-module`、
E401/E402/E404候補/E406/E407の逐語G5、`generate_layers.py --check`、journal start/checkpoint/stop、`make brief`。
ゲートの実装変更なし。sorry/admit/native_decide/独自axiom追加なし。PROTECTED_CLAIMSの変更なし。stage/commit/pushなし。
既存406Lean中は担当Audit以外のhashを保存し、別sessionの変更を保持した。[最終source manifest](data/joint_old_20261025/SOURCE_MANIFEST_FINAL.json)にactive410 sourceのhashを保存。
直接protocolに凍結した47source hashは全て一致するbytesをpacketへ保存。以前の短いsourceはprefix/guard差分から復元し、凍結SHA256が一致したものだけ採用（現active sourceの変更ではない）。

探索のCPUは完了timeログから別計上し、並行Lean検証を実時計へ加算しない。
完了timeから得られたCPUの既知部分和は302.83秒。途中終了jobはtimeが空、個別Lean/最終checkのCPUも全ては測定していないため、当日CPU総和は未計測。[資源の部分表](data/joint_old_20261025/RESOURCE_ACCOUNTING_PARTIAL.json)を完全総和と呼ばない。
**計測不備:** run_guardのRLIMIT_CPUは継承process単位で、group累積CPU予算の強制ではなかった。
wall/RSS/7:45はgroup監視。新規CPU許可前に累積計測/停止を検証する。CPU未計測を推定で実測扱いにしない。

## C1への距離・不確実性

一般の全Aから見たgapの鋭い必要条件と、無制限run familyのterminal条件が増えた。
一方、一般a_z≥5、実free個数との供給連鎖rank、r4の初期分類kernel、一般Q/C1は未解決。
さらに全体H/SLにはC2/TS等が残る。証明数/時間から完成率を算出しない。
人間レビュー未。G5の解説を定理ごとに精密化し、現在時点のEndN同値と未来free0 count結論の仮定を区別した。署名/数学sourceは変更なし。停止した方法と命題のCONJECTUREDを区別する。
新しいedgeが得られ連続無変化0（成果による更新、日付resetではない）。

## 次の判断・再開する一問

[H-20261026-01](HYPOTHESIS_CARD_2026-10-26_FREE_GAP.md): 同じ元基点zero・正不足・真のEndN履歴で、
**j+1≤先行非供給A数r**を語長/rに依らず導けるか。まず既知r2境界、小例、local/old、弱化履歴で反証する。
最初15分で独立な不等式/実prefix反例/候補削減がなければ方法を止め、key-return25分とmulti-run条件供給20分へ切替える。
全A≤2r/結論を仮定せず、r上限延長で再開しない。CPUは0から、上記計測不備の対処前に新探索しない。
自動実行の入口と同じlocal promptを更新し、ID/ACTIVE/時刻/thread/日次必須final報告の保持をreadbackした。
次回は本DAILY→[ノート](RESEARCH_NOTE_2026-10-25_C1_GAP.md)→H26カード。完了済み低mass初期評価/r3/C2/P監査を繰り返さない。
