# Hypothesis card: 三A-runの次供給条件を新入力に使う

- ID: H-20261026-09
- Status: CONJECTURED
- Parent: R-20261026-01、E-414。07:30途中保存後の別機構探索、gate07:40。

任意BlockWord元0実prefix後のtail Sh AM Sm AL Ss AT、元0のzero/全positive不足、次Sj後が実供給とする。
第一の問いは全run長でj+1<=実free数rか（親H01の三run制限）。補助候補は「次の実供給が可能なら先行全A<=2r+1」。
補助候補の反例は親free-gapの反例と区別する。既知ASAAA|S5 A3 S4 A4 S A3はA10/r4で無条件A<=2r+1を破るがterminalなので次供給条件は満たさない。この既知反例は新成果にしない。

本日の受入は新しい供給源不等式、候補削減、または実EndN ledger付き反例。有限違反なしだけならCOMPUTEDで方法STOPPED。
既存r3分類/r4全表/old-budget削減0のjobに時間を足さない。CPU予算0から、実行前にsingle-worker discovery/holdout各CPU10秒・wall15秒、controller予備2秒へ再配分し、探索枠から差引く。
discoveryは4 prefix×[1,2,3,4]^6の新三run形、holdoutは別prefix/tuple×[5,7]^6。既知terminal対照はfresh holdoutと呼ばない。
修理1回。補助案が反証されたら一度だけ必要条件を抽出し、親に新しい反例がなければ一般命題はCONJECTUREDを保持。

## 07:34 source-count subunit事前固定

三run conditional候補の有限discovery16384/holdout192組で親gapも補助countも違反0。一般の独立edgeはまだない。
別機構として、第三A-run前のSh AM Sm AL Ssにlocal供給clockが高々2かを、五源の同時mass/keyから攻撃する。第一S/第一A/第二S/第二A/末Sのsourceを独立tag化しない。
事前THREE_SOURCE_PROTOCOLでCPU合計10秒（各5秒/wall8秒）+controller2秒を探索残枠から再配分、07:40gateは延長しない。候補が反証されても親free-gapは未反証。

## 07:38 判定

親三run free-gap/条件付き全A<=2r+1はCONJECTURED、有限違反なしだけで一般化しない。local<=2と一回の修理<=3はE415 REFUTED、同じ小定数方法STOPPED（追加修理なし）。
代わりに既存のgeneric5run+old1予算を使う別の紙上chainを完成し、E416 PROVED-PAPER: 三run反例はr4〜9/A<=20/j<=9へ縮約。新しい無制限長入力であり、三runreduction全体は未Lean・人間レビュー未。
数学修理1回で停止。generic安全予算は失敗したlocal定数の再修理ではない。実EndN接着と残余排除は次回課題。

07:40別pass literal監査: 四clock例v A12は空BlockWord/元0zero/全正不足も満たす（COMPUTED）。第三A-run内の実EndNは2/3/9/11。Lean確認はlocal四clockのみで、元history監査は計算のまま。親free-gapの反例ではない。

## 当日journal確定実績
親cycle R-20261026-01: 06:02:22.120877〜07:59:56.352321、確認済み117分34.231秒、不足2分25.769秒。
このcardは同じcycleの一部で、別cycle/CPUとして追加加算しない。unit別実績/commands/再配分/失敗/残課題は[当日DAILY](RESEARCH_HANDOFF_2026-10-26_DAILY.md)と[journal](data/daily_research/2026-10-26.json)を参照。待機/未確認/前日分の加算なし。
