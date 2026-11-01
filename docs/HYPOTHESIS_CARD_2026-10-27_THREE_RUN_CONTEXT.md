# Hypothesis card: 三run反例を実historyの有限contextへ移す

- ID: H-20261027-09
- Status: PROVED-LEAN（E-423）
- Parent: R-20261027-01/E416/E419〜422。Mode: 活用、06:54開始、15分gate、CPU探索0。

任意BlockWord全prefixと三run Sh AM Sm AL Ss AT、relative全positive不足、実Sj後EndN、実free<j+1という反例を入力とする。
M/L/T/m/s/jは変えず、実符号列gと境界N/先頭Hを構成し、BlockWord(seg g0N)、N<=47、H<=39、m/s<=38、M+L+T<=20、j<=9、同じshapeと実target/元実free count/relative positive/違反を保存できるか。
最終target clock<=191（target A込み192符号）。元反例からの一方向縮約であり、有限領域内の反例不在やC1を証明したとは呼ばない。正準historyの絶対zeroを仮定し直さず、必要なrelative positiveを実count移送で供給する。

紙上chain: E416でA20/j9、E419/E420でm,s<39。h>=39はE421で空old/H39へ。h<39はE422でold最終47clockへ。この分岐は原history全clockの供給/free同値を証明済みにしてから行う。H39代表はh>=39排除ではない。
反証: n0/h0/emptyrun/j0、長いS/oldprefix、targetは窓条件に加えてA符号を保持、countはtargetを含まない半開区間、freeと供給の重複/基点移動。無予算消去E405を再開しない。
受入: 各actual条件と元free同値を含む存在命題をLean/G5/Audit/check。数値上界の単なる足算や新Prop定義は成果にしない。
15分で存在history/count接着ができなければSTOPPED。大表/旧N32の延長には切替えず、同じold prefixのsource共有に戻る。修理1回まで。

06:56全体check422jobs/2893宣言成功（最初はCURRENT_FRONTIER参照未追加でgate拒否、参照を追加して再検証）。数学修理0、assoc/list長/rw向きだけ修正。無制限から有限の実counterexample移送を供給し、有限領域の反例排除/C1は未解決。

## 当日journal確定実績
親cycle R-20261027-01: 06:01:46.075185〜08:00:04.411787、確認済み118分13.925秒、不足1分46.075秒。
このcardの明示unit実績はH-20261027-09/exploit/three-run-finite-context: 1分26.215秒、H-20261027-09/audit/finite-context: 2分28.204秒。
同じcycleの内訳で別cycle/CPUを追加加算しない。[当日DAILY](RESEARCH_HANDOFF_2026-10-27_DAILY.md)/[journal](data/daily_research/2026-10-27.json)に予定と実績・再配分・失敗・次判断を保存。
