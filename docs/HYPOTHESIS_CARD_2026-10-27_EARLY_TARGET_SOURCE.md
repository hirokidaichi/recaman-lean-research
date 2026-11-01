# Hypothesis card: 三run反例のtarget源を第二A-runより前へ制限

- ID: H-20261027-15
- Status: PROVED-LEAN（E-429）
- Parent: R-20261027-01/E428。Mode: 活用、07:25開始、15分gate、CPU探索0。

実三A-run free-gap反例の任意P2供給窓start tは、第二A-run開始n+h+M+mより前であるか。全元prefix/run長/実EndN/relative positiveを保持する。
E428は第二A-run内を排除済み。最後S開始以後の窓は具体S^s A^T S^jのlocal供給を意味し、T=2(j+1)、s>=j+1を供給する。既存E411の5run source予算をそのまま用いてT<=最後A-run実free+6。第一A-runが非空なら最初Aはfreeなので全free>=T-5>=j+1（j>=4）となり反例と矛盾。M0は既存二runfree-gapへ合併して排除する。
local<=2/<=3を新定数で修理するunitではなく、既存予算とtarget source形から特定の開始領域を全て排除する。
反証pass: M0、L0、T0、j0（実残余ではj>=4を導く）、firstA freeとtargetを半開countへ混ぜない、local/old重複は既存予算の和集合上界のまま。old/第一A/初期S/第二Sは残す。
受入: 任意actual target window tの開始上限をLean/G5/Audit/check。rやA上界を仮定せずE416から供給。数学修理1回、15分でactual source領域排除へ届かなければSTOPPED。

07:27全体check426jobs/2910宣言/G5/lint/Audit成功。数学修理0、assoc/count構文を同じ形に揃えて受理。M0は既存二runへ合併、sourceの新しい場所制約だけを供給した。C1反例不在は未証明。

## 当日journal確定実績
親cycle R-20261027-01: 06:01:46.075185〜08:00:04.411787、確認済み118分13.925秒、不足1分46.075秒。
このcardの明示unit実績はH-20261027-15/exploit/early-target-source: 2分05.716秒、H-20261027-15/audit/early-target-source: 1分04.206秒。
同じcycleの内訳で別cycle/CPUを追加加算しない。[当日DAILY](RESEARCH_HANDOFF_2026-10-27_DAILY.md)/[journal](data/daily_research/2026-10-27.json)に予定と実績・再配分・失敗・次判断を保存。
