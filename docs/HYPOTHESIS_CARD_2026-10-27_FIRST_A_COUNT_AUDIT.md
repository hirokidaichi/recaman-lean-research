# Hypothesis card: 第一A源の平方条件と既存countだけで排除できるか

- ID: H-20261027-16
- Status: REFUTED（count-only排除方法、E-430）。実第一A源排除/C1はCONJECTURED。
- Parent: R-20261027-01/E429。Mode: 別機構の局所探索、07:28開始、15分gate。

問いは、残る第一A-run内sourceを既存の必要count不等式とtarget平方条件だけで排除できるかという包含監査。自由Endable tag履歴を生成する枝は再開しない。
M,L,T>=0、1<=d<=M、A=M+L+T<=20、R=j+1∈5..10、m,s>=0、d²=(L+T)(L+T-2R)-2Ls、m+s=d+L+T-R。
実run別freeの必要条件を数値a1,a2,a3で弱化して監査: min(M,2)<=a1<=M、M<=2a1、M-a1<=2、0<=a2<=L、L-a2<=3、0<=a3<=T、T-a3<=6、M+L<=2(a1+a2)+1、4<=a1+a2+a3<R、A-(a1+a2+a3)<=11。
これは実EndN列/実zero/全positive不足を持つcounterexampleではない。SATなら『count条件だけからの排除』方法の反例で、第一A source排除命題/C1の反例ではない。UNSATなら実入力の各必要edgeをLeanで供給してからだけsource排除へ進む。

d/s/mの関係を変えない。A/S長上限延長・local小定数修理・同r4表再実行なし。費用/argv/dirty hashをFIRST_A_COUNT_AUDIT_PROTOCOL.jsonに固定、singlePython worker CPU2/3秒（探索/独立literal replay）、wall4/5秒、最初5数値witnessで停止。独立replayはwitnessのliteral mass/area/不等式照合でfresh holdoutではない。
受入は新しい未供給couplingの特定、または完全なsource排除。SAT数値tuple自体を実研究の反例進展に数えない。修理1回、gate失敗ならaudit停止、追加範囲なし。

07:28最初5の数値tupleで停止。全domain UNSATとは言わない。初例M1/L5/T6/R5/d1/m6/s1/free1,2,1はliteral source AS6 A5 S A6 S4のmass1/area0を持つが、空old/head39の実free10で数値4と一致しない。CPU discovery0.035630/replay0.031608秒。新たな実counterexampleなし。同じcount条件だけの方法STOPPED、H17源再使用制約へ切替。

## 当日journal確定実績
親cycle R-20261027-01: 06:01:46.075185〜08:00:04.411787、確認済み118分13.925秒、不足1分46.075秒。
このcardの明示unit実績はH-20261027-16/explore/first-A-count-audit: 3分43.665秒。
同じcycleの内訳で別cycle/CPUを追加加算しない。[当日DAILY](RESEARCH_HANDOFF_2026-10-27_DAILY.md)/[journal](data/daily_research/2026-10-27.json)に予定と実績・再配分・失敗・次判断を保存。
