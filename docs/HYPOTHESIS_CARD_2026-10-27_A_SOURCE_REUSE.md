# Hypothesis card: 同じA-run源の再利用はgap平方量を消費するか

- ID: H-20261027-17
- Status: PROVED-LEAN（E-431）
- Parent: R-20261027-01/H16。Mode: 活用、07:32開始、15分gate（07:45数学停止を優先）、CPU探索0。

任意内部語u、同じA-runからの二source長d,e、前のA-only未来i、後のA未来TとS-gap j。
A^e u A^iとA^d u A^T S^jが共に実P2のmass1/area0なら、2 cntF(u)(e-d)=j(j+2)を全語長で導けるか。i/T/uの長さやA数上限なし。
j>=1ならcntF(u)>0かつd<e。従って同じsourceを再利用するには、以前の窓がA-run中でより早い開始を使い、2cntF(u)がgap平方量j(j+2)を割り切る必要がある。『任意源は一回しか使えない』とは仮定しない。

紙上chain: A末尾追加はrunKeyを変えない。targetのSj末尾をmass式とarea0から外すとrunKey(A^d u)=-2(j+1)^2、前窓はrunKey(A^e u)=-2。prepend_Aの差4cntF(u)(e-d)をとり接着。
反証: j0ではd=eも可能でstrict順序を主張しない。u空/S0ならj>=1の二窓は不可能。符号負mass/任意長u/別のi,Tを許す。同じu/同じA-runという依存関係を落とさない。literal actual seg/Winで元clockを保存する。
H16の数値tupleはC1反例でなくcount-only排除の弱点。u=S6 A5 S、d1/j4では14(e-1)=24に整数解なし。u=S7 A6 S、d1/j5では16(e-1)=35も不可。これらを元count witnessのsource availability監査に使う。
受入: 全長word式/順序とactual同一A-run二Winへの接続、G5/Audit/lint/check。数値tupleを反例やC1解決に数えない。数学修理1回、07:45以降新探索なし。

07:37全体check427jobs/2918宣言/G5/lint/Audit成功。数学修理0、List.length_replicate/Int castの表記のみ修正。A版実adapterは残長d/eの0境界も許す。S版はliteral P2語の式で、全混合futureへのrankは供給していない。

## 当日journal確定実績
親cycle R-20261027-01: 06:01:46.075185〜08:00:04.411787、確認済み118分13.925秒、不足1分46.075秒。
このcardの明示unit実績はH-20261027-17/exploit/A-source-reuse: 3分19.326秒。
同じcycleの内訳で別cycle/CPUを追加加算しない。[当日DAILY](RESEARCH_HANDOFF_2026-10-27_DAILY.md)/[journal](data/daily_research/2026-10-27.json)に予定と実績・再配分・失敗・次判断を保存。
