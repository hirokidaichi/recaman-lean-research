# Run数別の実供給予算（監査中の派生候補）

- ID: H-20261029-07 / R-20261029-01/H17
- Status: PROVED-PAPER（未Lean・人間レビュー未）。候補はH16監査中に得たもので、初日から事前登録したと装わない。
- Question: 任意k>=3、全長のk個の非空A-runについて、同じ元0/pの実供給総数E<=k(k+1)-1を既存run予算から導けるか。
- Exact domain: f:Nat->Bool、n>=0、seg f 0 nはBlockWord。n以降はS^h A^a1 S^s1 A^a2 ... S^s(k-1) A^ak、h>=0、全ai>=1、全si>=1。長さB。全0<t<=BでcN(EndN f 0)n t+1<=cN(S)n t。全countの基点を0に固定する。元p版はpからのcountのzero/全positiveから相対条件を供給する。k・各長さ・old historyに上限なし。
- Acceptance: k=3/4の境界、4番目以降のold/localの完全包含とcount加法を別passで照合した完全な紙上chain。Leanへ移さない限りPROVED-LEANへ昇格しない。派生countを独立の大きな機構として数えない。
- Stop: 15分以内に同じold prefixの全supplierの包含またはcount加法が確認できなければCONJECTUREDのまま。任意runのfree-gapそのものは入力しない。
- Falsifier: k3は既存E416と一致、k4の3個のseparatorが全て1/初期h0の境界、old massに上限なし、E415の第三ray local4clockを保持。全positive条件とgenuine separatorを勝手に落とさない。
- CPU exploration: 0。既存証明の読取と紙上監査。有限history走査はしない。
- Hypothesized chain: first3 actual supplies<=11; ray t>=4 has2t-1 preceding constant tail blocks plus same old BlockWord withcntF>=3, so actual supply<=2t; intervening S hasEndN0; sum givesk(k+1)-1。
- Consequence to check: actual target afterS^j and putativefree r<j+1 forces4<=r<=k(k+1)-3, A<=2k(k+1)-4, j<=k(k+1)-3。S長/historyは依然無限。有限計算や全history有限分類とは呼ばない。
- Allocation: auditから最大15分の数学的派生検算へ移し、親の残時間から支払う。実績はjournal H17だけに計上。07:45を越えて新探索しない。

## 検算の決定

[完全な紙上chainと反証pass](RESEARCH_NOTE_2026-10-29_RUN_COUNT_BOUND.md)でcount加法/同じold prefix/3S境界を確認。k4のE19/r4..17/A36/j17は次の計画用派生評価。新しい源課金機構ではないため別のPROVED-LEAN行や成果数を増やさない。数学的CPU探索なし。次は四run old-targetのsource-conditioned actual free課金で、三run/旧finite表の再実行はしない。

## H21: 次の限定形式化（実行前の固定）

一問: 上の紙上chainの**k=4**について、同じ元0の全length/全old prefix/全positive不足の実供給<=19と反例残余free4..17/A36/j17をLeanへ移せるか。一般kの帰納法は今回形式化しない。予算19や実free結論を仮定にしない。最初の三run<=11/第四ray old<=1+local<=7を実cN分割で結合する。語長/A/Sを有限範囲に切らない。最初15分gate、07:45以降新形式化なし。資源上限は既存のper-process10CPU/512MB/20wall検証契約、CPU探索0。cold rebuildの上限増加・同job再実行はしない。kernel失敗なら一回の修理まで、未検証sourceはmain importへ加えない。成功しても派生予算であって四run free-gapや新rankとは呼ばない。

### H21実行結果

07:34:08 Nat全供給19/残余、07:35:05元p zero/padded count接続をLean確認。最初の試行はNat加法の括弧とD=B+vのcount項正規化のproof error、一回の修理で同じstatement/上限のまま通過。一般kはPROVED-PAPER、k4だけE456 PROVED-LEAN（fullcheck/Audit登録後）。Aは空も許可する強いcount statement、separator三つは非空。四run反例不在は未検査。

## 当日実績への参照

親R-20261029-01のjournal確定実績は115分25.230秒（不足4分34.770秒）。このカードへ親の全時間を追加計上しない。unit別時刻/予定と実績/CPUは[当日DAILY](RESEARCH_HANDOFF_2026-10-29_DAILY.md)と[journal](data/daily_research/2026-10-29.json)を正本とする。
