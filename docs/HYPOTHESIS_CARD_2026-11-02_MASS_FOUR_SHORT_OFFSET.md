# H-20261102-08: mass4/v5 no-old 境界

Status: PROVED-LEAN（末尾の終了時判断を正本とする。以下は開始時の仮説・費用条件）。07:05近傍開始、15分gate07:20。探索CPU追加0。親R-20261102-01。

問い: 同じ元p/padded/zero-fullpositive/正三run zerohead/同old targetmass4/最終S5、最後A-rayの全old source無しの部分枝の全長full-tail free-gapを得るか。全run長/全old historyを量化し、areaやheadfree結論を入力しない。old有り/他C/vは別scope。

chain: T=R+1、counterからheadfree4/local6飽和/headS12..15/R>=5。initialS源を0に制限し、firstA源の同target平方と共存が可能かを監査する。最初15分の受入はsource-conditioned inequality/strict候補削減/反例。初期S0排除だけをfullgapと呼ばない。

反証pass: i1は一般のsource-prefix cutだけで排除できない。source delay K=i+j-T=i-2の負境界を保持。targetmass4のkeyをmass3上界2で切らない。headfree5は早期oldを要する既存E497をno-oldへ使わない。

停止: 数値定数の追加修理一回まで。新source edgeも候補削減もなければ、残時間は独立したtargetsource/非zerohead仮定監査へ。既知S3/C3/長separator/C1初期監査を反復しない。旧表へ資源追加しない。

07:06:15: InitialFirstParityCollisionを個別512MBで検証。initialS0は全zeroheadでarea=-2(v+1)Sを固定しword parityよりS偶数。一方firstA1は(h-v)^2=2S-1を強制して平方がmod4の3となり矛盾。target mass/R/S上限/positivityを全て不要にできた。これはfullgapではなくsource非共存edgeで、C4専用の有限S候補と区別する。

07:09の拡張問い: 上の非共存と同target keyの単調比較から、C>=4/v=C+1の全長fullgapまで一般化できるか。全C/全v/全run長/全old履歴を量化し、旧C4限定のroot採用は全長実接着まで保留。最初15分gate07:24。area帯/no-old/oldseed/headfreeを無条件入力せず、old無しはlast5/headfree4、old有りは実clock<=1/mass>=5を内部供給して既存headfree6/last7で払う。進まなければ既に検証したsource非共存だけを正確なscopeで登録する。

## 終了時判断

E-517 PROVED-LEANへ一般化、全C>=4/v=C+1。raw parityは全vでtarget不要。 全体検証・逐語audit・実績正本は11/02 DAILY/journalを参照。親C1全体は未解決。
