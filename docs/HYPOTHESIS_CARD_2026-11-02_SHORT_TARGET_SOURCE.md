# H-20261102-11: 短separatorのactual source位置削減

Status: PROVED-LEAN（末尾の終了時判断を正本とする。以下は開始時の仮説・費用条件）。07:23開始、15分gate07:38、07:45探索終了。親R-20261102-01。探索CPU追加0。

問い: 任意元0/p/padded/zero-fullpositive/正三run zerohead/同old targetmass C>=4/1<=v<Cのcounterから、全old排除、initialS/firstA local源の排除、middleS源ならC=v+1/i0/M=R+1というstrict source削減を内部供給できるか。C/R/M上界やfree結論を入力しない。

chain: 実target keyとC4/1<=v<=CからheadS8、r3 countでheadfree4、counterからR5。第一A run供給2よりM<=R+1。同target順序でT<=jなので全old無し。E519 strict cutは全local sourceに適用可、firstA以前はprefix A<=M-1<=Rなので不可、middleSはprefix A=Mを保持しM>=R+delay+1。従ってdelay0/M=R+1、target balanceでC=v+1/i0。これをfree-prefixへ置換しない。

反証pass: local sourceがsource以前にM個のAを持つこととM個freeを持つことを混同しない。C=v+1 middleS/i0を切らない。target mass1のE453を再発見しない。三run符号長/oldprefixは無制限。

受入: 少なくともactual counter由来の新source/candidate削減と原文監査、Leanなら512MB/lint/G5/Audit/fullcheck。完全fullgapや有限history不在とは呼ばない。初回gateでedgeなしならSTOPPED、別pass監査へ。数学修理一回、旧job資源追加なし。

## 終了時判断

E-520 PROVED-LEAN、元p counterの全source削減。counter不在ではない。 全体検証・逐語audit・実績正本は11/02 DAILY/journalを参照。親C1全体は未解決。
