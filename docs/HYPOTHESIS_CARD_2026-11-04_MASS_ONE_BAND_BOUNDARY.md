# H-20261104-15: mass1 final-bandの非strict境界

Owner Codex、親R-20261104-01。CONJECTURED、CPU探索0。

Exact: 全正三run zerohead/同mass1 old target/元zero-fullpositive actual counter。R=j+1、最後S^v A^T S^j、T=v+R-1。最後ray clock i>=vのlocal sourceで、第二A-run開始以前にあるものを分類する。全source以前履歴を保持。no-oldはactual count接続でだけ使い、local source分類では入力しない。

候補: 初期S/第一Aのsourceなし。第二S源は先頭だけ、h=R+1/M=R/i=vを満たす一つの例外。C1へE519のstrictmass2 cutを使わず、E452のA>=R+delayとAS-cross strict cutを場合分けする。第一AのM=R+1境界はh=R+1とfirst actual<=1から実free>=Rで排除する。第二S深さd>0のAS strictも同様。d0ではcross0の平方がM-delay=R、h=R+1を強制しM=Rのみ残す。

受入: 原actual counterから新source-conditioned equality又は反例。局所例外だけを親C1反例と呼ばない。15分gate、数学修理一回、CPU0。M512 STOPPED H12/H13の再開なし。

07:14 proposer update: mass1 key0ではcross identityが2X²=2R²+4Q+4δNとなりX²-R²は偶数。したがってAS pairがあるstrict枝はX>=R+2（既存の+1より一つ強い）。これはC1 source固有の新edge。任意mixed bのcross=4Qを帰納で供給し、具体word/sourceの新不等式としてまずformalize。初期sourceや実free結論を仮定しない。boundary j>=2は保持する。

Falsifier repair (one mathematical repair): h=R+1 alone does NOT imply first supply<=1; existing long-first lemma requires2M<=h+3, false for M=R+1/R>=5. Therefore retain firstA boundary M=R+1, h=R+1, source after exactly R A at z=n+2R+1, clock i=v. The secondS-start boundary M=R is the same source position/clock. Do not erase either by a false free-prefix argument. Deep secondS sources have an AS pair and E548 gives M>=R+delay+2, impossible with M<=R+1. These boundaries together cost ONE clock, not two. No claimed fullgap/no-old absence. New candidate no-old last<=v+4/headfree<=4 still needs actual glue.

## 当日最終判断（2026-11-04）

PROVED-LEAN E548/E549及び修理後E551。first供給1補助案はE550 REFUTED。
完全な実時計・commands・失敗receipt・次の入口は[DAILY](RESEARCH_HANDOFF_2026-11-04_DAILY.md)と当日packetを参照。
