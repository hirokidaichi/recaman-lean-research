# H-20261031-07: 最終S長1の第二A源はclock2だけか

Status PROVED-LEAN、R-20261031-01局所探索。任意e,s,U,i:Nat、e>=1/s>=1、raw source Ae Ss AU S Aiがmass1/area0（同じkey-2）ならi=2を問う。Uは0を許すかは反証passで固定し、最初はU>=1に限定する。親C1/free-gapは入力しない。

紙上chain: p=s+1、r=p-2e、sourcekeyからpr=2U+1>0。p/rは正奇数、e>=1からp>=r+2。massから2i=4-(p-1)(r-1)>=0。r>=3ならp>=5で積>=8となり矛盾、r1でi2。小端s1/2、U0、e0を反証passで区別。e0を許すとs2/U4/i0の見かけ解が入るためe>=1を保持する。

受入は全長key/massからのclock分類と必要仮定のsharp対照、又は反例。10CPU/512MB/20wall個別検証。新CPU探索0、既存falsifierは別会計。sourceをprimitivePropとして仮定したfree-gapの包装にしない。成功すればsmall-vのarith source classifierの一族をclock2へ統合し、巨大local word tableの再実行を避ける。

## 日次の保存判断（保存時の監査）
E472、U0も許す
親cycleはR-20261031-01のみ。実時計/commands/CPU/変更sourceの正本は当日DAILY、journal、`data/ten_head_20261031/SOURCE_VALIDATION_INDEX.json`と`CPU_SUMMARY.json`。元0/pと全old prefixを維持。
