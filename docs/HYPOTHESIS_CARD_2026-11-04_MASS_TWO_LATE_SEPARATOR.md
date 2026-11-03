# H-20261104-06: mass2任意separator counterとv>=5のsmall-free排除

Owner Codex。Parent R-20261104-01。Status CONJECTURED、work active。探索CPU0。最初15分gate、new edgeなしならC2v3/4同sourceへ切替。

Exact: 同元Intp/padded BlockWord/zero-fullpositive/正三run zerohead/同old targetmass2、全v>=1のactual counterからR>=5を内部供給する。続いてv>=5の全old/no-old枝でfullgapを問う。全history/run長/他oldmassを保持しheadfree/数値候補/結論を入力しない。

Paper: counterでfullfree<=3なら既存r3 A上界とT+2=v+RよりS+v<=R+1。R<=4とS>=3ならv<=2、同target keyとheadkey下界に矛盾。故R>=5（r3分類再実行ではなく既存定理の消費）。一般last<=7からcounterはheadfree r+v<=8、v>=5ならr<=3、既存r3 boundでS<=2r+1。head positivityでr>=1。same target ku=2S²-4K-8(S+v)+2v²-2R²、K=M(m+s)+Ls>=3。r=1/2/3各境界でv<=7/6/5、S<=3/5/7とR>=5を代入した二次上界はku<-2となり、BlockWord target key>=-2に矛盾。

Falsifier: vの上界はcounter内部のactual last7からのみ供給し、最初から有限vに切らない。r3はheadの実freeでありfullfreeと同一視しない。K>=3は三正A-run/二正separatorから導き、非genuine/非zeroheadへ広げない。r0はactual positive/zeroheadで排除。C1へstrict mass2 source cutは適用しない。

受入: 任意v actual R5 edgeとv>=5元fullgap。数学修理1回、Lean-j1-M512/10CPU per-process/20wall、source hash/argv保存。一般C1の証明ではない。旧table/停止job再開なし。

## 当日最終判断（2026-11-04）

PROVED-LEAN E542。mass2全v>=5 fullgap。
完全な実時計・commands・失敗receipt・次の入口は[DAILY](RESEARCH_HANDOFF_2026-11-04_DAILY.md)と当日packetを参照。
