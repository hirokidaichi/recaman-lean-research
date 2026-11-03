# 2026-11-04: small separator / mass1 initial-S source

E554 PROVED-PAPER、未Lean・人間レビュー未。H21のv<=2/E<=16 raw source形式化は512MBでSTOPPED、packetへ隔離し再実行しない。H22の独立でより広いd<=2二窓lemmaだけはE555 PROVED-LEANである。

正確な領域は同元Intp/padded BlockWord/zero-fullpositive/正三run zerohead/同old targetmass1/全v>=1/no-old actual counter。E551/E553が内部でheadfree4、v<=2、E=S+v<=16、R>=5/T=v+R-1を供給する。

初期S源の先行S差をdとする。local source mass balanceでd+i=v+1、0<=d<=v+1<=3。同targetとlocal源のkeyを同headから引くとR²=2(d-1)E-d²+1。zerohead cross=4Qとtargetkey0からR²≡E(mod2)。これらは同じ実wordにおける必要条件で、独立scalarや結論の入力ではない。

- d0/1はR>=5に矛盾。
- d2はR²=2E-3。RoddなのでEodd、しかしodd square≡1mod8を代入すればEeven、矛盾。別証明としてlocal P2のS数Nが奇数でR²=2N+1≡3mod4となりE555が全E上界なしで排除する。
- d3ではR²=4E-8<=56から5<=R<=7。5/7は平方mod4に矛盾、R6ではE11がword parityに矛盾。

従って全initialS local sourceを排除。残る四source family（firstA/middleS/secondA/thirdS）は各1clock、finalSはclock2の1clockなのでlastlocal<=5。no-old仮定により元actual last<=5。

v2ならT=R+1、headfree4なのでfullfree>=4+(R+1)-5=R、counterに矛盾し全長fullgapを得る。v1ではT=R、得られるのはfree>=R-1だけで、fullgapは未証明。counterならlastactual5を必要とし、五familyの共同供給条件が次の一問となる。E554をPROVED-LEANと呼ばず、v1へ結論を拡張しない。全old履歴/他source位置/一般C1は未解決。
