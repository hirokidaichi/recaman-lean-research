# 2026-11-04: mass1/no-oldの同target source-family衝突

結論 E557: 元Intp/padded BlockWord/zero-fullpositive/正三run zero-mass head/同old targetmass1/全v>=1/最後A-ray全old供給なしの全長full-tail free-gap。PROVED-PAPER、未Lean・人間レビュー未。以下は新しいsource-family衝突であり、H21停止したglobal parity source形式化を再開しない。E556のfree=jだけを同値wrapperで言い換えた成果ではない。

## 領域と既存Lean入力

同日E545/E551/E553/E555/E556の全量化子を保つ。z=S^h A^M S^m A^L S^s A^U、全六長正、A=S。後続S^v A^T S^j、R=j+1。同じ元pのactual F<Rを反例とする。target suffixは同BlockWordのmass1なのでA/key0。source以前prefixをresetせず、他old sourceのmassを切らない。

既存LeanによりR>=5/M<=R+1/T=v+R-1、headfree4/v<=2。同actual counterでclock i>=v+1の全local sourceは第二A開始以後。local source classifierの六family（initialS/firstA/middleS/secondA/thirdS/finalS）は各高々1clock、finalSはclock2。no-oldにより元actual最後供給数はこのlocal時計の和集合である。有限history分類ではない。

二窓の同target cross式を共通記号で固定する。source以前のtail wordをb、source以後/最後A前のwordのS数をN>=v>=1、delta=i-v、X=ones(b)-deltaとすると
X²=R²+cross(b)/2+2*delta*N。
mass identityでX=cntF(b)-1。S^h A^aならcross0、S^h A^M S^dならcross=4Md。Nはそのsource固有の値であり、二源間で同じNと仮定しない。

## v1: firstAとmiddleSの和集合は高々1clock

E556は初期S源を全排除し、last actual=5を強制する。残り四family+clock2で5ならfirstA/middleSの両方が別clockに必要。両source位置は第二Aより前なのでlate-source排除により時計は0/1だけ。従って別clockなら次の二case。

A. firstA clock0、middleS clock1。
middleSのprefixはS^h A^M S^d。d>=1ならAS pairがありE548 +2 cutでM>=R+2、M<=R+1に矛盾。d0ならE549 cross0境界によりM=R/h=R+1。firstA源のprefix S^h A^aにはX=h-1=R、delta=-1、cross0なのでR²=R²-2N、N>=1に矛盾。

B. firstA clock1、middleS clock0。
firstA prefix S^h A^a、a<=M-1<=RにE549を適用しa=R/h=R+1、従ってM=R+1。middleS clock0のprefix S^h A^M S^dのmass identityでh+d=M+2、従ってd2。X=M+1=R+2、cross=4Md、delta=-1なので
(R+2)²=R²+2(R+1)*2-2N。
右辺はR²+4R+4-2N、左辺はR²+4R+4なのでN0となりN>=1に矛盾。

従ってfirstA/middleSは同時に別clockを供給できない。和集合高々1、残りsecondA/thirdS/finalS各1でlastlocal<=4。last actual=5に矛盾しv1 fullgap。

first-ray供給1という反証済みshortcut E550を使わない。個別のfirstA/middleS源を消去するのでなく、二源を同targetでcoupleして別時計共存を排除する。

## v2: initialSと最初二local familyのclock衝突

T=R+1/headfree4/F<Rなのでlastactual>=6。generic no-old local<=6により六family全てが別clockを持つ必要がある。

initialS源の先行S差dはzerohead/source massからd+i=3。d<=2ならE555の二窓排除に矛盾。従ってd3/i0。finalSはclock2。firstA/middleS源は第二Aより前なのでlate-source排除から各時計<=2。initialSの0とfinalSの2に衝突せず別時計を持つには両方clock1になり、互いに衝突する。六つの別clockは不可能、lastactual<=5、F>=4+(R+1)-5=Rで矛盾。

このv2証明はE554 PAPERの全initialS不在やE<=16/global parityを入力しない。initialSがある可能性を保ってclock0へ集約する独立機構であり、H21 sourceへのtactic/split/import修理ではない。

## 証拠水準と残り

上記二case/shared-target clock合流を完全紙上argumentとして記録した。source存在と時計範囲、同じ原p、source固有N>=1を全て保持する。新joint-source exclusionとactual union countのLean化は未完了、人間レビュー未。E557をPROVED-LEANと呼ばない。

E545（oldmass2 Lean）、E546（oldmass3 paper）、E547（oldmass>=4 paper）、上記no-old paperを、actual counter R5におけるold source mass>target massの既存順序と合わせれば、この限定zerohead/oldtargetモデルのmass1全域の紙上帰結となる。一般四run/C1/Q/H/SL/全射性ではない。mass2 v3/4 old枝、非zerohead/他target source位置等は未解決。
