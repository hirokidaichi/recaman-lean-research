# 初期Sを除くときの元actual/freeと不足（2026-11-13）

## 結論
E709 PROVED-LEANは、任意長initial S prefixの元actual sourceを高さで全排除したうえで、供給/全freeを厳密保存する。対象Aの高さ条件はcut+1以下。全depth/run/A数に上限はない。除去で不足がh減るので、C1のpositive domainまで保存したとは主張しない。E710はceiling2拡張とpositive自動保存をkernel反証。人間レビュー未。

## Exact transport and boundary
元f,h,K、全i<hでf i=S。全h<=i<h+KのA始点でFw(i)<=Fw(h)+1。g(i)=f(h+i)。すると元全区間[0,h+K)のEndN0件数とg[0,K)のEndN0件数は等しく、元全freeも等しい。元S数=gのS数+h、元不足=gの不足+h。
各旧source t<hはFw(t)>=Fw(h)+1なのでWinならtarget>=Fw(h)+2になり、高さ条件に反する。ここで全元sourceを尽くしてからsource cutoffをhへ変え、既存endN_nat_shiftを使う。新Propで同値や供給族を仮定しない。prefix全Sは重要であり、padded BlockWord後の局所source n+2で勝手にresetする定理ではない。

ceiling2ではSAAAをAAAへstripするとtarget3/2の元EndNが変わる。別にSA→Aは高さ条件とfree保存を満たすが、元positive不足1が0になりpositive domainが壊れる。自由数だけではC1 inductionに使えないという境界を両方向監査した。

既存InitialSeparatorTrimは全A予算Bから初期SをC>=2B-1まで残す。E709はA予算不要・全除去可能だが対象高さを限定する別scope。旧STOPPEDを再開したものではない。

## 全source二次分類helper（個別512MB、独立row/進展なし）
M=Fw(h+q)-Fw(h)とすると、元EndN0(h+q)は、local EndN h 又は endpoint A/2<=M<=h+1/2Ar(h,q)=2q(M-1)+M(M-1)へ尽くされる。初期S source時計はh-(M-1)に固定され、逆Winも構成する。
InitialSQuadraticSourceの全長statementは初回受理。ただし既存constant-prefix ray分類の全元clockでの明示形なので、helperの同値化だけを新coverage又はG進展へ計上しない。次の反証可能な不等式H09へ消費した。

## 次の未知edge H09/H10
D=cN(EndN f0かつ非EndN f h) h K、F=元全free。元全prefix正不足/initial S prefixの全depthでD<=Fを問う。これならstrip後free<=2Fへ接続できるが、positive marginはさらに必要。
D>F探索はbeam59302 prefix visits/valid59300、reverse holdout192/valid192で反例なし。best h2/AAAASAは既知SSAAAASAのD2/F3で、新証拠の再発見ではない。
強い案として、各exclusive initial-S供給を直前の元freeへ写す最新free単射も攻撃した。専用free固定beam89406 visits/valid83628、reverse holdout192/valid192で反例なし。最大free固定継続158はSだけの継続も含み、全深さ証明を意味しない。
両方法とも、新actual charge edgeも反例も得られず最初15分以内でSTOPPED、命題はCONJECTURED。finite不在で同workerを再実行せず、全source/freeを保持する紙上chronologyの未知辺へhandoffする。H10の反証が仮に得られてもD<=FやC1の反証にしない。

数学workerCPUはH09 .142662+.246134、H10 .156874+.252203秒。日計は3.701250秒（budget8）、controllerは別計。全protocol/argv/sourcehash/dirty revision/終了receiptは当日packet。新探索追加は行わない。
