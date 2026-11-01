# 結論: moment帯はold側だけを制御し、targetとcoupleすると二caseへ

E465はPROVED-LEAN: 任意zero-mass head zでS=cntF(z)、area(z)=-B、4S+6<=B<=6S+4なら、同じBlockWord old sourceによる後続Sv/A-ray供給はclock4以降。全語長/old mass/vに上限なし。E466 REFUTEDは帯からlocal halfまで足す強化で、三A-run/A=S10/B64でもclock0を持つ。親H01/C1の反例ではない。

## H24 / E467 PROVED-PAPER（未Lean・人間レビュー未）

量化子を固定する。任意非空BlockWord u、任意List Bool z、mass(z)=0、cntF(z)=10、area(z)=-B、46<=B<=64、全v>=1/T/j/q/i、1<=q<=v、i<T、T<=i+j、R=j+1>=5。old targetの同じraw P2 `u z Sv AT Sj`、local P2 `Sq Ai` を仮定する。このときu=Aで、

1. `(v,T,j,B)=(1,5,4,46)`、または
2. `(v,T,j,B)=(2,7,5,56)`。

語長やold prefixの恣意的cutoff、free結論、independent Endable tagを入力しない。zの三run条件はこの二case縮約には不要で、後の有限local分類では明示して加える。

証明: local Sq AiのP2からq1/i2、従ってT<=R+1。C=mass(u)>=1、mass balanceからC=v+R-T>=v-1。同じkeyの連結とold targetから

`runKey(u)=2B-4C(10+v)+2v²-2R²`。

BlockWordのkey>=-2により `R²+2C(10+v)-v²<=B+1<=65`。v>=3ならC>=v-1を用い左辺>=25+v²+18v-20>=68で矛盾、v=1/2だけ。

v1ではR²+22C<=66、v2ではR²+24C<=69。R>=5からどちらもC1、BlockWord mass1分類でu=A/key0。v1の等式はB=R²+21、v2はB=R²+20。どちらもR5/6だけ。mass0/S10からzの長さ20、areaは20..1の奇数符号付き和なので210と同じ偶数、Bも偶数。v1/R6のB57は除外、v1/R5/B46が残る。v2/R5/B45は下端外、v2/R6/B56が残る。mass balanceからT5/7、j4/5。以上。

実H01のcounter域でR>=5を勝手に仮定しない: head A10と元BlockWord/relative全positiveについて、もしhead free<=3なら既存r3全長countでA<=2free+1<=7に矛盾。head free>=4、full free>=head free、full free<RならR>=5。元p zero/full-positiveは既存cN加法とshiftからrelative条件を供給する。このcounter-to-R供給自体はここでは紙上、二case全部をkernel認証済みとは呼ばない。

さらに二caseの最後A-rayではold supplyが一件もない（紙上corollary）: E441により各old clockはi+j<T、すなわちv1 case i<1 / v2 case i<2。E465はi>=4なので両立しない。元基点の全old supplierを論理的に排除してからlocalへ移るので、高mass prefixを勝手に切っていない。

## 次の最小未知edge

三genuine A-run head `Sh AM Sm AL Ss AU` にA=S10、moment帯を加え、同じold targetの二caseを実0/pへ内部供給する。その上でcase1のlast A5にlocal free>=1、case2のlast A7にlocal free>=2を供給できるか。head free>=4と非重複加法でfull free>=5/6になる。local halfを無条件に要求するとE466に反するので、target-derived B46/56/v1/2/T5/7を保持する。B64のclock0反例は二case外。

全positive/full zeroや標準Recaman軌道の到達可能性とraw local counterを混同しない。二caseだけではlocal数え上げ・反例不在は未供給。三run headの正整数compositionは事前上限36×36=1296だが、sourceごとのcertificate cell数や商kernelは未評価、3000 gateを満たしたと推定しない。明日の新CPU許可前にcontract/preflight/discoveryと独立holdoutを固定する。同じ停止済み表/solverへ資源を足さない。

## 終了時の別pass意味監査（新探索を終えた後）

- 非空uはtarget old suffixであり、全old prefixではない。C1からu=Aを得ても頭部countsの基点を変えない。old targetのt<n、全prefixBlockWordとpadded版のsuffix性が必要。
- mass0/cntF10からA10/長さ20を得る。B偶数は任意長へ外挿せず、長20の重み20..1の総和210が偶数であることを使う。三run版では既存key formulaからも確認できる。
- v>=3時の下界は25+v²+18v-20でv3から68、上界65と矛盾。v1/v2のC2下界は69/73で66/69を超える。R5/6とu=A/key0から候補B46/57および45/56だけ、奇数57と下端外45を除く。B64のraw counterはここに紛れない。
- original counterからR>=5を得るにはhead free4を内部供給し、head≤fullという同じPのcN単調性を使う。R>=5を単に新しいdomainへ足しただけでoriginal域を覆ったと主張しない。
- 全last old排除はE441のj>=2（j4/5）とE465のv>=1を実窓へ適用する。case1でold i<1、case2でi<2、共にold i>=4に矛盾。局所boolと元actualEndNを同一視する前にこのpointwise除外を証明する。
- last localfree1/2は未証明。headfree4にlastfree1/2を足す際、Svのfree0と区間加法を供給し、target A/Sjを二重計上しない。
- finite head certificateは、old排除の証明後のlocal窓だけを評価する設計候補である。全prefixのFree/EndNをindependent tagで近似しない。1296というheadの算術上限はkernel cellsや実資源の測定ではなく、旧大表再開の承認でもない。
