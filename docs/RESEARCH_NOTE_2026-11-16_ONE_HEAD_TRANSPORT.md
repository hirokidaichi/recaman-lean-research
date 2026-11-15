# 一つの初期Sを残すと元actual/freeと正不足を運べる範囲

2026-11-16 / H-20261116-02 / E722。PROVED-LEAN（個別-j1/-M512受理、全体checkは日末；人間レビュー未）。任意の下excursion深さ・長さ・run数に適用するが、上への高さには明示条件がある。任意C1/任意上昇の深さ帰納は未証明。

## 新しく支払った辺

元f(0)=S、全k<=BでFw(k)<=1なら、全非空prefixで元実供給+1<=Sが成立する。free2を新Propで入力しない。
各prefixの元freeが2以上なら、既存の正確なFw=free-(S-EndN)とceiling1からS-EndN>=1。元freeが1以下なら、既存first-S-one-free定理がそのprefixの全A=free<=1を内部供給するので実供給0、先頭SがS>=1を保証する。両者で元actualの正不足を尽くす。
従来のSSAAからfree2を固定するE718は入力を強くした支持例であり、同じ結果の再引用ではない。今回first-Sしか要求せず、正不足の未知marginを実freeの二分岐で払った。

元initial-S h>=1、全h<=t<=h+KでFw(t)<=Fw(h)+2のもと、g(i)=f(h-1+i)とする。removed head全h-1本のsource高さは保持cutの高さより高く、全targetの必要source高さよりも高い。E709が全q<=Kの元EndN同値と元全供給/free件数の同値を供給する。残す一Sの直後の高さは元Fw(h)で、shift後の全高さは1以下。上のbootstrapで新history全prefixの元actual正不足を内部供給する。loss=0、free変化0、source prefixを新BlockWordと仮定し直さない。

この辺はE709のactual/free保存から**正不足までを同時輸送する**新しい消費先であり、供給保存の再包装だけを進展へ数えない。残存境界S一つの費用をどこから払うかが新しい部分。

## 境界と反証

h1はidentity、h>1で初期Sが厳密に短くなる。K0は一Sだけのprefixになり正不足を保つ。全q<=Kで端点も含み、元initial-S cutoffが最大S runである必要はない。
first-Sを外すとAだけの最初prefixはceiling1でも正不足に失敗する。first-Sのceiling1を2へ緩めるとSAAAのprefix4で元actual1/S1となって失敗する。
輸送条件のceilingは**全clock**Fw(h)..Fw(h+K)へかかる。SSAAA/h2/K3は上ceiling3で、cut後SAAAは最後actualを保っても正不足を失う。実A始点だけのceiling2に無断で置き換えない。先頭を全部除くSA→Aの失敗E710も残る。

## C1 counterへの接続契約（紙上consumer、一般C1証明ではない）

最後のS-gapの始点b>=h、長さj、元target b+jがactualで、[h,b]の元高さがFw(h)+2以下なら、gap中は下がるのでtarget高さにも同じ上界がある。
E722をK=b-hへ適用すれば、counted prefix [0,b)の元freeはgの[0,b-(h-1))と一致し、新しい正不足も供給される。E709のtarget iffを元clock b+jへ適用すると、そのactualもgのclock b+j-(h-1)へ運べる。gap符号は同じfutureを読むのでjも不変。したがってF<=jの元counterがあれば同じfree不足のg counterになる。
元n=0の空BlockWordはgでも空であり、元old履歴を任意途中でresetした議論ではない。任意のmixed BlockWord前史への移植は別義務。
この条件下では元global最小高さはfuture h以降（そこに元高さ-hがある）で達成する。gの最小高さはh-1だけ上がり、下向きexcursion深さはh-1だけ減る。future自体がさらに深く潜ることは許され、その深さに上限を置いていない。

## 残る上ceiling条件

この操作から全C1 counterのceiling2は導いていない。元futureがFw(h)+3以上へ上がる場合、保持一Sの正不足bootstrapが使えず、source-before-cutの新供給/損失も現れる。一般のV<=freeやUの支払いは依然未知。単にceilingを新Propとして入力し任意深さ一般解と呼ばない。次consumerは低ceiling域のcounter研究、又は同じ元source/freeを保つ有償の上ceiling拡張である。

## 一つの固定Cだけに限定しない同じ原理

任意1<=C<=hについて、future上界をFw(h)+C+1とすれば、g(i)=f(h-C+i)の全高さは1以下になる。initial-C prefixは非正、その後はFw(h-C)=Fw(h)+Cを使う。E709の全source iffと供給/free件数も同じ上界で成立し、先頭Sと新bootstrapが正不足を払う。従ってC=1だけの実例ではなく、すべての保持head Cの同じ操作に使える。相対上界Rならmax(1,R-1)<=hを満たす範囲でそのCを選べる。Rが大きく、この値がhを越えるなら非自明なcutは供給していない。既存height-only紙上R+1案より二つ少ないheadで正不足を保つ新bootstrapであり、過去STOP bytesを再修理して得たものではない。

## 元reserve側から見た新境界費用（同じedgeの監査）

futureの相対上界をRとする。各非空future prefixでM=E-S+Fなので必要positive reserveはE+1-S=M-F+1。元全historyはfirstSから始まり、initial-S内free0である。F<=1なら既存first-S-one-freeから全A=F<=1、従ってM<=Fで必要reserve<=1。F>=2なら必要reserve<=R-1。よって**U<=max(1,R-1)**。V<=max(0,R-1)は元source高さ式から従う。未知Uを仮定へ移さず、first-Sの元actual free分類で払った新しい上界である。
元fullpositiveを入力する全R版では、C=min(h,max(1,R-1))を選べる。C=hのidentity枝は元positiveをそのまま保持し、C<hならE722の一般C操作がactual/free/positiveを供給する。R+1という以前の十分headから二つ削れるが、freeに依存する深さ上界ではない。R1ではSAのzero-head失敗が残存一Sの必要性を示し、R>=3ではE721のh=R-1族がsource保存にC>=R-1を要求する。R0/K0等でさらに短くできる例はあり、この規則を全域の最小headとは呼ばない。C*=max(U,V)というE712の厳密最小性は別に保持する。
このreserve説明、retained-C kernel consumer、one-head特殊化は一つの新positive-bootstrap機構であり、別々の一般化成功へ数えない。
