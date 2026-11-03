# 2026-11-04: mass1 targetとold sourceの紙上free-gap

結論: 下記の同一領域でold supplier mass3及びmass>=4の枝のfull-tail free-gapを紙上で証明する。PROVED-PAPER、未Lean・人間レビュー未。H12/H13の512MB停止sourceは再開せず隔離する。E545のoldmass2はPROVED-LEAN。これらの主張はmass1 target全体やC1全体の証明ではない。

## 正確な領域と記号

任意e:Int→Bool、元基点p:Int、pからのpadded BlockWord prefixの末尾n、同じprefix内target t<n。元基点のEndable数とS数がnで等しく、n以後tail末尾gapまで全正prefixでEndable+1<=S。三genuine A-run head
z=S^h A^M S^m A^L S^s A^U、全h,M,m,L,s,U>=1、M+L+U=S=h+m+s。
その後S^v A^T S^j、v>=1、R=j+1。target窓は元P2そのもの、target suffix uは元BlockWord内のmass1 suffixである（末尾A仮定を追加せず既存block_mass_oneよりu=A/key0）。最後A-rayの任意実old source b<nとclock i<Tを取り、元P2供給を仮定する。D=mass(prefix.drop b)。他old supplierのmass/source以前prefixは一切制限しない。

rはheadの元actual free数、Fはgap前full tailの元actual free数、E=S+v、K=M(m+s)+Ls。反例をF<Rとする。元zero/fullpositiveからcN加法でrelative positiveを得る。以下は同じ元pのcountであり再基点化しない。

## 共通のactual必要条件

(1) target mass balance: T=v+R-1。target key:
0=2S²-4K-4E+2v²-2R²。

(2) generic actual last<=7、三run head<=10（既存InitialSTargetBounds.three_run_count_of_manyS）。head/最終S/lastの同じcount分割より
r+v<=7、E<=17。
head末尾relative positiveとA=Sよりr>=1、したがってv<=6。これらは結論/headfreeを入力した仮定ではない。

(3) R>=5。もしF<=3なら既存r3全長A<=2F+1を全tailへ適用する。A_full=S+T=E+R-1、F<=R-1なのでE<=R。R<=4とS>=3/v>=1からS3/v1/R4のみ。runKey(z)>=-2S²=-18に対しtarget keyは0=-key(z)-46<=-28、矛盾。r3を再分類しない。

(4) oldsource balanceはD+i=v+1。seed窓のkeyは-2、一般のhead append式より
ks=key(prefix.drop b)=2E-2+4Z (あるZ:Int)。同targetとの差は
-ks=4(D-1)E+2-2R²。
この式は同じold prefix/head/最終Sを共有する二窓から導出し、sourceを独立に選ばない。

## A: D=3の枝

primitive mass3 spectrumはks∈{-2,0,2}。Rが奇数ならR²=8q+1なので-ks=8E-16q。ksの三値からks0、E=2qは偶数。一方seed parity ks=2E-2+4ZはE奇数を強制し矛盾。

Rは偶数。ks0又は2ならR²=4E+1又は4E+2でeven squareの4倍に矛盾。従ってks=-2、R²=4Eかつseed parityからE偶数。R>=5/E<=17によりR<=8、evenRは6又8。R6ならE9で偶数に矛盾。従ってR8/E16。

D+i=v+1よりi=v-2、2<=v<=6。target keyでK=(v-8)²+16。各v2,3,4,5,6に対して2K+1=105,83,65,51,41。各々10²..11²、9²..10²、8²..9²、7²..8²、6²..7²の厳密な間。E536の全長initialS-source-square lemmaにより第三A-ray actual<=4。最初二runactual<=5、head<=9。

最後rayのinitialS sourceがあるとする。残る初期S長q>=1、d=h-q>=0。source balanceからd+k=v+1、従って0<=d<=v+1<=7。source keyと同oldmass3/key-2のseed keyを共有head append式で引くと
-2=4(d-3)E-2d²=64(d-3)-2d²。
d0..7の右辺は-192,-130,-72,-18,32,78,120,158で-2でない。従って全initialS sourceを排除する。

残るlocal source familyはfirstA/middleS/secondA/thirdSの各々高々1clockと最終Sのclock2。local<=5。全massのold sourceは共通BlockWord/S数>=3の既存old uniquenessにより合計高々1clock（D3だけに切らない）。従ってlast actual<=6。

全tail A数はE+R-1=23、全actual供給<=head9+last6=15、最終separator供給0。従ってF>=8=R、反例に矛盾。元Intp/padded/zero/fullpositiveの全長fullgapが従う。

## B: D>=4の枝

D+i=v+1なのでv>=3。i<=2なら既存E497 early-old-mass-four theoremの全仮定を元actualWinから供給でき、r>=5。r+v>=8に矛盾。

i>=3ならv>=D+2>=6。r>=1/r+v<=7によりv6/r1。headへ既存r3 A<=2r+1を適用しS<=3、全正三SよりS3。全正M,L,UでA=S3なのでM=L=U1、h=m=s1、K3、keyhead=-6。同target keyはR²=21となりR>=5に矛盾。headfree5をi>=3枝へ転用していない。

従ってD>=4の全source clock/全separator/全old historyで元actual fullgap。

## 証拠と限界

共通既存入力はPROVED-LEAN。A/Bを結合する全actual命題はPROVED-PAPERのみ。H12 raw circleとH13 actual glueはM512 STOPPEDであり、この紙上証明をLean受理と呼ばない。追加worker/finite probeなし。dやvの有限算術は内部導出したsource残余であり有限history分類ではない。明示old存在をno-oldへ拡張しない。C1全体/任意run数/rank/Q/H/SL/全射性は未解決。
