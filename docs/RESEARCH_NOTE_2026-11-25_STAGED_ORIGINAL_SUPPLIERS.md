# stage上昇語の元supplierと、旧履歴を残すfree会計

**PROVED-PAPER、未Lean・人間レビュー未。** 任意の旧符号履歴を保存し、以下の明示的stage族のすべての内部supplierを分類した。cut以前にしかsourceを持たない元actual Aを (O_c) と数えると、元freeとの和について

    F+O_c >= H+3,
    2A <= 3(F+O_c)-a_H-2 <= 3(F+O_c)-3

が成り立つ。初期headだけからの供給をfreeに置換していない。一般run/C1/Q/H/SL/全射性を証明した結果ではない。任意の旧履歴で (O_c=0) を内部供給する義務は残る。

**記号の監査：** 最新のclass研究でDは初期head以下の追加深さを表す。ここでのexclusive-old供給数は別物なので **O_c** と書く。カード初期案のD/D_cは採用記号ではない。下の空前史の例はD_depth=0でもO_c>0になり得る。両者を同一視しない。

## 1. 完全な量化と原点

任意の有限符号語U、n=length(U)、任意の整数H>=2、正整数a_0,...,a_Hを取る。m=H+2、c=n+mとして、完全な語を

    U ++ S^m ++ T,
    T = [product_(h=0..H) (AS)^(a_h-1) A] ++ S^(H+1) ++ AA

とする。Sは高さ-1、Aは+1。全EndN/freeは原点0から判定し、Uを捨てたりcで原点をresetしない。Aはtail中の全A数、Fは同じtailの元EndN0でないALL A数であり、LOWfreeだけの数やdistinct class数ではない。S^mにはAが無いので[c,end)で数えても同じ。

O_cは、tailのA qのうち、元EndN0 qは真だが、c<=u<qの元Win sourceが一つも無いものの**個数**である。旧sourceと内部sourceを両方持つtargetはO_cへ入れない。これは定義した結論を仮定するPropではなく、完全な元source集合から算出するexclusive-before-cut数である。

stage hのA始点はcutの床から相対h、stage内のAをj=0,...,a_h-1とする。stage開始clockをs_hと書く。cut以前の全old historyは任意であり、そのmass・source時計・共supplierを消さない。標準Recamán orbitやcoherent数値Stateによる実現可能性はここでは仮定も結論もしない。

## 2. 内部sourceの全分類

h>=2のstage A(h,j)について、内部source u>=cがある必要十分条件は

    a_(h-1)+3j < a_(h-2).                              (L)

この場合、内部sourceはただ一つで、stage h-2のpeak index

    i=a_(h-2)-a_(h-1)-3j-1,
    u=s_(h-2)+2i+1

にある。stage0/1と末尾AAには内部sourceがない。

証明：Winのrise1よりsource高さはh-1。qより前のcut以後でこの高さを持つ時計は、stage h-2のA後の山頂と、stage h-1の底の時計だけで尽くされる。より低いstageは高さh-1へ届かない。stage h-1の底からの窓は以後の高さがすべてsource以上で、最後の高さがsource+1なので面積は厳密に正。

stage h-2のi番目のA後の山頂をsourceとする。B=a_(h-2)と置く。最後の山頂i=B-1はstage h-1開始と同じなのでやはり正面積。それ以前では、次のSが相対面積-1、残るB-i-2個のASが各-1、最後のAが0を加える。stage h-1全体の相対面積はa_(h-1)、target前のstage hのj個のASは各3。従って窓面積は

    a_(h-1)-(B-i-1)+3j.

これが0になるindexは上の式だけであり、0<=i<=B-2となる条件が(L)。rise1はこのsource高さから既に成立する。

stage0の必要source高さ-1はcut以後では未到達。stage1の必要高さ0から先はすべて相対非負で最後が正。末尾AAの第一Aも必要高さ-1がcut以後に無く、第二Aは必要高さ0から先がすべて非負で最後が正。いずれも内部sourceを持たない。ここでは旧Uにsourceが無いとは言っていない。

L_hを(L)を満たすjの個数、h0/1では0、L=sum L_hとする。したがって

    L_h=min(a_h, max(0,ceil((a_(h-2)-a_(h-1))/3)))       (h>=2).

内部供給targetには必ず元actual供給がある。他の元actual targetはちょうどO_cなので、元actual E=L+O_c、全tail A=L+O_c+F、従って **F+O_c=A-L**。旧sourceを新仮定で除外せず、同じ元countへ接続した。

## 3. 任意の旧履歴を払う二つの不等式

まずa_(h-1)>=1よりL_h<=a_(h-2)-1。従って

    L <= sum_(i=0..H-2)(a_i-1),
    F+O_c = sum_(i=0..H)a_i+2-L
          >= H+1+a_(H-1)+a_H >= H+3.                  (G)

次に厳密な係数3/2を得る。正整数列a_0,...,a_(H-1)のstrict descent edges a_i>a_(i+1)を、maximalな連続runへ分ける。runは頂点も互いに共有しない。runにk>=1本のedge、末端値b>=1があるとする。各edgeで

    3ceil((a_i-a_(i+1))/3) <= a_i-a_(i+1)+2.

和はa_start-b+2k以下。一方、この値をrunの全k+1頂点のaの和から引いたものは、内部頂点の和+2b-2kである。strict integer descentより内部値はb+1,...,b+k-1以上なので、その差は

    (k+1)b+k(k-1)/2-2k
       >= (k-1)(k-2)/2 >=0.

よってrunの局所供給費用3倍はそのrunのA数で払える。すべてのrunを足し、各L_hが上のceil以下であることを使えば

    3L <= sum_(i=0..H-1)a_i = A-2-a_H.

F+O_c=A-Lへ代入して

    2A <= 3(F+O_c)-a_H-2 <=3(F+O_c)-3.               (C)

となる。深さHをbinderに加えただけのwrapperではなく、供給元を完全に分類した後、互いに共有しないdescent-runのA数へ最大負荷と端点a_Hを払った。

ただしAを無条件freeへ置換したのでもない。支払い先はF+O_cであり、O_cを元free/classesで払う一般法則は別問題である。このstage grammarでは各lower-peak bankが次の二段上のtargetだけを供給することが、上の支払いを可能にしている。一般の再下降・再上昇語ではこの性質を仮定できない。

## 4. 空前史ではhead sourceも尽くせる

Uが空の場合、cut以前のsource高さh-1は初期S-headのclock u=m-h+1だけ。K_h=sum_(t<=h-2)(2(h-t)-3)a_tと置くと、このhead sourceからA(h,j)への面積は

    a_(h-1)-K_h+3j.

実際、初期S^(h-1)の三角形面積と、各stageの最後Aの補正が相殺され、各完成stage tの係数は2t-2h+3となる。従ってhead sourceはa_(h-1)+3j=K_hのときだけ存在する。K_h>=a_(h-2)なので(L)の内部source条件と両立しない。ゆえに空前史ではO_c=sum_h delta_h、delta_hはこの等式を満たす0<=j<a_hの個数（0または1）と**正確に**同定できる。stage0/1と末尾AAはこの場合、元freeでもある。

「一stageの元供給は一件まで」という探索中の案は誤りだった。H2/a=(7,1,7)ではstage2のj0/1はそれぞれ内部peak source15/9、j2はhead source3を持ち、元E3/F14/O_c1となる。全sourceを照合したworkerが、欠落peak bankを検出した。

またH5/a=(1,1,1,2,1,1)では、元供給target9/12/14の全sourceはそれぞれ6/5/11。最初の二つはhead-onlyなのでO_c2、最後は内部SAA。全A9/F6、head7。O_cを捨てたfree>=headはこの完全な語で失敗する。しかしD_depth=0であり、この例を新たなC1反例とは呼ばない。否定したのはここでのold-debt省略である。

## 5. 両境界が同時に鋭い全nの族

任意n>=1、H=2n、a=(2,1)^n ++[1]、U空とする。完全な語は

    W_n=S^(2n+2) (ASAA)^n A S^(2n+1) AA.

元actual供給はstage2,4,...,2nの最初Aだけ。各sourceは二stage下の最初peakで、窓はSAA。head sourceはh2/3では上の面積を直接代入して除外できる（候補等式の左辺はKと一致しない）。h>=4ではK_h> a_(h-1)+3(a_h-1)なので存在しない。他の内部supplierも第2節の分類で尽くされる。従って

    A=3n+3, E=n, F=2n+3, O_c=0,
    F=m+1=H+3, 2A=3F-3.

いずれも有限計算からの外挿ではなく、すべての元sourceを上の分類へ代入した全nの証明である。係数3/2と加法境界-3は同時に改善できない。

全語の初期headは正確にm、head後の最大高さは-1、最後は2-m。したがって、ここで正不足を述べる区間は、初期S-headを含む **S^m ++ T**（Uの直後nからの区間）である。この区間のすべての非空prefixでS_seg>A_seg>=元actual E_segとなり、元正不足も成立する。cut cの後だけのTはAから始まるので、その最初からstrict positiveだとは主張しない。これはUが任意のときU以前の全prefixも正不足だという主張ではない。この族ではheadより下への追加深さD_depthは0、全tail深さmはnとともに増える。一般の追加深さにわたるC1の支払いを解決していない。

## 6. 反証pass、資源、次consumer

STAGED_SOURCE_PROTOCOL.jsonを両worker前に固定。discoveryはH2..4/a_i=1..3の351完全語・3942元A targetをforward height/prefix-areaで検査した。holdoutは未使用H5..8の40固定seed tuple・1269 targetを、独立reverse mass/加重面積で全u<qについて検査した。sharp族n1..8とn9..16、三つの負/境界対照も別に照合。有限検算はCOMPUTED、全量化子の証拠は上のPAPER証明である。

さらにholdoutで五つの非空前史U×三つのaを保持した。U=SAAASSSSAAAASA、a=(2,1,2,1,1)、cut20、target28では元sources=[9,25]で旧と内部が共存する。内部source25があるためこのtargetはO_cに入らない。旧source9を削除してから数えてはいない。parameter holdoutは同じsign族を共有し、canonical orbitのfresh holdoutとは呼ばない。

各workerは当日guard検証後のcooperative単一Python/no-descendant、1CPU秒/10wall秒で完了。discovery CPU0.041725秒、holdout0.046595秒。一般process-tree capではない。source/argv/card hash・正確出力・終了receiptは[data packet](data/depth_general_20261125)に保存。旧一般A<=3free census、完了depth、停止512MB Lean jobは再開していない。新Lean0。

次の一問：このsource bankが互いに二段下のstageへ限定される性質は、一般の下降・回復でどこで失われるか。O_cを残したまま、実S freshnessまたは元freeの新producerでその旧負債を払えるか。O_c=0を結論同然の新Prop入力にするadapterでは一般化にならない。
