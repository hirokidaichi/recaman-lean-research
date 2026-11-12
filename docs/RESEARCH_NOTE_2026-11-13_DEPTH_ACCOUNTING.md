# 任意深さの会計と時計の必要条件（2026-11-13）

## 現時点の結論
高さ別必要式E674だけを、歩みの段保存とprefix正不足で補っても、無重みA/freeの一様倍率は導けない。以下は全深さにわたる**緩和モデルのno-go**であり、元actual EndNの倍率3仮説やC1の反証ではない。証拠は完全な紙上構成（推論機構をREFUTED）、人間レビュー未。元historyの有限探索は別で、新しい証明を与えていない。

## H-20261113-03: 元historyの倍率3探索
元f/padded BlockWord/全非空prefixのactual供給+1<=Sで、A<=3freeを候補にした。既知A5/free2、A10/free4は候補を壊さない。discoveryは6つのBlockWord根、最大tail160、beam64で118074 prefix visits（全探索ではない）。独立reverse-window方式のholdoutは別の3根・tail192/224・seed2026111303で1536終端語。どちらも反例なし。完全なhistory-prefixの未見性は確認しておらず、globally fresh holdoutとは呼ばない。discoveryのbestはexcess A-3free=0の語Sであり、最大A/free値を報告する指標ではなかった。ゼロを有効な密度上界や進展と解釈しない。

有限結果はCOMPUTEDの範囲に留まり、仮説はCONJECTURED。新edgeなしで最初15分以内に同倍率探索をSTOPPED、worker再実行なし。既存trichotomy A=F+L+R+Oと補正B+C<=Lから、Oを残すA<=3(F+O)までは既存式の算術合成であり、新成果として登録しない。Oを勝手に0へ置換しない。

## H-20261113-04: 高さ別緩和モデルの無重み化no-go

### 入力と否定する結論
実有限±1語の高さ別A数A_hに、宣言供給mark E_h、宣言free F_hを付ける。A_h=E_h+F_h、全hで、さらに同じ基点のすべてのprefixについて

E_h <= Σ_{l<=h-2}(2(h-l)-3)A_l

を満たし、全非空prefixでS数>=宣言供給数+1も満たすとする。歩みは実語なので隣段移動と上下crossing保存を要求済みである。この入力だけから、深さによらない有限実定数cでΣA_h<=cΣF_hを導くという機構を否定する。E_hが元EndNに一致するとは要求していない。ここが元問題との相違である。

### 全mの構成と完全検証
任意m>=3で語S^m A^mを取る。谷底を高さ0とするとA始点は0,1,...,m-1を各一度通る。高さ0,1をfree mark、それ以外を供給markとする。したがってF=2、A=m、E=m-2。

1. 高さh=0,1ではE_h=0で必要式成立。2<=h<=m-1ではE_h=1、右辺はΣ_{d=2}^{h}(2d-3)=(h-1)^2>=1。範囲外のhではE_h=0で右辺は非負（負高さなら空和）。全整数hで成立する。Aをa個通った途中prefixでも、その時点で存在する各hには低い0..h-2のAがすでに全てあるので同じ計算が成立する。S中のprefixはE=0。従って同じ基点での全prefix高さ必要式を足しても排除できない。
2. 初期Sをk>=1個通ったprefixは宣言不足k。Aをa個通ったprefixでは不足m-max(a-2,0)>=2。すべての非空prefixで厳密正。
3. 各隣段を下へ一度、上へ一度通り、端点高さは同じ。深さはm。A_h=S_{h+1}=1（0<=h<m）で、実際のwalk-flow保存を壊していない。
4. 任意の有限cに対しm>max(2c,2)を選ぶとA=m>2c=cF。m=3ではA/F=3/2、m=6で3、m=7で7/2となる。したがって係数3に限らず、どの一様有限倍率もこの入力群だけでは導けない。

### なぜ元actual反例ではないか
元原点0/空BlockWordの同じ語で、A高さhの実Winを調べる。A中から始まる非空窓は正の面積を持ち0にならない。S中から始まる窓はS^s A^hで、mass1ならh=s+1、面積は1-s^2。0になるのはs=1,h=2、すなわち最後Sからの短SAA窓だけである。よってm>=3で元供給は1、元freeはm-1。m=3では宣言と一致するが、m>=4では上の宣言が架空の追加供給を含む。実際のA=m<=3(m-1)は破らない。標準Recamán orbitへの到達可能性も主張しない。

### 重複課金と次consumer
同じ低いA、とくに高さ0のAが、すべての高いhの右辺で再利用されている。E674は同高の単射を保証するが異高さのこの再使用は排除しない。深さmを増やす追加markを同じ二つの宣言freeだけで支払えてしまう。従って高さ必要式の再合算・線形係数調整だけによる無重み化は停止する。
次に必要なのは各E_hの元source存在と時計/面積を同時保持する条件である。E681を単に一件ずつ再引用するのでなく、複数窓の重複を相殺する項、又は深さ操作で元EndN/freeを運ぶ正確な契約へ進む。元倍率3の真偽、C1、一般深さfullgapは未解決。

## 資源・再現
数学探索worker予算はguard検証後に0→8CPU秒へ事前固定。実測workerCPUはdiscovery0.213481+holdout2.169102=2.382583秒。controller0.001602+0.002472秒は別。追加workerなし。guardの意図的killは探索CPUへ混ぜない。STARTUP・GUARD_PROTOCOL・UNIFORM3_PROTOCOL・各sourceとhash/argv/終了receiptは[data/depth_general_20261113](data/depth_general_20261113)を参照。紙上構成の思考時間はjournal、純CPU実測ではない。

## H-20261113-05: 元二実窓の共有財布への反例

元有限語SSAAAASA、空BlockWord境界0、区間[0,7]、基準r=-2とする。元Win(0,7)とWin(1,3)はそれぞれtarget7と4の元EndN0を供給する。全非空prefixの元供給+1<=Sも成立。元途中のfloorは-2。

財布P(s,b)を2areaFromLevel+belowTriangle端点差+2低A重み-aboveTriangle端点差とする。これは既存signed_area_with_low_weightsから非負。窓の請求Q(t,q)=2(F(t)-r)(q-t-1)-2は、元WinのAr=0/rise1を代入するとその窓のP以下である。

この例では低A重み0、全areaFromLevel14、aboveTriangle端点差6でP(0,7)=22。外窓Q(0,7)=22、内SAA窓Q(1,4)=2。異なる実targetであっても24>22となり、財布を一回だけ使う単純合算はREFUTED。E642の短triple/strict-record集合の反例とは別の、長い実窓と短い実窓の共有面積である。元C1/fullgap反例ではない。

Recaman/TwoWindowAreaOverlap.leanのtwo_actual_windows_exceed_one_resourceを-j1/-M512で個別受理。H05はWinのDecidable展開不足、唯一のH05-R修理で受理。lint4/4 substantive。root/Auditと全体checkは最終採用時に検証。人間レビュー未。

### 交差補正の紙上chain（PROVED-PAPER、未Lean）
Pは同じ元f/rに対して非負な区間加法的資源である。加法性は元area split・低A重みappend・上下triangle端点の相殺から従う。実Win t→qでF(t)>=rなら、P(t,q)=2(q-t)(F(t)-r)+2W(t,q)-2(F(t)-r+1)。W>=0なのでQ(t,q)<=P(t,q)。

二つの窓区間I,Jについて、区間加法性からP(I)+P(J)=P(I∪J)+P(I∩J)。離れている場合は右のunionを二成分の和と解釈する。どの場合もunionは元grand区間に含まれ、補集合のPは非負なので、

Q1+Q2 <= P(grand)+P(I∩J)。

空intersectionのPは0。交錯/包含/端点共有/離隔の全場合を含む。上の例ではintersectionが内SAAでP=2、22+2=24と等号になる。

これは低Aをfreeへ置換しない条件付き面積補正であり、全actual供給族の内部選択やintersection費用を同freeへ無限に課金できることを証明しない。既存恒等式の包装だけを一般化進展へ追加計上せず、進展の根拠は反証によって必要な重複費用を確定した点に置く。次consumerは、この交差資源をactual source順序又はfreeの新証拠で抑える義務である。

形式化H05-Iはring tactic未import、一修理H05-I-Rは最後の2*(k*d)/(2*k)*dの同一視でomega不受理。修理二回目をせずSTOPPED、全bytesをpacket/WindowAreaIntersection.STOPPED.lean.txtへ隔離、root/Audit未採用。紙上主張とLean受理を混同しない。同証明をtactic/import/splitだけ変えて再開しない。

## H05 fixed-factor falsifier: arbitrary witness load (PROVED-PAPER)

### Exact scope
全N>=0、Z=ASSSSAAA、V_N=SAA ++ Z^N、U_N=S^3 ++ V_N ++ A。元f_N=finiteSign U_N、空BlockWord境界n=0。正不足の量化範囲は有限語全体0<k<=7+8Nであり、無限のA継続を含めない。終端q_j=6+8j (0<=j<=N)、共通元source t=3、窓長k_j=3+8jを選ぶ。grand区間は[0,7+8N]、基準r=-5。相異なる実targetの**任意のwitness選択**の費用合算を固定M倍のPで払う機構を判定する。source一意性を追加監査するまで、最新/最短witnessについては未判定としていた。以下の追加証明でこの点を更新する。

### 全Nの実供給と履歴の検証
SAAはmass1/area0。Zはmass0、prefix高さ1,0,-1,-2,-3,-2,-1,0なのでarea=-8。従ってmass(V_{j+1})=1、area(V_{j+1})=area(V_j)+8*mass(V_j)-8=0。帰納法で全jのV_jはmass1/area0となり、同じ元source3からq_jへのWinを与える。j<Nのtarget文字は次のZの先頭A、j=Nは最後に付けたAなので、全q_jは元EndN f_N 0 q_j。旧/途中sourceを切り捨てたり別prefixへresetしていない。

最初の3S後のV_jとその途中prefixは、相対高さが-2以上2以下（SAA内部は-1..1、Zをmass1の上から始めると2,1,0,-1,-2,-1,0,1）。最後のA後も相対高さ2。したがって元Fwは全非空prefixで<=-1、かつ>=-5。初期3Sも同じ範囲に入る。元S-A=-Fw>=1であり、元EndNはAに含まれるので全prefixで元S-EndN>=1が内部供給される。深さは高々5、N>=1で実際に5。run数/長さ/target数に上限はない。

### 費用の厳密式
source3の高さは-3でrから2上。各請求はQ_j=2*2*(k_j-1)-2=6+32j。よってΣ_{j=0}^N Q_j=(N+1)(6+16N)。全実A始点はr以上なので低A重み0。最初3Sのr-relative areaは4+3+2=9。V_Nのsource-relative area0と長さ3+8Nからr-relative areaは2(3+8N)。最後のAはr-relative高さ4で面積4を追加し、上三角差も8増えるためPを変えない。従ってgrand資源は

P(0,7+8N)=2*(9+2*(3+8N))-12+30=48+32N。

N>=3ならP<=48N、ΣQ>=16N^2なのでΣQ/P>=N/3。任意固定実Mに対してN>max(3M,2)を選べばΣQ>M*P。固定深さ5でも、任意witnessを足す会計には一様最大負荷が存在しない。すべての窓が共通区間[3,6]を含み、実際の重なり本数もN+1である。

### 判定と限界
固定Mによる任意witness合算はREFUTED、構成族全体の証拠はPROVED-PAPER（未Lean・人間レビュー未）。E703の有限kernel反例を全Nのkernel証明と呼ばない。freeを固定した族ではない。全prefixでA<Sであり、選んだ各q_jの直前はAだから最後S-gapはj=0。最初のAは全S後のfreeなので、その元free-gapは満たす。一般C1の反例は構成していない。E598の最後ray供給定数、E511のclean source単射、10/20の窓型LP no-go、E674の最後crossing単射とは対象が異なる。既知の「重複はある」という警告だけを新発見とせず、今回の新規部分はE681由来Q/Pの全N式と深さ5でも負荷が非有界であること。

次consumerにはwitnessの選択規則が必要。E674の同高最後crossingは長いWinのsourceそのものとは異なる下降枠を選ぶ写像であり、その異高さ・共通freeへの結合は未解決。最新witnessの重複を新たに監査するか、交差Pを元freeへ払う境界負債を供給する。任意witnessのまま固定Mを探す計算は続けない。

### 追加source一意性監査（全NのPAPER、有限独立検算付き）
上で選んだ長いWinを短いWinへ取り替えれば重複を避けられるかを攻撃した。実は各q_jの元Winのsourceは**3だけ**である。

Winのrise1とF(q_j)=-2からsource高さは必ず-3。q_j以前の全その高さの時刻は、初期3S末端の3、SAA内の5、各先行Z_lのq_l+3とq_l+7（0<=l<j）で尽くされる。source5から最初targetq_0への窓はA一歩でarea1。source q_l+3から直後q_{l+1}への窓はSSAAAでarea-3、source q_l+7ならA一歩でarea1。それ以降targetまでZを一個追加するごとの面積増分は8*mass1+area(Z)=0。従ってこれらのsourceからどの後続q_jへ伸ばしてもareaは1又は-3で、0にならない。source3だけが全jでarea0。これで全候補時計を尽くした。

したがって最新source又は最短Winを選んでも同じ窓になる。この族では**どの実Win選択でも**共通区間[3,6]への負荷N+1が避けられず、費用比の発散も避けられない。E674の「最後下降交差」はWinのsourceを短くする操作ではないので、この反証と矛盾しない。深さ<=5でも実Win区間の一様重複上限を目指す路線を停止し、下降枠やfreeとの支払いへ移る。

反証passの有限検算はN0..8をreverse加重和、N9..24を全originからのforward面積和という別の計算で確認。全selected source=[3]、全prefix正不足、floor>=-5、Q/P式が一致。N24ではA99/actual E49/free50、Q9750/P816。全N証明は上の帰納と時計分類であり、有限不在からの推定ではない。各N履歴は互いにprefixを共有するのでfresh holdoutとは呼ばない。

事前再配分は今日8CPU秒内の未使用分から2秒（各1CPU/4wall、cooperative .75秒）を明示固定。実測reverse .032064/forward .369636 workerCPU秒、controller .001409/.001591秒。数学worker累積2.784283秒。最初の誤CLIはcontroller引数検査でworker未起動、CPU未計測で0にしない。NESTED_PROTOCOLとsourcehash/終了receiptをpacketへ保存。

## Local H01: E701 actual connection
E705は同元n+2 anchor area=-15と全元W+5H<=44からd(k-1)+5H<=9を内部供給。d>=3の元高sourceは旧/n/n+1を高さで除き、全k3/H0/d<=4へ。E706は最高Aがfreeなら次の高AはactualでH0と矛盾、従って二高Aをactual SAAへ供給して符号衝突。E701は最後targetの元EndNからsourceを選び、source<bを証明して旧/n+2/n+4を尽くす。個別512MB受理、root/Audit/G5登録、全checkは日末。
局所結果であり一般化停滞をリセットする根拠にしない。source n+2を全体の入力として仮定せず、旧historyも切らない。旧H49/Rbytesは不採用のまま、新producer budget9のstrict削減後の新consumerを使った。残る深さ6はj4/n+2で、一般C1は未証明。

### 独立監査補足: H09へ使った全Nのfree/D数
有限検算のF=2N+2を全Nの入力として使う箇所があるため、全A位置を紙上で尽くす。初期S^4直後の二Aはfree：最初は必要source高さが未到達、次は唯一候補sourceからの一A area1。各Z_lのAはq_l/q_l+5/q_l+6/q_l+7の四つ。q_lは唯一source3からactual、q_l+7はlocal source q_l+4のSAAからactual。残るq_l+5/q_l+6は元global floor -5とその一段上 -4のAなのでfree。前者は必要sourceがfloor未満、後者はsource=floorから全歩み非負・最後高さ1でarea>0。終端q_Nもactual。従って全NでA=4N+3/E=2N+1/free=2N+2。N0は初期二free/終端actualだけで同式。
初期S4を除いたときexclusive old-S供給Dになるのはsource3しか持たないq_jのN+1件。local SAA q_l+7はcut4以後のsourceを持つのでexclusiveでない。他Aは元free。よってD=N+1も全Nで成立し、H09候補のD/F=1/2は有限不在からの外挿ではない。この補足は既存E704族のconsumer監査であり新しい独立coverage/G進展へ数えない。
