# 2026-11-08 — 供給元と供給clockの共同予算

## 確定したedge

E590は元Nat及びIntp/padded BlockWord/zero-fullpositive/同実第三S対象に接続しPROVED-LEANへ。全run長・全old履歴でcounterならM+L+q+v<=15、q+v<=13、R<=12、T+U<=25、A<=27。実last7から第二A/第三Sそれぞれの区間内sourceを内部供給するE592と、共同OR予算E591を用いた。源clockを同一と仮定しない。

新しいS/S機構。早いSの残余b、後のSの残余kでz=s+v,y=k+vとおく。同keyの二源から (b+z)^2-y^2=2Lz、1<=y<=z。b>=Lなら左辺は少なくとも2bz+b^2>2Lz。したがって早いsource深さはb<L、sourceAt false mをsourceAt false (min m (L-1))へstrictに削減できる。

v>=1ならy>=2。L2はb1/y=z-1、L4はb2/y=z-2だけが残り、各sourceのmass式からclockが一致する。L1は両立不可。L3は小平方差3、L4の他depthは小平方差8から排除。L<=4で二S族のORcount<=1、local最後<=5、全oldを加えた元実最後<=6。L2では両源がclock0に共存するliteral例を保持。L5/m3/s2/U2/v2ではclock1/2に別々の源があり、同clock主張をL5へ広げられない。いずれもC1反例ではない。

同targetの偶奇機構。対象の(q+v)^2=R^2+2Uvと平方mod4の残余0/1からUvは偶数。第二A source深さaなら(s+v-a)^2=a^2+2Uv+1なのでaは偶数。第三S供給源の存在は不要。L1ではこのA族を除去し、S/S共同一件と末尾clock2によりlate suffix<=2、元実最後<=5。targetなしではA1/s2/U1/v1/clock2の源があるため、target条件は省けない。

## 06:15時点 E593 PROVED-PAPER（後段の独立証明で更新） — A/S二源の深さ4と二次上界

第二A depth aと第三S depth kの両源からx=s+v-a,y=k+vでx^2=a^2+y^2、y^2=1+2Uv、x=U+i-1>=-1、y>=1。x=-1/0は右辺>=2と矛盾しx>=1。a>=1からy<x。よってy<=x-1を平方比較して2(s+v)<= (a+1)^2。

a1/3ならyは奇数、xは偶数となりx^2=a^2+y^2はmod4で0=2。a2ならx/yの奇平方差は8の倍数だがa^2=4で矛盾する。従ってa>=4。L4/s8/U4/v1はa4,k2、clock2/0で両立する。この前のclock6という誤記はLean decideに拒否され2へ訂正した。

この紙上全長命題のLean試作H08は一回修理後もcntF_appendの名前解決で不受理、STOPPEDとしてpacketへ隔離。kernel採用しない。名前空間/tactic/import修正だけで再開しない。後続S/S機構と同target parityは別のsource比較でありH08に依存しない。

## 証拠の限界

小circle378tuple、小平方差25tupleはそれぞれ明示上界を先に証明した完全kernel算術補助。履歴の有限列挙や反例不在の実験ではない。全old historyと他supplier massは無制限で、C1/Q/H/SL/全射性は未証明。全成果で人間レビュー未。

## L1の元actual counter

E596 PROVED-LEAN。実last<=5と元head<=10/実partitionからM+1+q+v<=14。残余12ならM1/headactual10/last5/free=j、r>=4からheadA>=14/U>=12。元同targetはT+U=R+12/R5..11/144=R²+2Uv。U>=12でv<=4、28小整数枝が不可能。従って残余<=11/R<=10/T+U<=21/A<=24。Intpへの輸送は元padded履歴とzero/fullpositiveから相対条件を内部供給し、窓の始点も保存した。

## 任意mixed futureへの拡張と補助定数案の反証

E593は独立全word cross_four/primitive S奇数という新入力でPROVED-LEANへ更新。任意future xでA depth a%4=0、4(s+cntF x)<=(a+2)^2。旧H08のSAS専用試作は再実行せずSTOPPEDを保持。E597は前S depth<L、短AのS/S同clock、隣接S/AのL8排除を組み合わせ、L<=3のS-A-S三源を合わせ一clockへ。任意前置rsと元old付きでlast<=2+len(rs)+rayCount x。これは実free/rankの供給ではない。

E598 REFUTED。固定四runの最後7件を全runの固定定数へ外挿する補助案は偽。w0=SA2S2、w(k+1)=A^(4*3^k)S^(6*3^k)wk。全kでF=3*3^k/mass=-3^k/key=-2、全i<=NのwiがwNのsuffixなのでclock3^i+1を供給しrayCount(wN,3^N+2)>=N+1。

更にw_(N+1)を実Nat streamで実現し、d=3^(N+1)、初期S長3d+3、最後A長d+1とすると、元0の空BlockWord旧履歴/zero/全prefixpositive/同じ実EndN endpoint targetを持ちながら最後の元実供給>=N+1。全A<=3d+1<paddingでpositiveを内部供給した。最初A長4*3^Nと既存単一A予算から元fullfree>=2も供給。従ってこれはj0のC1反例ではなく、source-only固定定数上限の反証。actual free不足を追加した反例限定の一様上限は別問。

一般化には、増える供給を実freeで支払う償却課金が必要。A数の上界をfreeへ置換しない。旧E453のfree-prefix shortcut反証も保持する。

## E599 — 第三Sの全長元free-gap

07:07 Nat residual主定理、07:08〜09 original Int全第三S/既存lateとの統合を受理。actual counterでfree<=3ならr3全A<=2free+1と同target平方/質量が矛盾し、free>=4/R>=5/p=q+v>=6。E590のW+p15からM,L<=8。隣接sourceを初期S/第一Aと第二S/第二Aで共同課金しlast<=5、L<=3なら三族一clockでlast<=4。headfree r>=4と元free不足によりU>=p。L>=4ではp<=9、短Lではp<=11。

6<=p<=11/R5..10/v1..5の180完全整数tuple（割り切れ性とp<=U<p+R）から同targetは(p,R,U,v,T)=(11,5,12,4,4)/(11,7,12,3,6)だけ。p11とactual会計はM=L1を強制する。middle三sourceは平方73/74/97/98とs+v>=11で全排除、初期S/第一A共同一clockと末尾clock2、全old一clockで実last<=3。しかし元counterはlast4を要求し矛盾する。

全old履歴と各source以前prefixを保持。元Intpへabsolute zero/fullpositiveから相対positiveを内部供給。既存q<=3と合成して第三S全域、既存第三A以降との合成で第二A終了以降を閉じた。統合は追加source edgeと数えない。r3 checked countに依存し未検証r4/E384は不使用。全四run/任意runの証明ではない。

### 2026-11-08 07:28追加 — E-600/E-601/E-602

E-600 `PROVED-LEAN` はM,L<=8の元actual head<=M+L+3。E-601 `PROVED-LEAN` は元Intp/padded BlockWord/zero-fullpositive/真正四A-run/第二A内の同actual target全域のfull-tail free>=j+1。全gap/全run長/全old履歴を保持し、target以前prefixをresetしない。新head供給からD<=7/U帯を内部導出し、小平方矛盾で閉じる。E-599と既存late域の統合で第二A開始以降を供給、wrapperに別coverageを計上しない。E-602 `PROVED-LEAN` はwhole-A targetのkey単調性からA source族を排除、R>=2を保持。狭い開始target bandのcoverageはE-601に包含。

H26一般counter-band旧jobは512MB STOPPED、隔離を維持。E-601は独立E-600のhead削減を消費した同512MBの新証明で、単なるlayout/resource変更でない。残る局所対象は初期S/第一A/第二S。任意run数ではE-598の供給非有界族が固定定数法を反証しており、元actual freeへ増えるsourceを償却課金する機構が未供給。人間レビュー未、C1/Q/H/SL/全射性は未証明。

### 07:35 層状反証族の支払い監査と第二Sの停止

E-598の同じ全N構成で、元fullfree>=N+1、4*3^N<=fullfree+2、N>=1なら最後rayの全actual供給<=fullfreeをkernel供給。local上界2N+2と最初Aのfreeを結合したこの族だけの償却会計。一般historyのsource→free単射、全run/C1の証明ではなく、独立coverageに計上しない。固定定数法はREFUTEDのまま。

第二S actual counterのM9/p7/R5排除chainはPAPER。H39は一回import修理後512MB kernel STOPPED、counter未検証sourceと受理済みprofileをpacket隔離しroot/Auditへ採用しない。任意S源順序のH22案は既存ASourceReuseで既知と判明し再証明せず停止。次回の第二SではこのPAPERの再layoutでなく、同targetから別のsource族削減を先に得る必要がある。

### 07:39 E-603 — 第二S残余1の新actual source削減

`PROVED-LEAN`。同じ元Nat0/BlockWord旧履歴/四run/第二S残余1 actual target/j>=1から、同S族を全除去し元lastEndN<=6を供給。全M/L/old履歴でsource不存在やcount上界を入力しない。raw source単調性は任意mixed x、actual adapterは四run。j0では自己sourceが共存するliteral境界を受理。H39の一般counter jobを再開せず新source入力を得た。q1のfullgap、q>=2の第二S、初期S/第一Aは未証明。

### 07:41 第二S残余1の次の完全紙上chain（未Lean、E-604予定）

同元actual counterとq1、R=j+1、z=s+v、p=z+1。E603の実last6と元head10、r3、actual partitionからR>=5/M+p<=15、p>=R+2、M<=8、z<=13。同actual targetの既存initial-S式はL+U+T=R+p及びp²-R²=2Lz+2Uv。L>=8なら右辺>=16z+2、左辺<=z²+2z-24なのでz(z-14)>=26、0<z<=13に矛盾。従ってL<=7。ここは一般H39のM9飽和分類と異なり、新source6でbootstrapを先に切る。

E600からEH<=M+L+3、短pairからE<=5及びL<=3ならE<=4。L<pは平方とp>=7/L<=7（等号も不可能）から従いD=p-L>=1。平方を変形してD²=R²+L²-2L+2Uv。L²-2L>=-1、Uv>=1よりD>R、D>=6。全partitionでD<=7、E<=TでU<=R+2。headfree r<=3ならEH<=r+1でM+L+D<=r+5<=8。L>=4なら左辺>=11、L<=3ならE<=4でさらにM+L+D<=r+4<=7だが左辺>=8。従ってr>=4。最後ray free会計T+r<=F+EからU>=D。

D6..7/R>=5/R<D/D<=U<=R+2の平方式を確認する。D=R+1なら差2D-1はL²-2L+2Uv>=-1+2Dを下回れず、等号にはL1/U=D/v1が必要。L1ではE<=4かつr>=4からU>=D+1となり矛盾。残るD7/R5はU7、(L-1)²+14v=25。v>=2は不可、v1なら(L-1)²=11で平方3²/4²の間。よってq1 actual counterはない、全長fullgapが紙上では従う。

受入しているLean evidenceはE603のsource6とE600のhead予算まで。この全actual chainは未Lean・人間レビュー未、有限history分類やC1全体証明に昇格しない。次回の最初15分はsource6→M/L bootstrap又は元fullgapのkernel接着。一般H39 STOPは保ち、同じjobのlayout/tactic/resourceだけの再実行をしない。

07:42 helper停止。H52は未知定理名を一回修理後も未解決grindとなりSTOPPED。sourceはstopped/UnitSTargetSquare.lean.txt、root/Audit未採用、純算術helperの受理も主張しない。紙上chainは維持するがE604をPROVED-LEANへ上げない。再開するならD=R+1を単にgrind再投入せず、(L-1)^2+2(U-D)v+2D(v-1)=0の三非負項の小さい完全certificateという独立因数化を先に固定・検証し、同512MBの測定改善が必要。

falsifierの弱化会計境界。M1/L1/U6/T5/s5/v1/q1/R5/F4/E4/EH5/r3は、target平方、全partition A13=EH5+E4+F4、head依存供給EH<=M+L+3、last<=4、T+r<=F+Eを全て満たす。しかしr3の実head帰結EH<=r+1（5<=4）は偽となる。従ってsource countとscalar targetだけではq1 counterを排除できず、元historyからr3 checked countを同じheadへ接続することが不可欠。この弱化会計はactual positive履歴として実現したものでも親C1反例でもない。

### 07:44 別候補: 第二S残余2のcounter-conditioned source除去（PAPER、未Lean）

同第二S actual counterから既存供給17とr3によりR>=5/M+p<=16、p=q+s+v<=15。q2で同S sourceがあれば、既存S_source_reuse_orderよりk<2なのでk1。同じtarget/key差でR²-1=(2-1)(2+1+2z)=3+2z、z=s+v。従ってR²=4+2z、Rは偶数、R>=6、p=z+2=R²/2>=18となりp<=15に矛盾。q2の同S族もcounter内では全排除できる。これはq1の無条件除去と異なり、元counter会計を要する新joint source条件である。供給結論/counter帯を新Propとして主定理へ入力せず、元履歴から内部供給することが未知edge。

全actual接続は未Lean。q2 source排除からlast6/M<=8/p<=14、同target平方でL<=8（z<=12かつL>=9ならz(z-14)>=21が必要になり矛盾）という次のbootstrapが期待できるが、全length fullgapはここでは証明しない。q3ではk1/R5/z4又R7/z10という平方可能形が残り、q<=3を一括で源不存在に拡張してはならない。q2 counter-source除去をq1接着が停滞した場合の切替先にする。
