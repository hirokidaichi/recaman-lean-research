# Short-target counter band (2026-11-02)

結論候補 E-521: 同じ元p/padded BlockWord/zero-fullpositive/全正三run zerohead/同old target実mass C>=4/1<=v<Cで、full-tail free<R=j+1というcounterがあれば、下記五bandに限られる。全old履歴は無制限。紙上証明と別pass監査の後も、actual last count接着・残余全包含はLean未形式化なのでPROVED-PAPER、human review未とする。counter不在やC1全体ではない。

## Exact quantifiers and starting evidence

E-520のshort_source_intの全primitive phase/P2/zero/fullpositive仮定とcounterをそのまま使う。六head長h,M,m,L,s,Uは正、S=h+m+s=M+L+U、D=C-v>=1。T+C=v+j+1なのでT=R-D。全C/v/R/old prefix/historyに有限上限を入力しない。R>=5、M<=R+1、全old last供給なし、全initialS/firstA local源なし、middleS源はD1/i0/M=R+1のみ、はE-520が内部供給する。head actual supply<=10は既存InitialSTargetBounds.three_run_count_of_manyS（s>=1/S>=3）を使う。

## Full source coverage gives actual last budgets

E-520により最後A-rayの全P2源はmiddleS以後。D1ではmiddleS源はclock0だけ、第二A-runの源はconstant-run root uniquenessで高々1clock、第三S-runも高々1clock、第三Aと最後Sの源は既存AdjacentRunSupply.local_A_S_clock_iffで共有clock2だけ。従って実EndN supplied clockは高々4。D>=2ではmiddleSも全排除されるので高々3。各source族は存在する供給源から選ぶ全包含で、独立したEndable tagを仮定せず、複数sourceが同clockに重なる場合は上界を弱めるだけ。endpoint Aは実A-run条件に含まれ、全old last供給排除はE520から既に得ている。有限のrun長やsourceの列挙はない。

## Actual count addition

head A=S、last A=T=R-D。separator中のA/EndNは0。head supply<=10と上記last<=bを同じ元pで加算する。free<Rなので

    S+R-D = total A = total actual supply + total actual free
           <= 10+b+R-1,
    S <= D+9+b.

D1ではb4によりS<=14。D>=2ではb3によりS<=D+12。これはA countの独立仮定ではなくactual partitionからの帰結。

## Same target key and monotone substitution

同じtarget suffix uとhead zについて、E520の実target profileは

    ku = -kz -4CS -4Cv +2v² -2R².

BlockWord ku>=-2と全word kz>=-2S²より

    R² <= S² -2CS +v² -2Cv +1.                       (K)

R>=5、0<v<Cから右辺の定数v²-2Cv+1<0。よってS²-2CS>0、S>0なのでS>2C。従ってF(S)=S²-2CSはこの域で増加し、前段で証明したS上界へ代入できる。代入前に単調性の域を確認する。

D1: v=C-1、S<=14を(K)へ入れると

    R² <= 198-28C-C².

R>=5/C>=4からC4又は5。C4はR²<=70なのでR5..8、C5はR²<=33なのでR5だけ。従って(v,C,R)=(3,4,5..8)又は(4,5,5)。

D>=2: v=C-D、S<=D+12を(K)へ入れ、展開して

    R² +D²+4Dv+v²+24v <=145.                         (Q)

R>=5よりD²+4Dv+v²+24v<=120。v4/D2でも148>120なのでv<=3。
- v1: C>=4よりD>=3、D8ならD²+4D+25=121>120、従ってD3..7/C4..8。最小D3でR²<=99なのでR5..9。
- v2: D>=2、D6ならD²+8D+52=136>120、従ってD2..5/C4..7。最小D2でR²<=73なのでR5..8。
- v3: D>=2、D3ならD²+12D+81=126>120、従ってD2/C5。R²<=36なのでR5..6。

後三bandでは(Q)も保持し、箱の中の全tupleが実現するとは主張しない。全体でC<=8/v<=4/R<=9。S<=19、A=S+T<=21も同じ加法から従う。chosen targetより前のold prefix/全head履歴はなお無制限で、有限historyの分類や反例不在ではない。

## Separate falsifier/auditor pass

- D1のmiddleS/i0を消していない。D>=2だけがmiddleSを消せる。
- head10は全positiveの実履歴で使用し、generic三run11を無断で10にしない。
- last budget3/4は供給clockのunion上界。third A/final Sを共有clock2として扱い、別のclockを落としていない。
- S>2Cを証明する前のconvex二次式への上界代入を行わない。S=2Cは(K)の負定数で不可。
- C6/D1ではC²+28C=204>173、v4/D2では148>120、v1D8は121>120という各境界を逐語検算。
- R上界は各bandの(Q)又はD1式から供給し、r3 free-budgetや任意r rankへ置換していない。
- 新しい実C1反例は得ていない。既知mass1 E453は全適用域外、E520のcounter necessary restrictionsと親counter不在を区別する。

## Status and next decision

紙上chainは閉じている。証拠水準はPROVED-PAPER、人間レビュー未。未Leanの最弱edgeは、E520の実window/source削減から同じ元pのlast supplied<=4/3を供給するcount接着。その後(K)/(Q)と五band包含を形式化する。C/v/R上界を仮定した同値wrapperや既知大表の資源追加で代用しない。五bandの反例不在、C<=2、非zerohead、他target source位置、任意run/C1/Q/H/SL/全射性は未解決。

## 07:35 evidence update

E-522の元p実last3/4 count接着は個別512MBで成功し登録/全checkへ進んだ。上記source全包含を元Endable baseを保ったままliteral残余rayへ対応させる。E521五band包含の追加monolithic算術はNat/Int castのgrind失敗と512MB kernel memoryでSTOPPED、依存adapterは未検証。両sourceをpacket/intermediateへ隔離し、root/Audit未採用。E521はPROVED-PAPERのまま、人間レビュー未。次の再開にはactual S上界からfactored-circleで先にstrict候補削減する独立した証明構造が必要。時間/メモリ追加、単なるsplit/import移動では再開しない。
