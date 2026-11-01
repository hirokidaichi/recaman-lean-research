# 2026-11-01 C1: inversionがlocal供給を抑える

最終状態: E487 componentsだけでなくE492のD>=5 fullgap、E497のD>=4 headfree5もkernel供給。旧LargeOldSeedGapと一般I25 layoutはSTOPPEDを保持する。数学的帰結のカバーと失敗sourceの再開を区別する。

## 検証済みcomponent（E487、全check同期前）

I=M(m+s)+Ls、正M,m,L,s、任意h/第三A長K。I<=16なら第三ray local供給<=2、I<=36なら<=3。headS/全語長/h/K/old prefixに有限上限を入力しない。exact local source分類を初期S/第一A/第二S/固定clock2に分け、同じclockを一度だけ数える。

元BlockWord prefix/実relative-positiveの三run headへ接着すると、同じI<=16でhead実供給<=8、I<=36で<=9。第一二runの既存実供給5と、第三local2/3+共通old高々1を非重複countで合成。Iは測定可能な同じheadの量で、free結論や独立tagではない。

## 全長source証明chain

I<=16: 初期S源qのQ=q+m+sはQ²2I1<=33、Q3又は5、従ってI4又は12。第一A残りeのb=m+sは2eb+2Ls=b²-1、e<=Mからb<=5。b偶数は排除、b3はclock2、b5はLs7又は2。Ls7はi>=0と小さいsで不可能。Ls2はclock2か(M,m,L,s)=(2,3,1,2)/clock3。この例外ならb5で初期S源は不可能、第二S源の非clock2（L4/s1/m>=2/clock0）とも不両立。

第二S源は(q+s)²2Ls1、q<=m、I<=16からq+s3又は5。5ならLs12だがM(m+s)<=4とm+s>=q+s5が矛盾。3ならLs4、clock2又はL4/s1/m>=2/clock0。後者と初期S源が同時ならI12/M(m+1)=8で、q+m+1=5からm3/M2、初期Sもclock0へ合流。残る源unionは二clock以下。

I<=36: 初期S源Qは3/5/7、I4/12/24。初期S源があるとb<=6。第一Aがclock2でないならb5/e2/Ls2でI5M2だが、初期SはQ7/I24を要求し矛盾。b3ならclock2、偶数bは不可能。従って初期Sと非clock2第一Aが同時にない。初期S一clock又は第一A一clock、第二S一clock、固定2の高々三つ。

これはE415の無条件local2/3を再主張しない。E415の反例I84/612は今回のI上限外。上限だけを変更した補助仮説修理ではなく、同じwordの平方/source衝突を示す独立機構。

有限反証passはI<=14の1284直接ケース、fresh h17/clock0..18の214逆走査ケースでmax2（COMPUTED）。I<=16/36は上のsource算術を先に紙上診断してからLean化。有限結果をそのまま無制限の証明にしていない。

## 同じold sourceからのinversion不等式

uは同じBlockWord prefixの実old suffix、D=mass u、head zはmass0、S=cntF z、runKey z=4I-2S²。実old供給clockk<=1のmass/keyからv-D=k-1、従って(v-D)²<=1。原始key(u)>=-2から

`2I+2DS+D²-1<=S²`。

この不等式はword/windowを保持してLean検証。source以前prefixやその他old massを切らない。scalar helperはS<=N/D>=dから2I<=N(N-2d)-d²+1を与えるが、単独の算術helperをfrontier進展とはしない。

## E488 PROVED-PAPER（未Lean・人間レビュー未）

元p/padded/zero-fullpositive、正三run zero-mass head、同old targetと最終S final-band local、最後rayの特定実old supplierのmass D>=6なら元full-tail free>=R=j+1。

仮counterでは既存r3/A下限によりR>=5。E441はk<=1とv>=C(targetmass)を供給し、T=R+v-C。元全実供給17とF<RからS<=16。同じsource不等式のN16/d6から2I<=29、ゆえにI<=14。上の検証済みcomponentからhead実供給8、最後実供給は既存local6+old1<=7なので全実供給<=15。再度countercountを使うとS<=14。同じsource不等式N14/d6は2I<=-7を与え、I>=0に矛盾。全て内部出力で、新Propの仮定化なし。従ってtargetmassC>=5のold-seed枝もPAPERで排除できる（D>C）。

この全接着のmonolithic LargeOldSeedGap layoutは512MBで初回/一回repairとも失敗、Nat加法境界のomegaも未解決。packetへ隔離しroot/Auditへ入れていない。普通buildで上限を外して採用せず、compiled import移動だけで再開しない。PAPER全体と、Lean検証済みcomponentを区別する。

## 次の別機構

大きいold source D>=6がclock<=2なら、target/counterを仮定せずheadS>=15/head実free>=5を前向きに供給できるか（H05）。これは停止した全接着layoutの分割移動ではなく、仮定と数学的結論が異なるsource-conditioned lemma。低massC4はIのbootstrapが必要、まだ全gapを証明したとはしない。
