# C1 Q: 面積の結合と弱化historyの監査

今回のcycleは`R-20261022-MAKEUP`、[カード](HYPOTHESIS_CARD_2026-10-22_C1_Q_MAKEUP.md)を正本とする。
数学的な中心命題C1/Q/Hは未解決。ここでは停止した十分条件と次に必要な入力を区別して記す。

## 独立な前半面積は非負でない（REFUTED）

`SAAA|SSSSAAAASAAA`（p=0,k1=4,q0=16）でg=2、d(q0)=1、内部d>0、a_z=3。
Az=Σ_(4,16](F(u)−g+1)=−2。F(q0)=4なのでq0自身はQのguardを満たさない。
ここからSを2回進めたb=18ではF(b)=g、Y=3、Z=1。
したがって「Az≥0、Y≥0を別々に示す」という方法はSTOPPEDだが、Qの反例ではない。
Az≥1はz=Sでも0になるため偽。上の16clock例を最小反例とは称さない。

全量化子・定義は[仮定台帳](RESEARCH_ALLOCATION_2026-10-21.md)、直接和による再計算は
[check_witness.py](data/c1_q_makeup_20261022/check_witness.py)と[出力](data/c1_q_makeup_20261022/az-counterexample.json)。

## R: Sだけで初めてgへ戻る場合（CONJECTURED）

h=F(q0)−g=a_z−1>0なら、q0からh回のSでgへ戻ったときの面積は
`Az+h(h+1)/2`となる。これは恒等式であり、非負下界Rの証明ではない。
Rが真でも一般のyにはA/Endableが混じるので、それだけではQを閉じない。
長い履歴の凍結holdoutではRの最小1だったが、一様な紙上入力はまだない。

## 個数条件と走行最小値の禁止だけでは足りない（弱化モデル）

以下はEndableを自由tagに置き換えたモデル。実際のP2窓を持つ語の反例ではない。
任意の整数m≥4について、k1=p=0、g=0、z=`S^m A^(m+1)`、q0=2m+1とする。
最初の2個のAだけを非Endable、残るm−1個をEndableとtag付けする。続けてyにSを2個置き、b=q0+1とする。

- z内部のdは正で、d(q0)=1、a_z=2、F(q0)=1。yは非Endable Aを使わず、b+1までd≥1。
- tag付きEndable Aは全て走行最小値−mより2以上高いclockで始まる。
  従って既存のN「最小値または最小値+1のAは非Endable」をこのモデルは守る。
- zの通常面積は1−m²、長さは2m+1だからAz=2m+2−m²。
  bでF(b)=g、Y=1、Z=Az+1=2m+3−m²<0。
- 従ってN・dの個数条件・a_y≤1・Y≥0だけからR/B/Qを導くことはできない。

このモデルの偽tagを検出するため、実際の窓のmomentを計算する。
z中のA clock b'=m+jに対し、S-run内の始点でmass=1を満たすものはt=m−j+1しかない。
その窓は`S^(j−1) A^j`、momentは`1−(j−1)²`で、0になるのはj=2のみ。
A-run内の候補は直前のA（長さ1、moment=1）でP2にならない。
従って実際のEndableは1clockだけで、実際のd(q0)=m−1≥3となる。モデルのd=1とは一致しない。

これは自由tagから真のP2条件へ戻す必要性を示すno-goである。Qの数学的labelはCONJECTUREDを維持する。
別passでm=4..32の直接和を照合し、式・添字・真のEndableとの差を監査した。
一様なno-goの根拠は上の式で、有限計算をその代わりにはしない。

## 最低水準をq0以後に訪れる場合（PROVED-LEAN、E-379）

β+A^aのprefix終端をn=k1、q0≤r≤b、M=Fw(r)、全n≤u≤bでM≤Fw(u)とする。
元のp基点でa_p(q0,b)≤1なら、Fw(b)≤M+1。
実際、2段上なら離散中間値でr≤u<v<bにレベルMとM+1のAを得る。
既存のブロック接尾辞正値性から、この二つはいずれも元のpから非Endableなので予算に反する。
従って全n≤u≤bでFw(u)−Fw(b)+1≥0となりZ(b)≥0。

このchainは[BlockSuffixPositivity.lean](../Recaman/BlockSuffixPositivity.lean)の
`block_prefix_low_clock_not_endable`、`two_nonsupplied_additions_of_recovery`、
`area_nonneg_of_fresh_low_visit`（および整数clock版）として形式化した。
予算を2へ弱めると`SSSAAAS`のq0=1,r=3,b=6でZ=−3。
親Dからβを供給する短いEqClassWの依存を消したわけではない。

これで残るQのcaseは、[k1,b]全体の最低水準がq0より前にしかない場合となる。
有限区間の最低値は存在するが、その存在を仮定しただけでQを証明した扱いにはしていない。

## 深さを限定した古いprefixの正確な削減（PROVED-LEAN、E-380）

ブロックprefixの接尾辞は密度10S≤3L、mass R=L−2Sを満たすので2L≤5R。
窓の始点t<n、終点bならR=Fw(n)−Fw(b)+1。
Fw(b)≥Fw(n)−Dを仮定すると、tはnの直前floor(5(D+1)/2)clock以内にある。
従ってそれ以前のprefixを削ってもEndableは両方向に変わらない。

D=4ではR≤5かつL−Rが偶数。L=12ならRは偶数≤4となり密度に反するため、L≤11。
この削減は`endable_iff_last_eleven_of_depth_four`で形式化した。
残すのはk1直前11clockとk1以後の**全tail**であり、lag上限や有限状態機械ではない。
深さ4を元のDから供給する一様証明も得ていない。

半径を落とす対照は`SSAAAASAAA S^8 A^6`（n=10,b=23,D=3）。
唯一の窓始点は0で、prefix9clockだけでは失う。全始点の直接和を
[context-radius-sharp.json](data/c1_q_makeup_20261022/context-radius-sharp.json)へ保存した。

全体検証: 404 build jobs、2663宣言の公理監査が通過。
逐語監査は[E-379](statement_audits/E-379.md)と[E-380](statement_audits/E-380.md)。
数学的境界を保ったまま、次は深さ4・a_z≤3の有限context分類を検査する。

## 接尾辞閉性と代表の長さ（E-380の補助証明）

三つのatomのどのsuffixもBlockWordである。特にtripleの先頭Sを落とした
`SAAAA SAAA`は`SAAA A SAAA`に分解できる。
appendを切る位置で場合分けするとBlockWord全体の任意suffixもBlockWordとなる（`block_suffix`）。
従って元のprefixがいくら長くても、直前11clockそのものを長さ11のBlockWordで代表できる。
最初の安全な「最後のblock列の長さ≤20」より強い結果である。

## massに応じた二次面積と等号分類（PROVED-LEAN、E-381）

全BlockWord wについて

```text
mass(w)*(mass(w)+1) <= 2*areaW(w)+2
```

面積defect `2area−mass(mass+1)`は、atom Aを付けても変わらない。
SAAAを付けると4mass−2、tripleを付けると12mass−2だけ増える。
空prefixでは新しいdefectが−2、非空prefixのmassは1以上なので、その後の非A atomはdefectを増やす。
これで文法の帰納から下界が得られ、等号はちょうど

```text
SAAA A^j   または   SSAAAASAAA A^j     (j>=0)
```

となる。両族の等号も全jでLean確認し、定数2はsharp。
BlockWordを外すとSSAAA（mass1,area−3）で偽となる。

全suffixがBlockWordなので、旧始点t<k1の実際のprefix面積にも同じ下界を供給できる。
P2(t,b)があればr=F(k1)−F(b)+1、窓momentをk1で分けると`A_old+Z(b)=0`。
従って

```text
2Z(b) <= 2-r(r+1)
```

が古い窓の必要条件となる（`old_window_area_upper`）。
r≥2では、別に`Z(b)>=2-r(r+1)/2`を示せればmoment≥1となって排除できる。
r=1は既存のA_old≥1とZ≥0を使う。これは元Qを修理・証明したものではなく、
古い窓を排除するために必要な後半面積の評価を弱める新しいprefix入力である。
下界を仮定したwrapperを研究成果に数えず、証明した内容をBQ・等号分類に限定する。

## 深さ4・a_z≤3の全context分類（COMPUTED、E-382）

BlockWordの短いprefix50個と、長さ11のcontext21個、合計71代表を生成した。
全代表について実際のP2を使ってzとyを分岐させ、正slack・非Endable A予算・深さ4だけで枝刈りした。
語長やS数の数学的cutoffは置かず、保護guard512にも時間上限にも達せずに探索木を完了した。

- 46,674 node、517個のq0 endpoint、19,950 guard判定。Z最小1。
- a_z=0のzはS、1ではSA、2ではSAA/SSAAA。
- a_z=3ではSASAAA/SSAAAA/SSAAAASA/SSSSAAAASAAAの4語のみ。
  4語が全てのprefixで可能だという主張ではなく、許容contextはprefixに依存する。
- 最大の訪問stateはk1以後20clock分（endpoint bの符号は別に選ぶ）。
  これは任意長を事前に20まで切った検査ではない。
- 別Pythonで全始点の後ろ向きmass/momentと直接の面積和を使い、G式やmod4枝刈りなしで
  node数・全cut数・全候補・全min値が一致した。
- 文法の71代表も、13状態の独立NFAから得た全suffix集合と一致した。

再現: [context-classify.meta.json](data/c1_q_makeup_20261022/context-classify.meta.json)、
[context-tree-audit.json](data/c1_q_makeup_20261022/context-tree-audit.json)。
これは明示した深さ・A予算の下での計算分類で、Lean証明書への変換は未完了。
深さ4を元のDから供給したわけではなく、一般Q/C1/H/SLの証明に昇格しない。

## 制約探索の停止結果（ここまで）

- prefix SAAA,q0=32,b=64のQ-old-minモデルは27.575秒でINFEASIBLE。
  その有限パラメータの反例がないというCOMPUTED結果だけ。
- R-negative（q0=80）は900.256秒でUNKNOWN、peak-five（q0=80）は899.991秒でUNKNOWN。
  同じ設定の時間延長はSTOPPED。R_C1やpeak候補を証明・反証したとは扱わない。
- R_C1はこのノートの局所面積候補で、E-366のTheorem RやTSの状態座標Qとは別の記号。
- 次の仮定供給候補は、a_z≤3のdefect1で深さ5に達する実際の語があるか。
  その後、各old windowが面積spectrumに入るだけで共通prefixへ持ち上がるかを監査する。

## 適応的な共通prefixとtail長32（PROVED-LEAN / COMPUTED、E-380/E-383）

全後半区間[n,B)で高さがg−D以上なら、ある一つの切断s≤nで全endpointのEndableを同時に保存し、
残るprefix suffixはBlockWord、s=nまたはmassが1..D+1になる（endable_tail_mass_representative）。
最古の実際のold window始点を選ぶ証明で、各endpointごとに勝手に別のprefixへ取り替えたものではない。
ただし削除前の不足d(n)=0までこのLean定理が保存したとは言わない。

長さL≤32でd(q0)=1ならmass=a_z−1≥−1より全S≤16、全tailの高さはg−16以上。
従って必要なprefixはmass≤17の20111語へ帰着する。全代表のprefix不足0と非負性を独立検査した。
深さのcutoffを置かず、長さ1..32の全tailを125181373 nodeで完了し、a_z≤3で深さ≥5は0。
a_z=3のzはE-382と同じ4語、最大長12だが、32以後に新しい語がないという証明ではない。
元C++と、F/G・mod4を使わない別C++の全tree照合も2.53秒で完了し、全counts/min値/候補語が一致した。

## 古い面積の上界と全massのspectrum（E-381 / E-384）

BlockWordのareaは `4area≤5mass²−11mass+16` も満たす（PROVED-LEAN）。
A SAAAで等号、文法を落とすAAASSSはmass0/area9の反例。
下界と上界を併せた整数区間が、mass≥2で**実現できる全areaの集合ちょうど**になることを
[紙上の帰納](RESEARCH_NOTE_2026-10-22_BLOCK_AREA_SPECTRUM.md)で示した（PROVED-PAPER）。
mass0/1はそれぞれ{0}/{1}。存在方向は未Lean、人間レビュー未。
同じ一つのprefixで全clockの候補を同時に実現できる、という主張はしていない。

## 最終の制約結果と次の一問

- deep-three: 固定prefix SAAA、q0=80、a_z≤3、深さ≥5のexactモデルは900.0125秒でUNKNOWN。
- Y-triangle: 固定prefix SAAA、q0=32,b=64、2Y<h(h+1)のexactモデルは120.0023秒でUNKNOWN。
- old spectrum緩和: N=32の個別spectrum条件だけを残す緩和でも3.9078秒でINFEASIBLE。
  有限長32の結果だけ。SATではなかったためcommon_prefix_lift.pyの持上げ探索は実行していない。
- UNKNOWNの三つの900秒runと120秒runの時間延長をSTOPPEDとする。数学的R/Y/深さ候補はCONJECTURED。
- 次の一問は、prefix不足0・正不足excursion・終端不足1・a_z≤3から、語長に依存せず深さ≤4を供給できるか。
  強い補助入力の問いであり、反例が出ても完成D版Qが反証されたとは扱わない。
  有限長の延長、同じUNKNOWNモデルの再実行、Pの再監査を次unitにはしない。

最終検証は404 build jobs/2685宣言、許可した公理のみ。全逐語監査とregistry gateを通過した。
実時刻・実績・commands・費用・次の受入条件は[最終引き継ぎ](RESEARCH_HANDOFF_2026-10-22_MAKEUP.md)を参照。

## Qの部分領域を組み合わせる（COMPUTEDを含む、全Qの証明ではない）

E-382の深さ条件を全yへ永久に課す必要はない。
a_z≤3かつz=[k1,q0]の高さがg−4以上なら、任意の将来のguard endpoint bについて二分する。

1. [k1,b]全体がg−4以上なら、E-382の全探索木の範囲に入りZ≥1。
2. それを下回るなら、[k1,b]の最小値は必ずq0以後に達する。
   元のp基点のa_p(q0,b)≤1なので、E-379のfresh-low結果からZ≥0。

従って元の正不足・A予算などのguardの下で、**zの深さ≤4だけ**あれば将来のyの語長・深さに依存せずQが従う。
さらにz長≤32ならE-383がその深さ条件を供給する。
この結論はCOMPUTEDの有限木分類に依存するため、PROVED-LEANへ昇格させない。
またa_z≤3を外していない。次の一様な深さ入力が通っても、一般Qにはa_z≥4の場合が残る。
