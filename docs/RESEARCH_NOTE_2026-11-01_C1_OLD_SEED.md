# 2026-11-01: mass3 target/最終S4と実old seed

最終更新: E485はPROVED-LEAN。v4/old0はE490、old1はE499/E500の独立source平方比較で供給、anyold分岐も元pでkernel済み。以下は早朝PAPERの履歴。

結論: **PROVED-PAPER（未Lean・人間レビュー未）**。
[H02カード](HYPOTHESIS_CARD_2026-11-01_FOUR_S_OLD_SEED.md)の元Intp/padded/zero-fullpositive、
全正三run zero-mass head、old targetmass3、最終S4、final-band local source、最後Aに実old供給がある枝は、
元full-tail実free>=j+1を満たす。全run/old prefix/未来長に上限を入力しない。
同じsource条件での最終S3は[E484紙上chain](RESEARCH_NOTE_2026-11-01_C1_MASS_THREE.md)。
四run全体/old供給のない枝/任意run数/C1は未解決。

## 共通のcounter縮約

記号はH01と同じ、zの全S=全A=S、B=-areaW z、R=j+1。
targetmass3と最終S4のmassからT=R+1。仮counter F<Rなら、実r3とfinal-bandのA下限からF>=4/R>=5。
全供給<=17と `F=S+T-E=S+R+1-E<R` から **S<=15**。

実old source clockをkとする。E441の同じ実target/old順序はk+j<Tを与えるのでk<2。
したがってk=0又は1。その同じ窓のmassからold suffix mass D=5-k。
これは他old massを入力で切ったのではなく、仮counter中の特定の実supplierについて内部導出したもの。
全old窓は同じprefixのclock一意性でこのkへ合流する。

## k=0 / D5

BlockWordのmass5語は最初のblockを除いて、A+mass4六語、SAAA+mass3三語、trip+Aに完全に分かれる。
それらのareaは順に

`15,20,18,16,21,20; 14,17,19; 14`。

従って14<=a5<=21。語の差や共同prefixを同一視する必要はなく、この上下界だけを使う。
二つの原始keyは

`B=10S+a5+10`, `R²=4S+8+a5-a3`, `a3∈{5,6,7}`。

正三runなのでB<=S²-6。B>=10S+24とS<=15を合わせるとS>=13。
S13ではR²∈[67,76]、S14では[71,80]で平方はない。
S15ではR=9、a5-a3=13。a3=5/6/7からa5=18/19/20。
zero-mass語のB≡Sからa5は奇数、従って

**S15/B179/R9/T10/a5=19/a3=6**。

初期Sからd個を除いたlocal sourceはd+i=5、0<=d<=5、
`B=2d(S+4)-d²-15`。
d=0..5でBは `-15, 2S-8, 4S-3, 6S, 8S+1, 10S`。
S15ではいずれもB179にならず、初期S源はない。
残るlocalはexact source分類の五方向、各方向高々一clockでlocal<=5。
oldは全massを含めclock0だけで全last供給<=6。
head実供給<=10よりheadfree>=15-10=5。
従ってfullfree>=5+10-6=9=R、仮counterに矛盾。

## k=1 / D4

原始keyは

`B=8S+a4+7`, `R²=2S+5+a4-a3`, `a4∈{9,10,11,12,13}`。

S<=15、B<=S²-6よりS>=11。R>=5と平方範囲からR=6。
B≡Sを同時に使うと必要条件は四組:

| S | B | a4 | a3 |
|---:|---:|---:|---:|
|12|116|13|6|
|13|121|10|5|
|13|123|12|7|
|14|128|9|6|

T=7。初期S源の上記六候補はいずれもこのBに一致せず、全local初期Sを排除する。
第一A源は同じmomentから

`(h-(5-i))²=B+15-2(5-i)(S+4)+(5-i)²`, `0<=i<7`。

各行について、i=0..6の右辺は次の通り。

|S,B|i0|i1|i2|i3|i4|i5|i6|
|---|---:|---:|---:|---:|---:|---:|---:|
|12,116|-4|19|44|71|100|131|164|
|13,121|-9|16|43|72|103|136|171|
|13,123|-7|18|45|74|105|138|173|
|14,128|-12|15|44|75|108|143|180|

平方が残るのはS12/B116/i4とS13/B121/i1だけ。
前者は **(h-1)²=100** なのでh=11（h>=1）。正のm,sからh<=S-2=10で矛盾。
後者はi=1なので、残しても既に実在するold clock1へ合流する。
よって第一Aの全local供給はclock1へ含まれる。

全last供給は `{1,2} ∪ C_secondS ∪ C_secondA ∪ C_thirdS` に含まれる。
各constant-run source familyは高々一clock、従ってlast実供給<=5。
head全A>=12なのでr3によりheadfree>=4を内部供給できる。
fullfree>=4+7-5=6=Rで仮counterに矛盾する。
これでk=0/1の両枝、従ってH02の同じ元pの全長結論を得る。

## 反証pass・実在性（COMPUTED）

追加2CPU秒（各worker1、wall3）の独立literalを実行前に固定。
discovery: old AASAAA、head(10,5,1,4,1,3)、v4/S12/B116/R6/T7/j5。
元zero/fullpositive最小1、old源0はclock1、target源3、最後local q1/clock2。
headfree9/fullfree13、last供給1/2/3。

holdout: old SAAAASAAA、head(13,10,1,3,1,2)、v4/S15/B179/R9/T10/j8。
元zero/fullpositive最小1、old源0はclock0、target源6、最後local q1/clock2。
headfree13/fullfree21、last供給0/2。

出力のlegacyキー`old0_sources`はdiscoveryではclock1を調べた結果であり、clock0を調べたという意味ではない。
実行sourceのold_iとargvを正本にし、packetのschema clarificationにも保存。
有限適用例であり全長証明や標準Recamán軌道到達可能性の根拠にはしない。

## 意味監査と残る形式化

平方表の列i4は(h-1)²、i1は(h-4)²である。表を書いた際の草案にh²=100と読む行が混入したが、
数式との独立照合で採用前に訂正した。S12例外はh11で排除でき、h10という入力へ変えてはいない。
S13/i1を実在する源と断定せず、必要上界としてold clock1へ含めるだけでよい。

全sourceの一clock性/old全mass一意性/元count加法を用い、独立tagやheadfreeの新Propを入力していない。
Lean実装/逐語statement audit/人間レビューは未完了。PAPERをkernel結果へ昇格しない。
