# 深さ6の二つの実sourceと面積

E683 PROVED-LEANは元padded BlockWord後の全run/全長/正不足/全途中深さ6/最後6S/元actual targetでfree>=7。E685 PROVED-LEANは同じ深さ6/最後5S/選択旧source枝のfree>=6。人間レビュー未。C1全体・一般深さ・全射性は未証明。

## なぜ二つの窓を見るか

足し算が過去の数に支えられることを、この研究では歩いた高さと面積が決まった条件を満たす窓として扱う。元の履歴を最後まで残し、供給済みの足し算と空きを実際に数える。高い場所まで登るには、ある足し算が空きであるか、さらに前の窓に支えられる必要がある。

j6反例なら高い場所に空きが無い。最も高い所へ登る足し算にも実窓が必要だが、その窓は面積の残りからSAAという三歩に限られる。SAAの最初のAにも別の実窓が必要になる。この内窓は最後がSで、既存mod4と短窓分類から最低七歩。高い所に七歩の面積を支払うと、元履歴の面積予算は90<=80という矛盾になる。

j5旧source反例なら高い空きは一件まで。選んだ旧sourceの面積を残すと、各高い実窓には d*(k−1)+5H<=10 という同じ予算が付く。d>=2の窓は全て三歩になり、d<=5、2d+5H<=10。外SAAの最初Aを支える内SAAは、同じ時刻をAとSの両方にしなければならない。これで旧source枝が閉じる。

## 正確な依存

E678 cut二像、E679旧head5、E680最初A時計、E681全高internal-window面積、E682元高SAA、E683元j6 fullgap。E684元旧j5の正確面積とsource期間、E685全高SAA分類と旧j5 fullgap。SFinalWindowLengthは既存mod4/Win3の接着helperで独立coverageを数えない。r3 checked countへの既存依存は維持する。

旧/局所source別monolith H06、共通anchor H07/R、旧j5接着H16はSTOPPED。E683/E685はそれらの未受理bytesを使わず、新しいactual高sourceのstrict削減後のbytesで同512MB個別受理した。H04/R、H21/R、H22/Rも停止・隔離。一般5F輸送やfree1→A1をLeanで完了したとは書かない。

## 次の未知辺

j5局所source以前は、平方36とW+5H<=44から重み+5Hが8以下。二つの先行空きがあると、両方低いなら5+5、片方高いなら低重み5と高罰5、両方高いならH<=1に反する。三場合の小さい完全symbolic certificateを次のunitとする。source以前を新BlockWordへresetしない。j4、一般深さ、高さ別重みから無重みfreeへの共通償却は残る。

CPU探索workerは未起動/予算0。個別Leanは-j1/-M512、10CPU秒per-process、20wall秒。tree累積capではない。全検証receiptとfrozen source、当日journalはdocs/data/depth_six_20261112とdocs/data/daily_research/2026-11-12.json。

06:46更新: 二free位置の小complete certificateはH23、元clock16はH24で受理しE686へ。r3表を再生成せず、既存all-prefix count theoremを適用した。全graph one-free projection H25はrecursion cap STOPPED、clock2/4は未Leanで保持。

## 07:11 old-j4と全j old-source

E694 PROVED-LEANで旧j4も閉じた。E690はH<=1と2E2+H<=4を共同消費してW+8H<=36へ強める。ここから初期SSを内部供給し、切断せず元n+2の面積anchorで源予算d*(k−1)+8H<=9。高free>=1を排除しH0、残るk3/k7は同clockのS/A衝突又は予算9と矛盾。source=nのk7は小五符号certificateで初期SSと衝突する。H30/H32停止monolithは依存しない。

E683/E685/E694を合成した元深さ6・全j・全旧source・全run fullgapもLean受理。sourceを仮定化したadapterではなく、各実旧sourceに対する全長結果。ただし一般深さ/C1は未解決。残るj4/5は局所source。


## 最終局所source剪定 (07:38, E695–700)

j4局所source前も元free<=1 (E695)。初期Sだけの弱化prefix modelで元free1なら元A1 (E696)。したがってj4/5局所source時計はn+2又n+4 (E697)。n+4では四prefix SASS/SSAS/SSSA、全source-relative area<=4、高freeを唯一の一件として消費 (E698)。以後の全高Aはactual supplier。高sourceの同元窓budgetはd*(k−1)<=11なので全てSAA (E699)。最高上昇Aとその直前Aは両方actual、二つのSAAは同時計でSとAを要求して衝突 (E700)。これらは元履歴を切らない全run/上昇無制限の定理、人間レビュー未。

## E701 PROVED-PAPER: gap-five source at n+2

**全量化子**: 任意 f:Nat→Bool, n,a,b:Nat, w:List Bool。BlockWord w, seg f 0 n=w++replicate a true, n<b。全n<=i<=bでFw n−6<=Fw i。全0<k<=b−nで cN(EndN f 0)n k+1<=cN(S)n k。全b<=i<b+5でf i=S、EndN f 0(b+5)。結論は元cN(Aかつ非EndN0)n(b−n)>=6。全旧履歴/他source massは任意。証明はcounter free<=5を仮定し以下で排除する。source n+2を全体の入力として仮定しない。

1. E666/E668/E683でj5 counterのtarget高さはFn−1。選んだactual finalsourceが旧ならE685、局所ならE697でn+2/n+4。n+4はE700。actual source tは必ずt<b（t>=bなら最後の全S窓がrise1に反する）。従って未排除sourceはn+2、Winのrise1からFw(n+2)=Fn−2=:r。初期Sと二手の高さ差−2から初期SS。全source-relative area(n+2→b+5)=0、bの高さはr+6、最後5Sのarea=15。従ってarea(n+2→b)=−15。元n→n+2にはAがなくweight0なのでW_after=W。
2. 任意の元actual高A q<bで Fw q=r+d+1,d>=3をとる。実窓source uは高さr+d。旧sourceは元padded BlockWordの旧高さ<=Fn=r+2に反し、u=n,n+1も初期SSの高さに反する。従ってu>=n+2。E681内部窓area式を元clock n+2で使用する（BlockWordへresetしていない、式自体は全sign windowに成立）。三角形差は40+2d(k−1)、右辺は2W−30。よって d(k−1)<=W−35。E686で使う元W+5H<=44より **d(k−1)+5H<=9**。ここHは元全区間の高さ>=Fn−4のfree件数、E670でH<=1。
3. bはr+6にあるので、b以前にA at r+5 (q)があり、その前にA at r+4 (z)がある。qがfreeならH>=1。二つ目の高freeは不可能なのでzはactual。zのsource d3とWin長>=3から6+5H<=9となり矛盾。従ってqはactual。
4. qのsource d4なら4(k−1)+5H<=9。Win長は3又は>=7 (既存mod4/SAA分類)なのでk3かつH0。窓SAAの直前A q−1は高さr+4で、H0ゆえactual。そのsource d3も3(k−1)<=9からk<=4、従ってk3。outer source u=q−3はS、inner source v=q−4はv+1=uをAと要求し矛盾。
5. 旧/局所2/4を尽くしたので元gap5全actualsource fullgap。これをE683とE694/E700/E697に合成すると、深さ6counterの未解決はgap4/源n+2だけ。ただしこのE701接着全体は未Lean、人間レビュー未。

**反証pass**: d2はstep2に含めず、gap4へ誤適用しない。n/n+1 sourceを高さで排除してからanchorを使う。H1ならd3/k3でも11>9、H0/d4/k3は8<=9で単体では残り、二実sourceを同時に使う必要がある。k7/d3は18>9、境界u=n+2を許す。源前の旧履歴は一切捨てない。実orbit到達性、一般深さ/C1/全射性は主張しない。新CPU探索は実行せず、小境界はこの完全な整数場合と既存Win分類で攻撃した。

**Lean義務**: source n+2の実area anchor→d>=3 duration+5H<=9をproducerとして先に検証、次いで最高二Aのactual抽出・符号衝突。E701の結論やH0、bandを入力するadapterは受入にしない。H49/Rは別のcoverage consumerでunused shadowed binderを監査で発見し採用外。追加修理をしない。
