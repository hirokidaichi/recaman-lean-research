# 2026-11-09 source時計と元actual freeの課金

結論。E612は最外単一AS layerの時計増分を元最初A-run実freeへ限定課金。E613は一定倍率時計packingの反証（全l族・元zero/fullpositive輸送をLean検査）。E614はraw a²>=8i。E615は任意mixed prefixの4i+1<=A²、時計両順序を保つr3 actual source半径と非空例。E617は全run forward sourceが元prefix freeを少なくとも2必要とすること。E618は非負future keyによる全old源排除とSAAS後の最初Aがfreeというproducer。一般C1/rank/全射性は未証明、人間レビュー未。

## E612 / E613 / E614: 単一AS layer

任意mixed uとA^a S^b uがprimitive key=-2で、mass+固有clock=1をそれぞれi/jで満たす。b>=1。F=cntF u、d=j-i。既存primitive奇数性とkey比較からa<b、d>=2、a>=d+2、a²=d²+2dF。元BlockWord旧履歴の直後S^h A^aを持つ同actual historyでは既存single_A_run_free_budgetがa<=firstFree+2を与え、d<=firstFree。uは任意run数だが内側layer前のprefixをBlockWordへresetしてはならない。

E613の全l族。l>=1、u=S A^(2l²) S^(4l²-2)。F=4l²-1/key=-2/mass=1-2l²。A^(4l) S^(4l+2)uもprimitive、時計i=2l²/j=i+2。任意NでN*j<(N+1)*iとなる同word族をkernel構成。初期S paddingを既存定理で付けると元Nat0/空旧BlockWord/zero/fullpositiveと同final Aの両EndNも共存する。free不足や正末尾gapは課さずC1反例ではない。source clockに一定倍率成長を課す無条件案はREFUTED。

E614。標準AS pair上界からprimitive F>=3なら2i<=F+1。F1/u=Sのi2は例外で、単一非自明AS layerが存在すればF>=3を内部導出できる。a²=d²+2dF/d>=2からa²>=4+4F>=8i。上の全l族はa²=8iで係数sharp。firstFree平方への紙上帰結は正しいが、H43追加接着は一回修理後STOPPEDで未採用、PROVED-LEANへ昇格しない。

## E615: 任意mixed prefix / 時計両順序

p,uが同じ元futureのprimitive suffixでi!=j。A=ones p/B=cntF p。i<jならd=j-i>0、massp=-d、keyp=4dF。cross上界からA²>=d²+2dF、prefix S数偶数からA>=d+2。F1はi<=2/A>=3で処理、F>=3はprimitive clock半S上界を使う。d1ではA奇平方のmod8切上げ、d>=2ではA²>=4+4Fにより4i+1<=A²。

j<iならC=i-j>=1、keyp=-4CF。key下界からB²>=2CF、A=B+C、B正偶数。F1又はF>=3に分け同じ4i+1<=A²を得る。p=S2 A4/u=Sはi2/j0で開始順とclock順が逆になる。単一ASの差2や係数8を一般pへ外挿しない。

元Nat0/BlockWord境界nからp=seg f n Kを実prefixとして保ち、relative strictpositiveと実free r<=3を持つなら既存r3 checked countからA<=2r+1。従ってi<=r(r+1)<=12、advance側はA>=j-i+2からj<=17、decrease側もj<iで上界内。同fullprefixとlastA実符号から両EndNも内部供給。free3/strictpositiveの非空例 f=finiteSign(S2 A4 S1)、p=S2 A4/i2/j0をkernel監査した。これは新しいsource必要条件であり、r3全体のcoverageを再計上しない。より高free rankや他source開始境界は未供給。

## E616 PROVED-PAPER: 時間順の全run key予算

全f/Nat0/全n,K。全正prefix k<=KでE(k)+1<=S(k)。A/E/Sは同じ元actual A/EndN/S count、r=A-E。Wは各A時計でそれ以前のS個数の和。Jは各free A以前のEndN個数の和。Zは各A時計で S_before-E_current-1 の和。strictpositiveからZ>=0、J>=0。各供給AのE_currentは1..E、free AのE_current総和がJなので

W=A+E(E+1)/2+J+Z。

標準AS/SA pair補集合恒等式 key(p)=4AS-2S²-4W より

key(p)+2S²+4A+2E(E+1)+4J+4Z=4AS。

従ってJを保持したkey上界も全runで成立。証明は有限history検索ではなく、各Aのstrict deficitを足し合わせた全長算術。old supplierはEndN f0のまま全て数える。J=0/Z=0を常に仮定しない。SAAAではweak E<=SだけならW3/A3/E1で不等式が失敗しstrict +1が必要。SAAはE0/J0/Z0の等号。

同primitive p++u/u、clock i<j、d=j-i、F=cntF uではmassp=-d/keyp=4dF/S=A+d。代入して

d²+2dF+2J+2Z=A(2r-3)-r(r-1)。

r>=4ではAに依存する項が残る。これをfreeのみの一様予算やC1全体の証明と呼ばない。H49 saWeight proofは一修理後zero基底未閉鎖、H50新J/potential proofは一修理後S-stepのlist同一視未閉鎖でSTOPPED。両sourceはpacketだけ、root/Audit未採用。紙上の上式をLean受理済みと呼ばない。

## E617 / E618: kernelで供給した新consumer

E617は上のweighted未Lean式を入力しない。free<=1を反証仮定に既存r3 A<=3を内部供給し、新mixed prefix費用からA3/d1/S4/長さ7へ。strictpositiveは先頭Sを強制。全64word certificateで正keyはS A3 S3のみ。第三AがSAAのP2で元EndNとなり、prefix4のS1に対しEndN+1>=2となって矛盾。元free>=2を全run数/任意future u/全old履歴で供給する。元fullprefix/lastA条件を明記するが、それらはfree不等式のproof本体では使用しない。実sourceの関連付けの適用範囲として保持し、無条件orbit主張にしない。

E618。任意BlockWord wの実old suffix zは既存suffix閉性でBlockWord、C=massz>=1/keyz>=-2。任意mixed future xでkeyx>=0なら、F_x>=1ではkey(zx)>=-2+4C F_x>=2。F_x0ならmassx>=0とsource mass条件がC1を強制しz=[A]/key0となるため同様に不可能。全old sourceが消える。x=S A2 Sならlocal clock0も無供給なので元actual次Aはfree。clock2 localは存在するcontrolを検査し、次A一本から全A-run freeへ誤昇格しない。

## E619 PROVED-PAPER: forward sourceは実free>=3

E617でr0/1は排除済み。r2なら既存r3でA<=5。E616の完全式とd>=1/F>=1/J,Z>=0から lhs>=3、rhs<=A-2<=3。従ってA5/d1/F1/J0/Z0が必要。E=A-r=3。J0なら全free Aが全EndNより前、Z0なら各Aの直前S数はE_current+1。最初2AはfreeでS_before1なのでprefixはS A2。第三Aは供給でなければならず、その直前S_before2なので次のprefixはS A2 S。E618は同じ元旧BlockWordを保持したままその次Aをfreeとするので矛盾。r2も排除されfree>=3。

このproofは紙上で完全だが、時間順producer（source/free2からJ0/Z0を内部導出）が未kernel。E616を未証明Prop入力するadapterを進捗にしない。H49/H50旧sourceは再実行せず、source-conditioned temporal pruning又は小さい完全certificateと同512MB測定改善を必要とする。forward free3の実例/最適性は未供給、C1全体ではない。
