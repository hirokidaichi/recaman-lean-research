# stage容量の鋭い族は、全S新規性も保持する

**PROVED-PAPER、未Lean・人間レビュー未。** E776の全nの等号族

    W_n=S^(2n+2)(ASAA)^n A S^(2n+1)AA, n>=1

は、coherent有限Stateからの実greedy continuationとして実行できる。全future-free候補を最初からseenへ入れても、すべてのSが正かつ新規である。これによりE776の係数3/2と境界は、raw signだけでなくこの有限数値実行のclassでも鋭い。標準orbit/canonical前史は構成していない。E759の一般seed構成を新成果として再登録せず、今回の新入力はこの全n語の**完全なS chronology除外**である。

## 全量化子と使う旧入力

任意n>=1、m=2n+2、Q=8n+6、H/BはW_nの元原点0からの高さ/面積とする。E776の元ALL-source分類からA=3n+3、元actual E=n、ALLfree F=2n+3、exclusive-head O_c=0、全tail positive/return2-mが得られる。FはLOWfreeやcanonicalの全過去freeではない。

旧E759によれば、次の二種類の恒等衝突が無い有限語は、currentがseenに属する有限Stateから正確に実行できる。

    I: S landing vと任意prior output u<vについて
       H(u)=H(v), B(v)-B(u)=(v-u)H(v).
    II: S landing vと任意prior A clock q<vについて
       H(q)-1=H(v), B(v)-B(q)=(v-q)H(v).

以下ではこれらを結論と同値な新Prop入力にせず、W_nの全source-height候補を尽くして内部供給する。全old出力、最初のcurrent、earlier Aの全blockerを保持する。

## 初期S-headと各cycle内のS

初期headの各Sは新しい低い高さへ下り、同高のprior outputもprior Aも無い。

head後の床を相対0とする。cycle i（0<=i<n）の内部Sは相対高さ2iへ着地する。同高のprior outputは、head clock u=m-2iとcycle境界w=m+4iだけ。i=0では両clockが同じである。境界からこの着地へのAS面積は1。head sourceからの面積は、初期Sの三角形とi個のASAA、最後ASを直接足して

    1-6i^2-i.

i0では1、i>=1では負であり0でない。よってIを満たす衝突はない。IIに必要なearlier A始点の相対高さは2i+1だが、これまでのA始点は高々2i。したがってIIの候補自体が無い。

## 最終下降の全S

最後の長いS-runは相対2n+1から0まで下る。着地高さを任意の整数k in[0,2n]とする。

同高のhead clockはu=m-k。そこから着地までの相対面積は

    C_n-(6n+2)k, C_n=6n^2+3n+1.

計算：ascent (ASAA)^n Aの床相対面積は4n^2+2n+1。頭の残りS^kの面積と、下降の上三角差を足すと床相対の総和はC_n、窓長は6n+2となる。この面積が0となる実kは

    n+(n+1)/(6n+2),

で、nとn+1の間に厳密にある。従って整数kでは0でない。

head以外の同高prior ascent outputから先は、以後の床が上がっていくため、通常は着地まで高さがsource以上で、途中に厳密に上の点があり面積は正。ただ一つの例外形は、cycle iの最初のA後の山頂（高さ2i+1）で、直後Sだけsourceより一段低くなる。その山頂と同高の最終下降着地を考え、r=n-i>=1と置く。残るSAAの面積0、以後のcycleの面積4r(r-1)、最後Aの面積2r、下降の面積r(2r-1)から、窓面積は

    3r(2r-1)>=3.

したがってこの例外もIの0面積衝突を作らない。これで同高のprior outputsを尽くした。

IIに合うearlier Aの始点高さはk+1。そのA以後のascentは高さk+1を下回らず、最終下降もこのS着地まではkを下回らない。最初のA出力はk+2で正の余剰を持つので、source水準kから測った面積は厳密に正。最後AAはすべてのSより後なのでearlier Aに含まれない。従ってIIも全て排除された。

これは有限nの不在からの外挿ではなく、全nの全S phase、全prior output/earlier blockerの分類である。

## 完全seenからのactual continuation

N=Q+1、b=100N^2、x=100(b+Q+1)Nを取り、元ALLfree A qの候補

    C_q=x+(b+q+1)(H(q)-1)-B(q)

を**すべて**最初のseenへ入れる。

    V={0,x} union {C_q : qは元free A}.

旧E759の定量constructorにより、全出力と候補は正で、異高度の等値は大きいbで分離される。同高度のprior output/earlier Aとの等値は、上で排除したI/IIそのもの。future-free候補との等値はその未来Aに元Winを与え、元free性に反する。この旧定理を消費して、Vを一つも削除せず全S freshnessと全A強制を得る。元actual Aは元Winのprior outputで、元free Aは初期Vで支えられる。

F=2n+3から|V|<=2n+5だが、seed数をfree数と同一視しない。有限検算ではcandidate classesもpair-distinctだったが、K=Fは今回の全nの主張に採用しない。

この表示seedは旧E759/E755のglobal clock-cover費用によりcanonicalではない。これはseedの不適合であって、W_nというsign語のcanonical非到達証明ではない。元segment freeをseed以前まで含むcanonical全freeへ輸送していない。

## 反証passと失敗の記録

staged_greedy_probe.pyの初回はsyntax-invalidで失敗した。事前hash保存helperもparseに失敗し、shellが次のworkerへ進んだため、**最初の失敗bytesのhashは事前固定できていない**。元カードにはn範囲・3CPU当日枠・1CPU/10wall契約を事前記載していたが、それをhash固定成功と呼ばない。失敗source/正確出力/receipt、測定CPU0.046653秒を保存した。helper自身のCPUは未計測で0にしない。

唯一の実装修理でelse1構文を直し、事前提案外だった補助K=F assertを除いて観察値に戻した。範囲・cap・主命題は不変。修正版のsource/card/argv hashをSTAGED_GREEDY_PROTOCOL.jsonに保存した**後**、discovery n1..5と未使用parameter holdout n7/11/17/23を実行した。後者はreverse literal mass/areaで全元supplierを照合。全I/II pair、全phase面積式、全future-free seedを保持するgreedy replayが一致した。修理後CPU0.033074/0.040245秒。これらはCOMPUTEDであり、上の全n証明とは別である。修理枠は使い切り、追加retryや範囲拡大はしない。

新Lean/root/Audit採用0、旧512MB/source/table停止を保持。次のconsumerは、四つの明示canonical必要数値条件が、このcoherent finite-word languageに追加の制限を本当に与えるかという監査である。条件通過をcanonical前史と同一視しない。
