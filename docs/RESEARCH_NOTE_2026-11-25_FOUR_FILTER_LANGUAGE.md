# 四つの数値必要条件は、coherent有限語のlanguageを狭めない

**PROVED-PAPER、未Lean・人間レビュー未。** 任意の有限sign語w（空語を含む）について、次は同値である。

1. wはE759の完全なI/II chronology条件を満たす。
2. wを実行するcoherent有限Stateが存在し、そのbase b、current x、**全initial seen集合V**が次の四つの明示的数値条件をすべて満たす。

    |V|<=b+1,
    x congruent upperTri(b) modulo2,
    every v in V is in[0,upperTri(b)],
    upperTri(b)<=x+s(2b-s+1), s=|V|-1.                 (4)

従って、この四条件だけをcoherent有限語の排除filterとして追加しても、**どの有限語も新しく排除できない**。実際のcanonical前史、元過去符号、全clockでのgreedy履歴を与えたのではない。条件(4)をcanonical到達の十分条件へ変更しない。E759/E766の旧一般定理やE774の個別族を再登録したのではなく、今回は全有限語を通す完全なseed増補producerを得た。

## 原点・供給・全seedを固定した構成

Q=length(w)、N=Q+1>=1、wの元原点0の高さ/面積をH,Bとし、全元Win sourcesを保持する。元free A qのaffine candidate pairを

    (h_q,k_q)=(H(q)-1,(q+1)(H(q)-1)-B(q))

とする。重複を除いたpair集合をP、K=|P|とする。K<=Q=N-1であり、FやLOWfree数へ置換しない。次の具体値を使う。

    b=1000N^2,
    x=100(b+N)N,
    L=b/2-K-1,
    V=[0,L] union {x} union {x+b*h+k : (h,k) in P}.      (S)

低い連続区間も含む**全V**が初めからseenにあり、消したり後から必要な物だけ足したりしない。current xはVに属す。Vは有限で、範囲と有限pair集合によって完全に記述されている。

## 正値・分離・triangular rangeの完全な支払い

任意output pair O_i=(H(i),(i+1)H(i)-B(i))、任意A候補pairは、|h|<=N、|k|<=2N^2を満たす。これは|H(i)|<=Q、|B(i)|<=Q(Q+1)/2から直接従う。従ってすべてのprescribed出力と候補は

    x-bN-2N^2 =99bN+98N^2 > b,
    x+bN+2N^2 =101bN+102N^2

の間にある。b>4N^2なので、異なる整数slopeの値が一致すれば必要なbaseは高々4N^2となることに反し、異slope等値は無い。同slope・異interceptも当然異なる。よって異なるnormalized pairは異なる数値を持つ。

元free候補pairがcurrentの(0,0)と一致すれば、q>0では元Win(0,q)そのものになり、元free性に反する。q0ではcandidate slope=-1なので一致しない。従って高いseedは正確にK+1個で、すべてbより大きい。

N>=1に対しL>=500N^2-N>=0、L<b/2。従って低区間と高いseedは交わらず、

    |V|=(L+1)+(K+1)=b/2+1.                            (C)

また

    (101bN+102N^2)/b=101N+102/1000
        <=500N^2+1/2=(b+1)/2.

最後の不等式はN1で成立し、Nを増やすと差が増える。よって**すべてのseed値とcurrent**がupperTri(b)以下。単にcurrentだけのrangeを検査していない。

## 全S新規性を保ったgreedy実行

E766の旧generic-base構成より、b>4N^2で全候補が正、I/IIが無ければ、高いseed {x} union候補だけで元wを正確に実行できる。この旧証明はすべてのfuture-free候補までseenに入れ、全old output/earlier blocker/未来候補とS landingとの等値を排除する。ここでI/IIを結論同然の新Propへ包装したのではなく、任意wに対するlanguageの入力条件として明示している。

今回追加したのは低区間[0,L]。すべてのprescribed S landingはbより大きく、L<b/2なので、この全区間のどの値にも一致しない。既存Aの理由はseen増補で失われず、各Sの新規性も保持される。従って全seed(S)からの直接帰納で同じwのexact greedy continuationを得る。初期stockを途中で捨てる輸送ではない。

逆方向は、coherent有限Stateのgreedy実行なら旧E759の必要性からI/IIを満たす、というだけである。四条件が自動的にwをcoherentにするとは言っていない。

## 四条件を一つずつ確認

(C)から|V|=b/2+1<=b+1。bは4の倍数でupperTri(b)は偶数、xも100の倍数なのでparityが一致する。rangeは全seedについて上で支払った。最後にs=b/2なので

    x+s(2b-s+1)-upperTri(b)=x+b^2/4>0.

これはE755由来の指定されたsorted clock-cover必要不等式そのもの。別のより強いprefix matching条件を通過したとは言わない。low fillerの個数はbaseに比例して増え、旧の小さすぎるgeneric seedがglobal clock費用を払えない問題を、全seedを明示的に増やして解消している。小stockのまま結論を仮定していない。

空語Q0/N1/K0でも、b1000、x100100、L499、|V|501で同じ式が成立し、空replayはcoherentである。Q1も同じ証明が扱う。有限語によってseedを変えているので、一本の無限wordを一つの有限Stateが実現するという主張ではない。

## 反証passと証拠の境界

FOUR_FILTER_PROTOCOL.jsonでsource/card/argv hash・範囲・1CPU/10wallを実行前に固定した。discoveryは全63語（長さ0..5）をforward元source/prefix-areaで評価し、I/IIを満たす58語は全seedで成功、残る5語はchronology衝突によりreplay失敗。四つの数値条件自体は全63語で通った。bad chronologyを四条件で救済していない。

holdoutは未使用の全長さ6/7語とW_n n1/3/7。元sourceはreverse mass/加重面積、chronologyは直接の区間高さ和で別に照合し、全seed replayと四条件が理論どおり一致した。正確な大きい有限seedは[0,L]と高い有限点集合で表現し、全区間membershipを検査しており、数百万個の列挙やseedの一部省略ではない。有限結果はCOMPUTED、任意長・任意深さの主張は上の全word証明に置く。修理0、上限・範囲拡大なし。

この定理は必要条件(4)の有限語選別能力のno-goである。数値stockの真の符号前史、canonical実現、LOW classのdepth/span支払い、C1/Q/H/SL/全射性は未供給。次は「少なくとも一歩のcoherent前史がある」という、(4)に含まれない条件が有限語languageを狭めるかを、元source/全old候補を残して判定する。
