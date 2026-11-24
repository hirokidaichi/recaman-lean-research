# 全old stock損失を保ったまま、任意の有限A前史を付ける

**PROVED-PAPER、未Lean・人間レビュー未。** 旧E774の最強四filter付きstock損失counterについて、表示seed自体は一歩前を持たない。しかし全old stockを保存して必要な訪問/blockerを追加すると、任意の固定長Lのgreedy前史を実行でき、四つの数値filterと同じ二次stock損失を保てる。前史分の元freeも数える。これはcanonical前史を構成したのではない。固定深さ2の応用であり、この結果だけでdepth-general停滞をresetしない。

## 1. 完全なdistinct seen集合の一歩前と、旧表示seedの限界

ここでVはseenの**全distinct値集合**であり、ordered listの順序や重複度ではない。逆条件は更新後のdistinct集合がVとなるcoherentな前Stateの存在を述べ、固定されたseen listそのものの逆像を主張しない。forward producerはVplusを有限listとして全て初期化し、通常updateで値を記録する。prefix Aで重複が増えてもdistinct件数は変わらず、old値は全て保持される。

時刻a>=1、current Iが全distinct seen Vに属する有限Stateについて、更新後のseenが**正確にV**となるcoherent predecessorは次で尽くされる。

    preceding A iff I>=a, I-a in V,
                    and [I-2a<=0 or I-2a in V].
    preceding S iff I>0 and I+a in V.

Aなら直前currentはI-aで、拒否候補はI-2a。前seenをVのままとすれば十分であり、必要性は直前current/candidateがupdate後Vに残ることによる。Sなら直前currentはI+a、前seen=V without Iとすれば正のIへ新規着地できる。a>0なのでI+aは削除されない。他の前seenはVかV without I以外に無く、全old値の欠落を許していない。これは旧E752の個別predecessor監査で使った必要性を整理したもので、このlemma単独を新一般化進展には数えない。

E774の元表示seedでa=b-2、I=x+2b-1とする。I-a=x+b+1はC3=x+bとcurrent Iの間で、C_jの列にも他のseedにも無い。I+a=x+3b-3はC4=x+2b+2とC5=x+3b+5の間（b>5）で、他のseedはさらに低い。したがって**元の表示seed**はcoherentな一歩前を持たない。E774のsign語自体や、同じstock損失を持つ別seedが到達不能だとは言えない。

## 2. 新しい全(L,k)のtransport

任意L>=0と、k=20n+15>=max(15,L)を取る。旧族のl,b,a,gapは保ち、currentのtranslationだけを大きくする。

    l=3k, b=5k^2-k-2, a=b-2,
    x=(10L+90)k^2, I=x+2b-1,
    gap=4k^2-5k+1, y=x-gap,
    C_j=x+(j-2)b+j(j-3)/2.

旧E774の**全seed**を

    V0={0,I} union {C_j:1<=j<=l,j!=3}
          union {x-l^2-b-2l-1,x-l^2-1}
          union [y,x-1]

とする。xの増加はすべての正値/差のcollision証明を保存する。各j>=0で

    p_j=I-ja+j(j-1)/2,
    c_j=p_(j+1)-1

を置き、全prehistory stockを

    Vplus=V0 union {p_j:1<=j<=L} union {c_j:1<=j<=L}

とする。初期化する**実際の開始時刻**はa-L、currentはp_L。V0のどの値も消さない。

時刻a-jのp_jからp_(j-1)へ進むAの歩幅はa-j+1、拒否候補はc_j。これらはすべてVplusにあり正なので、前史A^Lが正確に強制される。c_jと全p_jを初めから保持し、未来のA訪問がseenを消したり減らしたりすることはない。k>=Lよりa-L>=4k^2>0。a<=5k^2とIの式からp_Lおよび最小のc_Lも正である。

## 3. 追加した全old値はSを妨げない

具体的に

    p1=x+b+1, p2=x+4, c1=x+3,
    p3=x-b+8, c2=x-b+7, p4=x-2b+13.

必要なjだけをseedへ入れる。jが増えるとp_jは単調減少し、j>=4の全追加値はp4以下（c_jは対応する次のpよりさらに1小さい）。

旧counterのhead S landingsはx+b,x。core S landingsは単調なY_d（0<=d<l）で、

    Y_d=x+db-d(d-1)/2+l(2d-l),
    Y0=x-l^2, Y1=y-1,
    Y2-x=k^2+10k-5, Y3-x=6k^2+15k-9.

直接差を取るとk>=15で、

    p1 in(Y2,Y3),
    x+3,x+4 in(x,Y2),
    p3,c2 in(Y0,Y1),
    p4<Y0.

例としてp1-Y2=4k^2-11k+4>0、Y3-p1=k^2+16k-8>0、Y1-p3=k^2+4k-12>0、p4-Y0=-k^2+2k+17<0。他の差も明示式から同様。従って**追加した全値**はhead/coreのすべてのS landingを避ける。旧V0の全S新規性は旧E774の完全producerで既知なので、Vplusを丸ごと保持したまま

    A^L SS A^l S^l AA

の正確なgreedy実行が得られる。前史seedを途中で別のStateへ取り替えていない。

追加値はすべてxより大きいか、yより小さい。cut時current xのold在庫と、次cut時current yのold在庫に、追加された低値は同じ個数だけ寄与する。重複があれば両方で同じように除かれる。新S出力は変わらないので、旧E774のstock損失

    Kold-Knext=gap-2=4k^2-5k-1

がそのまま残る。seed件数を元free数へ同一視していない。

## 4. 四filterを、前史の開始clockで払う

旧V0の正確な件数N0=4k^2-2k+3、s0=N0-1を使う。追加値は高々2L個だから

    |Vplus|<=N0+2L <=a-L+1,

最後の余裕はk^2+k-6-3L>=k^2-2k-6>0。current p_Lのparityは、元Iの正しいtriangular parityからL回のA歩幅を引くことで、upperTri(a-L)と一致する。

全追加値はI以下、旧高seedの最大C_lは

    <=15k^3+(10L+82)k^2 <=25k^3+82k^2
    <=8k^4 <=upperTri(a-L).

ここではa-L>=4k^2とk>=15を使った。全seed/全p_j/c_jが非負であることは上で支払った。

s=|Vplus|-1はs0以上でs<=a-L。s(2(a-L)-s+1)はこの範囲で非減少。さらに

    2(a-L)-s0+1=6k^2-9-2L>=5k^2,
    s0>=3k^2,
    upperTri(a-L)<=upperTri(a)<=13k^4.

従ってsorted clock-cover右辺はcurrentを除いても15k^4以上で、必要な13k^4を払う。四filterは**元counterの時刻aだけでなく、付加A前史より前の実初期化clock a-L**で通る。

補足：これら四scalar条件はcoherent greedy stepに対して前方保存される。seen件数は一歩で高々1増え、range/cardinality/parityは直接保存される。sorted余裕D=x+s(2u-s+1)-upperTri(u)の増分は、新規Sで0、既訪問Aで2s、新規Aで2(u+1)。従って前史・counterを実行する途中で同じ四条件を再検査しても失敗しない。これは支払いの補助恒等式であり、それ単独を新進展として追加計上しない。

## 5. 元signの前史とfreeを捨てない

完全な元語はA^L SS A^l S^l AAである。最初のA^Lはすべて元free。tailのascent targetがこのA-prefixをsourceにできるのは最初の三Aだけで、mass1から必要な旧A長は3,2,1。対応する窓AAA SS、AA SS A、A SS AAの面積は9,5,1で、すべて非零。tail最後のAAへの旧A-prefix source候補の面積も、それぞれl^2+2l+9、l^2+5で正。よってA-prefixから新たなactual供給は加わらない。

旧E774内部sourceは保持され、全原点0の元actualはtail第三A、sourceはtail第二Sだけ。従って

    E_whole=1,
    F_whole=L+l+1, F_tail=l+1,
    K_whole_classes<=F_whole<=4k+1.

tail以後の元正不足・return・LOW4/head2は、全old A-prefix sourcesを調べた後に保たれる。A-prefix開始からの全prefixが厳密正不足とは言わない：A^L内部はS-E=0である。このA-prefixをpaddedなold A履歴として残し、tail開始n=Lからの条件と元EndN0を区別する。途中で原点をresetしていない。

固定Lについてkを増やせばstock loss/F_wholeは発散する。Lをk以下で増やす場合も同じ上界から発散する。したがって任意固定の有限greedy lookbehind、四つの指定scalar canonical filter、全old stock、前史の元freeを含めても、固定線形stock-loss支払いは救済できない。未知のcanonical以前の真の符号履歴や、一本の無限過去を構成したのではない。

## 6. 反証passと次の決定

STOCK_LOOKBEHIND_PROTOCOLを前に固定。discoveryはtiny coherent Stateの576個について、全可能な前seen/currentの独立列挙と逆条件を比較した。新prefix predicateはk15/L0,1,3,5、heldout parameter controlsはk35/L2,10,35。全old intervalを含むseedからのliteral greedy、全元source（後者はreverse加重和）、四filter、両cut在庫が一致した。k15のstock loss824、k35の4724はLを増やしても不変。有限controlsはCOMPUTED、全(L,k)は上の完全PAPER証明による。旧family自体をfresh canonical holdoutとは呼ばない。

各workerは1CPU/10wall/単一cooperative Pythonで完了、修理0、範囲拡大なし。旧finite-State/source jobを資源追加で再開していない。新Lean/root/Audit採用0。

判断：元表示seedの前史欠落だけを理由に、旧stock-loss no-goの数学的結論を取り消さない。必要なblockerを払えば、その欠落を任意有限Lだけ後ろへ移せる。次に必要なのは、全実行済み前史を時刻0まで結ぶ条件、または元LOWfree/classへの新しい非線形会計である。有限lookbehindの長さを増やすだけ、四filterを未来で繰り返すだけの方法は停止する。C1そのものは未証明のまま。
