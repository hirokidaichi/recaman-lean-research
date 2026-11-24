# coherent有限語でも、coherentな一歩前を持たない

**REFUTED：すべてのcoherent-admissible有限語に、AかSのcoherent predecessorを付けられるという方法。** 以下の全量化子の構成はPROVED-PAPER、未Lean・人間レビュー未。四つの数値canonical必要条件を通す全seenを持つ有限実行であっても、**実行済みのcoherentな一歩前**があるとは限らない。

正のbase bで有限Stateを初期化することと、そのbaseまでの過去を構成することは別である。ここでの語は大きい正baseから実行できるので、「正のclockでは実行不能」とは言わない。不能なのは、既にcoherentだったStateから一歩実行した直後に、この語を開始することである。C1/正不足/初期S-domainの反例でも、全射性の結論でもない。

旧E752は特定の表示seedが前に延長できない例を扱った。今回は**どのbase/current/seedへ変えても同じ語のpredecessorが存在しない**というlanguage側の反証である。

## 1. 全有限語の一歩前の正確な判定

任意の元有限語wがE759 I/IIを満たすとする。H/Bは同じ原点0からの値。元S clock qについて、次が必要十分である。

    S++w がcoherent-admissibleでない
        iff some q has H(q)=2, B(q)=q+1.              (PS)

    A++w がcoherent-admissibleでない
        iff some q has [H(q)=0, B(q)=-q-1]
                    or [H(q)=-1, B(q)=-2q-2].       (PA)

証明：prependした符号をepsilon=+1/-1とすると、元clock tのshift後には

    H_g(1+t)=H_w(t)+epsilon,
    B_g(1+t)=B_w(t)+epsilon(t+1).

shiftした元output/元A同士のI/II等値はこの変換で保存され、元wがadmissibleなので新しい失敗ではない。追加output clock0からのIだけは別に検査する。S-prependなら、元S landingの高さが1（従って元preheight2）で、shift後B=B_w(q)-q-1=0が必要十分。(PS)を得る。

A-prependのclock0 Iでは元S preheight0、shift後B=B_w(q)+q+1=0。さらに新head A clock0のcandidate高さ-1を使うIIでは元S preheight-1、shift後の等式はB_w(q)+2q+2=0。これで(PA)の二場合を得る。prepend直後の最初の一手自体にS loopは無く、他の新prior output/A clockも無い。全old出力とearlier blockerを尽くしたので両方向が成立する。E759の旧必要十分定理をここで消費するが、predecessorの合法性自体を仮定してはいない。

同じことをoutput affine pair O_v=(H(v),(v+1)H(v)-B(v))で書くと、S landingに(1,0)があるとS-prepend不可、(-1,0)または(-2,0)があるとA-prepend不可である。これは既存E759の単なる再引用ではなく、新しい追加clockの全衝突を切り出した判定である。

## 2. 任意長・任意深さの反例族

任意の整数r>=6、r=0または1 modulo3について

    t=(r^2-4r-9)/3 >=1,
    w_r=AAS ++ S^r ++ A^r ++ (SA)^t ++ SS,
    Q=2r+2t+5.

とする。以下ではすべての元sourceと全earlier output/A候補を保持する。各語はE759 I/IIを満たすが、A/Sのどちらもprependできない。rとともに語長とminimum depthが増える。

### 完全なS chronology

最初のAASのS landingは高さ1/面積4/clock3で、output pair(1,0)。唯一の同高prior outputのinterceptは1、同じ高さのearlier A candidateは無いので衝突しない。

続くS^rでは、最初のlandingは高さ0/intercept-4。prior output高さ0のintercept0と、earlier A候補高さ0のintercept-1のどちらとも違う。第二landingは高さ-1/intercept-9で、earlier candidateの同高intercept-1とも違う。それ以下のlanding heightsにはprior outputもearlier A candidateも無い。ここで全initial下降Sを尽くした。

A^rの後は高さ1に戻り、面積は

    T0=4+2r-r^2.

その上昇中の高さ0 outputの面積はT0-1、従ってinterceptは1-T0。以後の(SA)^tの各Sと最後SSの第一Sはすべて高さ0へ着地し、面積はT0+j（0<=j<=t）。この区間全体が負である。実際

    T0+t=(3+2r-2r^2)/3<0.

それらのoutput interceptsは-T0-j>0で互いに異なり、上昇中の1-T0よりすべて小さい。他のprior高さ0 outputsのinterceptsは0,-4。earlier A candidate高さ0は初期第二Aのintercept-1だけである。従ってこれらのSにはI/II衝突がない。新しいAを一つずつ記録しても、その候補高さは-1なので高さ0のSをblockしない。

最後のSは高さ-1へ着地する。全語の高さ/面積は

    H(Q)=-1,
    B(Q)=3+2r-r^2+t=-(Q+1).

従って最後のoutput pairは(-1,0)。それ以前の高さ-1 output clocksは初期下降と後の上昇の二つだけで、そのinterceptsは

    -9, 3t+4.

earlier A candidateで高さ-1を持つものは、初期第一A、上昇の最後A、および各SAのAで尽くされ、そのinterceptsは

    -1, 3t+3, 3(t-j) (0<=j<t).

いずれも0でない。最後のSもI/IIを満たす。ここで単一supplierを選択して他を捨てたのではなく、candidate-heightが合うすべての時計を表で尽くした。

### 元actual source/freeの補助監査

初期の二Aは元free。A^r中のtargetの必要source高さはすべて0未満なので、古いAASのsourceは候補にならない。下降S部分と現在の単純上昇を比較すると、旧S source窓の面積0は第三AのSAAだけで、現在のA-run内sourceは一歩の面積1。したがって上昇中の元actual Aは第三Aだけ。

各SA-loop Aのcandidate pairは(-1,3(t-j))。既存output高さ-1のinterceptsは-9と3t+4で、どちらとも違い、その後SA-loopsは高さ-1へ出力しない。従って全SA-loop Aも元freeである。全語で元actual E=1、ALLfree F=r+t+1。これはC1の正不足/初期S仮定を満たすという主張ではない。

## 3. 完全seedで実行できても、どのseedからも一歩前へ延長できない

上の完全なI/II分類とE778の全seed増補producerにより、各w_rは四つの指定scalar filterを通すcoherent有限Stateからexact greedy実行できる。全initial seen区間と全future-free高候補を保持し、全Sが正かつ新規になる。元Fをseed以前のcanonical freeへ置換しない。

一方、S++w_rは必ず先頭SAASを持つ。この四手のmassとareaは0、最後はSなので、どのbase/currentでもそのSはcoherentな初期currentへ戻ろうとする。初期currentはseenにあるため新規Sになれない。

A++w_rは語全体のmassが0で、prepend公式よりarea=B_w(Q)+(Q+1)=0、最後はSである。従ってこちらも最後にcoherentな初期currentへ戻り、どのseedでも不可能。初期current0ならSの正値性自体にも反する。この否定は特定のgeneric seedが前に延ばせないというだけではない。

よって、coherent Stateから既に少なくとも一手実行した履歴の途中にw_rが出現することはない。直前一手がA/Sのどちらでも不可能だからである。ただし、正baseでw_rから**初期化して**実行することは上で構成済みで、baseが正というだけでは過去を意味しない。canonical初期0からの最初の三符号もAAAなので、AASで始まるw_rはcanonicalの開始位置0にも一致しない。これをC1や全射性の証明には使わない。

## 4. 固定counter、独立検算、停止状態

r6/t1が長さ19の

    AASSSSSSSAAAAAASASS

である。coherentな完全seedと20個の数値traceをpacketに保存した。A-prependの唯一のI衝突は(0,20)、S-prependでは(0,4)。独立direct-area/reverse-source検算でも一致した。長さ0..8の全511語ではadmissible387語について(PS)/(PA)と直接prepend検査を照合し、この有限範囲に両prepend不可は0件だった。長さ19が最小だとは主張しない。

全r族の有限controlはdiscovery r6/7/9/10、未使用parameter holdout12/13/15/16。全original source sets、全I/II、上の全intercept inventories、E778の完全区間seenによるreplayと四数値filterを確認した。r6は既知発見例を再使用したものでfresh holdoutではない。有限controlsはCOMPUTED、全rの証拠は上のphase分類とimmutable loop証明に置く。

PREDECESSOR_PROTOCOL/PREDECESSOR_FAMILY_PROTOCOLのsource/card/argv hashを実行前に固定、各1CPU/10wall、単一cooperative Python/no-descendantで終了した。修理0、範囲・cap延長なし。全実測CPUと完全seen recipe/trace/source/collision residualは[data packet](data/depth_general_20261125)に保存。新Lean0、旧停止jobは再開していない。

次の一問：C1の元positive/initial-S/return/全old-source条件を保つ実際の候補族のうち、どれがこのような「実行済み前史」の条件で除外され、どのfree/LOW財布への支払いが残るか。coherent seedの存在と四scalar filterだけでcanonical前史を仮定しない。逆に、ここでのA始まりcounterをC1領域のcounterへ昇格しない。
