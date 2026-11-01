# 四A-run old-target: 最終separator源の実free課金

- ID: H-20261030-01
- Owner: Codex。提案/反証/形式化/監査を別passで行う。人間レビュー未。
- Created: 2026-10-29
- Status: CONJECTURED
- Work state: 10/30 cycle終了、journal stop済み。最初15分gateはE457の新edgeで通過。全域free-gapは未解決、次は10/31 joint-targetカード。三run E451/完了固定seedを再実行しない。
- Parent: R-20261029-01/H17後の次cycle。次cycleのjournal名は実開始時に採番し、今日の時間を加えない。

## 一回の問いと全量化子

任意 `f:Nat->Bool`、`n,h,M,m,L,s,U,v,T,j:Nat`、`w:List Bool`、`BlockWord w`、`seg f 0 n=w` とする。M,m,L,s,U,v,T>=1、h,j>=0。`B=h+M+m+L+s+U+v+T`。n以降の長さB+jは正確に

`S^h A^M S^m A^L S^s A^U S^v A^T S^j`。

同じ元0のcountでzero `cN(EndN f 0)0 n=cN(S)0 n`、全 `n<q<=n+B+j` で `cN(EndN f 0)0 q+1<=cN(S)0 q`。実targetの符号 `f(n+B+j)=true` と実old source `t<n`、`Win f t (n+B+j-t)` を仮定する。従って実EndNであり、独立tagは与えない。

最初のsubunitは、最終separator S^v内の源zが最終A-rayの最後j個以内にlocal供給をする場合に限る。`D=h+M+m+L+s+U+v` とし、`n+D-v<=z<n+D`、`i<T`、`T<=i+j`、`Win f z (n+D+i-z)` を追加する。

**問い**: この部分枝で、全長一様に

`j+1<=cN (fun x=>f x=true ∧ ¬EndN f 0 x) n B`

を新しいsource-conditioned inequality/実count課金で導けるか。元p/padded BlockWord版ではf(q)=e(p+q)と同じ元pのzero/全positiveから上を供給する。結論、全C1、任意rank、全prefix A<=2free+1を入力しない。

## 最初15分の受入と停止

- E452/E454による `M+L+U>=j+1` は既存のA-count cutの代入なので、新edgeとして数えない。
- 受入は、同じtarget/local源のmass/area/keyと実EndNに基づく、既存cutより強い不等式・strict candidate削減・正確な反例のいずれか。上のfull-tail free-gapへつながる新しい支払い区間を特定する。
- E453により「z以前のfree>=j+1」への直置換はREFUTED。定数を一つ緩めただけの修理はしない。源以降のfreeを支払う場合、区間重複/同supplier二重計上をしない。
- 15分で新情報がなければこのunitをSTOPPEDとし、命題はCONJECTUREDのまま。残り45分を、共通old源の第一/第四ray共同clock制約25分と、初期S target/第四ray localの衝突十分条件20分へ移す。一unitの停止を一日の終了理由にしない。
- 単なるA36表の拡張、H06/旧r4/R19/R11 jobの再実行・compiled import移動・資源追加は不可。

## 紙上chainと最弱edge

old target -> E441で最終bandのold供給を排除 -> 各local源の同じsuffix mass/area -> E454の源以前A下界 -> **未知: 実freeを源以前と以後へ重複なく課金** -> full-tail free-gap。

E451は三runまで完了で、この第四runを含む未知edgeそのものの仮定には使わない。ただし最初の三runまでの実供給countや、実EndNがある個別prefixには適切な既存定理を使える。途中でEndN基点をn/zへresetしない。

## 依存と参考の数値範囲

- PROVED-LEAN: E441 old finalband exclusion、E451三run全長、E452/E454 source cut、E407全A gap、E410/E411実ray予算、既存kernel検証済みr3 simulation/count projection。
- PROVED-LEAN E456: k4の元p実供給<=19と反例free4..17/A36/j17。一般kの二次予算だけは[PROVED-PAPER](RESEARCH_NOTE_2026-10-29_RUN_COUNT_BOUND.md)（未Lean/人間レビュー未）。全S長とold historyは無限であり有限history分類ではない。源別課金の結論へ使うときは同じ実countから全premiseを供給する。
- 反例/停止: E453はauxiliary free-prefix強化、E455はkeyを捨てる弱化historyの反例。親C1の反例ではない。E415 local<=2/3、E405無予算消去、E430 count-onlyも保持。
- 一般四run/任意run数、一般Q/C1/H/SL/全射性はCONJECTUREDのまま。r4分類E388 COMPUTED/E404 CONJECTUREDを別物として保持。

## 反証pass / CPU契約

先にj0/1、T<j、h0、最終separator長1、local源の両端、source overlap、同mass old、他supplier mass>5を検査する。小例はE453のliteral R5とE415の4clockを対照にする。これらをfresh holdoutと呼ばない。弱化historyでsource再使用を許した場合と、同じBlockWord実historyを区別する。

CPU探索当初0。必要なら実行前に独立discovery/holdout・argv・source/revision/dirty hash・上限を固定し、実装済みCPU契約の計測/停止を確認して再配分する。単なる有限範囲走査の延長は受入にしない。

## 予定と実績

次日120分のsetup10/研究監査100/handoff10。研究監査は活用60/探索30/別pass監査10、最初の15分だけを本unitに先行確定。研究audit超過は活用/探索から引く。この段落は実行前計画。実績は10/30 DAILY/journalのclosed区間だけを参照し、120分を先取りしない。親cycleと二重計上しない。全体連続無変化0は10/29 E445/E450/E451/E454による更新で、日付でresetしない。旧r4枝2回0/0のSTOPPEDは継承する。

## 引き継ぎ時のsource型/親命題の監査

E453のsource z=12は第一A-run内のAであり、本unitの最終separator S源ではない。従ってE453は全sourceのfree直置換を反証するが、S源に限定した未知枝を反証したものではない。S源という機構上の限定を保って検査し、単なる定数の修理と混同しない。

本unitは元zero/全positiveを持つ局所free-gapの強い補助命題で、完成Dの終端不足0など全条件は仮定しない。将来このunitの正確な反例を得ても、完成Dまで別監査せずC1反例へ昇格しない。E453自身も末端d(28)=13-4=9であり、完成Dのd(k)=0を満たしていない。

## 10/30 H01 input contract（形式化前）

元のfull-tail free-gapはCONJECTUREDのまま。最終separatorのlocal窓はS^q A^iなのでq1/i2の境界を先に検算する。targetold suffix uのC=mass(u)>=1と同じkey/areaを保持し、H=M+L+U、R=j+1、K=j+2-T>=0とする。まず、前置Aと後続Sの交差項を捨てず、
`(H-K)^2 >= R^2+C^2+2P+2K-2`
（P=M(m+s+v-1)+L(s+v-1)+U(v-1)）を候補にする。次に全genuine head runs/三separatorの正性から`M+L+U+T>=2(j+1)+2`が従うかを判定する。既存source以前A>=Rの代入ではないstrict pruningを受入とし、実freeへの接続はまだ未知と明記する。

反証passはu=A、空u（old非空を外した弱化）、T<j/T=j+1/j+2、v1、M=L=U=1、E453のA-sourceが本S-source域外であること、raw strict old三run sharp族がband外であることを照合する。探索CPU0、紙上検算。最初15分はsetup終了のresearch checkpointから測り、new inequality/strict削減がなければ既定の25/20分切替へ。候補を仮定したactualfree wrapperは書かない。

## 10/30 H11 接着gate（06:56:57前に固定）

初回15分はE457の新+2で通過。E458で全供給17/残余13、E459でS源head-onlyも反証。E461のML<R枝は供給13/残余9、E462のML>=R枝はA>=2R+3。次の一問は同じ実0/p/zero-positiveで両枝を場合分けし、H01全域の反例必要条件free4..12/A29/j12を供給できるか。目標free-gapの不在は入力せず、反例failureを必要条件の前提として明示する。これは新しいrank機構ではなく、新area/clock pruningの同じactual countへの統合。15分でcoherent接着ができなければSTOPして他source joint clockへ。


## 10/30終了時の判断

親H01全域はCONJECTURED。E464の固定head四run族だけは元p fullfree-gapまでPROVED-LEAN、E457/E458/E461/E462の反例必要域4..12/A29/j12の不在は未供給。E463幅はNat relative coreだけがPROVED-LEAN、p幅版はPAPER/combined STOP。E465 old moment帯を局所へ外挿する案はE466でREFUTED。E467の同じtarget二caseはPAPER/未Lean・人間レビュー未で、次日H-20261031-01へ継続する。実績時間・配分はDAILY/journalを正本にして親/子の両方へ加算しない。

実績確定: 7170.354秒、119分30.354秒、不足29.646秒。waiting23.281秒除外/gapなし。各unit費用は同日DAILY/journal参照。
