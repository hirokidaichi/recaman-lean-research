# H-20261113-05: 元二窓の面積請求を一回だけ支払えるか

- Status REFUTED (one-wallet/fixed-overlap mechanisms); all-N construction PROVED-PAPER; parent H-20261113-02
- First general block remaining unit; hard stop06:37:47 JST

## Bounded statement
任意元f、区間[s,b]、基準r。窓i=1,2は元Win f ti(qi-ti)、s<=ti<qi<=b、実target EndN f 0 qi、q1!=q2。全区間Fw>=r。
Q(t,q)=2*(Fw(t)-r)*(q-t-1)-2、
P(s,b)=2*areaFromLevel(s,r,b-s)+belowTriangle(r,Fb)-belowTriangle(r,Fs)+2*lowAdditionWeights(s,r,b-s)-aboveTriangle(r,Fb)+aboveTriangle(r,Fs)。
**Q(t1,q1)+Q(t2,q2)<=P(s,b)** を、異なる二実targetだけを理由に主張できるか。E681の一窓必要式を二回同じ元free/面積財布へ請求する案である。重複を排除する仮定は置かない。

## Falsifier before Lean
small candidateは元語SSAAAASA、s0/b7/r-2、外Win0→7と内Win1→4。元EndN0と空BlockWord、全prefix正不足も検査する。外22・内2・財布22の可能性を独立算式で確認する。既知E642のshort/record集合重複とは別の、同source-area資源に対する長窓/短窓の重複である。

## Acceptance / stop / resources
元実二窓と数値をkernel認証した反例なら推論機構REFUTED。親C1やfree-gap反例ではない。修正案の交差区間資源は元actual countへ消費できるか別に監査し、既存恒等式の包装だけは新edgeにしない。
Lean個別-j1/-M512/10CPU/20wall、一修理まで。数学探索worker追加なし。失敗bytesはpacket隔離。時刻上限で局所副課題へ切替え、後半一般化30分は別の深さ操作機構へ。

## Falsifier result and corrected candidate (06:23)
H05の元SSAAAASAで外22/内2/財布22、全prefix actual正不足を個別-M512で認証。一修理はWinのDecidable展開だけ、H05-R受理。推論機構REFUTED。
修正候補は、交錯する元実窓 s<=t1<t2<q1<q2<=b について
Q1+Q2<=P(s,b)+P(t2,q1)。source高さr以下の仮定を使わず、r<=F(t1),F(t2)を要求する。Pは同じ元f/rの面積資源、交差区間一回だけを補正する。端点共有を含む弱順序でも検査する。
受入はPの非負・区間加法性から、実Winの費用を各窓のPへ内部変換する完全証明。一般深さに使える補正だが、交差Pから元freeへの支払い・全actual供給族の選択は別の未解決edgeと明示する。新定義の恒等式だけを一般化進展にしない。上限06:37:47、個別512MB/10CPU、一修理。

## Formalization / stop
元counterexampleはH05-R個別受理。交差補正はPAPER chainを保存、H05-I/Rは一修理後omega不受理でSTOPPED。packetへ隔離しroot/Auditへ採用しない。修理追加・import/tactic/splitだけの再開なし。一般化側の二重計上はせず、独立auditで反証edgeのみ判定する。

## Next falsifier: any fixed overlap factor (06:27:47 freeze)
否定候補は、上の元Pに対し、相異なる実targetの任意witness選択を全部足しても固定M倍で支払えるという案。
候補族はU_N=S^3 ++ SAA ++ (ASSSSAAA)^N、最後にtarget Aを置く。共通元source3、target q_j=6+8j (0<=j<=N)。空BlockWord、元EndN0、全prefix正不足・深さ5を内部検査する。
受入は全Nのmass/area・元targetA・hpos・floorとΣQ/Pの明示式。有限例を無限族へ推定しない。最新source/最短窓を強制した場合の反証ではなく、任意witnessを足す機構だけを判定する。既存E511 clean-source単射、E674最後crossing、10/20窓型LP no-goは保持し再実行しない。

## All-N paper verdict
U_Nの全元Win/actual target/全prefix正不足/深さ<=5を明示帰納で検証。ΣQ=(N+1)(6+16N)、grand P=48+32Nで比は非有界。任意witness固定M機構をREFUTED、全族はPROVED-PAPER・未Lean・人間レビュー未。最新witness選択や元C1への反例ではない。次はsource選択が必要というedgeを残し、固定M探索をSTOPPED。最終auditで既知no-goとの非重複を判定。

## Source uniqueness extension (06:30–06:32)
全q_jの必要source高さ-3の時計を3/5/q_l+3/q_l+7へ尽くした。3以外の面積は1又-3で、周期Zの追加でも不変。したがって全q_jの唯一sourceは3。最短/最新Winでも同じ共通区間の負荷N+1が不可避、固定M no-goを任意選択だけから**全Win選択**へ強化する完全PAPER証明を保存。N0..24の二方式有限検算も一致（COMPUTED、全N証明と別）。E674下降枠写像を短いWin選択と混同しない。
