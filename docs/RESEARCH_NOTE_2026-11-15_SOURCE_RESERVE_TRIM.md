# 元sourceと不足reserveによるinitial-Sの最小化（2026-11-15）

## 結論
PROVED-PAPER、未Lean・人間レビュー未。任意の元initial-S履歴について、全供給・全free・全prefix正不足を保つ最小の残存head長を、元source深さの最大値Vと元不足reserve Uから明示する。C*=max(U,V)。全depth/run/A数/長さに上限なし。ただしU/Vを元freeだけで支払う一様不等式は未証明で、一般C1の深さ帰納は完成しない。

## Exact statement
f:Nat→Bool、h,K:Nat。全i<hでf i=S、全0<l<=h+Kで元EndN f0供給数+1<=元S数。0<=k<=KにE(k)=cN(EndN f0) h k、S(k)=cN(f=false) h k、M(k)=Fw f(h+k)−Fw f h。
U=max({0}∪{max(0,E(k)+1−S(k)):1<=k<=K})（右式は整数からNatへの非負化）。
V=max({0}∪{M(q)−1:0<=q<=K、EndN f0(h+q)、非EndN f h(h+q)})。
Vの非零項は元Winから1<=M(q)−1<=hのNatである。C*=max(U,V)。g_C(i)=f(h−C+i)（0<=C<=h）。
すると0<=C*<=h。C*<=C<=hの全Cで、全q<=Kの元EndN f0(h+q) iff EndN g_C0(C+q)、全k<=Kの元全供給/全free件数が一致し、全0<l<=C+Kでg_Cの元positive deficitが成立する。逆に、この全target同値と全positive deficitを持つC<=hは必ずC*<=C。C0/K0を除外しない。

## 完全な紙上証明
1. 元initialS内に供給Aはない。元S数はh+S(k)、元供給数はE(k)。元positiveより、k>=1でE(k)+1<=h+S(k)なのでU<=h。
2. 元exclusive old target qの任意Win始点tはt<h。全initialSからFw(t)=−t、Fw(h)=−h、Win質量1からM(q)=h−t+1。従ってt=h−(M(q)−1)は一意で1<=M−1<=h。二次area条件はInitialSQuadraticSourceの逆向きも満たすので、自由なsourceタグでない。よってV<=h。
3. C>=Vで元EndNを取る。local source t>=hがあればそのままt−(h−C)へ移る。なければexclusiveなので一意source t=h−d(q)>=h−C。いずれも元のWinが同じsign suffixに移り高さ差/面積/端点Aを保つ。逆にg_Cの全Winは元t>=h−Cへ戻る。これで全sourceを尽くした同値を得る（selected witnessだけで済ませない）。
4. 初期S h本/C本はいずれもA/供給/free0。コピーしたfutureの端点Aと全供給が一致するため、cN分割で全prefix供給E(k)と全freeが一致する。g_CのS数はC+S(k)。C>=Uよりk>=1ではE(k)+1<=C+S(k)。C>0ならinitialSの非空prefixもpositive。C=0ならcopied k0は空区間でpositive義務がなく、k>=1で十分。よって全domainを内部供給する。
5. 最小性。全target同値を持つCでは、exclusive old target qのg_C sourceを元へ戻すとlocal sourceではなく、唯一のinitialS source h−d(q)でなければならない。従ってd(q)<=C、V<=C。k>=1で新positiveと供給一致からE(k)+1<=C+S(k)、U<=C。従ってmax(U,V)<=C。新free/positiveをPropとして仮定して証明を包装していない。

## 高さ依存操作は系であり二重計上しない
全q<=KでM(q)<=Rなら、元A数=E+FとwalkからE(k)−S(k)=M(k)−F(k)。従ってU<=R+1。exclusive old sourceはd=M−1<=R−1、V<=R+1。C*<=min(h,R+1)なのでH02の高さ依存trimを得る。そのsource iffだけは既存E709の派生であり新原理と数えない。新しい内容は全sourceとpositiveを保つ最小Cの明示的二費用とその必要十分性。
H02 Lean試作は一修理後実装診断でSTOPPED、paperのこの系をkernel受理と呼ばない。H02bytesを修理・分割・資源変更で再開しない。

## 反証passと境界
V1のU>=1固定はK0で最小性を破るためREFUTED。唯一の数学修理V2はUにk0を入れず、empty maximum0/C0を許す。SAはU1/V0でhead全除去失敗を保持。SSSAをh2で切るとfutureSAでU0/V0、head0もvalid。h5のAAAはU2/V1/C2、空futureはU=V=C0。h0は元historyそのもの。
E711の71語はU2/V1/C2で、全head長2..12が同じ元供給/free/positiveを保つ（sourceを捏造しない）。simple max-height式はR11/C12で無変化だったので、source-awareに見る実効差がある。h12→C2は深さ全体を定数へ落とした結果ではなく、この有限例の源reserveの差である。
6例の全Cをreverse literal全sourceで検算した結果はCOMPUTED、一般定理の証明ではない。元全source二次分類と上記finite-max論証が全量化紙上の根拠。worker実測.034235CPU秒、日計.259687、controller/guard/Lean別計。

## 残る未知辺
U=max(M−F+1)、V=max(exclusive old sourceのM−1)。D<=Fは旧供給の個数を抑えるだけで、Vという最大source深さやUを一様に支払ったことにはならない。H03のM<=2FはCONJECTURED、有限不在だけでbeam方法STOPPED。同じcutoffを増やして証明とは呼ばない。一般C1/標準全射性・人間レビューは未了。

## 採用するLean支持定理E713との境界
InitialSSourceCutのretained_source_iff/lost_source_iff/cut_tail_count_costは同512MBで初回受理、全元initial-S cutのsource保持/損失と実free費用を供給する。G1-G5/fullcheckは日次保存前に確認する。E712のU/V有限max・全domain・最小性全体をkernel化したとは呼ばない。E713の既存分類からの派生会計を別の一般化coverage進展へ二重計上しない。
