# H-20261113-03: 任意深さの無重みA/free倍率を反証する

- Status CONJECTURED
- Work state candidate frozen; proposer/falsifier first, formalizer only after paper chain
- Parent H-20261113-02; general-principle unit 1, first gate 15 minutes, total first block30

## Exact statement
任意 f:Nat→Bool, n,a,K:Nat, w:List Bool。BlockWord w, seg f 0 n=w++A^a。
全0<k<=Kで cN(EndN f 0)n k+1<=cN(S)n k と仮定し、
**additions f n K <= 3*free f n K** が成り立つか。
深さ/高さ/run数/oldmass/長さの上限を仮定しない。元EndN f 0と全履歴を保持する。
強い補助命題でありC1の結論ではない。反証してもC1/標準orbit反例と呼ばない。

## Why this candidate
E660のA5/free2と既知A10/free4は係数2を破るが3を直ちに破らない。
E674は同高の元suppliedを低い全Aへ払うだけ、E675は幾何重みのPAPERで無重み上界ではない。
係数3の全高/任意深さ上界は供給密度のuniform controlになり、平方負債へ消費する追加edgeが必要。
これは停止した床+2三順位H25/R、幾何cN輸送H38/Rを再開するものではない。

## Acceptance and falsifier
既知幅4、free0/1、旧prefixを残す境界を紙上で攻撃後、凍結した単一Pythonworkerで探索する。
受入は(1)元actualの新しい任意深さedgeを含む完全証明、又は(2)厳密な元history反例。
有限の不在や候補式作成を一般化進展にしない。反例は独立のreverse-sign検算と可能ならLeanで認証。
既存r4表/既存graphは再実行しない。探索は新しい有限historyのbeam/period機構と明記する。

## Cost/roles/stop
数学探索CPU予算は初期0。子禁止cooperative single-Python契約をguardで再検証後に限り
新規8CPU秒（discovery4/independent-holdout4、各cooperative3.3秒/8wall秒）へ事前再配分する。
未検証時は数学workerを起動しない。全argv/revision/dirty+source hashを実行前に凍結。
proposerの不等式とfalsifierの反例は別記し、形式化は元反例/最弱edgeの確定後のみ。
最初15分で新edge/一般機構の反証が無ければ同じ倍率探索を延長せず別機構へ。
Leanは個別-M512/10CPU/20wall、一修理。原理や親C1の証拠labelと方法のSTOPPEDを分ける。

## First gate (2026-11-13)
有限beam118074 prefix visits / reverse holdout1536で反例なし、新edgeなし。仮説はCONJECTURED、同倍率探索方法をSTOPPED。2.382583 workerCPU秒で終了し、同workerを再実行しない。excess best=0は自明語Sであり比率上界の証拠ではない。H04の宣言mark反例はこの元actual仮説の反証ではない。
