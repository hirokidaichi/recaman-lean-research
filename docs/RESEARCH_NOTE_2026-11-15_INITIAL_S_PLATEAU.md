# 初期S供給の最新free単射を破る元履歴（2026-11-15）

## 結論と証拠水準
REFUTED: 同じinitial-S元履歴/全prefixの元actual正不足でも、二つのexclusive old-S供給の間に元freeがないことがある。従って各供給を最新の元freeへ送る単射は偽。完全な紙上証明を以下に記す。71時計のLean試作は一修理後kernel512MBでSTOPPED、採用外。未Lean・人間レビュー未。D<=FやC1/標準軌道の反例ではない。既存H09/H10 finite worker/r3/r4表を再実行していない。

## 紙上構成（sourceを逆に設計）
A=+1,S=−1。H(k)は先頭k符号の和、B(k)=Σ_{i=1}^k H(i)。
u=S^3 A^3 S^3 A^4、v=S A S^4 A^7。
P=S A^11 S^13 u v = S A^11 S^16 A^3 S^3 A^4 S A S^4 A^7。
P長51、H(51)=1、B(51)=0。Q=P A S^4 A^3 A、長60。元wordは S^11 Q、長71。元fはこのwordを読み、範囲外はA（有限horizon内だけを主張するため、その後の延長は使用しない）。h=12（初期Sは12本）、K=59。q1=62、q2=70。

Winの元定義は0<q−t、H(q)=H(t)+1、B(q)−B(t)−(q−t)H(t)=0。前置S^11はQ内窓の高さ差/面積を変えない。ここでq,tはまずQ座標で示す。

| Q時計t | H(t) | B(t) | 用途 |
|---:|---:|---:|---|
| 0 | 0 | 0 | 両targetの旧source |
| 25 | −3 | 93 | 56のlocal source |
| 38 | −2 | 37 | 57のlocal source |
| 51 | 1 | 0 | 一つ目の旧target |
| 55 | −1 | 2 | 58のlocal SAA source |
| 56 | −2 | 0 | 供給中間A |
| 57 | −1 | −1 | 供給中間A |
| 58 | 0 | −1 | 供給中間A |
| 59 | 1 | 0 | 二つ目の旧target |

u長13/mass1/area−17、v長13/mass3/area−11。
B25=93、B38=93−3·13−17=37、B51=37−2·13−11=0。
中間period A S^4 A^3はmass0、cut基準area−8で、cut高さ1ゆえB59=B51+8−8=0。
従ってWin(0,51),Win(0,59)。元sourceは11でh=12以前にあり、元q1/q2はactual。

中間のAはQ時計56,57,58のみ（52..55はS）。その供給窓は:
- t25→q56: mass1、area0−93−31(−3)=0。
- t38→q57: mass1、area−1−37−19(−2)=0。
- t55→q58: mass1、area−1−2−3(−1)=0。
元ではsource36/49/66、target67/68/69。すべてsource>=hの元actual local供給なので、q1とq2の間にfreeはない。

## 全sourceの排除（選んだ窓だけの確認で済ませない）
Qの0<=t<60でH(t)=0となる時計を各runの一次式から尽くすと
**0,2,22,50,54,58**だけで、B値はそれぞれ **0,−1,99,−1,3,−1**。
両targetはH=1/B=0。Winならsource高さ0、かつsourceのB=0が必要なので、sourceは0だけ。前置初期S^11内の元時計0..10は高さが−11より大きく、source高さに一致しない。元全sourceは11だけで、h=12以降のsourceはない。従ってEndN f0 q1/q2かつ非EndN f h q1/q2。

元clock12の最初Aは、始点高さ−12に対し必要source高さ−13がそれ以前にないのでfree。最新freeは両targetの前で存在し、中間に追加freeがないため二targetが同じ最新freeへ写る。単射補助案はREFUTED。

## 元正不足・scope監査
P/Qの全prefix高さの最大は10（最初A^11直後）。残りはrun端点から2以下。S^11の前置後、全非空prefixの元Fwは<=−1。よって元S数>=元A数+1、EndN供給数<=元A数から全0<k<=71で元供給数+1<=元S数。供給markerを自由tagへ置換していない。
元初期S条件、元EndN0、local cutoff12、全prefix正不足、源以前prefixと全sourceを維持。有限sign-historyの反例であり標準Recamán軌道到達は未供給。D<=Fは最新free以外の割り当て/過去freeの貯蓄で成り立つ可能性を残す。h/Kを無限走査した不存在主張ではない。

## Lean停止と次の判断
H01-COUNTER: recursion-depth/Fin normalization errors、.730253 CPU秒。唯一の実装修理H01-COUNTER-R: maxRecDepth4096とFin.valの明示化、同-j1/-M512/10CPU/20wall、kernel512MB STOPPED、1.999415 CPU秒。試作全bytesはpacket .lean.txtへ隔離、root/Audit不採用。未計測CPUを0とせず、per-process capをtree累積capと呼ばない。資源/tactic/import/splitだけで再開しない。
次は最新free単射を修理して候補数を増やすのでなく、履歴依存のdepth operationの元全source/free会計という独立機構へ切り替える。親D<=FはCONJECTUREDのまま。

## 独立した有限検算（06:28、COMPUTED）
Guard normal/fork/exec/wall/threadCPUを当日確認したcooperative no-child単一Python workerで、事前凍結71語を一度だけ検算。forward (height,area−clock·height) key と reverse literal全sourceの二方式が全時計で一致。元全A31/S40/actual11/free20/exclusive old3。actual clocksは14,41,47,50,57,58,62,67,68,69,70。二targetの最新freeは両方61。元D3<=F20なので親不等式を破らない。有限検算は紙上証明の検算であり、未Leanをkernel証明へ昇格しない。argv/revision/worker hash/dirty sourceとwait4 receiptはpacket、worker実測.029260CPU秒、controller別計。探索や既存beamの再実行ではない。
