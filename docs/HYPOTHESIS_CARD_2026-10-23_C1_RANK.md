# Hypothesis card: deficit-one endpointへのrank入力

- ID: H-20261023-03
- Cycle: R-20261023-01（局所探索枠。親と二重計上しない）
- Status: CONJECTURED
- Work state: 07:02 JSTに次の一問を固定。探索開始の実時刻はjournalで記録。
- Parent: E-385〜E-387、[本日のnote](RESEARCH_NOTE_2026-10-23_C1_DEPTH.md)。

## 一問・全量化子

任意のpadded BlockWord prefix後の元0基点・正不足excursionで、終端不足1、
非Endable A数rについて、全A数≤2^r−1を供給する**任意rのrank/課金則**があるか。
受入はcutoffに依存しない非循環なpotential/strict progressの証明、または全条件付き実反例。
r=0ではz=SによりA=0。r=1/2/3はE-386の8語から一致する。

## 最初に棄却する強い読み

終端不足1を外した「全prefixでA≤2^r−1」は、既知語SAAA|SSSSAAAASAのprefixで
r=2・全A5・不足2となる疑いがある。全P2を直接再計算し、正しければこの強化をREFUTEDとする。
親の終端不足1の命題の反例にはしない。各r phaseで一様に倍化を課す手法もこの入力なしには使わない。

## bounded falsifier・機構比較

補助問い: r≤4の正不足prefixが16個目のAへ到達できるか。
E-385により、その停止線以前のold suffix mass≤14、local P2長≤29、S≥29でold supplyなし。
任意S長を29フラグ＋末尾29符号で圧縮し、全BlockWord mass≤14を代表できる。
発見shard mass0..4、独立holdout shard mass5..14を実行前に固定する。
既知mass≤17の文法contextは前日も使ったため、未使用motifとは呼ばない。

16個目のAの実語が見つかっても終端不足が2以上なら、強い補助問いの反例だけ。
その先のd=1へのco-reachabilityが次の未知edgeで、parent endpoint boundを自動反証しない。
到達なしでもr=4の入力だけで、任意rのrankの証明と呼ばない。
同じN32の延長やUNKNOWNモデルへの時間追加は行わない。

## 費用と停止・切替

- 局所探索30分を上限、07:35頃から別pass監査、07:45以降は新規探索なし。
- 追加探索CPUは当日の240秒上限内。発見/holdout各30秒、wall28秒、状態数100万/stack1024は保護guard。
  source/hash/argv/revision/dirty hashを実行前に固定。guard到達は未完了。
- 最初の反例、完全終了、または予算で止める。修理一回まで。実語witnessの独立全ledgerを確認。
- 任意rのpotentialに非同値な新edgeが出なければ方法をSTOPPEDとし、一般QをCONJECTUREDに残す。
  次の再開条件は共通prefixの整合制約か、終端d=1へ戻るための独立なjoint-area入力。

## 07:06までの判断と、一回だけの修理

全prefixの指数上限という強化はREFUTED。SAAA|SSSSAAAASAの全始点ledgerで
非Endable A2・全A5・不足2・全tail正不足を確認した。親の終端不足1はCONJECTUREDのまま。

実prefixによる第16A probeは発見mass0..4で完了、最高A10。
holdout mass5..14は28秒guardで停止（3708context中782完了、1中断、299569152訪問）。
反例なしを全prefixの証明にせず、同設定の時間追加はSTOPPED。

一回の修理v2を実行前に固定する：全正不足prefixについて

`P=A−2(d−1) ≤ 2^r−1`。

SでPは2減り、非Endable Aで1増え、Endable Aで3増える。
従って未知edgeは「Endable Aを許すclockでは、供給済み上界から少なくとも3の余裕があるか」。
空prefix(d=0)は対象外。終端d=1では元のendpoint boundになる。
係数2は上の反例をdeficitで補正する修理で、最適性や任意rでの正しさは未確認。

次の機構比較は全old signatureを独立に許すprefix-free緩和へ変更する。
同じ実prefixprobeの延長ではない。r≤4・第16A停止線・任意S圧縮29で、P_v2とendpoint語を監査する。
CPU30秒/経過28秒を同じ240秒上限内で実行前固定。
緩和反例は実prefixへの持上げを全P2で確認するまで実語の反例と呼ばない。
修理v2に実反例があればこのrank方法をSTOPPED。親のendpoint boundは別判定にする。

## 終了判定

一般endpoint/rankはCONJECTURED。全prefix強化はREFUTED、修理Pの任意rを供給する方法はSTOPPED（次のslack edge未供給）。
同じ有限rを増やすだけでは再開しない。
prefix-free r≤4緩和は全440943訪問・46892 saturated状態で完了、最大A10。独立forward/literal signature版が全counts/候補/P最大を照合。
r4 endpointは8候補、深さ4、P最大はr0..4で0/1/3/7/8。E-388/COMPUTEDとして限定して保存。
実prefix holdoutは未完了、同設定CPU追加はSTOPPED。新しいS-gap入力E-389へ切替えた。
