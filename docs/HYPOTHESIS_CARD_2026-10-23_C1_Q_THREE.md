# Hypothesis card: a_z≤3の場合のC1面積Qをkernelへ移す

- ID: H-20261023-02
- Parent cycle: R-20261023-01。親と費用を二重計上しない。
- Parent: [深さカード](HYPOTHESIS_CARD_2026-10-23_C1_DEPTH.md)、C1 Q。
- Status: PROVED-LEAN（E-387、a_z≤3のQとold P2排除）
- Work state: 06:43:54から実行、06:59台に全体check通過。次unitへ継続。

## 一問・全量化子

任意の有限±1語、元0基点の実際の全P2/Endable、padded BlockWord prefix終端nを取る。
元不足d(n)=0、n<u≤b+1でd(u)≥1、n<q≤b、d(q)=1、
z=[n,q)の非Endable A数≤3、y=[q,b+1)の非Endable A数≤1、F(b)≤F(n)とする。
全n≤u≤bでF(u)≥F(n)−4のとき、

`Z(b)=Σ_(n,b](F(u)−F(b)+1)≥0`

を個別old signature緩和の有限グラフからkernelで証明できるか。
深さを下回る将来のyは、z深さ≤4（前カード）とE-379のfresh-low caseで別に扱う。
一般a_z≥4、C2/F/TS、全C1/H/SLはこの問いに含めない。

## 機構と受入・停止

- zは前カードの8語。local P2は全suffixを直接判定し、oldは同じmass/areaの必要signatureがあるときだけ任意tagを許す。
  実語はこの緩和へ含まれるが、緩和の反例を実語の反例と呼ばない。
- 受入: Qを満たす有限閉グラフとactual-word simulation、または具体的な緩和反例とその限界。
- 停止: 緩和Z<0を一つ発見、探索CPU30秒/経過28秒/保護stack512到達、または未供給の仮定へ循環。
  保護guardに達したら完了ではない。修理一回まで、語長/S上限の延長にしない。
- 提案→短語/境界/既知Az反例の反証→紙上chain→形式化→別pass監査。

## 配分・CPU・実績

C1活用の残りから実行し、7:10を目安に局所探索へ移る。7:45以降の新規探索なし。
CPUは当日の240秒上限内で、完了runの未使用予約を戻して30秒と独立監査30秒を確保。
発見は全8zからの完全な緩和tree。独立監査は別実装の全遷移とraw面積和、
既知SAAA|S4A4SAAAのAz<0/後続SSのZ=1をcontrolとする。
source hash・argv・revision/dirty hashを実行前にdocs/data/c1_depth_20261023へ固定。
実績は同じjournalのunit切替で保存し、この予定を先取りしない。

## 結果と限界

全8zからの個別old signature緩和は312状態で閉じ、guard265・Z最小1。
独立版が実BlockWordのmass1..5の全signatureとforward areaで全状態・全edgeを照合した。
同じ有限閉グラフをkernelで検査し、任意長Kのactual future simulationを証明。
深さ4外は、E-386で全区間最低値がq以後にあることを供給し、E-379へ接続した。

最終定理には深さ/語長/lag仮定がない。Ayは[q,b)≤1だけで足り、当初の[q,b+1)≤1より強い。
元不足d(n)=0からglobal countを分割する版と、全t<nの実P2窓を排除する版も形式化。
将来のA数やword長20を仮定せず、stepSが長さ21の語を返せるpositive controlもkernelで確認した。

`./scripts/check.sh`: 406 jobs / 2736宣言、許可3公理内。
新規QData moduleのlint、[逐語監査E-387](statement_audits/E-387.md)を保存。
この1証明書を312件やchunk数の研究成果に数えない。

残余は一般C1/Qのa_z≥4、C2/F/TS/SL/H。次は一般budgetへのrank入力を評価し、
完了したa_z≤3の深さ/Qを反復しない。親journalで全経過を一度だけ計上する。
