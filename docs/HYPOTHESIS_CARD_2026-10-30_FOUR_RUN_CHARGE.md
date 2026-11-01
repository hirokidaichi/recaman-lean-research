# 四runの加法的charge候補

- ID H-20261030-09 / R-20261030-01/H15、Status CONJECTURED（一般四run charge）。random/有限seed methodはSTOPPED、固定seedの別source proofだけE464 PROVED-LEAN。
- 入口の見直し: 既存two_run_supply_of_positiveは<=5（<=4ではない）。従ってML>=R+5なら最初二runのfreeだけでRを払う、ML>=Rの反例候補はML=R..R+4という紙上corollary。ただし既存countの代入なので独立した数学的成果に数えない。last二runはBlockWord prefixではなく、two-run定理を途中基点へresetして適用してはいけない。
- New bounded question: 全BlockWord実prefix/元0 zero/全relative positiveの四genuine A-run `Sh AM Sm AL Ss AU Sv AT` について、target/次供給を仮定せず `totalA<=2*actualfree+3` が成立するか。全run長/old履歴無制限。強い補助案であり、反例は親H01/C1の反例ではない。全prefixA<=2free+1という既知偽命題を再開しない。
- Paper value: H01の最終S源はE457でA>=2R+2。もし四run charge<=3を結論から独立に供給できれば整数性でfree>=Rになる。単なる同値wrapperを証明したと数えず、最小未知edgeは実供給の再使用を四run全体へ重複なく課金することである。各runごとのcharge<=1への分割は後続runが全供給の場合があるので入力にしない。
- Falsifier before Lean: known terminalA10/free4はcharge2で+1を反証するが+3には反例ではない。旧E415 local4clockを保持し、自由Endable tagや有限r3分類の一般化を入力しない。小例/境界とactual wholeprefixを保持した別範囲discovery/holdoutで攻撃する。
- New CPU contract: 数学既使用2.181532CPU。最後のsingle-Python worker1件だけOS1CPU/wall3秒、process内で独立seed/独立EndN algorithmのdiscovery/holdoutを各0.35CPU上限、最大各100000 tuples。全体実測でも4CPU以内（OS上限のtick超過を含めても余裕>0.8CPU）。子processなし当日検証済み。data/argv/source/revision/dirty hashは先にfreeze。discoveryR等のtarget参数は使わず、全A/signshapeを直接sampleする。
- Discovery seed20261230: wholeoldmass0..8/len<=20、全A12..20を4正A-runにランダム分配、h/m/s/v1..8。Holdout seed20261231: wholeoldmass9..16/len<=40、全A21..30を4正A-runに分配、h/m/s/v1..10（全A/wholemass範囲disjoint）、独立後退literal実EndN。全old source/prefixzero/全positiveを実検査し、最初のcharge>3で停止。target/sourceS条件を反例へ勝手に追加しない。
- 受入: 正確な反例か、全量化子を保つ新しい供給/charge inequality。15分で何も出ずsample予算終了ならSTOP、同じworkerへ時間を足さず別機構の紙上へ。偽の場合は定数修理しない。有限passでCONJECTUREDをPROVEDへ昇格しない。

実行前設計監査: 各run A9..14という当初holdout案は全A>=36となり既存供給17でcharge<=3が自明なので棄却した。未実行の範囲を上記全A21..30へ置き換え、供給17でcharge>3があり得る必要領域を攻撃する。全A>=31は既存実countだけで除外されるためsampleせず、前3free以下も既存r3により反例域外。

## H15 07:11:14 sample結果 / H16構造的falsifier契約

Discovery7474 tuples/zero7474/positive6929/maxcharge=-1、holdout3172/zero3172/positive2937/maxcharge=-9、反例0。各0.35CPUで未完走、実worker0.731902CPU、当日数学実測合計2.913434CPU。既知の正charge terminal motifを一度も再現していないため、無作為sampleの受入判断情報は弱い。random methodはSTOP、時間追加しない。命題はCONJECTURED。

H16は別の入力として既知E389/E395の高charge seedそのものを使う。oldASAAAとtail S5A3S4A4SA3は三run/charge2であり四genuine-runの対照ではない点を訂正する。これに新しいSv ATを追加して四runにする。E389は最初の追加Aがfreeであることを要求するが、その後の供給再使用がcharge<=3を破らないかを直接攻撃する。

新single workerを1件だけOS1CPU/wall3/自発全体0.7CPU、数学総実測4CPU以内（現在2.913434、CPUtick余裕約0.08秒）へ割当。discovery: prefixASAAA/新separator1..8/最後T1..12、holdout: prefixA/AA/SAAA/tripW/新separator9..16/最後T1..12、独立後退literal実EndN。両組のprefixとgapを分離し、seedの元zero/全positiveと全freeを再検査する。全固定tupleを終えたら停止、最初のcharge>3反例でも停止。source/revision/argv/hashを先にfreeze。finite motif familyの検査であり任意四run証明ではない。修理/追加CPUなし。この先は紙上source/charge機構へ切替える。

H16 07:12:44: discovery96/holdout384固定tupleを全検査、元zero/positiveとも480件valid、charge>3反例0、最大chargeは2/1。固定seed族のみCOMPUTEDで四run全域証明ではない。高charge2を再現したのでH15 randomより対照は改善したが、新しい無制限edgeは未供給。worker0.048728CPU、当日数学実測2.962162CPU。時間/範囲を足さず計算unitは終了、命題CONJECTUREDを維持して紙上source/chargeの必要入力へ。
