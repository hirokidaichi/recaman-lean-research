# H-20261113-09: initial-S消去で失う実供給を元freeへ償却する

- Status CONJECTURED at freeze; next consumer of H08 source classification
- Main general-principle unit, first gate15 minutes, no fixed depth/run bound

## Exact statement
任意元f,h,K、全i<hでf i=S、全0<k<=h+Kで元EndN f 0の供給+1<=元S数。
D=cN (fun q => EndN f 0 q ∧ ¬EndN f h q) h K、F=free f 0(h+K)。
**D<=F** を証明又は元history反例で判定する。Dは除去で失うexclusive old-prefix実供給で、全旧sourceと全local供給を残す。元EndN0を新Prop仮定で供給しない。
成功すればstrip後free<=2*元freeへのexact count consumerがあるが、strip後positive不足のmarginは別義務。全C1と同値なwrapperにしない。

## Before search falsifier
E704族ではD=N+1/F=2N+2で候補を破らず、Dが固定hで有界という案は既に偽。ceiling1ではD0、ceiling2 SAA境界はD1/F2。これらの再発見を進展にしない。反例にはliteral reverse全source検算と全prefix actual正不足を要求。弱化historyだけの違反は親反例にしない。

## Frozen budget and stop
当日math worker8CPU秒内の未使用分から4秒を明示再配分（既測2.903377、二job各2CPU/5wall、algorithm1.4秒以下、最悪累積6.903377）。子禁止cooperative single-Python guard契約を再利用。一般tree capと呼ばない。
discoveryはroot S^h (h1,2,3,4,8,16)、最大tail128/beam40、新しいD/F目的のみ。既存r4表/停止job/既存graphを実行しない。holdoutはh5,9,17×length192/224×32、seed2026111309、reverse全source。全終端長はdiscoveryより大きいがprefixの未見性は主張しない。
最初15分で新actual charge edge/反例がなければ同探索をSTOPPED、命題はCONJECTURED。有限不在で延長しない。07:37以後は独立audit、07:45新探索禁止。

## First gate result
H09 beam59302/valid59300 + reverse192/valid192でD>Fなし。best既知D2/F3、新charge edgeなし。方法STOPPED/命題CONJECTURED、source chronology paper義務を次回へ。 同worker再実行なし、有限不在をG進展へ数えない。
