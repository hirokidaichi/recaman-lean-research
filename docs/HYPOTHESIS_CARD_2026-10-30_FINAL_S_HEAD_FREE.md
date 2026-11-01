# 最終S-sourceに限ったhead free下限

- ID H-20261030-03 / R-20261030-01/H06、Status REFUTED（COMPUTED literal counterexample; Lean未検査）。
- Exact stronger auxiliary: H-20261030-01と同じ全量化子/実old target/最終S local源/band/元zero/全positiveに対し、最後のA-rayより前のhead（先行3A-run）の実freeだけでj+1以上を支払えるか。源がSなので源以前freeとheadfreeは同じ。全full-tail free-gapより強い。
- E453は第一A源のcountermodelなので本S-source限定案を反証しない。これはconstant修理ではなく、源の種類を固定した別の構造的問い。反例が出てもfull-tail free-gap/C1を自動反証しない。
- 受入: exact full-domain実counterexample、または同じsourceに基づく新下界。有限passはCOMPUTED、無制限の証明にしない。最初15分で判断情報がなければSTOPして元のfull-tail課金/共通prefix sourcepairへ戻る。定数修理なし。
- Paper falsifier control: old AA、h5/M1/m1/L1/s1/U3/v1/T5/j3はraw +2 sharp、headfreeは候補4=R。A-source E453/free4<R5は本source型外。全old prefixを一つ固定し、供給済みAを自由tag化しない。

## 実行前の計算契約

新しいsource-area +2 cutと供給17という独立pruningを得た後の小さなfalsifier。旧r4/H06の全状態表を再開しない。CPU探索0から数学worker合計4CPU秒（discovery2/holdout2）へ再配分する。各workerは子processなしcooperative single Python、1.6CPUで自発停止/OS上限2CPU/壁5秒/8時deadline。guard CPU1/壁0.2/fork拒否は検証別枠で実行する。一般tree累積CPU上限とは呼ばない。agent unit上限15分は局所探索枠から引き、CPU秒をagent分へ加算しない。

- Discovery: seed20261030、最大200000 sampled tuples、old words A/AA/SAAA、R4..10、M/L/U1..6、T3..R+1、s/v1..6。mを同じold mass/area identityから整数として解き、hを同じmass balanceから解く。全数網羅の計画ではない。
- Holdout: 実行前に別固定。seed20261031、最大200000 sampled tuples、old words tripW/SAAASAAA/AASAAA、R11..14、M/L/U1..10、T3..R+1、s/v1..10。old mass/areaとgap rangeを分離。actual EndNは独立の後退literal窓実装で再計算する。
- 各実候補は選んだold全語/全実P2/window/zero/全prefix正不足を検査する。target sourceは0、local sourceは最終S文字、i2。head違反を見つけたら一件で停止し、全word/EndN clocks/countsを保存する。full-tail違反も別判定する。
- 予算/件数停止は不完全sampleと明記。既存データをfresh holdoutと呼ばない。counter replayは同じ例の独立検証でありfresh holdoutとは別。source/revision/tracked dirty hash/argv/正確stdoutをpacketへ保存する。

## 06:35:40 falsifier結果

COMPUTED: discovery4640 sample/実zero-positive67候補目で、old A、h6/M1/m4/L4/s1/U6/v2/T10/j8の反例。head実free8<9、full-tail17>=9。Win0/43とWin24/3（最終S源/clock2）、EndN=[14,17,19,27,43]、元0/zero n1/全positiveを有限literal確認。独立holdoutは別old mass4/R11..14/後退literalで101659 sample/337実候補、tripW/h16/M6/m2/L3/s1/U6/v1/T14/j12、head11<13/full24を得た。各々最初のhead反例で停止、全sample完走ではない。親H01/full-tail/C1反例なし。定数修理なし、head-only課金をSTOPし、最後A-rayのfreeも含める。

CPU実測: discovery0.049643s、holdout0.432664s、合計0.482307s（worker/全thread、controller別）。数学予算4sの未使用を実績にしない。guard検証normal/fork/exec/2thread CPU/wallも別JSON保存。数学source/argv/revision/tracked dirty SHAはH06-PREFLIGHT.json。独立holdoutは異なるword/rangeであり、同じ反例のreplayと混同しない。discovery反例はLean逐語確認中、成功前はCOMPUTED/REFUTED auxiliaryとして保持する。

06:36:28: literal43 Leanの`decide`展開が512MB kernel memoryで失敗（H06-final-S-head-counterexample）。未検証sourceはpacketのH06-counter-unverified.lean.txtへ隔離し通常importしない。有限反例のLean化はSTOP、資源追加/compiled移動だけで再開しない。数学的反例自体はCOMPUTED/REFUTED。追加の独立replayへ未使用数学CPUから上限1CPU（cooperative0.6CPU、wall3秒）を再配分し、全数学実測累積4CPU秒以下を維持する。新source/argvを実行前にH06-REPLAY-PREFLIGHT.jsonへ固定し、同じwitnessのreplayをfresh holdoutと呼ばない。

06:37:20: 二反例の全source列を独立後退literalでreplay、zero/positive/oldtarget/最終S-source clock2/real EndN/freeを一致確認。replay worker0.031451CPU、数学合計0.513758CPU。H06-independent-replay.logを証拠とする。
