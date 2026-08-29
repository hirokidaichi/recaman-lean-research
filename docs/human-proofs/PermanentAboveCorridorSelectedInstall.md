# PermanentAboveCorridorSelectedInstall

**役割:** below-target predecessorから選択したcanonical crossingを、旧親と同じhistory horizonを持つ次のpermanent-tail cycle親としてsemanticに「install」し、その親の上で次のdischarge証明書をselected crossing timeを型情報として保持したまま構成する。

## このモジュールの役割

恒久上方tail(仮想的な最小未出`target`が強制する、以後ずっと`target`より大きい軌道区間)の解析では、historical blockerのbelow-target predecessorから`PermanentAboveCorridorPredecessorCrossing.lean`が新しいready crossing node(`terminalPredecessorCrossingNode parent crossingTime`)を選択できる。しかしこの選択したnodeを次の探索cycleの「親」として実際に使うには、旧親が持っていたpermanent-tail semantics一式(tail所属、履歴予算0、horizonでの厳密上方性、future downcross不在、historical minimum証明書)を新しいnodeへ移送しなければならない。本モジュールは、選択nodeが旧親とhorizonを共有しanchor(探索の基準となるpre-crossing値)だけを変えることを使ってこの移送を行う。さらに、既存のcombined証明書はcrossing時刻をexistentialに隠しているため、cursor rank(anchorとcrossing時刻の辞書式比較)の反復で時刻情報を失わないよう、次のdischarge証明書を直接構成し、その`oldCrossingTime`がselected crossingの時刻に定義的に等しいことを型に保持する。残る反復上の分岐は、次のhistorical downcross endpointがselected時刻より前か後かというchronology(時系列)だけである。

## 主要な定義

### `TerminalSelectedCrossingInstallCertificate` (L22)

選択crossing `crossingTime`のfull semantic installation。四つの要素を保持する: (1) `permanent_crossing`: 選択node上の`PermanentTailCrossingCertificate`(予算0のready crossing、tail内horizon、future downcross不在などの束、`PermanentAboveTail.lean`参照)、(2) `combined`: 旧親と同じminimum時刻・初出時刻での`PermanentTailCombinedCertificate`、(3) `same_horizon`: 選択nodeのhorizonが`parent.horizon`に等しいこと、(4) `selected_anchor`: 選択nodeのanchorが`a(crossingTime)`であること。

### `TerminalSelectedCrossingDischargeCertificate` (L98)

install済み親の上の次のdischarge証明書。`discharge`(選択nodeを親とする`PermanentTailDischargeReturnCertificate`、historical downcrossからreturn upcrossingまでの全時刻・値provenanceの束)に加えて、`old_crossing_time_eq : discharge.oldCrossingTime = crossingTime`を保持する。既存のexistential witnessではなく、旧crossing witnessがまさに選択crossingであることを定義レベルで固定した点が新しい。

### `TerminalSelectedCrossingIterationChronology` (L191)

次のinstalledサイクルでeligible restart定理を適用できるかの正確な境界。二つのconstructorを持つ: `eligible`(次のdowncross endpointがselected時刻以前: `next.discharge.downTime + 1 ≤ crossingTime`)と`mismatch`(selected時刻がendpointより前: `crossingTime < next.discharge.downTime + 1`)。

## 定理と証明

### `TerminalBelowPredecessorCrossingCertificate.install` (L48)

**主張:** すべての選択crossing証明書は`TerminalSelectedCrossingInstallCertificate`へinstallできる。

**証明:** 選択node `terminalPredecessorCrossingNode parent crossingTime = ⟨parent.horizon, a(crossingTime), normal, a(crossingTime)⟩`は、旧親とhorizonを共有し、anchorだけをcrossing直前値へ差し替えたものである。`PermanentTailCrossingCertificate`の各fieldを検査すると、`ready_crossing`は選択証明書自身が保持しており、残りの五条件 — horizonがtail内にあること、tail開始がhorizonより真に前であること、履歴予算0(`missingBelowCount target horizon = 0`)、horizon値の厳密上方性、future downcross不在 — はすべてnodeのhorizon成分だけに依存する命題なので、旧親のcertificateからそのまま移送できる(Leanでは`simpa`による書き換えのみ)。combined証明書もtail部分とminimum部分は親から引き継ぎ、crossing部分だけを今作ったものに差し替える。`same_horizon`と`selected_anchor`は定義から`rfl`である。

### `TerminalSelectedCrossingInstallCertificate.exists_nextDischarge` (L120)

**主張:** installされた親の上に、`oldCrossingTime = crossingTime`を型として保持した次のdischarge証明書が存在する(`Nonempty`)。

**証明:** historical dischargeの構成を、旧crossing witnessだけ差し替えて再実行する。

まず`combined.tail`に`PermanentAboveHistory.lean`の有限下降定理`exists_historicalDowncrossCertificate`を適用し、tail開始`tailStart ≤ start`、strict-above tail、minimum証明書、historical downcross(時刻`downTime`、endpointはbelow-targetのfresh初出で`downTime + 1 < tailStart`)を得る。

次にreturn crossingを構成する。endpoint値はtarget未満なので、`exists_firstWeakUpcrossingStep_from_below`により`downTime + 1`以後の最初の弱上方crossing(`FirstWeakUpcrossingStep`、canonical return)`returnTime`が存在する。一方`a(tailStart)`はtailにより`target`より上なので、区間`[downTime + 1, tailStart)`のどこかで上向き横断が起きる(`exists_weakUpcrossingStep_between`)。canonical returnは任意のwitness以下なので`returnTime + 1 ≤ tailStart`が従う。

旧crossingにはselected crossing自身を使う。選択証明書の`first_crossing`から、`crossingTime`での弱upcrossing(below、endpoint_ge、forced addition)を開始点0からの`WeakUpcrossingStep`として読み替えられる。また`crossingTime ≤ source.returnTime`と旧dischargeの`returnTime + 1 < parent.horizon`から`crossingTime + 1 < parent.horizon`、すなわちinstall後のhorizonでも旧crossing境界条件が成り立つ。

以上の材料で`PermanentTailDischargeReturnCertificate`を`oldCrossingTime := crossingTime`と明示して組み立てると、`old_crossing_time_eq`と`old_anchor_eq`(installed nodeのanchorが`a(oldCrossingTime)`に等しいこと)はいずれも`rfl`で閉じる。

### `TerminalSelectedCrossingDischargeCertificate.chronology` (L214)

**主張:** 次のdischargeは必ず`eligible`か`mismatch`のいずれかに分類される。

**証明:** `next.discharge.downTime + 1 ≤ crossingTime`は自然数の決定可能な比較なので、成り立てば`eligible`、成り立たなければその否定から`mismatch`を得る。二値の場合分けのみ。

### `TerminalCrossingAnchorGrowthCertificate.installedProgress` (L235)

**主張:** anchor growth証明書(strict anchor growthの有限rank化、`PermanentAboveCorridorAnchorCandidates.lean`)が持つremaining-gap進捗は、installed nodeのanchor成分についての関係`TerminalCrossingAnchorProgress target (installedNode.anchorParent) (parent.anchorParent)`として生き残る。

**証明:** installed nodeのanchorは定義上`a(crossingTime)`なので、growth証明書の`gap_progress`(`target − a(crossingTime) < target − parent.anchorParent`)を定義の書き換えだけで読み替える。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「selected crossing install」(semantic反復parentを構成済み)に対応する。上流は`PermanentAboveCorridorPredecessorCrossing.lean`(選択crossingのready性)と`PermanentAboveCorridorAnchorCandidates.lean`(anchor growthの有限rank)、および`PermanentAboveCycleExit.lean`のdischarge証明書と`PermanentAboveHistory.lean`の有限下降定理である。下流では、`PermanentAboveCorridorChronologyRank.lean`が`mismatch`枝をmissing-budgetのstrict下降へ変換し、`PermanentAboveCorridorMasterRank.lean`が七成分master rankへ統合する。さらに`PermanentAboveCorridorInstalledStep.lean`の`exists_install`と`PermanentAboveCorridorTerminalSuccessor.lean`の反復可能なinstalled master構成が、本モジュールの`install`と`exists_nextDischarge`を直接使う。crossing時刻を型に固定したことで、cycle反復のcursor rankがexistential witnessの再選択によって壊れることを防いでいる。
