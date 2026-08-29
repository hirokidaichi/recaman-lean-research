# PermanentAboveCorridorImmediateClosure

**役割:** immediate historical valley(即時履歴谷)のexact二歩式`a(downTime+2) = a(downTime) + 1`から`CoverageStep`を構成し、canonical coverage adapterでtarget出現またはglobal semantic phase-rank下降へ閉じることで、immediate insufficient残余を数値残余から除去する。

## このモジュールの役割

terminal正規化(`PermanentAboveCorridorTerminal.lean`)は、恒久上方tailのhistorical dischargeを「即時谷」と「有限all-forced crossing窓」の二形へ縮約した。有限窓の側は明示的なreturn-clock候補listに閉じ込められるが、即時谷を同じ数値bandへ押し込む必要はない。即時谷のexact方程式は帯域評価よりずっと強く、二遷移後の値が谷の入口値のちょうど`+1`である。入口値`a(downTime)`はtargetより真に上なので、その初出を取れば「target以上で、二遷移後の値より真に小さい既出値」が得られ、これは`CoverageStep`(目標出現、または親より真に小さい値の初出を与える一段の証明)そのものである。既存のcanonical coverage adapterはこれをtarget出現またはstrictなsemantic phase-rank childへ変換するので、immediate insufficient残余は数値的terminal分岐ではなくなり、数値枝として残るのはfinite return候補だけになる。

## 主要な定義

### `ImmediateTerminalSemanticOutcome` (L36)

immediate insufficient枝をsemantic閉包した結果の型。`target_occurs`(`a(witness) = target`となる時刻の存在)または`semantic_step`(semantic invariant付きchildと、canonical開始node `targetStartNode (downTime+2)`に対する`PhaseSearchProgress`、すなわち四成分位相ランクの厳密下降)の二形。

### `PermanentTailTerminalSemanticallyClosedOutcome` (L63)

discharge levelのterminal outcomeの精密化。`history_progress`、`finite_return_candidate`はそのまま、旧`immediate_insufficient`は谷・insufficient証明書に加えて上記semantic outcomeを保持する`immediate_semantic`へ置き換わり、`historical_complete`(`PermanentAboveCorridorAboveClosure.lean`のcomplete outcome)も保持される。

## 定理と証明

### `ImmediateHistoricalValleyCertificate.coverageStep` (L25)

**主張:** 即時谷証明書(missing-target provenance、`a(downTime+1) = a(downTime) − (downTime+1) < target < a(downTime)`、および谷方程式`a(downTime+2) = a(downTime) + 1`を保持する、`PermanentAboveCorridorTerminal.lean`のProp)から、`CoverageStep target (a(downTime+2)) (downTime+2)`が従う。

**証明:** 値`a(downTime)`は時刻`downTime`の軌道値なので履歴`valuesThrough downTime`に属し、履歴の元は必ず初出時刻を持つ(`history_member_has_firstAt`)。その初出`firstTime`を取る。谷証明書の`source_above`から`target < a(downTime)`、すなわち`target ≤ a(downTime)`。谷方程式から`a(downTime) = a(downTime+2) − 1 < a(downTime+2)`。よって`y = a(downTime)`は「`target ≤ y`、初出時刻付き、`y < a(downTime+2)`」を満たし、`CoverageStep`の第二選択肢(より小さい値の初出)を与える。座標や履歴予算の仮定は一切使わない。

### `ImmediateHistoricalValleyCertificate.semanticOutcome` (L50)

**主張:** `0 < target`なら、即時谷はinsufficient-value副証明書とは独立に、通常のcanonical coverage adapterを通じて`ImmediateTerminalSemanticOutcome`へ閉じる。

**証明:** L25の`CoverageStep`に`CanonicalOracle.lean`の`canonicalCoverage_phaseSemantic`を適用する。この定理は、canonical開始nodeから見たCoverageStepを「target出現」または「semantic invariantを満たすchildへのstrictなphase-rank辺」へ変換する。どちらの枝も対応するconstructorへそのまま写る。

### `PermanentTailDischargeReturnCertificate.terminalSemanticallyClosedOutcome` (L94)

**主張:** すべてのdischarge/return証明書は、唯一の数値枝がfinite return候補listであるterminal outcome `PermanentTailTerminalSemanticallyClosedOutcome`を持つ。

**証明:** `PermanentAboveCorridorAboveClosure.lean`の`terminalCompleteInstalledOutcome`を場合分けし、`immediate_insufficient`枝でのみL50を適用する(targetの正値性はcombined tail証明書から取る)。他の三枝は情報を変えずに写す。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「immediate valley closure」(numeric残余をsemantic閉包済み)に対応する。上流は`PermanentAboveCorridorTerminal.lean`(即時谷証明書)、`PermanentAboveCorridorAboveClosure.lean`(complete installed outcome)、`CanonicalOracle.lean`(canonical coverage adapter)である。下流では`PermanentAboveCorridorReturnSelection.lean`が本モジュールの`terminalSemanticallyClosedOutcome`を出発点として唯一の数値枝であるfinite return候補を有限選択stateへ通し、最終的には`PermanentAboveCorridorFiniteClosure.lean`がそのfinite枝自体を算術的に排除する。即時谷が「数値帯の住人」ではなく「CoverageStepの供給源」だと判明したことは、terminal residual treeの数値部分を一本(finite window)へ絞る上で決定的である。
