# PermanentAboveCorridorBalance

**役割:** 即時履歴谷と終端全強制加算窓という二つのterminal形に共通する最終遷移 — 未出targetの強制的な厳密上方crossing — の算術を`StrictTerminalCrossingBalance`として抽出し、target gapとovershootの和が加算clock `returnTime + 1`に等しく各々正かつ`returnTime`以下であることを、両枝共通のinterfaceとして統一する。

## このモジュールの役割

`PermanentAboveCorridorTerminal.lean`は、任意のhistorical discharge(historical downcrossからcanonical returnまでの型付き証明書)が、即時履歴谷`ImmediateHistoricalValleyCertificate`または終端全強制加算窓`TerminalAllForcedCrossingWindow`の二形へ正規化されることを示した。本モジュールは、この二形が見かけ上異なるにもかかわらず、最後の一歩がまったく同じ形 — target未満の値からの強制加算による厳密upcrossing — であることに注目する。targetが軌道に未出である限り、crossingはtargetちょうどに着地できないので厳密であり、crossing直前のtarget gap(`target − a returnTime`)と直後のovershoot(`a (returnTime+1) − target`)は最終加算clock `returnTime + 1`を正の二つの部分に分割する。従って両差はいずれも`returnTime`以下という有限上界を持つ。この釣合い算術に、最終のfresh below-target endpoint(初出のtarget未満着地点)とそのcanonical returnを添えた共通データが`NormalizedTerminalCrossingData`であり、以後のblocker解析(`PermanentAboveCorridorBlocker.lean`以降)は枝によらずこの単一interfaceの上で進められる。

## 主要な定義

### `StrictTerminalCrossingBalance` (L16)

未出targetの強制的厳密crossingが満たす算術の束。フィールドは: targetが全軌道で未出、`a returnTime < target < a (returnTime+1)`、最終stepが強制加算、加算式`a (returnTime+1) = a returnTime + (returnTime+1)`、target gapとovershootがともに正、分割等式`(target − a returnTime) + (a (returnTime+1) − target) = returnTime + 1`、および両差が`returnTime`以下であること。

### `TerminalFreshEndpointCertificate` (L69)

discharge証明書`source`に対する最終fresh endpointの証明書。endpointが回廊区間内(`source.downTime + 1 ≤ freshEndpoint ≤ source.returnTime`)にあり、その値が初出(`FirstAt`)かつtarget未満で、そこからのcanonicalな最初のupcrossingがちょうど`source.returnTime`で起きることを保持する。

### `NormalizedTerminalCrossingData` (L83)

枝に依存しない共通terminalデータ: fresh endpoint証明書の存在と、`source.returnTime`でのstrict crossing釣合い。

## 定理と証明

### `WeakUpcrossingStep.strictTerminalCrossingBalance` (L35)

**主張:** targetが未出なら、任意のweak upcrossing(`a returnTime < target ≤ a (returnTime+1)`、強制加算)はstrictな釣合い証明書`StrictTerminalCrossingBalance target returnTime`を与える。

**証明:** まず`a (returnTime+1) = target`はtargetの出現になるので未出仮定に反し、弱い不等式`target ≤ a (returnTime+1)`は厳密になる。最終stepは強制加算なので`a (returnTime+1) = a returnTime + (returnTime+1)`。このとき

```text
(target − a returnTime) + (a (returnTime+1) − target) = returnTime + 1
```

は加算式の単純な並べ替えである。`a returnTime < target < a (returnTime+1)`から両差は正であり、正の二数の和が`returnTime + 1`なので、各々は`returnTime`以下である。以上を構造体に詰めるだけでよい。

### `PermanentTailDischargeTerminalShape.normalizedCrossingData` (L93)

**主張:** 正規化されたterminal二形のどちらの枝からも、同一のfresh endpoint + gap分割interfaceが得られる。

**証明:** terminal形で場合分けする。

*即時谷の枝。* fresh endpointとしてdowncross endpoint `source.downTime + 1`自身を取る。谷証明書の`return_eq`(`returnTime = downTime + 1`)によりendpointはreturn以下であり、初出性はdischarge証明書の`endpoint_first`、target未満は谷証明書の`endpoint_below`、canonical returnはdischarge証明書の`return_crossing`そのものである。釣合いは、`return_crossing`の下にあるweak upcrossingへ谷証明書の`target_missing`を渡してL35を適用する。

*有限crossing窓の枝。* fresh endpointとして窓のterminal endpointを取る。区間条件・初出性・target未満・canonical returnはすべて窓の下にあるsuffix証明書(`PermanentAboveCorridorWindow.lean`)のフィールドから読み出せる。釣合いはsuffixのfirst returnのcrossingにL35を適用する。

二つの枝で最終crossingは同じ`source.returnTime`で起きるため、得られる釣合いの型も一致する。

### `PermanentTailDischargeReturnCertificate.strictTerminalCrossingBalance` (L128)

**主張:** 釣合い算術は、terminal正規化を経なくても、すべての型付きdischarge証明書から直接得られる: `StrictTerminalCrossingBalance target h.returnTime`。

**証明:** discharge証明書は`return_crossing`(canonical return upcrossing)を必ず持ち、その下のcombined証明書のtail部分が`target_missing`を持つ。L35を適用するだけである。

### `PermanentTailDischargeReturnCertificate.normalizedTerminalCrossingData` (L137)

**主張:** 強い正規化 — 共通釣合いに最終fresh endpointを添えたもの — もすべての型付きdischargeから得られる。

**証明:** `PermanentAboveCorridorTerminal.lean`の正規化定理`terminalShape`(suffix cursorに対する強帰納)で二形のいずれかへ落とし、L93を合成する。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「terminal crossing balance(共通算術へ統一済み)」に対応する。入力は`PermanentAboveCorridorTerminal.lean`のterminal二形と、`PermanentAboveCorridorWindow.lean`の窓・suffix証明書である。直接の下流は`PermanentAboveCorridorBlocker.lean`で、そこでは本モジュールの釣合い(特に最終stepが強制加算であるという事実)を定義まで巻き戻し、「最終減算が失敗した理由」を、predecessor値がclock以下という数値帯(`target < 2(returnTime+1)`)か、正の減算candidateが既出だったというhistorical blockerかの二形へ分類する。また`TerminalFreshEndpointCertificate`は、`PermanentAboveCorridorOuterHistory.lean`のouter blocker証明書や`PermanentAboveCorridorBlockerPosition.lean`のblocker位置比較(blockerの初出時刻とfresh endpointの前後関係でstrict budget進捗かouter historyかを分ける)の基準点として、そのまま引き継がれる。
