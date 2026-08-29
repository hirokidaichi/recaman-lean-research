# PermanentAboveCorridor

**役割:** rebased stationary cycleの内部に、historical downcrossのfresh endpointからその最初のweak upcrossingの直前までの「canonical below corridor」(全値がtarget未満の有限軌道区間)を型付きで切り出し、内部の各遷移を「履歴予算の厳密下降」または「target有界のclock」へ完全分類する。

## このモジュールの役割

`PermanentAboveCycleRebase.lean`までの解析で、恒久上方tail(以後ずっとtargetより大きい軌道区間)のzero-budget crossing反復には、canonicalなreturn選択を行っても解消されないstationary core(child = parentの停留残余)が残ることが確定した。本モジュールはその停留の内側に踏み込み、historical downcross(target以上からtarget未満への実遷移)のfresh endpoint `downTime + 1`から、最初のweak upcrossing(強制加算によるtarget未満→target以上の横断)`returnTime`の直前までの閉区間を有限の解析対象として抽出する。first upcrossingの最小性から、この区間上の全値はtarget未満である。さらに区間の第一歩と内部の任意の遷移を分類し、合法減算はfreshなbelow-target値の初出を作って履歴予算`missingBelowCount`(未出のtarget未満値の個数)を厳密に下げること、強制加算はそのclockが`target`未満に押し込められることを示す。従って予算を下げない内部区間は有限なtarget有界領域に限られる。

## 主要な定義

### `CanonicalBelowCorridorCertificate` (L53)

fresh downcross endpointからそのcanonical first return crossingまでの型付き有限回廊。次を束ねる:
(1) `0 < target`、(2) `MissingStrictAboveTail target tailStart`(targetが全軌道で未出、かつ`tailStart`以後は常に`target < a(time)`)、(3) `FutureDowncrossStep target historicalFirstTime downTime`(時刻`downTime`で`target ≤ a(downTime)`かつ`a(downTime+1) < target`となるdowncross)、(4) endpoint `a(downTime+1)`の初出`FirstAt`が時刻`downTime+1`にあること、(5) `downTime + 1 < tailStart`(endpointはtail開始前)、(6) `FirstWeakUpcrossingStep target (downTime+1) returnTime`(endpoint以後の最初のweak upcrossing)、(7) `returnTime + 1 ≤ tailStart`(returnもtail開始前)。

## 定理と証明

### `FirstWeakUpcrossingStep.value_below_of_between` (L22)

**主張:** `FirstWeakUpcrossingStep target start returnTime`で`a(start) < target`なら、`start ≤ time ≤ returnTime`の全時刻で`a(time) < target`。

**証明:** 背理法。ある`time`で`target ≤ a(time)`とすると、区間`[start, time]`はbelow-targetからat-or-above-targetへの有限区間なので、`exists_weakUpcrossingStep_between`により隣接する二時刻のどこか、すなわちある`earlier`(`earlier + 1 ≤ time ≤ returnTime`、従って`earlier < returnTime`)で強制加算によるweak upcrossingが起きている。これは`returnTime`が最初のupcrossingであること(`first`条件)に矛盾する。

### `FutureDowncrossStep.canSubtract` (L39)

**主張:** downcrossの一歩は必ず合法減算である: `CanSubtract (downTime+1) (stateAt downTime)`。

**証明:** 強制加算なら`a(downTime+1) = a(downTime) + (downTime+1) ≥ a(downTime) ≥ target`となり、endpointがtarget未満であること(`endpoint_below`)に矛盾する。値を増やす遷移でtarget以上からtarget未満へは降りられない。

### `PermanentTailDischargeReturnCertificate.exists_belowCorridor` (L64)

**主張:** 型付きdischarge証明書(`PermanentAboveCycleExit.lean`の、historical downcrossから最初のreturn upcrossingまでの全provenanceを持つ証明書)は、常に自身のcanonical below corridorを供給する。

**証明:** 証明書が保持する`historical_tail`、`downcross`、`endpoint_first`、`return_crossing`などの成分をそのまま射影するだけである。

### `CanonicalBelowCorridorCertificate.value_below` (L79)

**主張:** 回廊上の任意の時刻`downTime + 1 ≤ time ≤ returnTime`で`a(time) < target`。

**証明:** downcrossのendpoint条件`a(downTime+1) < target`を開始点の下側性としてL22を適用する。

### `CanonicalBelowCorridorFirstStepOutcome` (L90)

回廊の第一歩の完全分類を表す三constructorのinductive命題。

- `immediate_rebound`: `returnTime = downTime + 1`の即時return。減算式`a(downTime+1) = a(downTime) − (downTime+1)`、加算式`a(downTime+2) = a(downTime+1) + (downTime+2)`、およびそれらの合成である谷形の等式`a(downTime+2) = a(downTime) + 1`を保持する。
- `delayed_subtraction`: 遅延return(`downTime + 1 < returnTime`)で次の一歩が合法減算。着地値`a(downTime+2)`の初出、below-target性、履歴予算の厳密下降`missingBelowCount target (downTime+2) < missingBelowCount target (downTime+1)`を保持する。
- `delayed_forced_addition`: 遅延returnで次の一歩が強制加算。加算式、着地値のbelow-target性、およびclock境界`downTime + 2 < target`を保持する。

### `CanonicalBelowCorridorCertificate.firstStepOutcome` (L121)

**主張:** すべてのcanonical below corridorは上記三分類のいずれかに入る。

**証明:** `returnTime = downTime + 1`かどうかで場合分けする。

*即時の場合。* downcrossの一歩はL39により合法減算で、減算式が成り立つ。return crossing自体は定義上強制加算なので加算式も成り立つ。両式を合成すると、減算可能性から`downTime + 1 < a(downTime)`なので

```text
a(downTime+2) = (a(downTime) − (downTime+1)) + (downTime+2) = a(downTime) + 1
```

という正確な谷形の等式を得る。

*遅延の場合。* first returnの`start_le`から`downTime + 1 < returnTime`、従って`downTime + 2 ≤ returnTime`であり、L79により`a(downTime+2) < target`。時刻`downTime+2`での減算可能性で分ける。合法減算なら着地値は定義上未出(`firstAt_succ_of_canSubtract`)で、below-targetの新初出は`missingBelowCount`を厳密に下げる(`missingBelowCount_strict_of_firstAt`)。強制加算なら`a(downTime+2) = a(downTime+1) + (downTime+2) ≥ downTime + 2`が成り立ち、これがtarget未満なので`downTime + 2 < target`が強制される。

### `CanonicalBelowCorridorCertificate.delayed_budgetDrop_or_clockBound` (L160)

**主張:** 遅延回廊(`downTime + 1 < returnTime`)は直ちにstrictな二者択一を与える: 履歴予算の厳密下降、または`downTime + 2 < target`というclock境界。

**証明:** L121の三分類のうち、即時枝は遅延仮定と矛盾し(omega)、残り二枝がそれぞれ左右の選択肢を与える。

### `CanonicalBelowCorridorCertificate.internalSubtraction_budgetDrop` (L177)

**主張:** 回廊の内部時刻`downTime + 1 ≤ time < returnTime`での合法減算は、freshなbelow-target endpointを作り、`missingBelowCount target (time+1) < missingBelowCount target time`。

**証明:** `time + 1 ≤ returnTime`なので着地値はL79によりtarget未満。合法減算の着地値は未出なので初出は時刻`time+1`にあり、below-target値の新初出は履歴予算を厳密に下げる。

### `CanonicalBelowCorridorCertificate.internalForced_clockBelowTarget` (L195)

**主張:** 回廊の内部時刻での強制加算はclockがtarget有界である: `time + 1 < target`。

**証明:** 加算式`a(time+1) = a(time) + (time+1)`より`time + 1 ≤ a(time+1)`。着地値はL79によりtarget未満なので`time + 1 < target`。従って加算だけを続けるbelow区間は、いくら長いreturnを選んでも時刻`target`未満の有限領域から出られない。

### `CanonicalBelowCorridorCertificate.internalStep_budgetDrop_or_clockBound` (L210)

**主張:** 回廊の任意の内部遷移で一様なstrict二者択一が成り立つ: 履歴予算の厳密下降、または`time + 1 < target`。

**証明:** 遷移が合法減算か強制加算かで分け、それぞれL177とL195を適用する。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「canonical below corridor」(局所完全分類済み)に対応する。上流は`PermanentAboveCycleRebase.lean`のstationary core分析と、`PermanentAboveCycleExit.lean`の`PermanentTailDischargeReturnCertificate`、`PermanentAboveCanonical.lean`の`FirstWeakUpcrossingStep`である。下流では、`PermanentAboveCorridorRank.lean`が「予算を下げない補集合」を`AllForcedAdditionCorridor`として型付けしてremaining-clock rankで有限化し、`PermanentAboveCorridorSuffix.lean`が本証明書から`toSuffix`でsuffix cursor解析を開始する。停留cycleという大域的障害を、有限区間内の局所分類問題へ翻訳する入口が本モジュールである。
