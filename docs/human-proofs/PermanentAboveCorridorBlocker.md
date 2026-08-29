# PermanentAboveCorridorBlocker

**役割:** terminal crossing(回廊終端の強制的なtarget横断)の最終減算が失敗した理由を定義まで遡り、「値が小さすぎる数値帯」と「returnより前に初出した正のhistorical blocker」のちょうど二形へ型付きで分類する。

## このモジュールの役割

仮想的な最小未出target(軌道に一度も現れない最小の目標値)を固定すると、恒久上方tail(以後ずっとtargetより大きい軌道区間)の解析は、`PermanentAboveCorridorTerminal.lean`と`PermanentAboveCorridorBalance.lean`により、canonical下側回廊(target未満の値だけを通る有限軌道区間)の終端で起きる一回の強制加算upcrossing(target未満からtarget以上への横断)へ正規化されている。この最終一歩は「時刻`returnTime + 1`での減算が不可能だった」からこそ強制加算になった。本モジュールはその不可能性の理由を、レカマン数列の減算可能性の定義(`CanSubtract`: 減算先が正で、かつ未出であること)まで戻って解剖する。理由は二つしかない。減算候補`a(returnTime) − (returnTime + 1)`が非正である(このとき`target`は明示的な二重時計の数値帯に閉じ込められる)か、候補が正だがすでに履歴に出現している(このとき候補はreturnより厳密に前に初出した、target未満のhistorical blocker=既出値による下降妨害になる)かである。証明地図の「terminal forced blocker」段階に対応する。

## 主要な定義

### `TerminalInsufficientValueCertificate` (L18)

最終減算のpredecessor(直前値)`a(returnTime)`が時計に対して小さすぎた場合の明示的な有限数値帯の証明書。三条件

```text
a(returnTime) ≤ returnTime + 1
a(returnTime + 1) ≤ 2 * (returnTime + 1)
target < 2 * (returnTime + 1)
```

を保持する。targetが`returnTime`で添字づけられた有限の帯に入るため、後続の`PermanentAboveCorridorCandidates.lean`でこの帯は明示的なリストへ列挙される。

### `TerminalHistoricalBlockerCertificate` (L26)

最終減算を妨げた正の候補値についての証明書。候補`candidate`と初出時刻`firstTime`について、

- `candidate = a(returnTime) − (returnTime + 1)`(減算候補そのもの)、
- `0 < candidate`(正)、
- `FirstAt a candidate firstTime`(初出の証明)、
- `firstTime < returnTime`(returnより厳密に前)、
- `candidate < a(returnTime)`(predecessorより小さい)、
- `candidate < target`(target未満)

を束ねる。target未満の既出値がreturnより前に実在するという、過去向き探索の出発点となるデータである。

### `StrictTerminalCrossingBalance.ForcedReason` (L37)

strict terminal crossing balance(最終強制加算のtarget gapとovershootの釣合い算術を保持する証明書、`PermanentAboveCorridorBalance.lean`)に対する、上の二証明書を選言肢とする帰納型。`insufficient_value`枝と`historical_blocker`枝のみを持ち、最終減算失敗の理由の完全な分類を型として表す。

## 定理と証明

### `StrictTerminalCrossingBalance.forcedReason` (L52)

**主張:** すべてのstrict terminal crossingは、`ForcedReason`のいずれかの枝を必ず与える。すなわち二重時計の数値帯か、returnより前の具体的なhistorical blockerが常に取り出せる。

**証明:** 減算候補が正か否か、すなわち`returnTime + 1 < a(returnTime)`かで場合分けする。

*候補が正の場合(historical blocker枝)。* balanceの`forced_addition`は時刻`returnTime + 1`で減算が不可能だったことを言う。減算不能の理由は定義上「候補が非正」または「候補が既出」の二択(`not_canSubtract_iff_nonpositive_or_seen`)だが、いま候補は正なので前者は排除され、

```text
c := a(returnTime) − (returnTime + 1) ∈ valuesThrough(returnTime)
```

を得る。履歴の元は必ず初出時刻を持つ(`history_member_has_firstAt`)ので、`firstTime ≤ returnTime`なる初出`FirstAt a c firstTime`を取る。ここで`firstTime = returnTime`はあり得ない: もし等しければ`a(firstTime) = c < a(returnTime)`が`a(returnTime)`自身と矛盾する。よって`firstTime < returnTime`。また`c < a(returnTime)`は引き算から明らかで、balanceの`predecessor_below`(`a(returnTime) < target`)により`c < target`も従う。これで`TerminalHistoricalBlockerCertificate`の全成分が揃う。

*候補が非正の場合(insufficient value枝)。* `a(returnTime) ≤ returnTime + 1`である。balanceの最終方程式`a(returnTime + 1) = a(returnTime) + (returnTime + 1)`に代入すると`a(returnTime + 1) ≤ 2(returnTime + 1)`。さらにbalanceの`endpoint_above`(`target < a(returnTime + 1)`)と合成して`target < 2(returnTime + 1)`。これで数値帯の三条件が揃う。

この定理の意義は、「強制加算だった」という否定的事実を、どちらの枝でも正の算術データ(有限の数値帯、または初出時刻つきの具体的な既出値)へ変換する点にある。

### `NormalizedTerminalCrossingData.forcedReason` (L101)

**主張:** 正規化されたterminalインターフェース(immediate valley / all-forced windowの分岐に依らない共通データ)からも同じ`ForcedReason`が得られる。

**証明:** 内蔵する`balance`にL52を適用するだけである。immediate/all-forcedの場合分けを再び開く必要はない。

### `PermanentTailDischargeReturnCertificate.terminalForcedReason` (L109)

**主張:** discharge return証明書(historical downcrossからcanonical return upcrossingまでの全provenanceを束ねた証明書、`PermanentAboveCycleExit.lean`)から直接、terminal forced reasonを取り出せる。

**証明:** 証明書に付随するstrict terminal crossing balanceへL52を適用する補助適配定理である。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「terminal forced blocker」(二残余へ分類済み)に対応する。入力は`PermanentAboveCorridorBalance.lean`の`StrictTerminalCrossingBalance`と`NormalizedTerminalCrossingData`である。出力の二証明書はそれぞれ別の下流で消費される: `TerminalInsufficientValueCertificate`の数値帯は`PermanentAboveCorridorCandidates.lean`で有限リストへ列挙され(最終的に`PermanentAboveCorridorFiniteClosure.lean`が算術的に矛盾へ落とす)、`TerminalHistoricalBlockerCertificate`は`PermanentAboveCorridorBlockerPosition.lean`(fresh endpointとの位置比較)、`PermanentAboveCorridorOuterHistory.lean`(backtrack rank)、`PermanentAboveCorridorBlockerGeneration.lean`(生成遷移の分類)の共通の題材となる。
