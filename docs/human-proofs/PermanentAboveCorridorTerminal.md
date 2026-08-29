# PermanentAboveCorridorTerminal

**役割:** corridor suffixの距離cursorに対する強帰納法でlegal endpoint列を有限回で消費し、missing-target下のhistorical dischargeを「即時履歴谷」または「終端全強制加算crossing窓」の二形へ型付きで正規化する。

## このモジュールの役割

`PermanentAboveCorridorSuffix.lean`は、canonical below corridor(freshなhistorical downcross endpointから最初のweak upcrossing=first returnの直前までの、全値がtarget未満の有限軌道区間)の内部で合法減算(legal subtraction)が起きるたびに、suffixのendpointをreturnへ向けて厳密に近づけられることを示した。また`PermanentAboveCorridorBoundary.lean`は、target未出(missing-target)の仮定下ではlegal endpointがreturn predecessorと一致できないこと(一致すればexact targetが実現してしまう)を示した。本モジュールはこの二つを結合し、残距離`returnTime − endpointTime`への強帰納法を実際に実行する。結論として、任意の遅延corridorは有限回のlegal endpoint移動の後、全遷移が強制加算(all-forced addition)のsuffixで停止し、`PermanentAboveCorridorWindow.lean`の有限算術証明書`TerminalAllForcedCrossingWindow`に到達する。returnが即時(downcrossの直後)の場合は、二歩で元の値+1へ戻る「谷」の等式群を`ImmediateHistoricalValleyCertificate`として型付きで取り出す。これによりhistorical discharge(historical downcrossからcanonical return upcrossingまでの一回の排出過程)の終端は、ちょうど二つの明示的な形に縮約される。

## 主要な定義

### `ImmediateHistoricalValleyCertificate` (L72)

first returnが即時(`returnTime = downTime + 1`)である場合に残るexact valley(谷)の証明書。target未出、`target < a(downTime)`(sourceはtargetより上)、`a(downTime+1) < target`(fresh endpointはtarget未満)、下降等式`a(downTime+1) = a(downTime) − (downTime+1)`、復帰等式`a(downTime+2) = a(downTime+1) + (downTime+2)`、およびそれらを合成した谷の等式

```text
a(downTime+2) = a(downTime) + 1
```

を保持する。合法減算の一歩とその直後の強制加算の一歩が、正確に元の値の一つ上へ着地するという算術的事実である。

### `PermanentTailDischargeTerminalShape` (L113)

typed historical discharge証明書`PermanentTailDischargeReturnCertificate`(historical downcross、fresh endpoint、canonical first return、旧crossing provenanceを束ねた`PermanentAboveCycleExit.lean`の構造)の正規化された終端形。二つのconstructorしか持たない。

- `immediate_valley`: 上記の即時谷証明書。
- `finite_crossing_window`: `downTime + 1 ≤ terminalEndpoint`を満たすある終端endpointでの`TerminalAllForcedCrossingWindow`(endpoint < return < target、strict crossing、加算trace、target gapとovershootがともに正かつreturn clock以下、を保持する有限算術証明書)。

## 定理と証明

### `CanonicalBelowCorridorSuffix.exists_terminalAllForced` (L20)

**主張:** target未出の下で、`endpointTime < returnTime`なるcanonical below corridor suffix(endpointが初出でtarget未満、returnがそのendpointから見た最初のweak upcrossingであるという証明書)は、有限回のlegal endpoint移動の後に必ずall-forced terminal suffixへ到達する。すなわち`endpointTime ≤ terminalEndpoint < returnTime`なる終端endpointと、その位置のsuffix証明書、およびその内部に合法減算が一切存在しないこと(`AllForcedAdditionSuffix`)のwitnessが存在する。

**証明:** 残距離`corridorSuffixRemaining returnTime endpoint`(実質`returnTime − endpoint`)についての強帰納法。現在のsuffix内部に合法減算可能な時刻`time`(`endpoint ≤ time < returnTime`)が存在するかで場合分けする。

- 存在する場合、`PermanentAboveCorridorBoundary.lean`の`child_of_internalSubtraction_missing`を適用する。この補題はmissing-target仮定を使い、着地点が`time + 1 < returnTime`と厳密にreturnより前に留まること(さもなくば二歩式でexact targetが出現する)、新endpoint `time+1`での子suffixの成立、および`CorridorSuffixProgress`(残距離cursorの厳密下降)を同時に与える。残距離が真に減るので帰納法の仮定を子に適用でき、得られた終端endpointは`endpoint ≤ time+1 ≤ terminalEndpoint`により元のendpoint以後にある。
- 存在しない場合、「合法減算可能な内部時刻が無い」ことはまさに`AllForcedAdditionSuffix`の定義であり、現在のendpoint自身が終端witnessになる。

残距離は自然数なので無限下降できず、帰納法は必ず停止する。

### `CanonicalBelowCorridorCertificate.immediateHistoricalValley` (L85)

**主張:** canonical historical corridor証明書(tail開始・historical初出時刻・downcross・first returnを束ねたもの)がtarget未出かつ即時return(`returnTime = downTime + 1`)を満たすなら、`ImmediateHistoricalValleyCertificate`が成り立つ。

**証明:** まずsourceについて、downcrossの`start_at_or_above`から`target ≤ a(downTime)`、target未出から`a(downTime) ≠ target`なので`target < a(downTime)`。次にcorridorの最初の一歩の完全分類`firstStepOutcome`(`PermanentAboveCorridor.lean`)を場合分けする。`immediate_rebound`枝はまさに必要な三つの等式(下降・復帰・谷)を供給する。`delayed_subtraction`と`delayed_forced_addition`の二枝は`downTime + 1 < returnTime`というgapを持つため、即時仮定`returnTime = downTime + 1`と算術的に矛盾して排除される。

### `PermanentTailDischargeReturnCertificate.terminalShape` (L131)

**主張:** すべてのtyped historical dischargeは、ちょうど二つの明示的終端形のいずれかへ正規化される: 元の即時谷、または有限なall-forced crossing窓。

**証明:** discharge証明書から`exists_belowCorridor`でcanonical below corridorを取る。`returnTime = downTime + 1`かどうかで場合分けする。

- 即時なら、L85によりそのまま`immediate_valley`。
- 遅延なら、first returnのcrossingが`downTime + 1 ≤ returnTime`を保証するので`downTime + 1 < returnTime`。corridorをsuffix形へ移し(`toSuffix`、endpointは`downTime + 1`)、L20の強帰納法で終端endpointとall-forced suffixを得る。target未出・endpoint < returnと合わせて`TerminalAllForcedSuffixCertificate`を組み、`PermanentAboveCorridorWindow.lean`の`crossingWindow`で有限算術証明書へ変換する。終端endpointが`downTime + 1`以後にあることも帰納法の返す不等式から従う。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「corridor terminal normalization(二形へ縮約済み)」に対応する。上流は`PermanentAboveCorridor.lean`(corridorの最初の一歩の分類と`exists_belowCorridor`)、`PermanentAboveCorridorSuffix.lean`(suffix cursor)、`PermanentAboveCorridorBoundary.lean`(missing-targetによるlegal return境界の排除)、`PermanentAboveCorridorWindow.lean`(crossing窓の算術)である。下流では`PermanentAboveCorridorBalance.lean`が二つの終端形に共通するstrict crossingの釣合い算術(gap + overshoot = return + 1)を抽出し、以後のBlocker・Residual・Candidates系の解析はすべてこの`PermanentTailDischargeTerminalShape`の二分岐を出発点とする。`ImmediateHistoricalValleyCertificate`は後に`PermanentAboveCorridorImmediateClosure.lean`で谷の等式からCoverageStepへ、`finite_crossing_window`は`PermanentAboveCorridorFiniteClosure.lean`で数値的矛盾へと、それぞれ閉じられる。
