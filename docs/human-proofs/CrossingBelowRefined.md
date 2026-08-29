# CrossingBelowRefined

**役割:** 保存horizonの軌道値がtarget未満であるready crossingを完全に分類する: targetの出現、refined子への進捗、または「予算安定かつanchor非減少」の成長残余のいずれかであり、残余は実軌道(target 19)で実在する。

## このモジュールの役割

ready crossingノードのhorizonでの軌道値`a(node.horizon)`がtarget未満なら、`DowncrossBudgetGap`の存在定理により次の弱上方crossing(強制加算によるtarget未満からtarget以上への横断)が必ず存在する。それが厳密な横断なら新しいready crossingノードが得られるが、`CrossingRefinedBoundary`が示したとおり、crossing間のランク辺が成立するのは「新しいbelow-target値が履歴予算を消費した」か「pre-crossing anchorが旧anchorより小さい」場合に限る。本モジュールは、この続行が進捗になる場合とならない場合を、どちらの事実も弱めずに正確に二分する。進捗しない残余`CrossingContinuationGrowthResidual`は仮定の弱さではなく実軌道に実在する現象であることも、カーネル検証済みの具体例で示す。

## 主要な定義

### `CrossingContinuationGrowthResidual` (L17)

below-targetの保存horizonからready crossingを続行した後の、正確な障害の記録である。次の厳密上方crossingは存在するが、crossing間ランク辺が使える二成分のどちらも減っていないことを、次のデータで同時に保持する: 横断時刻`time`とpost-state座標、子ノード`child = ⟨time+2, a(time), normal, a(time)⟩`、続行の`WeakUpcrossingStep`、子がready crossingであること、履歴予算の安定(`missingBelowCount`が親と等しい)、anchorの非減少(`parent.anchorParent ≤ child.anchorParent`)、そして`PhaseSearchProgress`の不成立。

## 定理と証明

### `ReadyCrossingSearchInvariant.refinedStep_or_continuationGrowth_of_horizonBelow` (L38)

**主張:** ready crossingノード`node`が`a(node.horizon) < target`を満たすなら、次の三つのうちいずれかが成り立つ。

1. targetがすでに軌道に出現している。
2. refined domainの子`child`が存在して`node`へランク進捗する。
3. `CrossingContinuationGrowthResidual target node`: 続行は存在するが予算安定・anchor非減少で進捗しない。

存在部分に再帰や非有界探索の仮定は使わない。次の弱上方crossingは`exists_weakUpcrossingStep_from_below`が無条件に与える。

**証明:** horizonの値はtarget未満なので、`exists_weakUpcrossingStep_from_below`で次の弱上方crossing時刻`time`(`node.horizon ≤ time`)を取る。まず二つの即時出現枝を除く: targetが時刻`time`までの履歴に含まれるならその出現時刻が証人であり、横断の着地が`a(time+1) = target`なら`time+1`が証人である。

残る場合、横断は厳密(`target < a(time+1)`)である。強制加算なので`a(time+1) = a(time) + (time+1)`が成り立ち、`DebtCrossing`が組める。post-state座標を取り、子ノードを`child = ⟨time+2, a(time), normal, a(time)⟩`とし、`CrossingRecoveryInvariant`を構成する(target未出、強制加算、厳密横断、座標、`time+1 < time+2`、predecessor `a(time) <`旧anchor `a(time+1)`)。親のhorizon-ready性と`node.horizon ≤ time`から`target ≤ time+3`が従い、子はready crossingである。

次にランクを比較する。`node.horizon ≤ time+2`なので履歴予算は単調性により増えない。二分する。

- **予算が厳密に減った場合:** 辞書式第一成分で進捗し、子はrefined domainのcrossing成分として枝2に入る。
- **予算が等しい場合:** anchorを比べる。親のanchorは旧crossingのpre-crossing値`a(oldTime)`、子のanchorは新しいpre-crossing値`a(time)`である。
  - `a(time) < a(oldTime)`なら、horizonが縮まずanchorが厳密に下がるので`phaseSearchProgress_of_horizonAndAnchor`で進捗し、枝2に入る。
  - そうでなければ枝3である。進捗の不成立は`CrossingRefinedBoundary`の同値定理`crossingNumeric_progress_iff_budgetDrop_or_anchorDrop`による: crossingノードの数値形では進捗は「予算低下またはanchor低下」と同値だが、いま予算は等しくanchorは下がっていないので、進捗はあり得ない。予算安定・anchor非減少・進捗不成立をすべて記録して残余を返す。

### `crossingContinuationGrowth_actual_example` (L142)

**主張:** 成長残余は実際のレカマン軌道で実現される。target 19は時刻6で厳密に横断され(`a(6)=13 < 19 < a(7)=20`)、その後のready horizon 31では軌道は再び19未満(`a(31)=14`)である。しかし直後の続行(時刻31での横断`14 → a(32)=46`)は、19未満の新しい値を一つも発見しないまま、crossing anchorを13から14へ引き上げる。すなわち親`⟨31, 13, normal, 13⟩`はready crossingであり、`a(31) < 19`であり、`CrossingContinuationGrowthResidual 19`が成立する。

**証明:** 親のcrossing証明書(横断時刻6、旧anchor 20、座標`a(7) = 7·2 + 6`)、子`⟨33, 14, normal, 14⟩`のcrossing証明書(横断時刻31、旧anchor 46、座標`a(32) = 32·1 + 14`)、予算の安定(時刻31から33の間に19未満の新値はない)、anchorの非減少`13 ≤ 14`、および数値同値定理を経由した進捗の不成立を、すべてLeanカーネルの`decide`で有限計算として検証する。

## 全体の中での位置づけ

証明地図の「crossing horizon-below」の行に対応し、状態は「完全分類済み(target 19に残余の実例)」である。`RefinedOracleBoundary`の残余`CrossingRefinedStepHypothesis`のうち、horizonがbelow-targetの枝をこのモジュールが担い、`CrossingDowncrossRefined`(downcrossがある枝)と対をなす。実例定理は、残余が証明インターフェースの弱さではなく軌道の実挙動であることを固定し、安易な「続行すれば必ず進捗する」型の補題探しを排除する。残余の子horizonは必ずtarget以上に戻るという観察は、直後の`CrossingTailRefined`で「その後のdowncrossは元の親への厳密予算辺を作る」という形で回収され、残る枝が長期のtail return命題へ縮約される。
