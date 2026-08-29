# PermanentAboveHistory

**役割:** tail最小値のhistorical blockerを反復可能にし、有限回で必ずfreshなhistorical downcrossと履歴予算下降に到達することを示す一方、その後のupcrossing再構成では停留するcycle成長残余が必ず構成できることも証明する。

## このモジュールの役割

`PermanentAboveTail.lean`は、恒久上方tail(以後ずっとtargetより大きい軌道区間)の最小値の直下値`a(time) − 1`がtail開始前に初出するというhistorical blocker(既出値による下降妨害の証明書)を与えた。本モジュールはこのblockerを出発点とする過去向きの探索を形式化する。その初出時刻以後にdowncross(target以上からtarget未満への実遷移)があれば、endpoint はfresh(初出)で履歴予算`missingBelowCount`(未出のtarget未満値の個数)を厳密に下げる。downcrossがなければ初出時刻から新しいstrict-above tailが始まり、その最小値は旧最小値より厳密に小さい。後者は自然数の下降なので無限には続かず、強帰納法により必ず有限回でdowncross枝に到達する。しかし、そのdowncross後のupcrossing(target未満からtarget以上への強制加算横断)をzero-budget crossing親と同じhorizonに載せ直すと、anchor(pre-crossing値)が下がらない停留残余`HistoricalCycleGrowthResidual`を必ず構成できることも示す。これは現行のcrossing選択自由度の本質的境界であり、後続モジュールの動機となる。

## 主要な定義

### `PermanentTailCombinedCertificate` (L17)

一つの仮想的な最小未出tailが同じ`target`と`start`の上で同時に強制する三つの証明書の束: (1) `MissingPermanentAboveTail`(tail本体)、(2) `PermanentTailCrossingCertificate`(zero-budget ready crossingの障害)、(3) `PermanentTailMinimumCertificate`(tail最小値のhistorical blocker)。

### `HistoricalPredecessorOutcome` (L57)

tail最小値から直下値の初出時刻`predecessorFirstTime`へ移動した後に起こり得る、ちょうど二つの大域的可能性を表す帰納型。

- `downcross`枝: 初出時刻以後のある`downTime`で`FutureDowncrossStep`が起き、endpoint `a(downTime + 1)`は初出(`FirstAt`)、その時刻はtail開始前(`downTime + 1 < start`)、そして履歴予算が厳密に下がる。
- `renewed_tail`枝: 初出時刻から新しい`MissingStrictAboveTail`が始まり、その最小値証明書が取れて、新最小値は旧最小値より厳密に小さい(`a(newMinimumTime) < a(minimumTime)`)。

### `HistoricalTailDowncrossCertificate` (L148)

historical blockerの反復の有限な終着点。元の開始時刻以前のあるstrict tail(`tailStart ≤ originalStart`)、その最小値証明書、初出時刻以後の実際のdowncross、endpoint のfresh性、endpoint がそのtailより前にあること、および履歴予算の厳密下降、をまとめた存在命題である。

### `HistoricalCycleGrowthResidual` (L235)

historical downcross後に再構成したupcrossingが、combined証明書のzero-budget crossing anchorを下げない場合の正確な残余。downcross、upcross、ready crossing子、親と同一のhorizon、anchor非減少(`parent.anchorParent ≤ child.anchorParent`)、そして`PhaseSearchProgress`(四成分位相ランクの厳密下降)の不成立を同時に保持する。

## 定理と証明

### `MissingPermanentAboveTail.exists_combinedCertificate` (L27)

**主張:** 完成履歴付き恒久tailは、zero-budget crossing障害とhistorical minimum blockerを同時に供給する: combined証明書を持つ`crossingNode`、`minimumTime`、`predecessorFirstTime`が存在する。

**証明:** `PermanentAboveTail.lean`の`exists_crossingCertificate`と`exists_minimumCertificate`をそれぞれ適用し、tail本体とあわせて束ねる。

### `LeastMissingTarget.exists_permanentTailCombinedCertificate` (L44)

**主張:** 最小未出targetは、抽象的なeventually-above命題だけでなく、完全なcombined障害を露出する。

**証明:** `LeastMissingTarget.exists_missingPermanentAboveTail`で`start`とtail証明書を取り、L27を適用する。

### `PermanentTailMinimumCertificate.historicalPredecessorOutcome` (L80)

**主張:** strict tailの最小値証明書に対し、`HistoricalPredecessorOutcome`のいずれかの枝が必ず成り立つ。すなわち初出時刻からの未来には、tail開始前のfresh below-target downcrossか、より小さい最小値を持つ更新されたstrict tailか、どちらかが具体的に存在する。

**証明:** `predecessorFirstTime`以後にdowncrossが存在するかで場合分けする。

*downcross枝。* downcross遷移`a(downTime) ≥ target > a(downTime+1)`は値を下げるので、強制加算(値を`downTime+1`だけ増やす)ではあり得ない。よって合法減算であり、合法減算の着地値は定義上未出なので、endpoint は時刻`downTime+1`での初出である。endpoint はtarget未満だが、tailは`start`以後で常にtargetより真に上なので、`downTime + 1 < start`。履歴予算の厳密下降は`FutureDowncrossStep.strict_budget_drop`(freshなbelow-target値が一つ増えるため)から従う。

*renewed_tail枝。* downcrossが一つも無ければ、`a(predecessorFirstTime) = a(minimumTime) − 1 > target`を起点に`no_futureDowncross_iff_tail_atOrAbove`が「以後ずっとtarget以上」を与える。targetは未出なので不等号は厳密になり、`predecessorFirstTime`を開始時刻とする`MissingStrictAboveTail`が得られる。その最小値証明書を取れば、新最小値は開始点の値以下: `a(newMinimumTime) ≤ a(predecessorFirstTime) = a(minimumTime) − 1 < a(minimumTime)`。

二つの枝は現時点では異なる尺度(履歴予算と最小値)に住んでいることに注意する。この分裂を一つのrankへ統合するのが`PermanentAboveCanonical.lean`以降の主題である。

### `PermanentTailCombinedCertificate.historicalPredecessorOutcome` (L136)

**主張:** combined証明書についての同じ二分法。

**証明:** tail本体をstrict形へ忘却し、内蔵する最小値証明書にL80を適用する。

### `MissingStrictAboveTail.exists_historicalDowncrossCertificate` (L165)

**主張:** historical predecessorでtailを更新し続けることは永遠には続かない。すべてのmissing strict-above tailは`HistoricalTailDowncrossCertificate`を持つ。すなわち下降列のどこかのtailで、初出時刻以後の未来に実際のfresh below-target downcrossと履歴予算の厳密下降が現れる。

**証明:** 現在のtail最小値`a(currentMinimumTime)`を尺度とする自然数上の強帰納法。各段でL80の二分法を適用する。downcross枝ならその場で証明書の全成分が揃い終了。renewed_tail枝なら最小値が厳密に下がった新しいtailへ移る。このとき新しい開始時刻`currentFirstTime`は旧tailの開始時刻より前(`firstTime_before_tail`)なので、`tailStart ≤ originalStart`という不変条件も保たれる。最小値は自然数なので無限下降できず、有限回で必ずdowncross枝に到達する。

### `MissingPermanentAboveTail.exists_historicalDowncrossCertificate` (L202)

**主張:** 完成履歴付き証明書についての同じ結論。

**証明:** strict形へ忘却してL165を適用する。

### `MissingPermanentAboveTail.exists_positiveBudget_historicalDowncross` (L212)

**主張:** 完成履歴付き恒久tailにおいて、上の有限下降は真に正の履歴予算から始まり、zero-budget tail horizonの前で終わる。すなわち`FutureDowncrossStep target predecessorFirstTime downTime`、endpoint のfresh性、`downTime + 1 < start`、`0 < missingBelowCount target predecessorFirstTime`、`missingBelowCount target start = 0`を同時に満たすwitnessが存在する。

**証明:** L202の証明書を展開する。`downTime + 1 < tailStart ≤ start`から時刻条件を得る。予算の厳密下降`missingBelowCount(downTime+1) < missingBelowCount(predecessorFirstTime)`は左辺が自然数なので右辺の正値性を強制する。`start`での予算0は`budget_zero`。これにより、historical blockerと最終的なcrossing障害を隔てる実際の予算消費イベントが特定される。

### `PermanentTailCombinedCertificate.refinedStep_or_historicalCycleGrowth` (L251)

**主張:** historical downcross後にupcrossingを再構成してcombined crossingと同じzero-budget horizonへ載せると、次のいずれかちょうど一方が成り立つ。(1) refined子とその`PhaseSearchProgress`が存在する(anchorの厳密下降)。(2) 文字どおりの同予算・anchor成長残余`HistoricalCycleGrowthResidual`。

**証明:** L165の証明書からdowncross endpoint `a(downTime+1) < target`を取り、tail開始点`a(tailStart) > target`までの区間に`exists_weakUpcrossingStep_between`を適用して、時刻`crossingTime`のupcrossingを得る。targetは未出なので着地値は厳密にtargetより上で、`target ∉ valuesThrough crossingTime`。着地時刻の座標を取り、子node

```text
child = ⟨parent.horizon, a(crossingTime), normal, a(crossingTime)⟩
```

を作る。crossing時刻はtail開始前、tail開始はhorizonより前なので`crossingTime + 1 < parent.horizon`となり、`CrossingRecoveryInvariant`が成立する。clock条件は親のready crossingから継承され、childはready crossingになる。ここでanchorを比較する。

- `a(crossingTime) < parent.anchorParent`なら、同一horizonでのanchor厳密下降が`phaseSearchProgress_of_horizonAndAnchor`により`PhaseSearchProgress`を与え、childはcrossing invariantを介して`OrbitReadyRefinedInvariant`を満たす。第一の枝が成立。
- そうでなければanchorは非減少である。このときprogressは成り立たない: もし成り立てば`crossing_zeroBudget_progress_forces_anchorDrop`(親の予算は0)がanchor下降を強制し矛盾する。よって全成分の揃った残余が構成される。

### `MissingPermanentAboveTail.exists_stationaryHistoricalCycleResidual` (L346)

**主張:** historical cycle残余は単なるインターフェース上の可能性ではない。すべての恒久tailについて、combined証明書と残余を同時に満たす親crossingが実在する。具体的には、historical downcross後に再構成したそのupcrossing自身を親に選ぶと、cycleの再生は数値的に同一のcrossing nodeを返し、anchorは等しく、rank進捗は成立しない。

**証明:** L202の証明書からdowncrossとupcrossing(時刻`crossingTime`)を取り、`exists_crossingCertificate`(L289、PermanentAboveTail)と同じ構成でhorizon `max(start+1, target)`上の親node

```text
parent = ⟨horizon, a(crossingTime), normal, a(crossingTime)⟩
```

を作る。この親は`PermanentTailCrossingCertificate`の全条件(ready crossing、horizonがtail内、予算0、horizonの値が厳密上方、future downcross不在)を満たし、最小値証明書とあわせてcombined証明書になる。一方、同じdowncross・同じupcrossingから残余を構成すると、子は親そのものになる。`PhaseSearchProgress target parent parent`は、予算0でのprogressがanchorの厳密下降を強制する(L189、PermanentAboveTail)ことと`a(crossingTime) < a(crossingTime)`の不可能性から否定される。よってanchor同値・progress不成立の`HistoricalCycleGrowthResidual`が親自身を子として成立する。

したがって、任意のcrossing証明書を許す現行のdomainでは、historical cycleを一回再生することはrank下降にならない。証明を進めるには、crossing選択をcanonicalに拘束するか(earliest/latest/minimum-anchorなど)、複数cycleを同時に測る真に新しいwell-founded量を導入するかが必要である。この一cycle構成は現行rankの中では反復できない。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「historical tail反復」(有限化済み)と「historical cycle接続」(残余まで分類)に対応する。入力は`PermanentAboveTail.lean`の二つの証明書と`CrossingDowncrossRefined.lean`の`FutureDowncrossStep`、`DowncrossBudgetGap.lean`のupcrossing存在定理である。出力の`HistoricalPredecessorOutcome`と`HistoricalCycleGrowthResidual`は、`PermanentAboveCanonical.lean`(earliest upcrossingのcanonical化とdual budget `seenBelowCount`)および`PermanentAboveCycleRank.lean`(anchor最外層の一方向cycle rank)がそれぞれの角度から停留問題を攻める際の共通の題材となる。L346の停留構成は、README末尾に述べられた現在の核心「crossing選択のcanonical拘束またはcycle横断の新rank」という未解決点を、Lean内の定理として固定したものである。
