# PermanentAboveCorridorPredecessorCrossing

**役割:** below-target blocker predecessorの時刻から最初のweak upcrossingを再選択し、それが旧parent horizon内のready crossingとしてrefined domainに入ることを証明する。時刻0のpredecessorも吸収し、残る唯一の残余をcrossing anchorの非下降に限定する。

## このモジュールの役割

`PermanentAboveCorridorPredecessorAdapter.lean`のbelow-target枝は、terminal blockerの直前値がtarget未満であるという事実と、discharge return時刻への弱いcrossingを保持していた。本モジュールはこのpredecessor時刻`firstTime − 1`を起点に、canonical化された「最初のweak upcrossing」(`FirstWeakUpcrossingStep`、below-target点以後で最初に起きるtarget未満→target以上の強制加算横断)を選び直す。最初性により選ばれたcrossing時刻は既存のdischarge return以下、従って旧parent horizonより厳密に前にあり、target未出(missing-target)によってcrossingは厳密(着地値はtargetより真に上)になる。座標が必要なのは正時刻であるpost-crossing時刻`crossingTime + 1`だけなので、predecessor時刻が0の境界例も同じ構成に吸収される。得られたnodeは旧horizon上のready crossing(target到達可能なclock条件`target ≤ horizon + 1`を持つcrossing状態)であり、refined semantic domain(`OrbitReadyRefinedInvariant`)に属する。旧crossing親とはhorizonが同じなので、四成分位相ランクの下降はcrossing predecessor anchor(pre-crossing値)の厳密下降と同値であり、下降しない場合の残余はanchor非減少ただ一つに絞られる。

## 主要な定義

### `terminalPredecessorCrossingNode` (L24)

旧history horizonの上に置く数値的なcrossing node

```text
⟨parent.horizon, a(crossingTime), normal, a(crossingTime)⟩
```

である。anchorはcrossing直前の軌道値(pre-crossing値)そのものになる。

### `TerminalBelowPredecessorCrossingCertificate` (L29)

below-target predecessorから選択されたready crossingの完全なadapter証明書。三条件を保持する: (1) `FirstWeakUpcrossingStep target (firstTime − 1) crossingTime`(このcrossingが当該時刻からの*最初*のもの)、(2) `crossingTime ≤ source.returnTime`(既存のdischarge return以下)、(3) 上記nodeについての`ReadyCrossingSearchInvariant`。パラメータの`quotient`, `remainder`はpost-crossing時刻の座標である。

## 定理と証明

### `TerminalBelowPredecessorCrossingCertificate.refined` (L46)

**主張:** 選択されたcrossing nodeは自動的に既存のrefined child domain(`OrbitReadyRefinedInvariant`)に属する。

**証明:** refined invariantは「orbit-ready normal、ready debt、extended-history、crossing」の選言であり、ready crossing証明書のcrossing成分がそのcrossing枝をそのまま与える。

### `TerminalBelowPredecessorCrossingCertificate.backtrack` (L64)

**主張:** crossing childを選択した後も、元のblockerが持っていたbacktrack証明書(初出直前へのmissing budget下降・seen budget増加のrank辺)はそのまま利用可能である。

**証明:** blocker本体の`backtrackCertificate`の射影のみ。crossing選択はblockerの履歴的事実を消費しない。

### `BelowTargetHistoricalPredecessorCertificate.exists_crossingCertificate` (L83)

**主張:** すべてのbelow-target predecessorから、旧parent horizon上のready crossingを与えるadapter証明書が構成できる。この証明はpredecessor時刻の座標を必要としないため、時刻0の境界も含む。

**証明:** 本モジュールの中核である。

*最初のcrossingの選択。* `predecessor_eq`により`a(firstTime − 1) = predecessor < target`。targetの正値性とあわせて`exists_firstWeakUpcrossingStep_from_below`(`PermanentAboveCanonical.lean`)を適用し、時刻`crossingTime`の最初のweak upcrossingを得る。adapterが保持していたreturn時刻への弱いcrossingは同じ開始点のwitnessなので、最初性の最小値性質`time_le`から`crossingTime ≤ source.returnTime`。

*crossingの厳密化。* 着地値`a(crossingTime + 1)`はweak条件では`target ≤`だが、target未出により等号は不可能なので`target < a(crossingTime + 1)`。同様に`target ∈ valuesThrough crossingTime`なら出現witnessが得られて矛盾するので、targetはcrossing時点で未出である。

*座標とhorizon内包。* post-crossing時刻`crossingTime + 1`は常に正なので`exists_coordinatesAt`で座標が取れる(predecessor時刻自体の座標は不要であり、`firstTime − 1 = 0`でも構成は同一)。また`crossingTime ≤ returnTime`とdischarge証明書の`return_before_parentHorizon`から`crossingTime + 1 < parent.horizon`。

*invariantの組立て。* 以上でtarget未出・強制加算・厳密crossing・座標・horizon内包・predecessor < anchorの全フィールドが揃い、`CrossingRecoveryInvariant`が成立する。clock条件(horizon readiness)は旧parentのready crossingから`horizon`が同一のまま継承され、`ReadyCrossingSearchInvariant`になる。

### `TerminalBelowPredecessorCrossingRankOutcome` (L148)

crossing childの旧parentに対する正確なrank結果を表す帰納型。`refined_progress`(`PhaseSearchProgress`、四成分位相ランクの厳密下降)または`anchor_growth`(`parent.anchorParent ≤ a(crossingTime)`、anchor非減少)の二形。

### `BelowTargetHistoricalPredecessorCertificate.crossingRankOutcome` (L174)

**主張:** below-target adapterは常にrefined crossing domainへ入り、そのrankは直ちに下降するか、非減少anchorだけを残す。

**証明:** L83でcrossing証明書を取り、`a(crossingTime) < parent.anchorParent`かどうかで場合分けする。下降する場合、旧parentのready crossing証明書の`node_eq`からparentのanchorが実軌道値`a(oldTime)`であることを取り出し、horizonが同一(等号)でanchorが厳密に下がることから`phaseSearchProgress_of_horizonAndAnchor`により`PhaseSearchProgress`を得る。下降しない場合は`anchor_growth`をliteralに返す。

### `TerminalBlockerPredecessorRefinedOutcome` (L205)

adapterのsemantic三分類のbelow枝をrank付きcrossingへ精密化した帰納型。`normal_ready`と`above_residual`は`PermanentAboveCorridorPredecessorAdapter.lean`と同一で、第三のconstructorが`crossing`(below証明書とそのrank outcomeの組)になる。

### `TerminalOuterHistoricalBlockerCertificate.predecessorRefinedOutcome` (L236)

**主張:** below-target枝の精密化で新たに導入される残余はcrossing anchorの成長だけであり、時刻0の場合はすでに吸収されている。

**証明:** adapterの`predecessorSemanticOutcome`を場合分けし、`normal_ready`と`above_residual`はそのまま移送、`below_historical`にはL174のrank outcomeを添えて`crossing`へ詰め替える。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「blocker predecessor crossing(refined crossingへ接続済み)」に対応する。上流は`PermanentAboveCorridorPredecessorAdapter.lean`(below-target証明書)、`PermanentAboveCanonical.lean`(最初のweak upcrossingの存在と最小性)、`OrbitReadyRefinedStep.lean`(refined domain)である。下流では、`PermanentAboveCorridorPredecessorCursor.lean`が残余`anchor_growth`をcrossing-time cursor(五成分cycle rank)でさらに分解し、`PermanentAboveCorridorMasterRank.lean`が同じ三分岐をinstalled master rankへ統合する。また`terminalPredecessorCrossingNode`と本証明書は`PermanentAboveCorridorSelectedInstall.lean`で次のpermanent-tail cycle parentとしてinstallされ、terminal解析の反復の基礎になる。
