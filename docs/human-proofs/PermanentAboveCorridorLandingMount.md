# PermanentAboveCorridorLandingMount

**役割:** parent horizonの内側で完結するfirst weak upcrossingが、missing-target tailの下で常に`CrossingRecoveryInvariant`の全条件を満たすことを示し、境界付きlandingをready crossing node(refined semantic domainの実object)として搭載する。これで閉じたterminal解析の全interface枝が外側探索のsemantic domainの言葉を話す。

## このモジュールの役割

`PermanentAboveCorridorLandingHorizon.lean`はlandingとそのrestart crossingがparent historyの厳密な内側にあることまでを示したが、fresh landing枝が運ぶのはまだ数値データ(時刻・値・初出証明)であり、外側探索が受け取るnode(`PhaseSearchNode`)とその不変量ではなかった。本モジュールはその最後の変換を行う。missing-target tailでは、upcrossingの着地値はtargetと一致できない(一致すればtargetの出現witnessになる)ためcrossingは自動的に両側strictになり、crossingの一歩は定義上certified forced additionで、正時刻の着地には商剰余座標が必ず存在する。target到達可能なclock条件(readiness clock `target ≤ horizon + 1`)は、搭載先のnodeがparentのhorizonをそのまま再利用するのでparentのready crossing証明書から輸送される。結果として、history辺のlandingは`terminalPredecessorCrossingNode parent c = ⟨parent.horizon, a(c), normal, a(c)⟩`上の`ReadyCrossingSearchInvariant`という、refined semantic domainの実objectになる。semantic枝・replay枝とあわせ、interfaceの三枝すべてが外側探索のdomainのobjectを手渡す段階に達した。

## 主要な定義

### `PermanentTailTerminalMountedOutcome` (L72)

history枝が実際のsemantic nodeを運ぶterminal interface。三constructorを持つ。

- `landing_crossing`: history progress、landing値のbelow-target性、`parentTime < landingTime`、landingの初出、restart crossing、境界`nextCrossingTime + 1 ≤ start`と`nextCrossingTime + 1 < parent.horizon`に加えて、搭載済みnodeの不変量`ReadyCrossingSearchInvariant target (terminalPredecessorCrossingNode parent nextCrossingTime)`を保持する。
- `semantic_progress`: 比較元付きsemantic位相辺。従来のまま。
- `exact_replay`: replay固定点(`TerminalExactDischargeReplayCertificate`)。従来のまま。

## 定理と証明

### `PermanentTailCombinedCertificate.landingReadyCrossing` (L25)

**主張:** combined証明書の下で、`landingTime`からのfirst weak upcrossingが`nextCrossingTime + 1 < parent.horizon`を満たすなら、node `terminalPredecessorCrossingNode parent nextCrossingTime = ⟨parent.horizon, a(nextCrossingTime), normal, a(nextCrossingTime)⟩`は`ReadyCrossingSearchInvariant`(crossing証明書+readiness clock)を満たす。

**証明:** `ReadyCrossingSearchInvariant`は二成分 — crossing不変量`CrossingSearchInvariant`と`horizon_ready : target ≤ horizon + 1` — からなる。以下`c = nextCrossingTime`と書く。

*crossingが両側strictであること。* upcrossingの定義から`a(c) < target ≤ a(c+1)`。targetは未出(tail証明書の`target_missing`)なので`a(c+1) = target`は不可能であり、`target < a(c+1)`が従う。

*targetが履歴に無いこと。* `target ∈ valuesThrough c`ならある時刻での出現witnessが取れて`target_missing`に矛盾。よって`target ∉ valuesThrough c`。

*座標の存在。* 着地時刻`c + 1`は正なので、`exists_coordinatesAt`により商剰余座標`CoordinatesAt (c+1) q r`が取れる。

*recovery不変量の組み立て。* 以上と、upcrossingが保持するcertified forced addition(減算不能の証明)、その加算式`a(c+1) = a(c) + (c+1)`、仮定の`c + 1 < parent.horizon`、そして`a(c) < target < a(c+1)`から従う`predecessor_lt_anchor`(crossing直前値はanchor `a(c+1)`より小さい)を束ねると、`CrossingRecoveryInvariant target parent.horizon (a(c+1)) c q r`が成立する。

*nodeへの搭載。* 搭載先nodeは定義上`⟨parent.horizon, a(c), normal, a(c)⟩`なので、node形状の等式は自明(`rfl`)であり、targetの正値性とrecovery不変量とあわせて`CrossingSearchInvariant`の存在文が埋まる。readiness clock `target ≤ parent.horizon + 1`は、parent自身のready crossing証明書(`PermanentTailCrossingCertificate.ready_crossing`)の`horizon_ready`を、nodeがhorizonを共有することを使ってそのまま輸送する。

### `PermanentTailCombinedCertificate.terminalMountedOutcome` (L103)

**主張:** すべてのcombined証明書はmounted outcomeを持つ: 閉じたterminal解析の各枝が、外側探索のsemantic domainのobject(搭載済みready crossing node、semantic child、またはreplay固定点)を手渡す。

**証明:** `terminalHorizonAnchoredOutcome`(`PermanentAboveCorridorLandingHorizon.lean`)の三形を場合分けする。semantic枝とreplay枝はそのまま移送する。fresh landing枝では、horizon境界`nextCrossingTime + 1 < parent.horizon`を仮定としてL25を適用し、得られた`ReadyCrossingSearchInvariant`をlandingデータに添えて`landing_crossing`を構成する。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「landing crossing mount」(history枝をsemantic node搭載へ完了済み)に対応する。上流は`PermanentAboveCorridorLandingHorizon.lean`(horizon境界)、`CrossingRecovery.lean`(`CrossingRecoveryInvariant`)、`CrossingDowncrossRefined.lean`(`ReadyCrossingSearchInvariant`)、`PermanentAboveCorridorPredecessorCrossing.lean`(node形`terminalPredecessorCrossingNode`)である。`PermanentAboveCorridorReplayBoundary.md`以来の課題だった「history辺の先で外側再帰を実際に継続する素材」が、本モジュールでrefined semantic domainの実objectとして確保された。下流では、`PermanentAboveCorridorLandingInstall.lean`が、この搭載nodeへcombined証明書全体を移送して同じterminal解析を再入可能にし、landing crossingが終端の葉ではなく次のparentであることを確定する。
