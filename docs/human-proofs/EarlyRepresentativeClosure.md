# EarlyRepresentativeClosure

**役割:** early representativeの `legal_downcross` 残余を将来のcrossing recoveryで閉じ、残余を強制加算分岐(forced below-candidate)ひとつに縮約する。

## このモジュールの役割

`EarlyRepresentative.classify` が残した `legal_downcross` 残余は、`代表時刻 + 1` にtarget未満の実軌道値をすでに持っている。target未満の点から出発すれば将来必ず**弱上方crossing**(target未満の値から強制加算でtarget以上へ跳ぶ遷移)が存在するので、そのcrossingを既存のsemantic状態 `crossing_recovery` に格納すればよい。履歴horizonは `max(node.horizon, crossingTime + 2)` へ拡大する。履歴予算(`missingBelowCount`)の単調性がこの拡大を許し、pre-crossing値はtarget未満、したがって旧代表anchorより真に小さいから、四成分rankのanchor成分が真の下降を与える。この閉包の後、early-representative分類に残る残余は、既出のtarget未満候補にblockされた強制加算分岐だけになる。

## 主要な定義

### `EarlyRepresentativeForcedResidual` (L102)

legal downcross閉包後に残る唯一のearly-representative残余。constructorは `forced_below_candidate` のみで、`EarlyRepresentativeResidual` の同名constructorと同一のデータ(証明書、候補の式・正値性・target未満・既出性、減算不能、強制加算の値の式)を保持する。

### `EarlyClosureInvariant` (L120)

legal downcross閉包後の成功domain: `EarlyRefinedInvariant ∨ CrossingSearchInvariant`。すなわちextended-history node、current/debt node、そして本モジュールが新たに生成するcrossing recovery nodeである。

## 定理と証明

### `EarlyRepresentativeResidual.legalDowncross_phaseSemanticStep` (L27)

**主張:** legal downcross残余のデータ(early証明書と着地 `a(代表時刻 + 1) < target`)から、目標の出現、または `CrossingSearchInvariant`・semantic不変量・親からの真のrank下降を同時に持つchildが得られる。残余に格納された2つの予算不等式は使わない(それらは代表局所の下降が輸送できない理由の説明であり、本定理は別の辺を使う)。

**証明:** target未満の点 `代表時刻 + 1` から `exists_weakUpcrossingStep_from_below` で弱上方crossingの時刻 `crossingTime` を取る: `a(crossingTime) < target ≤ a(crossingTime + 1)` かつ次遷移は強制加算である。

- 目標が時刻 `crossingTime` までに既出なら、その出現証人を返す。
- `a(crossingTime + 1) = target` なら、それが証人である。
- 残るのは真の横断の場合である。強制加算の値の式と合わせ `DebtCrossing` が成り立ち、post-state `crossingTime + 1` の商・剰余座標を取る。childを

  `⟨max(node.horizon, crossingTime + 2), a(crossingTime), normal, a(crossingTime)⟩`

  と定める。crossingは新horizonより真に前にあり、目標はcrossing前に未出、pre-crossing値は `a(crossingTime) < target ≤ a(代表時刻) = 旧anchor` を満たす。これらが `CrossingRecoveryInvariant` の全フィールドを埋め、childは `CrossingSearchInvariant` を持ち、semantic不変量の `crossing_recovery` 枝に入る。rank下降は、horizon拡大による履歴予算の非増加とanchorの真の下降(`a(crossingTime) < a(代表時刻)`)から `phaseSearchProgress_of_horizonAndAnchor` で従う。

### `EarlyRepresentativeCertificate.refinedStep_or_forcedResidual` (L128)

**主張:** legal downcrossを除去した精密化されたearly-representative分類: 任意のearly証明書について、目標の出現、`EarlyClosureInvariant` と広いsemantic証明書の**両方**を持つchildへの真の下降、または `EarlyRepresentativeForcedResidual`、の三択が成り立つ。

**証明:** `classify` を実行して各分岐を写す。出現はそのまま。forward childはextended-history側、debt childはcurrent/debt側の選言肢に入る(どちらもsemantic証明書とprogressを分類が保持している)。`legal_downcross` 残余には前定理を適用し、出現でなければcrossing childを `CrossingSearchInvariant` 側の選言肢として返す。`forced_below_candidate` 残余はそのまま新残余へ写す。各成功childが機構別のrefined不変量と広いsemantic証明書を同時に保持する点が、後のrefined domain統合(`ExtendedHistoryDirectRefined`)の準備になっている。

### `earlyRepresentative_five_three_crossingClosure` (L171)

**主張:** target 5の具体的なearly representative(親 `⟨4, a(3), normal, a(3)⟩`、`a(3) = 6`)は、実在する弱いcrossing `a(4) = 2 → a(5) = 7` を通じて閉じる。child `⟨6, a(4), normal, a(4)⟩` は `CrossingSearchInvariant`・semantic不変量・親からの真のrank下降をすべて持つ。

**証明:** recovery horizonは6、crossing時刻は4である。目標5はcrossing前の履歴 `{0, 1, 3, 6, 2}` に未出、時刻5の遷移は強制加算(`2 − 5` は非正)、`a(5) = 2 + 5 = 7 > 5` は真の横断、座標は `7 = 5·1 + 2` で `(q, r) = (1, 2)`、pre-crossing anchor 2は旧anchor 6より真に小さい。各条件はLeanカーネルの `decide` で数値検証する。

## 全体の中での位置づけ

証明地図の「意味的探索domain: early representativeのcrossing recovery接続」に対応する。`EarlyRepresentative` の2残余のうち片方をここで閉じ、もう片方(forced below-candidate)は `EarlyForcedCandidateClosure` が同じ将来crossing構成の変種(候補の過去の出現点から代表時刻までの区間のcrossing)で閉じる。両者を合流させるのが `EarlyRepresentativeComplete` であり、さらに時計情報を保持したrefined domain上の対応構成が `ExtendedHistoryDirectRefined` の `legalDowncross_refinedStep` である。
