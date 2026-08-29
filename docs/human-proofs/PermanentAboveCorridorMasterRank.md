# PermanentAboveCorridorMasterRank

**役割:** installed-cycle反復のkernelを、missing履歴予算・残りanchor gap・crossing時刻・restart seen予算・一方向phase・局所seen予算・tail最小値の七成分辞書式rankへ統合し、chronology mismatch、strict anchor growth、equal-anchorの早いcrossing、stationary restartのすべてを単一のwell-founded relationの厳密辺にする。逆向きのstrict anchor下降は反復ではなく既存の大域`PhaseSearchProgress`へのexitとして分離する。

## このモジュールの役割

ここまでの解析で、installed cycle(selected crossingを親としてdischargeを再構成する反復)の各枝には個別のrank辺が用意された: chronology mismatchはmissing予算の下降(`PermanentAboveCorridorChronologyRank.lean`)、stationary restartはrestart cursorのseen下降(`PermanentAboveCorridorRestartRank.lean`)、strict anchor growthはremaining gap `target − anchor`の下降(`PermanentAboveCorridorAnchorCandidates.lean`)、equal-anchorの早いcrossingはcrossing-time cursorの下降(`PermanentAboveCycleExit.lean`)である。しかしこれらは別々の関係であり、反復全体の停止性を一度に述べられない。統合の障害はanchorの二方向性である: crossing anchorの厳密な「下降」は即時に大域phase rankのexitであり、反復の内側で起こるのは逆向きの「増加」である。同じanchor座標を一つのrankに素朴に入れると、この二方向は両立しない。本モジュールはphase exitをrankの外に分離したうえで、増加方向を`target − anchor`という残りgapに読み替え、七つの座標を辞書式に並べた`TailInstalledCycleProgress`を定義する。全反復枝はこの単一関係で厳密に下降し、関係自体は整礎である。

## 主要な定義

### `TailInstalledCycleSearchNode` (L31)

installed-cycle探索のnode。フィールドは順に、chronology cursorとしてのhistory clock `budgetTime`、crossing anchor `anchor`、crossing時刻`crossingTime`、restart cursor `restartTime`、phase(`crossing/backtrack/discharge`)、局所history時刻`historyTime`、tail最小値`minimumValue`の七つ。

### `tailInstalledCycleRank` (L41)

nodeの七成分rank

```text
(missingBelowCount target budgetTime,
 target − anchor,
 crossingTime,
 seenBelowCount target restartTime,
 phase.rank,
 seenBelowCount target historyTime,
 minimumValue)
```

第二成分は`terminalCrossingAnchorRank`(`PermanentAboveCorridorAnchorCandidates.lean`)であり、anchorそのものではなく残りgapを測ることで「anchor増加 = rank下降」の向きに揃えている。

### `TailInstalledCycleProgress` (L51)

七成分rankの辞書式順序による厳密下降関係。

## 定理と証明

### `natSeptLex_wellFounded` (L61)

**主張:** 右結合に七重に入れ子にした自然数の辞書式順序は整礎である。

**証明:** 最外成分の`Nat.lt`の整礎性と、残り六成分の整礎性`natSextLex_wellFounded`(`PermanentAboveCorridorRestartRank.lean`)を`Prod.lexAccessible`で合成する。

### `tailInstalledCycleProgress_wellFounded` (L75)

**主張:** installed-cycle master rankは整礎である。

**証明:** L61のaccessibilityをrank写像`tailInstalledCycleRank`に沿ってnodeへ引き戻す標準的な議論である。

### `tailInstalledCycleProgress_of_historyDrop` (L97)

**主張:** chronology cursorでのmissing予算の厳密下降は、内側六成分の値によらずmaster rankの下降である。

**証明:** 最外成分の下降として直ちに辞書式下降。strict history進捗がinstalled-cycleの他のすべての座標を支配することを意味する。

### `tailInstalledCycleProgress_of_anchorGrowth` (L113)

**主張:** chronology cursorを固定したとき、strictなanchor増加(`parentAnchor < childAnchor`、かつchild anchorはtarget未満)は第二成分の残りgapを下げる。

**証明:** `childAnchor < target`と`parentAnchor < childAnchor`から`target − childAnchor < target − parentAnchor`(`Nat.sub_lt_sub_left`)。第一成分が等しいので第二成分の下降が辞書式下降を与える。child anchorのtarget未満性は、後で適用する際、crossing直前値がweak upcrossingの定義によりtarget未満であることから供給される。

### `tailInstalledCycleProgress_of_earlierCrossing` (L130)

**主張:** 予算とanchorが等しく、crossing時刻が厳密に早いなら、第三成分の下降としてmaster rankが下がる。

**証明:** 辞書式順序の第三成分の直接構成。

### `tailInstalledCycleProgress_of_restartSeenDrop` (L146)

**主張:** 外側三成分(予算・anchor・crossing時刻)が停留していても、restart cursorのseen予算の厳密下降は第四成分の下降としてmaster rankを下げ、内側のphase上向きresetを覆い隠す。

**証明:** 辞書式順序の第四成分の直接構成。`PermanentAboveCorridorRestartRank.lean`のL109と同じ設計原理を七成分版に埋め込んだものである。

### `TerminalBelowPredecessorMasterRankOutcome` (L163)

eligibleなbelow-target predecessorのmaster統合outcome。constructorは二つ: `phase_exit`(選択crossingが既存の大域`PhaseSearchProgress`を与える — anchorの厳密下降はここに入る)と、`master_progress`(child node `⟨parent.horizon, a crossingTime, crossingTime, firstTime − 1, crossing, firstTime − 1, 0⟩`がparent node `⟨parent.horizon, parent.anchorParent, source.oldCrossingTime, firstTime, discharge, firstTime, 0⟩`に対しmaster rankで下降する)。両nodeのchronology cursorは同じ`parent.horizon`である点に注意する。

### `BelowTargetHistoricalPredecessorCertificate.masterRankOutcome` (L192)

**主張:** 旧crossingのeligibility(`source.downTime + 1 ≤ source.oldCrossingTime`)の下で、すべてのeligibleなbelow-target predecessorは、既存の大域phase rankでexitするか、installed-cycle master rankを厳密に下降するかのいずれかである。

**証明:** `PermanentAboveCorridorPredecessorCrossing.lean`の`crossingRankOutcome`(refined_progress / anchor_growth)で場合分けする。

*refined_progress*(新crossing anchorが旧anchorより厳密に小さい)は、そのまま大域`PhaseSearchProgress`なので`phase_exit`。

*anchor_growth*(anchor非減少)は三つに細分する。(i) 厳密増加`parent.anchorParent < a crossingTime`なら、crossing直前値のtarget未満性とあわせてL113のanchor-growth辺が使え、`master_progress`。(ii) anchorが等しく`crossingTime < source.oldCrossingTime`なら、anchor等式を書き換えてL130の第三成分下降で`master_progress`。(iii) anchorが等しくcrossing時刻も早くないなら、eligibilityから`returnTime ≤ oldCrossingTime`(`PermanentAboveCycleExit.lean`)、選択crossingは`crossingTime ≤ returnTime`なので、はさみうちで`crossingTime = oldCrossingTime`、すなわちliteral stationaryである。このときblockerのbacktrack証明書の`seen_gain`(restart cursorが`firstTime`から`firstTime − 1`へ動く際のseen厳密下降、`PermanentAboveCorridorOuterHistory.lean`)がL146の第四成分下降を与え、やはり`master_progress`。

従って非進捗の残余は存在せず、restart rank(六成分)で三形に分かれていたoutcomeが二形へ縮む。

### `TerminalSelectedCrossingChronologyProgressCertificate.masterProgress` (L246)

**主張:** installed next dischargeのchronology mismatchも、同じmaster rankの辺である — その最外のhistory座標を通じて。child nodeのchronology cursorは次のdowncross endpoint `next.discharge.downTime + 1`、parent nodeのそれはselected時刻`crossingTime`であり、他の六成分は同一で、rankは厳密に下がる。

**証明:** mismatch証明書の`missing_drop`(`PermanentAboveCorridorChronologyRank.lean`)をL97に渡すだけである。これにより、eligible側の三辺とmismatch側の一辺が、名実ともに同一のwell-founded relationの上に載る。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「installed master rank(反復kernelを一relationへ統合済み)」に対応する。入力は`PermanentAboveCorridorPredecessorCrossing.lean`のcrossing分類、`PermanentAboveCorridorOuterHistory.lean`のbacktrack証明書、`PermanentAboveCorridorRestartRank.lean`の六成分整礎性、`PermanentAboveCorridorAnchorCandidates.lean`のremaining-gap座標、`PermanentAboveCorridorChronologyRank.lean`のmismatch下降である。直接の下流は`PermanentAboveCorridorInstalledStep.lean`で、terminal residual tree全体をこのmaster pipelineへ接続し、さらに`PermanentAboveCorridorTerminalProgress.lean`が最終的に「target出現・strict history・semantic phase・installed master」の四形へ平坦化する際、installed master枝の進捗はすべて本モジュールの`TailInstalledCycleProgress`で測られる。anchorの厳密下降を大域phase exitとして反復の外に置くという分離は、二方向のanchor移動を単一rankで扱えないという構造的制約への、このプロジェクトにおける最終的な解答である。
