# PermanentAboveCorridorSuccessorRank

**役割:** installed successor(selected crossingを親に再構成した次のdischarge)へ実際に輸送される座標 — 共有history horizonのmissing予算・installed crossing anchorの残りgap・old crossing cursor — だけを三成分のdischarge-level rank `terminalDischargeIterationRank`として取り出し、successorがこのrankを厳密に下げるか、anchorとcursorがともに一致してrankが文字どおり不動になるexact replay固定点であるかをtotalに分類する。

## このモジュールの役割

`PermanentAboveCorridorMasterRank.lean`の七成分master辺は反復の全枝を一つのwell-founded relationに載せたが、そのnodeの内側cursor(restart cursor、局所history時刻)は特定の一回の解析のblocker初出時刻`firstTime`に言及している。この量はsuccessor discharge(`PermanentAboveCorridorTerminalSuccessor.lean`が構成する次のdischarge証明書)へは持ち越されないため、連続する二本のmaster辺は「前の辺のchild = 次の辺のparent」という形で連結するとは限らない。本モジュールは反復の実行時に確実に輸送される座標だけに注目する。installationで固定されるのは、共有されるhistory horizon(のmissing予算)、installed crossing anchor(の残りgap `target − anchor`)、そして次のdischarge証明書に型として記録されるold crossing時刻の三つであり、いずれもdischarge証明書そのものから読み出せる。これを辞書式に並べたdischarge-level rankの上では、installed successorはanchor growthまたはequal-anchorの早いcrossingで厳密に下降し、下降しない唯一の場合はanchorとcrossing時刻がともに親を再現するexact replayである。replayではrankの等式が成り立つことまで保持し、全構成chain(blocker → predecessor → crossing → install → next discharge)を型付き証明書として残す。こうしてterminal解析の反復は「大域辺・strict下降・literal固定点」の三択へ、dischargeを単位として初めて連結可能な形で縮約される。

## 主要な定義

### `terminalDischargeIterationRank` (L25)

discharge証明書`source`(親node `parent`上)の輸送可能な外側測度

```text
(missingBelowCount target parent.horizon,
 target − parent.anchorParent,
 source.oldCrossingTime)
```

第二成分は`terminalCrossingAnchorRank`(`PermanentAboveCorridorAnchorCandidates.lean`)であり、anchor増加が下降になる向きに揃えてある。三成分ともdischarge証明書と親nodeだけから決まり、blocker解析の内部cursorに依存しない。

### `TerminalDischargeIterationProgress` (L35)

異なる親nodeに載っていてもよい二つのdischarge証明書の間の、上記三成分rankの辞書式厳密下降。

### `TerminalExactDischargeReplayCertificate` (L102)

exactなdischarge-level replayの証明書。blocker以降の全数値パラメータ(freshEndpoint、candidate、firstTime、predecessor、predecessorFirstTime、crossingTime、quotient、remainder)と全構成chain(outer historical blocker、below-target predecessor、選択crossing、install、next discharge)に加えて、`a crossingTime = parent.anchorParent`(anchor再現)、`crossingTime = source.oldCrossingTime`(cursor再現)、およびrankの等式`terminalDischargeIterationRank target next.discharge = terminalDischargeIterationRank target source`を保持する。

### `PermanentTailTerminalIterationOutcome` (L131)

discharge-levelで測ったterminalのtotal outcome。constructorは五つ: `target_occurs`(targetの出現witness)、`history_progress`(`TerminalChronologyHistoryProgress`によるmissing予算の厳密下降)、`semantic_progress`(意味的不変量付きchildへの既存`PhaseSearchProgress`辺)、`iteration_progress`(installed node上のsuccessor discharge `next`、`next.oldCrossingTime = crossingTime`という型付きcursor記録、およびiteration rankの厳密下降)、`exact_replay`(上記replay証明書)。

## 定理と証明

### `terminalDischargeIterationProgress_of_anchorGrowth` (L48)

**主張:** horizonが共有され(`childParent.horizon = sourceParent.horizon`)、childのanchorがtarget未満で、sourceのanchorより厳密に大きいなら、childのdischargeはsourceのdischargeに対しiteration rankで厳密に下降する。

**証明:** 第一成分はhorizon等式によって等しい。第二成分は`childAnchor < target`と`sourceAnchor < childAnchor`から`target − childAnchor < target − sourceAnchor`(`Nat.sub_lt_sub_left`)であり、辞書式順序の第二成分で決まる。

### `terminalDischargeIterationProgress_of_earlierCrossing` (L67)

**主張:** horizonとanchorがともに共有され、childのold crossing cursorが厳密に早いなら、第三成分の下降としてiteration rankが下がる。

**証明:** 前二成分を等式で書き換え、第三成分`oldCrossingTime`の厳密下降を辞書式に埋め込む。

### `terminalDischargeIterationRank_eq` (L84)

**主張:** horizon・anchor・old crossing cursorの三つがすべて等しければ、二つのdischargeのiteration rankは等しい — 正確なrank固定点である。

**証明:** rankの定義を展開して三つの等式を代入するだけである。この等式が、replay証明書の`rank_eq`フィールドの供給源になる。

### `PermanentTailDischargeReturnCertificate.terminalIterationOutcome` (L162)

**主張:** すべてのterminal dischargeは、確立済みの大域辺(target出現・history進捗・semantic進捗)を発火させるか、輸送可能なiteration rankを厳密に下降するsuccessor dischargeを引き渡すか、さもなくばexact rank replayである。

**証明:** `PermanentAboveCorridorFiniteClosure.lean`の`terminalFiniteClosedOutcome`(finite数値枝がFalseとして排除済みのtotal outcome)で場合分けする。

*history_progress*はそのまま第二形へ写す。*immediate_semantic*の内側は、target出現か、即時谷のcanonical coverageに由来するsemantic step(比較元は`targetStartNode (downTime + 2)`)である。*historical_complete*の内側のうち、target出現はそのまま、early step / ready step(`PermanentAboveCorridorAboveClosure.lean`のabove-target predecessor閉包)はそれぞれhistorical / current predecessor nodeを比較元とするsemantic進捗へ写す。

核心はbelow_master枝である。まず旧crossingのeligibility `source.downTime + 1 ≤ source.oldCrossingTime`で場合分けする。

*eligibleでない場合。* `oldCrossingTime < downTime + 1`であり、downcross endpoint `a (downTime + 1)`はtarget未満の値の初出なので、`missingBelowCount_strict_of_firstAt`によりold crossing時刻からendpointへmissing予算が厳密に下がる。これは`history_progress`である(`PermanentAboveCorridorChronologyRank.lean`のmismatch論法のdischarge-level版)。

*eligibleな場合。* `PermanentAboveCorridorPredecessorCrossing.lean`の`crossingRankOutcome`で場合分けする。

- *refined_progress*(新anchorが厳密に小さい)は、選択crossingのrefined証明書を`PhaseSemanticInvariant`へ持ち上げ、`semantic_progress`とする。
- *anchor_growth*(anchor非減少)では、まず選択crossingから`install`(`PermanentAboveCorridorSelectedInstall.lean`)を作り、その`exists_nextDischarge`からsuccessor discharge `next`を取り出す。`next`の親はdefinitionallyにinstalled node `terminalPredecessorCrossingNode parent crossingTime`であり、そのhorizonは`parent.horizon`、anchorは`a crossingTime`なので、iteration rankの比較に必要なhorizon共有は定義的等式(`rfl`)で済む。三分する:
  1. 厳密増加`parent.anchorParent < a crossingTime`なら、crossing直前値のtarget未満性とあわせてL48が`iteration_progress`を与える。
  2. anchorが等しく`crossingTime < source.oldCrossingTime`なら、`next.old_crossing_time_eq`でchildの第三成分を`crossingTime`に書き換え、L67で`iteration_progress`。
  3. anchorが等しくcrossing時刻も早くないなら、eligibilityから`returnTime ≤ oldCrossingTime`、選択の`crossingTime ≤ returnTime`とあわせて`crossingTime = oldCrossingTime`。すなわちanchorとcursorの両方が親を再現するliteral replayであり、L84でrank等式を作り、全構成chainを詰めた`TerminalExactDischargeReplayCertificate`として`exact_replay`を返す。

restart rank(`PermanentAboveCorridorRestartRank.lean`)ではstationary枝をrestart cursorのseen下降で「進捗」にできたが、そのcursorはsuccessorへ輸送されない。本定理はあえてその辺を使わず、輸送可能な三成分だけで測ることで、非進捗を偽装のないliteral固定点として型に露出させている。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「discharge iteration rank(successor反復を三成分rankへ縮約済み)」に対応し、corridorファミリーの現時点での最終モジュールである(`Recaman.lean`から直接importされる)。入力は`PermanentAboveCorridorFiniteClosure.lean`のfinite-freeなtotal outcome、`PermanentAboveCorridorTerminalSuccessor.lean`と`PermanentAboveCorridorSelectedInstall.lean`のnext discharge構成、`PermanentAboveCorridorPredecessorCrossing.lean`のcrossing分類、`PermanentAboveCorridorAnchorCandidates.lean`のanchor gap座標である。master rank(`PermanentAboveCorridorMasterRank.lean`)が一回の解析の内部を閉じたのに対し、本モジュールは解析から解析への連結可能性を初めてdischarge単位のrankとして与えた。第一・第二成分は有限(missing予算はtarget以下、anchor gapもtarget以下)なので、strict下降は有限回しか続かない。残る`exact_replay`は、`PermanentAboveCorridorExactRevisit.lean`系列の有限key選択が扱うexact revisitのdischarge-level対応物であり、この固定点を排除または矛盾へ導くことが、恒久tail仮説の反証 — ひいてはtail return経由の全射性予想 — へ向けた次の未証明点である。
