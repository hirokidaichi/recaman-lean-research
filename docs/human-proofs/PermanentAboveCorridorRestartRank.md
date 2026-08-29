# PermanentAboveCorridorRestartRank

**役割:** 通常のhistory座標とは別に、stationary restart(停留crossingをblockerの初出直前から再開すること)だけが消費する専用のrestart cursorを追加した六成分整礎rankを定義し、blockerのseen予算厳密下降が上向きのphase resetを上書きすることで、eligible predecessor kernelの非進捗残余をstrict anchor growth一形へ縮約する。

## このモジュールの役割

`PermanentAboveCorridorPredecessorCursor.lean`は、eligible(旧crossingが元のdowncross endpoint以後にある)条件下で、blocker predecessorから再選択したcrossingの帰結を、phase進捗・cursor進捗・strict anchor growth・literal stationary(同anchor同時刻)の四形へ分類した。最後のstationary枝を厳密下降にするため、通常のhistory座標をphaseより外側へ移すという素朴な修正は機能しない: 実際のdowncrossがdischargeへ入る際にhistory clockは前へ進み得るので、その並べ方では既存の正当な辺が壊れる。本モジュールの解は、既存座標に手を触れず、cycle一周(crossing/backtrack/discharge)の間は固定され、stationary restartの瞬間にだけ動く専用のrestart cursorを一つ挿入することである。restart時にはhistory clockをblockerの初出時刻`firstTime`からその直前`firstTime − 1`へ引き戻すので、`seenBelowCount`が厳密に下がり(`PermanentAboveCorridorOuterHistory.lean`)、この下降がrestart座標より内側にあるphase rankの上向きreset(discharge 0 → crossing 2)を辞書式に覆い隠す。結果として、eligible kernelに残る非進捗はstrict anchor growth(crossing anchorが厳密に増える枝)だけになる。

## 主要な定義

### `TailRestartCycleSearchNode` (L25)

restart cursor付きのcycle探索node。フィールドは順に、crossing anchor `anchor`、crossing時刻`crossingTime`、restart cursor `restartTime`(stationary restartだけが消費するhistory clock)、phase(`crossing/backtrack/discharge`)、通常のhistory時刻`historyTime`、tail最小値`minimumValue`の六つ。

### `tailRestartCycleRank` (L34)

nodeの六成分rank

```text
(anchor, crossingTime, seenBelowCount target restartTime,
 phase.rank, seenBelowCount target historyTime, minimumValue)
```

外側二成分`(anchor, crossingTime)`は`PermanentAboveCycleExit.lean`のcrossing-time cursorをそのまま埋め込み、第三成分にrestart cursorのseen予算を、その内側に従来のphase・seen・minimumを置く。

### `TailRestartCycleProgress` (L43)

六成分rankの辞書式順序による厳密下降関係。

## 定理と証明

### `natSextLex_wellFounded` (L54)

**主張:** 右結合に六重に入れ子にした自然数の辞書式順序は整礎である。

**証明:** 最外成分の`Nat.lt`の整礎性と、残り五成分の整礎性`natQuintLex_wellFounded`(`PermanentAboveCycleExit.lean`)を`Prod.lexAccessible`で合成する。

### `tailRestartCycleProgress_wellFounded` (L68)

**主張:** restart-cycle rankは整礎である。

**証明:** L54のaccessibilityをrank写像`tailRestartCycleRank`に沿ってnodeへ引き戻す、この系列で標準の議論である。

### `tailRestartCycle_exit_of_cursorProgress` (L89)

**主張:** crossing-time cursorの厳密下降(`TailCrossingCursorProgress`)は、restart座標とhistory座標の値によらず、dischargeからcrossingへの復帰をrestart rankの下降にする。

**証明:** cursor進捗の数値的意味(`tailCrossingCursorProgress_iff`、`PermanentAboveCycleExit.lean`)により、anchorが厳密に下がるか、anchorが等しく時刻が厳密に早いかのいずれかである。前者は第一成分、後者はanchor等式を書き換えたうえで第二成分の辞書式下降になる。どちらの場合も第三成分以降は比較されないので、restart cursorやphase resetの影響を受けない。既存のcursor下降辺がそのまま保存されることを意味する。

### `tailRestartCycle_exit_of_restartSeenDrop` (L109)

**主張:** crossing anchorとcrossing時刻がともに停留していても、restart cursorのseen予算の厳密下降はdischargeからcrossingへの復帰をrank下降にする。すなわちphaseの上向きreset(rank 0 → 2)はrestart座標の下降に覆い隠される。

**証明:** 第一・第二成分が等しいので第三成分`seenBelowCount target restartTime`で比較され、仮定の厳密下降が直ちに辞書式下降を与える。第四成分のphase rankが増加していることは、辞書式順序では第三成分が決着した後なので無関係である。restart cursorをphaseより外側に置いた設計そのものが、この定理の内容である。

### `TerminalBelowPredecessorRestartRankOutcome` (L123)

restart cursor追加後の、eligibleなbelow-target predecessorの最終outcome。constructorは三つ: `phase_progress`(選択crossingが既存の大域`PhaseSearchProgress`を与える)、`restart_cycle_progress`(child node `⟨a crossingTime, crossingTime, firstTime − 1, crossing, firstTime − 1, 0⟩`がparent node `⟨parent.anchorParent, source.oldCrossingTime, firstTime, discharge, firstTime, 0⟩`に対しrestart rankで下降する)、`anchor_growth`(`parent.anchorParent < a crossingTime`という厳密anchor増加のみ)。

### `BelowTargetHistoricalPredecessorCertificate.restartRankOutcome` (L158)

**主張:** 旧crossingのeligibility(`source.downTime + 1 ≤ source.oldCrossingTime`)の下で、equal-anchor earlier-timeとliteral stationaryの両returnはいずれも厳密下降であり、非進捗として残るのはstrict anchor growthだけである。

**証明:** `PermanentAboveCorridorPredecessorCursor.lean`のeligible四分類`eligibleRankOutcome`で場合分けする。

- *phase_progress*はそのまま第一形へ写す。
- *cursor_progress*(anchor下降または同anchorでの早いcrossing時刻)はL89により`restart_cycle_progress`になる。
- *anchor_growth*はそのまま第三形として残す。
- *stationary*(同anchor・同時刻)が本モジュールの核心である。選択crossing証明書の`backtrack`(`PermanentAboveCorridorOuterHistory.lean`のbacktrack証明書)が`seen_gain`、すなわち`seenBelowCount target (firstTime − 1) < seenBelowCount target firstTime`を与える。stationaryの等式でchildのanchorと時刻をparentのそれに書き換えると、childのrestart cursorは`firstTime − 1`、parentのは`firstTime`なので、L109がrank下降を与える。従ってstationaryは`restart_cycle_progress`に吸収される。

こうして、`PermanentAboveHistory.lean`以来の停留残余(child = parentの再生)は、eligibleな設定では初めて無条件に厳密下降となり、rank非進捗の可能性はanchorが数値的に増える一方向だけに絞られた。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「stationary restart rank(stationaryをstrict化済み)」に対応する。入力は`PermanentAboveCorridorPredecessorCursor.lean`のeligible四分類、`PermanentAboveCorridorOuterHistory.lean`のbacktrack証明書(seen_gain)、`PermanentAboveCycleExit.lean`のcrossing-time cursorと五成分整礎性である。残った唯一の非進捗`anchor_growth`は、直接の下流`PermanentAboveCorridorAnchorCandidates.lean`が「anchorはstrict crossing直前値なのでtarget未満、従って`target − anchor`のremaining-gap rankで有限回しか増えられない」ことにより有限rank化する。さらに`PermanentAboveCorridorMasterRank.lean`は、本モジュールのrestart座標を第四成分として七成分master rankへ吸収し、反復kernel全体を単一のwell-founded relationに統合する。
