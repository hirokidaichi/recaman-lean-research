# PermanentAboveCorridorPredecessorCursor

**役割:** blocker predecessorから選んだcrossingを、位相ランクに加えてcrossing-time cursor(`(anchor, crossingTime)`辞書式)でも測り、equal-anchorでも時刻が早ければ五成分cycle rankを下降させる。一般残余はgrowth/chronologyの二形、旧crossingがeligibleならgrowth/literal stationaryの二形へ縮約する。

## このモジュールの役割

`PermanentAboveCorridorPredecessorCrossing.lean`は、below-target predecessorから再選択したcrossing childの残余を「anchor非減少」一つに絞った。しかし通常の四成分位相ランクは、horizonを固定するとcrossing predecessor anchorしか見えない。一方`PermanentAboveCycleExit.lean`のpermanent-tail cursor rankは、外側比較を`(anchor, crossingTime)`の辞書式量へ精密化しており、anchorが等しくてもcrossing時刻が旧crossingより早ければ進捗になる。本モジュールは両方のランクを順に照会するcombined outcomeを定義し、predecessor crossingのequal-anchor・earlier-time枝を既存の`TailCrossingCursorProgress`へ接続する。これによりdischargeからcrossingへ戻る辺が五成分cycle rank上で下降することが示され、chronology仮定なしの残余は「strict anchor growth」と「同anchorで時刻が早くない」の二形になる。さらに旧crossingが元のdowncross endpoint以後にある(eligible)なら、canonical性が新crossing ≤ canonical return ≤ 旧crossingを与えるため、後者の残余は同一anchor・同一時刻のliteral stationary(文字どおりの停留)へ縮む。

## 主要な定義

### `TerminalBelowPredecessorCombinedRankOutcome` (L23)

位相ランクとcursorランクを両方照会した後の四分岐を表す帰納型。

- `phase_progress`: `PhaseSearchProgress`(四成分位相ランクの厳密下降)。
- `cursor_progress`: `TailCrossingCursorProgress ⟨a(crossingTime), crossingTime⟩ ⟨parent.anchorParent, source.oldCrossingTime⟩`(anchor同値でもcrossing時刻の厳密な前進で下降する辞書式cursorの辺)。
- `anchor_growth`: strictなanchor成長`parent.anchorParent < a(crossingTime)`。
- `same_anchor_not_earlier`: `a(crossingTime) = parent.anchorParent`かつ`source.oldCrossingTime ≤ crossingTime`というchronology残余。

### `TerminalBelowPredecessorEligibleRankOutcome` (L121)

旧crossingのchronological eligibility(`source.downTime + 1 ≤ source.oldCrossingTime`、旧crossingが元のdowncross endpoint以後にあること)を仮定した場合の四分岐。最初の三constructorは上と同一で、最後だけが`stationary`(`a(crossingTime) = parent.anchorParent`かつ`crossingTime = source.oldCrossingTime`)というliteralな一致になる。

## 定理と証明

### `BelowTargetHistoricalPredecessorCertificate.combinedRankOutcome` (L63)

**主張:** 選択されたblocker crossingは、二つの既存rankのいずれかを下降させるか、正確なgrowth/chronology kernelに達する。

**証明:** `crossingRankOutcome`(前モジュール)を場合分けする。`refined_progress`枝はそのまま`phase_progress`。`anchor_growth`枝(anchor非減少)では、まずstrictな成長かどうかを見る。strictなら`anchor_growth`。等しい場合、`crossingTime < source.oldCrossingTime`かどうかを見る。早ければ、`tailCrossingCursorProgress_iff`の第二選択肢(anchor同値かつ時刻の厳密下降)でcursorの辺を組み、`cursor_progress`。早くなければ`same_anchor_not_earlier`をliteralに返す。四枝は網羅的である。

### `TerminalBelowPredecessorCrossingCertificate.cursorCycleProgress` (L96)

**主張:** blocker predecessor crossingからのcursor progressは、既存の五成分cycle rank(`(anchor, crossingTime, phase, seenBelowCount, tailMinimum)`辞書式)のdischargeからcrossingへの上向き辺を閉じる。すなわち任意のhistory時刻成分・minimum成分に対して、child(phase `crossing`)からparent(phase `discharge`)への`TailCursorCycleProgress`が成り立つ。

**証明:** 五成分rankの外側二成分はまさに`(anchor, crossingTime)`のcursorであり、`tailCursorCycle_exit_of_cursorProgress`(`PermanentAboveCycleExit.lean`)がcursor辺をそのままcycle rankの辺へ持ち上げる。phaseがdischargeからcrossingへ上がる(phase成分は増える)にもかかわらず、より外側のcursor成分が先に下降するため辞書式順序で厳密に小さくなる。

### `BelowTargetHistoricalPredecessorCertificate.eligibleRankOutcome` (L161)

**主張:** 旧crossingのeligibilityの下では、chronology残余は正確な等式になる。すなわち残余は同一anchor・同一crossing時刻のliteral stationaryに限る。

**証明:** L63のcombined outcomeを場合分けし、最初の三枝はそのまま移送する。`same_anchor_not_earlier`枝では、eligibility `downTime + 1 ≤ oldCrossingTime`にdischarge証明書の`returnTime_le_oldCrossingTime`を適用して`returnTime ≤ oldCrossingTime`を得る。一方、選択されたcrossingはcanonical性から`crossingTime ≤ returnTime`(前モジュールの`crossingTime_le_return`)。合わせて`crossingTime ≤ oldCrossingTime`であり、残余の`oldCrossingTime ≤ crossingTime`と挟んで`crossingTime = oldCrossingTime`。よって`stationary`が成立する。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「blocker predecessor cursor(二rank統合・kernel縮約済み)」に対応する。上流は`PermanentAboveCorridorPredecessorCrossing.lean`(crossing証明書とrank outcome)と`PermanentAboveCycleExit.lean`(crossing-time cursorと五成分cycle rank)である。ここで確定した「eligible時の非進捗はstrict anchor growthとliteral stationaryのみ」という分類は、`PermanentAboveCorridorRestartRank.lean`がstationaryをblocker初出直前へのseen-budget下降で上書きしてanchor growth一形に絞り、`PermanentAboveCorridorAnchorCandidates.lean`がそのgrowthを`List.range target`上の有限rankへ変換する、という後続二段の入力になる。すなわち本モジュールは、blocker predecessor経由のdischarge脱出を「どのwell-founded量が下がるか」の言葉で完全に台帳化する中継点である。
