# PermanentAboveCorridorOuterHistory

**役割:** 正のterminal historical blocker(終端の減算を妨げた既出値)の初出時刻が必ず正であることを使い、その直前clockへ戻るbacktrackingが履歴予算の双対`seenBelowCount`を厳密に下げること、すなわち既存tail-cycle rankの正当なbacktrack辺になることを証明し、非clock残余三形を位置感応的なrank outcomeへ分類する。

## このモジュールの役割

`PermanentAboveCorridorBlocker.lean`は、terminal crossingの最終減算が失敗した理由のひとつとして、正の減算candidate `a returnTime − (returnTime+1)`が既出であり、その初出時刻`firstTime`が`returnTime`より厳密に前にあるというhistorical blockerを抽出した。`PermanentAboveCorridorCandidates.lean`は有限clock帯の枝を分離し、残る非clock残余を三形(immediate insufficient、immediate historical、finite outer blocker)に絞った。本モジュールはこのhistorical blockerを数値的なrank辺へ変換する。鍵は、blocker candidateが正であることから初出時刻`firstTime`が0でない(時刻0の値は0だから)という一点である。すると`firstTime − 1 < firstTime`の間でこのtarget未満の値がちょうど初出するので、`missingBelowCount`は`firstTime − 1`から`firstTime`へ厳密に下がり、双対の`seenBelowCount`は厳密に上がる。読み替えると、history clockを`firstTime`からその直前`firstTime − 1`へ逆向きに選べば、`PermanentAboveCycleRank.lean`の四成分tail-cycle rankのbacktrack辺として厳密下降になる。残る義務はこの数値predecessorを意味的探索nodeとして実際に選ぶprovenanceであり、それは後続の`PermanentAboveCorridorBlockerGeneration.lean`以降が引き受ける。

## 主要な定義

### `TerminalOuterHistoricalBlockerCertificate` (L21)

immediate枝とfinite枝に共通するouter blockerのprovenance。最終fresh endpoint証明書(`PermanentAboveCorridorBalance.lean`)、historical blocker証明書(candidate値、初出時刻`firstTime`、target・predecessor未満性)、および`firstTime ≤ freshEndpoint`(blockerがfresh endpoint以前に生まれたこと)を束ねる。

### `TerminalHistoricalBacktrackCertificate` (L32)

正のhistorical blockerがその初出直前clockで露出する局所的なdual予算辺。blocker証明書に加え、`0 < firstTime`、`firstTime − 1 < firstTime`、missing予算の厳密下降`missingBelowCount target firstTime < missingBelowCount target (firstTime − 1)`、およびseen予算の厳密増加`seenBelowCount target (firstTime − 1) < seenBelowCount target firstTime`を保持する。

## 定理と証明

### `TerminalHistoricalBlockerCertificate.backtrackCertificate` (L45)

**主張:** すべての正のhistorical blockerは初出時刻が非零であり、局所的なdual履歴予算辺(backtrack証明書)を供給する。

**証明:** まず`firstTime = 0`と仮定すると、初出の定義から`a 0 = candidate`だが、`a 0 = 0`でありcandidateは正なので矛盾。よって`0 < firstTime`。次に、candidateはtarget未満の値で時刻`firstTime`に初出するから、`missingBelowCount_strict_of_firstAt`(target未満の値の初出をまたぐとmissing予算が厳密に下がる、`HistoryBudget.lean`)を区間`firstTime − 1 < firstTime`に適用してmissing予算の厳密下降を得る。seen予算の厳密増加は分割等式`seen + missing = target`による双対化(`seenBelowCount_strict_of_missingBelowCount_strict`、`PermanentAboveCanonical.lean`)である。

### `TerminalHistoricalBacktrackCertificate.tailCycleProgress` (L74)

**主張:** この局所blocker証明書は、anchorとtail最小値をどう固定しても、既存permanent-tail cycle rankの正確なbacktrack辺である: node `⟨anchor, backtrack, firstTime, minimumValue⟩`から`⟨anchor, backtrack, firstTime − 1, minimumValue⟩`への`TailCycleProgress`が成り立つ。

**証明:** anchorとphase(ともにbacktrack)が等しいので、四成分辞書式rankは第三成分`seenBelowCount`で比較され、backtrack証明書の`seen_gain`がちょうどその厳密下降(子のhistory時刻`firstTime − 1`でのseenが親の`firstTime`でのseenより小さい)を与える(`tailCycleProgress_backtrack_of_seenDrop`、`PermanentAboveCycleRank.lean`)。

### `TerminalHistoricalBacktrackCertificate.tailCycleProgress_of_selected` (L87)

**主張:** 明示的な選択境界: 次のhistorical clockとしてblockerの初出直前`firstTime − 1`を選ぶなら、既存cycle rankは厳密に下降する。

**証明:** 選択の等式を代入してL74に帰着する。数値的なrank辺は常に利用可能であり、残っているのは対応する意味的探索nodeを構成すること — これがouter selectionの未証明義務である — をこの定理は型として明示している。

## 定理と証明(残余分類)

### `PermanentTailTerminalNonClockRankOutcome` (L100)

三つの非clock残余に対する位置感応的なrank outcome。constructorは:

1. `immediate_insufficient`: 即時谷かつ数値的不足証明書(`a returnTime ≤ returnTime + 1`帯)。rank辺なしの純数値残余。
2. `original_history_blocker`: `firstTime ≤ source.downTime + 1`(blockerが元のdowncross endpoint以前に生まれた)場合。outer blocker証明書とbacktrack証明書を保持する。
3. `forward_budget_progress`: `source.downTime + 1 < firstTime`の場合。blockerの初出が元のendpointより後なので、前向きにもmissing予算が`downTime + 1`から`firstTime`へ厳密に下がることを併せて保持する。

### `PermanentTailTerminalNonClockResidual.rankOutcome` (L132)

**主張:** 非clock残余(`PermanentAboveCorridorCandidates.lean`の三constructor)は、immediate数値障害、original outer-history blocker、またはstrict forward履歴予算進捗のいずれかであり、historicalな二枝はどちらも局所tail-cycle backtrack辺を併せて露出する。

**証明:** 残余のconstructorごとに処理する。

*immediate_insufficient*はそのまま第一形へ写す。

*immediate_historical*(即時谷+blocker、`firstTime < downTime + 1`)では、fresh endpointとしてdowncross endpoint `downTime + 1`を谷証明書から構成し(`PermanentAboveCorridorBalance.lean`のimmediate枝と同じ組み立て)、outer blocker証明書を束ねる。位置条件は仮定`firstTime < downTime + 1`から自動的に`original_history_blocker`枝であり、backtrack証明書はL45で作る。

*finite_outer_blocker*(全強制加算窓+blocker、`firstTime ≤ terminalEndpoint`)では、fresh endpointとして窓のterminal endpointを窓のsuffix証明書から構成する。そのうえで`firstTime`と`downTime + 1`の大小で場合分けし、前または同時なら`original_history_blocker`、後なら`missingBelowCount_strict_of_firstAt`を区間`downTime + 1 < firstTime`に適用して前向き予算下降を得て`forward_budget_progress`とする。いずれの枝もL45のbacktrack証明書を添える。

immediate谷ではfresh endpoint = returnであり、blockerの初出は必ずreturnより前なので、immediate枝が常にoriginal(outer history)側に落ちることがこの場合分けから見て取れる。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「outer historical blocker(数値rank edgeまで接続済み)」に対応する。入力は`PermanentAboveCorridorCandidates.lean`の非clock残余三形、`PermanentAboveCorridorBalance.lean`のfresh endpoint証明書、`PermanentAboveCorridorBlocker.lean`のblocker証明書、および`PermanentAboveCycleRank.lean`のtail-cycle rankと`PermanentAboveCanonical.lean`のdual予算定理である。`forward_budget_progress`枝はstrict budget進捗としてそのまま大域rankへ流れる一方、`original_history_blocker`枝が残す「firstTime − 1を意味的nodeとして選ぶ」義務は、直接の下流`PermanentAboveCorridorBlockerGeneration.lean`(blocker初出を作った実遷移の分類)から`PermanentAboveCorridorPredecessorAdapter.lean`・`PermanentAboveCorridorPredecessorCrossing.lean`(predecessor時刻からのcrossing再選択)を経て、`PermanentAboveCorridorRestartRank.lean`のstationary restart(本モジュールの`seen_gain`がphase resetを上書きする)で回収される。ここで定義した`TerminalOuterHistoricalBlockerCertificate`は、その全pipelineの共通の親certificateである。
