# PermanentAboveCorridorReturnSelection

**役割:** finite return候補listを「未消費の候補集合」を持つ選択stateとして保持し、fresh選択のたびに`List.erase`でlist長が厳密下降するwell-founded選択rankを与える。残る唯一の残余は、大域的には有効だがすでに消費済みの候補へのliteral revisitである。

## このモジュールの役割

`PermanentAboveCorridorCandidates.lean`の明示的return候補list `terminalReturnCandidates target`は、後のclock候補を選んだときの`target − return` rank下降をすでに供給している。しかし「同じclockを繰り返し選ぶことを禁じるsemantic規則」は供給しない。本モジュールはこの二つの関心を分離する。選択stateはまだ消費していない候補を保持し、残っている候補を選ぶとそれをeraseしてlist長が厳密に減る。したがってfresh選択は、later-clock規則が最終的に証明されるかどうかとは独立に有限回しか起こらない。残余は「global候補listには属するがremaining listにはない」literal revisitのみで、semantic再訪排除の問題と有限fresh選択の問題が型のレベルで切り離される。

## 主要な定義

### `TerminalReturnSelectionState` (L20)

未消費のreturn候補list `remaining`と、その全要素がglobal候補list `terminalReturnCandidates target`(`List.range target`を`target < 2(return+1)`でfilterしたもの)に属するという証明を持つ選択state。

### `initialTerminalReturnSelectionState` (L26)

global候補list全体を`remaining`とする初期state。

### `TerminalReturnSelectionProgress` (L36)

state間の関係: 子の`remaining`のlist長が親より真に小さいこと。

### `TerminalReturnSelectionState.erase` (L56)

選択したclock一つを`List.erase`で除去するstate更新。除去後もglobal候補への所属証明は`List.mem_of_mem_erase`で保たれる。

### `TerminalReturnFreshSelectionCertificate` (L66)

fresh選択のproof-carryingな記録: global候補所属、remaining所属、次state、次stateがちょうど`erase`であること、そしてstrictな選択rank辺(`TerminalReturnSelectionProgress`)。

### `TerminalReturnCandidateSelectionOutcome` (L77)

選択の完全な結果型。`fresh`(上記証明書)または`revisited`(global候補ではあるが`remaining`に属さない)の二形。

### `PermanentTailTerminalReturnSelectedOutcome` (L124)

discharge levelのterminal outcomeに選択stateを通した形。`history_progress`、`immediate_semantic`、`historical_complete`は`PermanentAboveCorridorImmediateClosure.lean`の形のまま、唯一の数値枝が`finite_selection`(full finite window証明書+その`returnTime`に対する選択結果)へ置き換わる。

## 定理と証明

### `initialTerminalReturnSelectionState_length_le` (L32)

**主張:** 初期stateのremaining list長は`target`以下である。

**証明:** `PermanentAboveCorridorCandidates.lean`の`terminalReturnCandidates_length_le`(filterの長さは`List.range target`の長さ以下)をそのまま使う。

### `terminalReturnSelectionProgress_wellFounded` (L40)

**主張:** 選択rank `TerminalReturnSelectionProgress`は整礎である(無限のfresh選択列は存在しない)。

**証明:** stateをそのremaining list長へ写すと、選択rankは自然数の`<`の引き戻しになる。`Nat.lt`のaccessibility(到達可能性)に関する帰納法をstateへ持ち上げる、本リポジトリで繰り返し使われる標準的な引き戻し論法である。

### `TerminalReturnSelectionState.select` (L89)

**主張(構成):** global候補`returnTime`と任意のstateに対し、選択結果`TerminalReturnCandidateSelectionOutcome`を必ず構成できる。

**証明:** `returnTime ∈ state.remaining`は決定可能なので場合分けする。属していれば`List.length_erase_of_mem`によりerase後の長さは元の長さ`− 1`で、元の長さは所属により正なのでstrictに減る。fresh証明書を組んで`fresh`を返す。属していなければ`revisited`を返す。

### `TerminalReturnFreshSelectionCertificate.laterProgress` (L112)

**主張:** fresh選択された子候補が親候補より後のclockなら(`parentReturn < childReturn`)、既存のremaining-clock rank `TerminalReturnCandidateProgress`(`target − return`の厳密下降)も同時に成り立つ。この条件はfreshness-list progressとは独立である。

**証明:** 両clockのglobal候補所属から`PermanentAboveCorridorCandidates.lean`の`terminalReturnCandidateProgress_of_later`を適用するだけである。

### `PermanentTailDischargeReturnCertificate.terminalReturnSelectedOutcome` (L155)

**主張:** すべてのdischarge/return証明書と任意の選択stateに対し、`PermanentTailTerminalReturnSelectedOutcome`が成り立つ。

**証明:** `terminalSemanticallyClosedOutcome`を場合分けし、`finite_return_candidate`枝でのみ、finite証明書の`candidate_membership`を使ってL89の`select`を呼び、選択結果を添えて`finite_selection`とする。他の枝は情報を変えずに写す。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「finite return selection」(fresh選択を有限rank化済み)に対応する。上流は`PermanentAboveCorridorImmediateClosure.lean`(semantic閉包済みterminal outcome)と`PermanentAboveCorridorCandidates.lean`(候補listとclock rank)である。下流では`PermanentAboveCorridorWindowSelection.lean`が選択keyを`(returnTime, terminalEndpoint)`の対へ拡張して同clock別endpointの偽revisitを除去し、さらに`PermanentAboveCorridorInstalledWindowSelection.lean`がanchorとold crossing cursorまで含むfull keyへ精密化する。この選択列の終端で`PermanentAboveCorridorFiniteClosure.lean`がfinite certificate自体をFalseへ落とすため、本モジュールの選択機構は最終的には「finite枝が存在しない」ことの足場として吸収されるが、literal revisit残余を型として分離した設計はreplay境界の解析(`PermanentAboveCorridorReplayBoundary.lean`)へ引き継がれた。
