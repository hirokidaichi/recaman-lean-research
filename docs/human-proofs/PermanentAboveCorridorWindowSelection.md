# PermanentAboveCorridorWindowSelection

**役割:** terminal crossing窓の有限選択keyをreturn clock単体から`(returnTime, terminalEndpoint)`の区間keyへ精密化し、明示的な二重`List.range`列挙とeraseによるlength厳密下降で選択を整礎化する。再訪残余は同一のcrossing窓区間そのものに限定される。

## このモジュールの役割

`PermanentAboveCorridorReturnSelection.lean`は、finite insufficient枝のreturn clockを`terminalReturnCandidates`(`List.range target`のfilter)から選ぶ有限選択stateを導入した。しかしkeyがreturn clockだけだと、同じclockで終わる異なるterminal suffix(terminal endpointが違う窓)が同一視され、endpointの違う枝が「偽の再訪」として潰れてしまう。本モジュールは、有限窓証明書が`terminalEndpoint < returnTime < target`という二重の上界を持つことを使い、keyを`(returnTime, terminalEndpoint)`の対へ精密化する。key全体は明示的な二重rangeで有限列挙でき、freshなkeyのeraseはremaining listのlengthを厳密に下げるので選択は整礎である。これで再訪はcrossing窓区間のliteralな同一性を意味するようになる。ただしkeyに含まれないinstalled parentのanchorとold crossing cursorの同一性は、意図的に次のprovenance境界(`PermanentAboveCorridorWindowSnapshot.lean`)へ残している。

## 主要な定義

### `TerminalReturnWindowKey` (L23)

terminal all-forced crossing区間の有限な同一性: `returnTime`と`terminalEndpoint`の対。等値判定可能(`DecidableEq`)なデータ型である。

### `terminalReturnWindowKeys` (L29)

初等的なterminal clock境界が許すすべての区間key。`List.range target`の各`returnTime`に対し`List.range returnTime`の各`terminalEndpoint`を対にした二重列挙で、`terminalEndpoint < returnTime < target`のkeyを尽くす。

### `TerminalReturnWindowSelectionState` (L72)

未選択の候補区間のstate: remaining list(全要素が`terminalReturnWindowKeys target`に属するという不変量付き)。

### `initialTerminalReturnWindowSelectionState` (L77)

全候補keyを残した初期state。

### `TerminalReturnWindowSelectionProgress` (L83)

子stateのremaining lengthが親より厳密に小さいという選択進捗関係。

### `TerminalReturnWindowSelectionState.erase` (L101)

一つのkeyを`List.erase`で取り除いたstate。remaining所属の不変量は`List.mem_of_mem_erase`で保存される。

### `TerminalReturnWindowFreshSelectionCertificate` (L112)

未選択区間を一つ消費したことのproof-carryingな記録: keyの候補性、remaining所属、次state、`next_state = state.erase key`、そしてlength厳密下降の進捗。

### `TerminalReturnWindowSelectionOutcome` (L123)

正確な区間選択の結果: `fresh`(上記証明書)または`revisited`(keyは候補だがremainingにない — literalな区間再訪)。

### `PermanentTailTerminalWindowSelectedOutcome` (L157)

discharge-levelの全域outcomeを窓選択経由に組み替えた四分類: `history_progress`(履歴予算の厳密下降`TerminalChronologyHistoryProgress`)、`finite_window_selection`(有限窓証明書とその区間keyの選択結果)、`immediate_semantic`(immediate valley + insufficientをcanonical coverage経由で閉じたsemantic outcome)、`historical_complete`(outer historical blockerのcomplete step outcome)。

### `TerminalReturnWindowRevisitResidual` (L209)

正確な有限窓再訪の後に残るもの: 区間keyがremainingに無いこと、およびkeyが候補列挙に属することだけを保持する。区間は同定されたが、そのinstalled parent / cursorの同一性は有限keyの一部ではない、という限界を型で明示する。

### `TerminalReturnWindowRefinedSelectionOutcome` (L223)

情報を失わない選択分解: `fresh`(消費証明書)または`revisited`(上記residual)。

## 定理と証明

### `mem_terminalReturnWindowKeys_iff` (L34)

**主張:** keyが`terminalReturnWindowKeys target`に属することは、`key.terminalEndpoint < key.returnTime ∧ key.returnTime < target`と同値である。

**証明:** `List.mem_flatMap`と`List.mem_map`、`List.mem_range`の標準的な往復。構成方向はrange所属を作って対を組み、分解方向はflatMap/mapのwitnessを取り、対の射影の等式で成分を同定する。

### `TerminalFiniteReturnWindowCertificate.key_mem` (L60)

**主張:** 完全な有限窓証明書(`PermanentAboveCorridorInstalledStep.lean`で定義される、窓・insufficient・clock band・候補所属を束ねた証明書)の区間key `⟨returnTime, terminalEndpoint⟩`は候補列挙に属する。

**証明:** 窓の`endpoint_before_return`(非空suffix)が`terminalEndpoint < returnTime`を、窓の`return_before_target`が`returnTime < target`を与え、L34を適用する。

### `terminalReturnWindowSelectionProgress_wellFounded` (L87)

**主張:** 窓選択進捗は整礎である。

**証明:** 自然数の整礎性をremaining lengthに沿ってstateへ引き戻す標準的な議論。

### `TerminalReturnWindowSelectionState.select` (L135)

**主張(構成):** 候補keyについて、remainingに属するかを判定し、属するなら`fresh`(eraseによるlength厳密下降付き; `List.length_erase_of_mem`とlist非空性から`length − 1 < length`)、属さないなら`revisited`を返す全域選択関数。

### `PermanentTailDischargeReturnCertificate.terminalWindowSelectedOutcome` (L188)

**主張:** すべてのtyped dischargeは、任意の窓選択stateに対して`PermanentTailTerminalWindowSelectedOutcome`を持つ。

**証明:** `PermanentAboveCorridorImmediateClosure.lean`の`terminalSemanticallyClosedOutcome`(semantic閉包済みのdischarge全域分類)をcaseで写す。`history_progress`、`immediate_semantic`、`historical_complete`の三枝はそのまま通す。`finite_return_candidate`枝だけを、有限窓証明書のkey所属(L60)を使って`state.select`にかけ、選択結果込みの`finite_window_selection`へ差し替える。従来clock単位の選択だった有限枝が、endpoint込みの区間選択として保存される点が本定理の中身である。

### `TerminalReturnWindowSelectionOutcome.revisitResidual` (L237)

**主張(構成):** 区間選択の結果を情報を失わずに`TerminalReturnWindowRefinedSelectionOutcome`へ分解する。`fresh`はそのまま、`revisited`は非所属と候補性を`TerminalReturnWindowRevisitResidual`へ詰め替える。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「finite window selection」(endpoint込みで有限rank化済み)に対応する。上流は`PermanentAboveCorridorReturnSelection.lean`(clock単位の有限選択)と`PermanentAboveCorridorInstalledStep.lean`の有限窓証明書である。同じreturnでendpointだけ異なる枝を別keyに分離したことで、偽の再訪が除去され、真の選択残余は同一窓区間のliteral revisitだけになった。下流では、`PermanentAboveCorridorWindowSnapshot.lean`が本モジュールの限界(installed parentのanchor・old crossing timeがkeyに含まれない)を正面から扱い、各窓出現に三つの外側座標のsnapshotを付与する。さらに`PermanentAboveCorridorInstalledWindowSelection.lean`が窓key・anchor・old crossingの直積を有限列挙してfull-key選択へ拡張する。
