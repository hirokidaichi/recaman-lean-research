# PermanentAboveCorridorCandidates

**役割:** terminal insufficient残余の時計帯`return < target < 2(return+1)`を`List.range target`のfilterによる明示的な有限候補リストへ変換し、後のreturnへの移動で厳密に下がるwell-foundedなrankを与え、非時計的なouter residualを三形へ絞る。

## このモジュールの役割

`PermanentAboveCorridorResidual.lean`のmaster theoremは、恒久上方tailのdischarge(historical downcrossの排出処理)の終端残余を四つの構成子に縮約した。そのうちfinite insufficient枝は、returnの時計が抽象的な二重不等式

```text
returnTime < target < 2 * (returnTime + 1)
```

を満たすという情報だけを持つ。本モジュールはこの抽象的な帯を、targetで添字づけられた具体的な有限リスト`terminalReturnCandidates target`へ落とす。帯への所属はリストへの所属と同値になり、リストの長さはtarget以下、そして候補の中で後の時計を選ぶ移動は残余量`target − returnTime`を厳密に下げる。これによりfinite insufficient枝の「無限に別のreturnを選び続ける」可能性が有限化され、outer residual全体はこの有限候補枝と、時計に依らない三つの残余(immediate insufficient、immediate historical、finite outer blocker)へ分離される。証明地図の「finite return candidates」段階に対応する。

## 主要な定義

### `terminalReturnCandidates` (L17)

finite insufficient帯と両立し得るreturn時計の明示リスト:

```text
terminalReturnCandidates target = (List.range target).filter (fun r => target < 2 * (r + 1))
```

`List.range target`が`returnTime < target`側を、filterが`target < 2(returnTime + 1)`側を担当する。

### `terminalReturnCandidateRank` (L45)、`TerminalReturnCandidateProgress` (L48)

候補を選んだ後に残る時計の包絡量`target − returnTime`と、それを比較するrank関係。子のrankが親より厳密に小さいときに`TerminalReturnCandidateProgress target child parent`が成り立つ。

### `PermanentTailTerminalNonClockResidual` (L85)

finite clock band枝を除いた後に残る、時計に依らない三つの真の残余。

- `immediate_insufficient`枝: immediate historical valley(即時谷)と数値帯証明書。
- `immediate_historical`枝: 即時谷と、fresh endpoint(`downTime + 1`)より厳密に前に初出するblocker。
- `finite_outer_blocker`枝: terminal all-forced crossing window(全強制加算のterminal窓)と、そのterminal endpoint以前に初出するblocker。

## 定理と証明

### `mem_terminalReturnCandidates_iff` (L22)

**主張:** `returnTime ∈ terminalReturnCandidates target`は、二つの帯不等式`returnTime < target ∧ target < 2(returnTime + 1)`と同値である。

**証明:** `List.range`とfilterの所属条件の展開そのものである。

### `TerminalFiniteClockBandCertificate.mem_terminalReturnCandidates` (L29)

**主張:** finite clock band証明書(`PermanentAboveCorridorResidual.lean`)を持つreturnは必ず候補リストに属する。

**証明:** 証明書の二成分`return_before_target`と`target_lt_twice_clock`がちょうどL22の右辺である。

### `terminalReturnCandidates_length_le` (L37)

**主張:** 候補リストの長さはtarget以下である。

**証明:** filterは元のリストの長さを増やさず、`List.range target`の長さは`target`である。従って各targetについてfinite insufficient形のreturn時計は高々`target`通りしかない。

### `terminalReturnCandidateProgress_wellFounded` (L54)

**主張:** rank関係`TerminalReturnCandidateProgress target`はwell-founded(無限下降列を持たない)である。

**証明:** 関係は自然数値`target − returnTime`の通常の`<`の引き戻しである。自然数の`<`の整礎性から、rank値についてのaccessibility(到達可能性)を帰納で持ち上げる標準的な議論で従う。

### `terminalReturnCandidateProgress_of_later` (L72)

**主張:** 親も子も候補リストに属し、子の時計が親より後(`parentReturn < childReturn`)なら、`TerminalReturnCandidateProgress target childReturn parentReturn`が成り立つ。

**証明:** 両者の所属からとくに`childReturn < target`。従って`target − childReturn`と`target − parentReturn`はどちらも真の引き算として振る舞い、`parentReturn < childReturn`から`target − childReturn < target − parentReturn`。すなわち帯の内部で「より後のreturn」を選び直すたびに残余包絡が厳密に縮む。

### `PermanentTailTerminalOuterResidual.finiteCandidate_or_nonClockResidual` (L115)

**主張:** master outer residual(四構成子、`PermanentAboveCorridorResidual.lean`)は、returnが明示的な有限候補リストに属するか、三つのnon-clock residual構成子のいずれかに属するかのどちらかである。

**証明:** 四構成子を順に振り分ける。immediate insufficient、immediate historical、finite outer blockerの三枝はそれぞれのprovenanceを保ったまま`PermanentTailTerminalNonClockResidual`の対応する構成子へ移す。finite insufficient枝だけはclock band証明書を持つので、L29により候補リスト所属へ変換される。情報の損失はどの枝にもない。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「finite return candidates」(有限列挙・rank済み)に対応する。入力は`PermanentAboveCorridorResidual.lean`のmaster outer residualとclock band証明書である。候補リストと所属同値は下流で二段階に使われる: `PermanentAboveCorridorInstalledStep.lean`の`TerminalFiniteReturnWindowCertificate`は候補所属を恒久的な成分として保持し、`PermanentAboveCorridorReturnSelection.lean`はこのリストをremaining stateとして消費する有限選択rankを構成する(選ぶたびに`List.erase`で長さが下がる)。最終的に`PermanentAboveCorridorFiniteClosure.lean`が、この帯に入る証明書は実はすべて矛盾する(`target = 4, 5`の実軌道検証に帰着)ことを示し、finite枝はterminal outcomeから消える。
