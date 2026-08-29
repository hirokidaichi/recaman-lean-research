# PermanentAboveCorridorExactRevisit

**役割:** ready crossing不変量からdischarge親nodeが`(horizon, anchor)`だけで一意に決まることを示し、dischargeの構成時に残る選択 — 元のdowncross endpoint、historical初出時刻、historical最小値 — がすべて固定horizonで有界な数値であることを証明して、installed windowの有限選択keyをこれらのhistorical provenanceまで拡張する。残る選択残余は、全数値provenanceが一致するexact revisitのみになる。

## このモジュールの役割

`PermanentAboveCorridorInstalledWindowSelection.lean`は、固定horizonのfinite枝を`(window, anchor, oldCrossingTime)`の有限keyで列挙し、fresh keyの消費をerase-lengthのwell-founded下降にした。しかしdischarge証明書の構成には、keyに現れないhistorical選択 — どのdowncrossを使ったか、どのtail開始・最小値証明書を使ったか — がまだ残っており、「同じkeyの再訪」が本当に同じ反復なのかを確定できない。本モジュールは二段でこの自由度を消す。第一に、ready crossing不変量の`node_eq`から親は必ず`⟨horizon, anchor, normal, anchor⟩`の形なので、horizonとanchorが等しい二つのdischargeの親`PhaseSearchNode`は文字どおり等しい。第二に、down endpoint・historical初出時刻はいずれもparent horizon未満、historical最小値は`upperTri horizon`以下という明示的上界を持つため、installed keyへこの三つを追加した拡張keyもなお有限listに列挙できる。さらに、二つのdischargeのdown endpointが異なれば、後の側のendpointが初出のbelow-target値であることから片方向のmissing予算厳密下降が必ず得られる(chronology history進捗)。従って拡張keyによる有限選択の後に残る残余は、down endpointからhistorical最小値まで全数値provenanceが一致するexact revisitだけである。

## 主要な定義

### `TerminalExactWindowDownEndpointComparison` (L77)

二つのdischarge証明書のdown endpointの比較。constructorは、currentの側のmissing予算がstoredの側より小さい`current_progress`、逆向きの`stored_progress`、絶対時刻が一致する`same_endpoint`の三つで、進捗はいずれも`TerminalChronologyHistoryProgress`(`PermanentAboveCorridorChronologyRank.lean`)で表す。

### `TerminalExactInstalledHistoryKey` (L110)

installed windowを固定した後の有限数値provenance。installed key(`window, anchor, oldCrossingTime`)に、`downEndpoint`、`historicalFirstTime`、`historicalMinimumValue`の三つを追加した六成分(入れ子で四フィールド)のkey。`DecidableEq`を持つので、list上のerase・membership判定ができる。

### `terminalExactInstalledHistoryKeys` (L117)

固定の`target`と`horizon`に対する全拡張keyの明示有限list。installed keyのlistに`List.range horizon`二つ(endpointと初出時刻)と`List.range (upperTri horizon + 1)`(最小値)を`flatMap`で直積化する。

### `TerminalExactInstalledHistorySelectionState` (L195)

固定horizonにおける残existing拡張keyのlistと、その全要素が候補listに属するという証明を持つselection state。`initialTerminalExactInstalledHistorySelectionState` (L201)は全候補listから始める。

### `TerminalExactInstalledHistorySelectionProgress` (L208)

残listの長さの厳密下降をselection進捗とする関係。

### `TerminalExactInstalledHistoryFreshSelectionCertificate` (L241)

fresh選択の証明書: keyの候補membership、残listでのmembership、erase後の次state、およびlength進捗。

### `TerminalExactInstalledHistorySelectionOutcome` (L252)

選択のtotal outcome: `fresh`(上記証明書)または`exact_revisit`(候補ではあるが残listにない — すでに消費済みのkeyの再訪)。

## 定理と証明

### `PermanentTailDischargeReturnCertificate.parent_node_shape` (L24)

**主張:** 型付きdischargeを持つpermanent-tail crossing親には、隠れたphase・局所値の自由度がない: `parent = ⟨parent.horizon, parent.anchorParent, normal, parent.anchorParent⟩`。

**証明:** combined証明書のready crossing不変量からcrossing証明書を取り出すと、その`node_eq`がparentを`⟨horizon, a crossingTime, normal, a crossingTime⟩`の形に固定する。anchorParent成分を射影すれば`parent.anchorParent = a crossingTime`であり、書き戻すと主張の形になる。

### `PermanentTailDischargeReturnCertificate.parent_eq_of_horizon_anchor` (L35)

**主張:** horizonとanchorが等しい二つのdischarge証明書の親`PhaseSearchNode`は等しい。

**証明:** 両親をL24の標準形に書き、仮定の二等式を代入する。有限keyに`(horizon, anchor)`しか入れなくても親node全体が決まることを保証する。

### `PermanentTailDischargeReturnCertificate.down_endpoint_before_horizon` (L45)

**主張:** `source.downTime + 1 < parent.horizon`。

**証明:** 不等式の鎖`downTime + 1 < tailStart ≤ start < parent.horizon`。最初はendpointがhistorical tail開始より前という証明書フィールド、次はtail開始のstart以下性、最後はcombined証明書の「tailはhorizonより厳密に前に始まる」である。

### `PermanentTailDischargeReturnCertificate.historical_first_before_horizon` (L53)

**主張:** `source.historicalFirstTime < parent.horizon`。

**証明:** L45と同じ鎖を、historical最小値証明書の`firstTime_before_tail`(初出時刻はtail開始より前)から始める。

### `PermanentTailDischargeReturnCertificate.historical_minimum_value_le_upperTri_horizon` (L62)

**主張:** historical tail最小値は`upperTri parent.horizon`以下である: `a source.historicalMinimumTime ≤ upperTri parent.horizon`。

**証明:** 最小値の最小性をtail開始時刻自身に適用して`a historicalMinimumTime ≤ a tailStart`。実軌道の上界`a n ≤ upperTri n`(`OrbitBounds.lean`の`a_le_upperTri`)と、`tailStart ≤ parent.horizon`での`upperTri`の単調性をつなぐ。時刻が非有界な最小値witnessと違い、値そのものはhorizonで一様に抑えられることが、有限key化を可能にする。

### `terminalExactWindowDownEndpointComparison_total` (L94)

**主張:** down endpointの比較は全域である: 任意の二つのdischarge証明書は、`current_progress`、`stored_progress`、`same_endpoint`のいずれかに入る。

**証明:** 二つのendpoint時刻の三分律で場合分けする。storedの側が先なら、currentのendpointはbelow-targetの値がstoredのendpoint時刻より後に初出したものなので、`missingBelowCount_strict_of_firstAt`によりmissing予算がstoredからcurrentへ厳密に下がり、`current_progress`。逆なら対称に`stored_progress`。どちらでもなければ時刻が等しく`same_endpoint`。すなわち「endpointが違えば必ずどちらか片方向のstrict history進捗が取れる」ので、rank下降できない再訪はendpoint一致の場合に限られる。

### `mem_terminalExactInstalledHistoryKeys_iff` (L126)

**主張:** 拡張keyが候補listに属することは、installed keyの候補membership、`downEndpoint < horizon`、`historicalFirstTime < horizon`、`historicalMinimumValue ≤ upperTri horizon`の連言と同値である。

**証明:** `flatMap`と`List.range`のmembershipを両方向に展開する機械的な議論である。

### `TerminalFiniteReturnWindowCertificate.exactHistoryKey` (L170) / `exactHistoryKey_mem` (L179)

**主張:** finite return窓証明書から拡張key `⟨installedWindowKey, downTime + 1, historicalFirstTime, a historicalMinimumTime⟩`が作れ、それは固定horizonの候補listに必ず属する。

**証明:** membershipはL126の同値の右辺を検証すればよく、installed keyの部分は`PermanentAboveCorridorInstalledWindowSelection.lean`の`installedWindowKey_mem`、追加三成分の上界はL45・L53・L62である。

### `terminalExactInstalledHistorySelectionProgress_wellFounded` (L213)

**主張:** 残listの長さによるselection進捗は整礎である。

**証明:** 自然数`<`の整礎性をlength写像に沿って引き戻す。

### `TerminalExactInstalledHistorySelectionState.erase` (L230) / `select` (L265)

**主張:** stateから候補keyを一つ選ぶ操作はtotalであり、keyが残listにあれば`List.erase`で長さが厳密に減るfresh証明書を、なければ`exact_revisit`を返す。

**証明:** membershipの排中律で分岐する。fresh側の長さ下降は、要素を含むlistのeraseは長さをちょうど1減らすという`List.length_erase_of_mem`による。

### `TerminalFiniteReturnWindowCertificate.exactHistorySelection` (L286)

**主張:** 任意のfinite return窓証明書は、自身の拡張keyについてのselection outcomeを直接持つ。

**証明:** L170のkeyとL179のmembershipをL265の`select`に渡すだけである。以上により、finite枝の反復で拡張keyがfreshである限り有限listが厳密に消費され、消費し尽くした後に起こり得るのは全数値provenance(window・anchor・old crossing・down endpoint・historical初出・historical最小値)が過去の出現と完全一致するexact revisitのみとなる。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「exact revisit history(historical数値provenanceまで有限化済み)」に対応する。入力は`PermanentAboveCorridorInstalledWindowSelection.lean`のinstalled key選択、`PermanentAboveCorridorChronologyRank.lean`のhistory進捗関係、`PermanentAboveCycleExit.lean`のdischarge証明書、`OrbitBounds.lean`の軌道上界である。直接の下流は`PermanentAboveCorridorCanonicalMinimum.lean`で、そこでは残る二つのcursor(permanent start、historical tailStart)も同様にhorizon未満であることを使ってkeyへ追加し、非有界だった最小値witness時刻をcanonicalな`FirstAtOrAfter`で一意化する。さらに`PermanentAboveCorridorCanonicalStateStep.lean`が本モジュールのselection outcomeをterminal constructor treeへ接続し、`PermanentAboveCorridorReplayBoundary.lean`は「exact revisit residual自体はvisited listだけでは矛盾にできない」というno-goを示して残余をresolver一命題に絞る — その数値枝を最終的に無条件で閉じるのが`PermanentAboveCorridorFiniteClosure.lean`である。
