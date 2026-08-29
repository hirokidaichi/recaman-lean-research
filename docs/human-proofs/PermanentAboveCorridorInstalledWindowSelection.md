# PermanentAboveCorridorInstalledWindowSelection

**役割:** old crossingが親horizonより前にあるという上界を使い、固定horizonでのterminal window出現を`(window key, anchor, old crossing time)`のfull有限keyへ直積列挙する。master prefixの向きによらずfresh keyのeraseでlist長が厳密下降し、選択残余は同一window・同一anchor・同一crossing cursorのexact revisitに限定される。

## このモジュールの役割

`PermanentAboveCorridorWindowSnapshot.lean`は、各terminal window出現にhistory-budget cursor・親anchor・old crossing時刻のsnapshotを付与したが、二つのsnapshotのmaster-rank prefix比較は前向き下降・後向き下降・三座標一致の三方向に分かれ、visited情報だけでは反復の向きを決められないことも露呈した。本モジュールはこの後向きの場合を有限性で吸収する。dischargeのold crossingは常に親horizonより前(`oldCrossingTime + 1 < parent.horizon`)であり、親anchorはtarget未満なので、固定されたhorizonの下でterminal出現の完全な数値的同一性は有限個のkeyに収まる。したがってmaster prefixがどちらへ動こうと、未出のfull keyを消費するたびに有限listが厳密に縮み、無限反復には必ず「同じwindow・同じanchor・同じold crossing cursorをそのまま再利用するexact revisit」が要る。この残余の解析が次段の`PermanentAboveCorridorExactRevisit.lean`へ渡される。

## 主要な定義

### `TerminalReturnInstalledWindowKey` (L25)

installed terminal出現のexactな有限数値identity。window key(`(returnTime, terminalEndpoint)`の対、`PermanentAboveCorridorWindowSelection.lean`)、親anchor、old crossing時刻の三つ組で、等値性は決定可能(`DecidableEq`)。

### `terminalReturnInstalledWindowKeys` (L33)

固定した`target`と`horizon`の下で許されるすべてのinstalled key。window keyのlist、`List.range target`(anchor)、`List.range horizon`(old crossing時刻)の三重の直積を`flatMap`/`map`で明示的に列挙した有限listである。

### `TerminalFiniteReturnWindowCertificate.installedWindowKey` (L73)

一つのfinite terminal証明書から抽出するfull key: `⟨⟨source.returnTime, terminalEndpoint⟩, parent.anchorParent, source.oldCrossingTime⟩`。

### `TerminalReturnInstalledWindowSelectionState` (L96)

固定horizonでの残余full key listと、その全要素がL33の列挙に属する証明を持つ選択state。

### `initialTerminalReturnInstalledWindowSelectionState` (L102)

列挙全体を`remaining`とする初期state。

### `TerminalReturnInstalledWindowSelectionProgress` (L109)

remaining list長の厳密下降として定義される選択rank。

### `TerminalReturnInstalledWindowSelectionState.erase` (L131)

一つのkeyを`List.erase`で除去するstate更新。候補所属証明は`List.mem_of_mem_erase`で保存される。

### `TerminalReturnInstalledWindowFreshSelectionCertificate` (L143)

fresh full identityの消費記録: 候補所属、remaining所属、次state(ちょうど`erase`)、strictな選択rank辺。

### `TerminalReturnInstalledWindowSelectionOutcome` (L155)

選択の完全な結果型: `fresh`(上記証明書)または`exact_revisit`(候補ではあるがもうremainingにない、すなわちすべての有限installed座標のliteralな再利用)。

## 定理と証明

### `mem_terminalReturnInstalledWindowKeys_iff` (L40)

**主張:** `key ∈ terminalReturnInstalledWindowKeys target horizon`は、`key.window ∈ terminalReturnWindowKeys target`かつ`key.anchor < target`かつ`key.oldCrossingTime < horizon`と同値である。

**証明:** 順方向は`List.mem_flatMap`と`List.mem_map`を二回ずつ展開し、構成されたkeyと元のkeyの成分ごとの等値を`congrArg`で取り出して代入すると、`List.mem_range`から各不等式が従う。逆方向は同じmembership補題を逆向きに組み立てるだけである。純粋にlist計算の補題であり、数列の性質は使わない。

### `TerminalFiniteReturnWindowCertificate.installedWindowKey_mem` (L82)

**主張:** 親horizonが`horizon`に等しければ、finite証明書のfull keyはL33の列挙に属する。

**証明:** L40の同値の三条件を順に確かめる。window keyの所属はfinite証明書の`key_mem`(`endpoint < return < target`、`PermanentAboveCorridorWindowSelection.lean`)。anchorのtarget未満は`windowSnapshot_anchor_below`(親anchorはold crossingの直前値`a(oldCrossingTime)`であり、弱upcrossingの定義によりtarget未満)。old crossing時刻のhorizon未満は`windowSnapshot_crossing_below_horizon`(dischargeのfield `oldCrossingTime + 1 < parent.horizon`から)。いずれも`PermanentAboveCorridorWindowSnapshot.lean`で用意された上界である。

### `terminalReturnInstalledWindowSelectionProgress_wellFounded` (L114)

**主張:** 固定horizonのfull key選択rankは整礎である。

**証明:** stateをremaining list長へ写して自然数`<`の整礎性を引き戻す、選択state系モジュール共通の標準論法である。

### `TerminalReturnInstalledWindowSelectionState.select` (L168)

**主張(構成):** 列挙に属する任意のkeyと任意のstateから、選択結果`TerminalReturnInstalledWindowSelectionOutcome`を必ず構成できる。

**証明:** keyの`remaining`所属は決定可能。属していれば`List.length_erase_of_mem`と所属による長さの正値性からerase後の長さが厳密に減り、fresh証明書を組む。属していなければ`exact_revisit`であり、これは「同じwindow区間・同じ親anchor・同じold crossing cursorの完全な再現」を意味する。

### `TerminalFiniteReturnWindowCertificate.installedWindowSelection` (L191)

**主張(構成):** 親horizonがstateの固定horizonに一致するfinite出現は、そのfull keyでL168の選択を直接呼び出せる。

**証明:** L82でkeyの候補所属を得て`select`に渡すだけである。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「installed window selection」(full snapshotを有限rank化済み)に対応する。上流は`PermanentAboveCorridorWindowSelection.lean`(window key列挙)と`PermanentAboveCorridorWindowSnapshot.lean`(anchor・old crossingの上界とmaster prefix三分類)である。snapshotの数値比較で向きが決まらなかった反復も、本モジュールにより「fresh keyの有限消費」へ吸収され、残余はexact full-key revisitだけになる。下流では`PermanentAboveCorridorExactRevisit.lean`がこのrevisitにhistorical数値provenance(down endpoint差の履歴下降、first time上界、minimum上界)を追加し、`PermanentAboveCorridorCanonicalMinimum.lean`・`PermanentAboveCorridorCanonicalStateStep.lean`を経て`PermanentAboveCorridorReplayBoundary.lean`のreplay resolver、最終的に`PermanentAboveCorridorFiniteClosure.lean`でのfinite枝全体の排除へつながる。
