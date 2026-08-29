# PermanentAboveCorridorWindowSnapshot

**役割:** 同一の窓key `(returnTime, terminalEndpoint)`の再訪でもinstalled parentが異なり得ることを扱うため、各窓出現にhistory-budget cursor・parent anchor・old crossing timeの三座標snapshotを付与し、二つのsnapshotを「forward master下降」「reverse master下降」「rank prefix一致」へ全分類する。

## このモジュールの役割

`PermanentAboveCorridorWindowSelection.lean`の有限区間keyは軌道上のcrossing窓を一意に同定するが、その窓を生成したinstalled cycle parent(七成分master rank `tailInstalledCycleRank`の上位座標を決めるdischargeの親)は同定しない。exactな窓再訪は、履歴予算・anchor・old crossing cursorが動いた別のsemantic文脈から到来し得る。本モジュールは、master rankの外側三座標(missing history budget、remaining anchor gap、crossing time)を数値snapshotとして各窓出現に添付し、二つのsnapshotの間にmaster rankの向き付き三分法(現在側の厳密辺・保存側の厳密辺・三座標一致)が常に成り立つことを示す。とくに「保存側が厳密に小さい」というreverse constructorを型として露出することが重要で、visited情報を覚えるだけでは次のsemantic反復の向きを決められない — rank後退を排除または別途消費する将来のselection不変量が必要である — という限界を形式化している。

## 主要な定義

### `TerminalInstalledWindowSnapshot` (L23)

一つのterminal窓に付随するinstalled-cycleの数値provenance: `budgetTime`(履歴予算を評価する時刻)、`anchor`(parentのanchor値)、`oldCrossingTime`(旧crossingの時刻)の三つ組。等値判定可能なデータ型である。

### `TerminalInstalledWindowSnapshot.node` (L32)

snapshotを七成分master rankのnode `TailInstalledCycleSearchNode`へ埋め込む。内側四座標(restart時刻、phase、history時刻、minimum)は`0`と`discharge`に固定する。比較は新しいhistorical blocker restartを選ぶ前に決まるので、外側三座標だけが効く。

### `PermanentTailDischargeReturnCertificate.windowSnapshot` (L39)

discharge出現が運ぶsnapshot: `⟨parent.horizon, parent.anchorParent, oldCrossingTime⟩`。

### `TerminalInstalledWindowRankPrefixEq` (L63)

master rankが見る外側三座標の一致。第一成分は時刻そのものではなく`missingBelowCount target budgetTime`の一致であることに注意 — `budgetTime`が違っても同じmissing countを運べば、rankにとっては同じである。第二・第三成分はanchorとold crossing timeのliteralな一致。

### `TerminalInstalledWindowSnapshotComparison` (L74)

同一の有限窓keyに対する二snapshotの全域的な向き付き比較: `current_progress`(現在の出現が保存された出現に対するmaster rank `TailInstalledCycleProgress`の厳密辺)、`stored_progress`(逆向きの厳密辺 — 反復方向に対する真のrank後退)、`rank_prefix_equal`(三座標一致)。

### `TerminalReturnWindowSnapshotEntry` (L160)

proofを持たない一つのstate要素: 窓keyとsnapshotの対。妥当性は包含するstateが保持する。

### `TerminalReturnWindowSnapshotState` (L166)

過去の有限窓出現とそのinstalled provenanceのリスト。各entryについて、keyが`terminalReturnWindowKeys target`に属し、snapshotのanchorがtarget未満であることを不変量として持つ。

### `initialTerminalReturnWindowSnapshotState` (L171) / `TerminalReturnWindowSnapshotState.record` (L177)

空の初期stateと、妥当性証明付きでentryを先頭に追加する操作。

### `TerminalFiniteReturnWindowCertificate.snapshotEntry` (L193)

完全な有限窓証明書から、exact窓keyとinstalled parent snapshotの両provenanceを失わずにentryを取り出す。

### `TerminalReturnWindowSnapshotSelectionOutcome` (L213)

有限出現に対するprovenance-state結果: `fresh`(同keyの先行entryが無く、現在entryをrecordした次stateを返す)または`revisited`(同keyの保存entryと、現在/保存snapshotの完全な向き付き比較を返す)。

## 定理と証明

### `PermanentTailDischargeReturnCertificate.windowSnapshot_anchor_below` (L45)

**主張:** dischargeのsnapshotのanchorはtarget未満である。

**証明:** discharge証明書の`parent_anchor_eq`により`parent.anchorParent = a(oldCrossingTime)`であり、これは旧weak upcrossingのpre-crossing値なので`old_crossing.below`によりtarget未満。

### `PermanentTailDischargeReturnCertificate.windowSnapshot_crossing_below_horizon` (L53)

**主張:** snapshotのold crossing timeはparent horizonより厳密に前にある: `oldCrossingTime < parent.horizon`。

**証明:** discharge証明書が生成時から保持する`old_crossing_before_horizon`(`oldCrossingTime + 1 < parent.horizon`)から直ちに従う。この上界は、後続モジュールが固定horizon上でold crossing座標を有限列挙するための鍵である。

### 補助補題 (L87, L101)

private補題二件。予算count一致の下で、(1) anchorの厳密成長`stored.anchor < current.anchor`は、両anchorがtarget未満なのでremaining gap `target − anchor`の厳密減少となり、master rankの第二成分での`current_progress`辺を与える(L87)。(2) 予算・anchorが一致してold crossing timeが厳密に早ければ、第三成分での辺を与える(L101)。いずれも`tailInstalledCycleRank`を展開して辞書式`Prod.Lex`のconstructorを直接組む。

### `terminalInstalledWindowSnapshotComparison_total` (L116)

**主張:** anchorがともにtarget未満の任意の二snapshotについて、向き付き比較`TerminalInstalledWindowSnapshotComparison`が必ず成り立つ(辞書式三分法)。

**証明:** master rank prefixを外側から順に比較する。まず`missingBelowCount`同士: 現在側が小さければ`current_progress`(history drop辺)、保存側が小さければ`stored_progress`、等しければ次へ。anchorの比較では、rankの第二成分がremaining gap `target − anchor`なので、anchorが「大きい」側がrankの小さい側である — 保存側よりanchorが成長していれば補助補題(L87)で`current_progress`、逆なら対称に`stored_progress`。anchorも等しければold crossing timeを比較し、早い側が第三成分の辺を得る(L101)。三座標がすべて決着しなければ`rank_prefix_equal`である。第二の厳密枝(stored_progress)は反復方向に対する真のrank後退であり、これが常に排除できるわけではないことを型として保持する点が本定理の設計意図である。

### `TerminalFiniteReturnWindowCertificate.snapshotEntry_valid` (L201)

**主張:** 有限窓証明書のentryはstate不変量を満たす: keyは候補列挙に属し(`key_mem`)、snapshotのanchorはtarget未満である(L45)。

**証明:** 両成分の直接適用。

### `TerminalReturnWindowSnapshotState.select` (L233)

**主張(構成):** 現在entryについて、同じkeyを持つ保存entryの存在で場合分けする全域選択関数。存在すれば選択公理でwitnessを取り、state不変量から保存snapshotのanchor下界を得て、L116の全域比較を添えた`revisited`を返す。存在しなければ現在entryをrecordした`fresh`を返す。

### `TerminalFiniteReturnWindowCertificate.snapshotSelection` (L251)

**主張(構成):** 完全な有限窓証明書は、snapshot-aware選択を直接呼び出せる: 自身のentryとその妥当性(L201)で`select`を起動する。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「installed window snapshot」(master prefix比較済み)に対応する。上流は`PermanentAboveCorridorWindowSelection.lean`の有限区間keyと、`PermanentAboveCorridorMasterRank.lean`の七成分rank、`PermanentAboveCycleExit.lean`のdischarge証明書(とくに`old_crossing_before_horizon`)である。成果は二つある。第一に、exact窓再訪の残る自由度(installed parentの同一性)を三座標に特定し、その比較をmaster rankの言葉で完全に向き付けた。第二に、L53のhorizon上界により、`PermanentAboveCorridorInstalledWindowSelection.lean`が固定horizonの下で`(window, anchor, oldCrossingTime)`のfull keyを明示有限listへ直積化する道を開いた。これによりselection residualはfull keyまで一致するexact revisitに縮み、その処理は`PermanentAboveCorridorExactRevisit.lean`以降へ引き継がれる。
