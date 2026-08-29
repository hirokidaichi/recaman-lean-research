# PermanentAboveCorridorAnchorCandidates

**役割:** blocker predecessor kernelに最後に残ったstrict anchor growth(crossing anchorの厳密成長)を、全anchorが`List.range target`に属するという事実で有限rank化し、成長のたびに残余gap `target − anchor`が厳密に下がるwell-founded関係を与える。

## このモジュールの役割

恒久上方tailのdischarge解析では、terminal historical blockerのbelow-target predecessor(target未満の直前値)から新しいcrossing(target横断)を選び直す反復が生じる。`PermanentAboveCorridorRestartRank.lean`までの一連のrank精密化により、この反復で進捗しない残余(kernel)は「新しいcrossingのanchor(pre-crossing値)が旧anchorより厳密に大きい」というstrict anchor growth一形だけに絞られた。成長は一見rankの逆行だが、本モジュールはこれを逆手に取る。crossing anchorはstrict crossingの直前値なので必ず`target`未満であり、従って可能なanchorは長さ`target`の明示リスト`List.range target`の元しかない。すると厳密成長のたびに残余量`target − anchor`が厳密に減り、この関係はwell-foundedである。すなわちanchor growthは無限には反復できない。残る境界は数値ではなく、成長した新anchorを次cycleの親として実際にinstallするsemantic selection provenanceだけであり、それは`PermanentAboveCorridorSelectedInstall.lean`の主題になる。証明地図の「crossing anchor candidates」段階に対応する。

## 主要な定義

### `terminalCrossingAnchorCandidates` (L21)

targetのstrict crossingのpredecessor anchorとして可能な値の全リスト。定義はそのまま`List.range target`である。

### `terminalCrossingAnchorRank` (L34)、`TerminalCrossingAnchorProgress` (L37)

anchorの上に残る有限包絡`target − anchor`と、子のrankが親より厳密に小さいことを表す関係`TerminalCrossingAnchorProgress target childAnchor parentAnchor`。

### `TerminalCrossingAnchorGrowthCertificate` (L60)

strict anchor growth outcomeの背後にある有限候補データを型付けした証明書。選択されたpredecessor crossing証明書(`TerminalBelowPredecessorCrossingCertificate`、`PermanentAboveCorridorPredecessorCrossing.lean`)に対し、

- 旧anchor `parent.anchorParent < target`、
- 新anchor `a(crossingTime) < target`、
- 厳密成長 `parent.anchorParent < a(crossingTime)`、
- 両anchorの候補リスト所属、
- gap進捗 `TerminalCrossingAnchorProgress target (a crossingTime) parent.anchorParent`

を同時に保持する。

## 定理と証明

### `mem_terminalCrossingAnchorCandidates_iff` (L24)

**主張:** `anchor ∈ terminalCrossingAnchorCandidates target ↔ anchor < target`。

**証明:** `List.range`の所属条件そのものである。

### `terminalCrossingAnchorCandidates_length` (L29)

**主張:** 候補リストの長さはちょうど`target`である。

**証明:** `List.range target`の長さの計算。

### `terminalCrossingAnchorProgress_wellFounded` (L43)

**主張:** 残余gap関係`TerminalCrossingAnchorProgress target`はwell-foundedである。

**証明:** 関係は自然数値`target − anchor`上の`<`の引き戻しなので、自然数の整礎性からrank値のaccessibilityを持ち上げる標準的議論で従う。

### `TerminalBelowPredecessorCrossingCertificate.anchorGrowthCertificate` (L84)

**主張:** 選択されたpredecessor crossingが実際にstrict growth(`parent.anchorParent < a(crossingTime)`)を示すなら、完全な有限候補・残余gap証明書`TerminalCrossingAnchorGrowthCertificate`が構成できる。

**証明:** 三つの下界を確かめる。第一に旧anchor: discharge return証明書の`parent_anchor_eq`により`parent.anchorParent = a(oldCrossingTime)`であり、これは保存された旧crossing(`WeakUpcrossingStep`)の直前値なので、その`below`成分から`target`未満。第二に新anchor: 選択されたcrossing証明書の`first_crossing`はupcrossingであり、その直前値`a(crossingTime)`はやはり`below`により`target`未満。第三にgap進捗: 両anchorが`target`未満で新anchorが旧anchorより大きいことから

```text
target − a(crossingTime) < target − parent.anchorParent
```

が算術的に従う。所属はL24から。

### `TerminalCrossingAnchorGrowthCertificate.progress_of_selected` (L117)

**主張:** 次cycleの親anchorとして新crossing値`a(crossingTime)`を選ぶ(installする)なら、その選択に対して`TerminalCrossingAnchorProgress target nextParentAnchor parent.anchorParent`が成り立つ。

**証明:** 代入するだけである。この定理の役割は証明よりも境界の明示にある: 数値的rankはすでに揃っており、残る問題は「`nextParentAnchor = a(crossingTime)`という選択を意味的な次cycle親として実現するprovenance」だけであることを型として記録している。

### `BelowTargetHistoricalPredecessorCertificate.finiteRankOutcome` (L171)

**主張:** old-crossing eligibility(`downTime + 1 ≤ oldCrossingTime`、旧crossingがdowncross endpoint以後にあること)の下で、below-target predecessorの反復は次の三形(`TerminalBelowPredecessorFiniteRankOutcome`, L138)へ完全分類される。

1. `phase_progress`: 選択crossing子が既存の四成分位相ランク`PhaseSearchProgress`を厳密に下げる。
2. `restart_cycle_progress`: 六成分のrestart cycle rank(`TailRestartCycleProgress`、`PermanentAboveCorridorRestartRank.lean`)が厳密に下がる。
3. `finite_anchor_growth`: strict anchor growthだが、完全な`TerminalCrossingAnchorGrowthCertificate`つき。

**証明:** `PermanentAboveCorridorRestartRank.lean`の`restartRankOutcome`を適用すると、phase progress、restart cycle progress、生のanchor growthの三択が返る。前二者はそのまま対応する構成子へ移し、anchor growth枝だけをL84で有限候補証明書へ昇格させる。これにより、旧来「進捗不能の残余」だったanchor growthも、well-foundedな残余gap辺を伴う型付きデータになる。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「crossing anchor candidates」(growthを有限rank化済み)に対応する。入力は`PermanentAboveCorridorRestartRank.lean`のrestart rank outcomeと、`PermanentAboveCorridorPredecessorCrossing.lean`の選択crossing証明書である。出力の`finite_anchor_growth`枝は`PermanentAboveCorridorSelectedInstall.lean`が受け取り、選択されたcrossingを同じhorizon上の次のcombined parentとして実際に再構成する(そこで`progress_of_selected`の仮定`nextParentAnchor = a(crossingTime)`が満たされる)。さらに`PermanentAboveCorridorMasterRank.lean`は、この残余gapを七成分master rankの第二成分(remaining anchor gap)として組み込み、anchor growth・chronology mismatch・stationary restartをすべて一つのwell-founded relationに統合する。
