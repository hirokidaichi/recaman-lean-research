# PermanentAboveCycleExit

**役割:** canonical discharge returnの完全なprovenanceを保持する証明書を構成し、cycle rankの最外キーをanchor単独から`(anchor, crossing時刻)`のcursorへ精密化して、discharge退出の失敗を「anchor厳密成長・時系列不適格・文字どおりの停留」の三つの型付きkernel残余に完全分類する。

## このモジュールの役割

`PermanentAboveCycleRank.lean`の一方向cycle rankは、dischargeからcrossingへ戻る唯一の道をstrict anchor drop(anchor: 探索の基準となるpre-crossing値)に限定したが、anchor非減少のgrowth residualが退出障害として残った。本モジュールはこの退出問題を二段階で精密化する。第一に、historical downcross(target以上からtarget未満への実遷移)の有限下降と、その endpoint からのcanonical(earliest)なreturn upcrossing、および親crossingの生成元時刻を、一つの型付き証明書`PermanentTailDischargeReturnCertificate`にまとめる。第二に、rankの最外キーをanchor値だけでなく`(anchor, crossing時刻)`の組(cursor)へ拡張した五成分rankを導入する。この精密化により、等anchorでもより早いcrossingへの復帰は進捗になる。さらに、旧crossingがdowncross endpoint以後にあるという時系列適格性の下では、canonical選択の最小性から復帰時刻は旧crossing時刻以下となるため、退出できない場合は「anchorの厳密成長」「旧crossingがendpointより前」「同一anchorかつ同一時刻の文字どおりの停留」の三つに限られることを示す。隠れた一般的非減少ケースはもはや存在しない。

## 主要な定義

### `PermanentTailDischargeReturnCertificate` (L23)

combined permanent-tail障害のhistorical downcrossからcanonicalに帰還するための完全な証明データ。combined証明書(tail・zero-budget crossing・最小値blocker)に加えて、有限下降が到達したstrict tail(`tailStart ≤ start`)とその最小値証明書、初出時刻以後のdowncross(endpoint はfreshで`tailStart`より前)、endpoint からのcanonicalな最初のupcrossing`return_crossing`(`returnTime + 1 ≤ tailStart`で完了)、そして親crossingの生成元: 時刻0からのweak upcrossingとしての`oldCrossingTime`(`oldCrossingTime + 1 < parent.horizon`)と、anchor等式`parent.anchorParent = a(oldCrossingTime)`を保持する。

### `TailCrossingCursor` (L114)

crossing cursorの本体: predecessor anchor値`anchor`と、それを生み出した正確な軌道時刻`crossingTime`の組。

### `tailCrossingCursorRank` (L119)

cursorを自然数の組`(anchor, crossingTime)`へ写す。

### `TailCrossingCursorProgress` (L122)

cursor rankの二成分辞書式順序による厳密下降関係。

### `CanonicalDischargeReturnResidual` (L164)

時刻cursorを加えた後の残余の帰納型。`anchor_growth`(`parent.anchorParent < a(returnTime)`、anchorの厳密成長)と、`same_anchor_not_earlier`(anchorが等しく、canonical returnが旧crossingより早くない: `oldCrossingTime ≤ returnTime`)の二つのconstructorを持つ。

### `TailCursorCycleSearchNode` (L264)

cursor精密化後の完全なcycle探索node: `anchor`、`crossingTime`、phase(`crossing/backtrack/discharge`)、履歴時刻`historyTime`、tail最小値`minimumValue`の五つ組。

### `tailCursorCycleRank` (L272)

五成分rank

```text
(anchor, (crossingTime, (phase.rank, (seenBelowCount target historyTime, minimumValue))))
```

crossing時刻がanchorの直下、phaseより上位に置かれる点が本モジュールの核心である。

### `TailCursorCycleProgress` (L279)

五成分rankの辞書式順序による厳密下降関係。

### `CanonicalDischargeKernelResidual` (L367)

時系列適格性まで露出させた後の最終kernel。cursor退出に失敗した場合は次の三つの具体的現象のいずれかである: `anchor_growth`(値の厳密成長)、`old_crossing_before_endpoint`(旧crossing時刻がdowncross endpointより前: `oldCrossingTime < downTime + 1`、時系列不適格)、`stationary`(同一anchorかつ同一時刻: `a(returnTime) = parent.anchorParent`かつ`returnTime = oldCrossingTime`)。

## 定理と証明

### `PermanentTailCombinedCertificate.exists_dischargeReturnCertificate` (L50)

**主張:** すべてのcombined証明書から、型付きのdischarge/return証明書が組み立てられる: `Nonempty (PermanentTailDischargeReturnCertificate target start parent)`。

**証明:** 有限historical下降定理(`PermanentAboveHistory.lean`の`exists_historicalDowncrossCertificate`)がstrict tail・最小値証明書・downcross・endpoint のfresh性を与える。endpoint `a(downTime+1) < target`に`exists_firstWeakUpcrossingStep_from_below`(`PermanentAboveCanonical.lean`)を適用してcanonical return `returnTime`を得る。endpoint から`tailStart`(値は厳密にtargetより上)までの区間に何らかのupcrossing witnessがあるので、canonicalの最小性(`endpoint_le_of_witness`)により`returnTime + 1 ≤ tailStart`。最後に、親のready crossing証明書を展開すると、そのcrossing遷移は時刻0からのweak upcrossingと見なせ(`a(oldCrossingTime) < target ≤ a(oldCrossingTime+1)`、強制加算)、`crossing_before_horizon`とnode等式からanchor等式`parent.anchorParent = a(oldCrossingTime)`も取り出せる。

### `PermanentTailDischargeReturnCertificate.return_before_parentHorizon` (L104)

**主張:** canonical returnは親のzero-budget horizonより真に前に完了する: `returnTime + 1 < parent.horizon`。

**証明:** `returnTime + 1 ≤ tailStart ≤ start < parent.horizon`の連鎖。したがってreturnは未来のデータではなく、真のhistorical provenanceである。

### `tailCrossingCursorProgress_wellFounded` (L128)

**主張:** cursor精密化は整礎性を保つ。

**証明:** 自然数の二重辞書式順序の整礎性`natPairLex_wellFounded`を、rank写像に沿ってcursorへ引き戻す標準的議論。

### `tailCrossingCursorProgress_iff` (L144)

**主張:** cursor進捗の正確な数値的意味: `⟨childAnchor, childTime⟩`から`⟨parentAnchor, parentTime⟩`への進捗は、`childAnchor < parentAnchor`、または`childAnchor = parentAnchor`かつ`childTime < parentTime`、と同値である。

**証明:** 二成分辞書式順序の定義の展開。等anchorでも、より早いcrossing時刻への移動が進捗として数えられるようになったことを意味する。

### `PermanentTailDischargeReturnCertificate.cursorProgress_or_residual` (L178)

**主張:** すべてのcanonical discharge returnは、整礎cursorを下げるか、`CanonicalDischargeReturnResidual`に属するかのいずれかである。子cursor`⟨a(returnTime), returnTime⟩`、親cursor`⟨parent.anchorParent, oldCrossingTime⟩`について排他的に分類できる。

**証明:** `a(returnTime)`と`parent.anchorParent`の比較で三分する。厳密に小さければanchor成分で進捗。等しければ時刻を比較し、`returnTime < oldCrossingTime`なら第二成分で進捗、そうでなければ`same_anchor_not_earlier`残余。厳密に大きければ`anchor_growth`残余。

### `PermanentTailDischargeReturnCertificate.returnTime_le_oldCrossingTime` (L203)

**主張:** 旧crossingがhistorical endpoint以後にあるなら(`downTime + 1 ≤ oldCrossingTime`)、旧crossingはcanonical returnが考慮する適格なupcrossingの一つなので、`returnTime ≤ oldCrossingTime`。

**証明:** 旧crossingのweak upcrossingデータの開始時刻条件だけを`downTime + 1`に付け替えれば、endpoint からのupcrossing witnessになる。canonical returnの最小性(`FirstWeakUpcrossingStep.time_le`)がそのwitness以下であることを与える。

### `PermanentTailDischargeReturnCertificate.cursorProgress_or_growth_or_stationary` (L219)

**主張:** 時系列適格性の下では、残余はもはや曖昧な非減少ケースではない: cursor進捗、anchorの厳密成長(`parent.anchorParent < a(returnTime)`)、または同一anchorかつ同一時刻(`a(returnTime) = parent.anchorParent`かつ`returnTime = oldCrossingTime`)、のいずれかである。

**証明:** L178の分類を取り、`same_anchor_not_earlier`枝(`oldCrossingTime ≤ returnTime`)にL203の逆向き不等式`returnTime ≤ oldCrossingTime`を合わせれば時刻の等号が出る。

### `PermanentTailDischargeReturnCertificate.stationary_of_oldCanonical` (L242)

**主張:** 旧crossingがすでに同じendpoint からのcanonical crossingであるなら、canonical化は同一の時刻を返す: `returnTime = oldCrossingTime`。

**証明:** `FirstWeakUpcrossingStep.unique`(`PermanentAboveCanonical.lean`)の一意性そのもの。時刻cursorは非canonicalな等anchor loopを除去するが、文字どおりの停留crossingは単独では除去できない。

### `natQuintLex_wellFounded` (L251)

**主張:** 自然数の五重辞書式順序は整礎である。

**証明:** 最外成分の整礎性と、内側四成分の整礎性`natQuadLex_wellFounded`を`Prod.lexAccessible`で合成する補助定理。

### `tailCursorCycleProgress_wellFounded` (L286)

**主張:** cursor精密化後のpermanent-tail cycle rankは整礎である。

**証明:** L251のaccessibilityを`tailCursorCycleRank`に沿ってnodeへ引き戻す。

### `tailCursorCycle_exit_of_cursorProgress` (L305)

**主張:** cursorの下降は、本来上向きの`discharge → crossing`phase遷移を覆い隠し、完全なcycle辺を閉じる。すなわちcursor進捗があれば、discharge nodeからcrossing nodeへの`TailCursorCycleProgress`が成り立つ。

**証明:** cursor進捗をL144で展開する。anchor下降なら最外成分で決まる。等anchorかつ時刻下降なら第二成分`crossingTime`で決まり、その内側のphase rankの上昇(0→2)は辞書式順序に影響しない。

### `tailCursorCycle_exit_iff_cursorProgress` (L324)

**主張:** 逆も成り立つ: 完全なcycleがdischargeから上向きに復帰できることは、`(anchor, crossing時刻)`cursorの下降とちょうど同値である。

**証明:** (⇐)はL305。(⇒)は辞書式下降を展開すると、anchor成分かcrossingTime成分で決まったか、両者同値で内側が下降したかだが、後者ではphase rankが`0`(discharge)から`2`(crossing)へ増加しており不可能。`PermanentAboveCycleRank.lean`の`tailCycle_exitCrossing_iff_anchorDrop`のcursor版である。

### `PermanentTailDischargeReturnCertificate.cycleExit_or_residual` (L351)

**主張:** 型付きdischarge証明書は、完全な整礎cycleでの真の退出(returnを子crossing nodeとする`TailCursorCycleProgress`)か、絞られたcanonical残余のいずれかを与える。

**証明:** L178の分類にL305を合成するだけである。

### `PermanentTailDischargeReturnCertificate.cycleExit_or_kernelResidual` (L384)

**主張:** 完全なcycleは退出するか、三つの型付きkernel障害(値の成長、時系列の不適格、文字どおりの停留)のちょうど一つに到達する。

**証明:** L351の残余枝を場合分けする。`anchor_growth`はそのままkernelの第一constructor。`same_anchor_not_earlier`では、旧crossingがendpointより前(`oldCrossingTime < downTime + 1`)なら`old_crossing_before_endpoint`。そうでなければ時系列適格なのでL203により`returnTime ≤ oldCrossingTime`となり、`not_earlier`と合わせて時刻の等号が出て`stationary`。

### `PermanentTailDischargeReturnCertificate.kernelStationary_of_oldCanonical` (L408)

**主張:** 旧crossingがこの正確なendpoint からのcanonical crossingそのものであるなら、kernelは実際にstationary constructorを含む。

**証明:** L242で時刻の等号を得て、anchor等式`parent.anchorParent = a(oldCrossingTime) = a(returnTime)`を書き換える。kernelのstationary枝が空でない(排除すべき実在の現象である)ことの確認である。

### `tailCursorCycle_no_stationary_exit` (L420)

**主張:** 文字どおり同一のcrossing(同anchor・同時刻)は、cursor精密化後もcycle退出として禁止されたままである。

**証明:** L324の同値でcursor進捗に還元すると、`anchor < anchor`または`(anchor = anchor かつ time < time)`が要求され、いずれも不可能。

## 全体の中での位置づけ

本モジュールは`PermanentAboveCycleRank.lean`の未解決点「discharge exit anchor dropの構成」を直接攻める、permanent above-target tail解析ファミリーの新しい最前線である。入力は`PermanentAboveHistory.lean`の有限historical下降と`PermanentAboveCanonical.lean`のcanonical upcrossing・`seenBelowCount`である。成果は二つ: (1) 等anchorでもより早いcrossingへの復帰を進捗と数えるcursor rankにより、非canonicalな等anchor loopは退出可能になった。(2) 退出の失敗は三つの型付きkernel残余に完全分類され、一般的な「anchor非減少」という曖昧さが消えた。続く`PermanentAboveCycleRebase.lean`は、このkernelのうちanchor成長と時系列不適格の二枝が、canonical returnを次の親に据え直すrebase操作で文字どおりのstationary kernelへ正規化されること(そして正規化ではstationary自体は消えないこと)を証明する。
