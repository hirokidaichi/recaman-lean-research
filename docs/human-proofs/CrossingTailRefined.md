# CrossingTailRefined

**役割:** ready crossingに残る最後の枝を長期軌道命題`TargetTailReturnHypothesis`(tail return)まで縮約し、tail returnがあればready crossingの局所stepが完全に閉じること、および全targetのtail returnが全射性予想そのものと同値であることを証明する。

## このモジュールの役割

`CrossingDowncrossRefined`は「保存horizon以後にdowncross(target以上からtarget未満への一歩の下方横断)がある」枝を、`CrossingBelowRefined`は「horizonの値がtarget未満」の枝を処理した。後者の成長残余では、拡大した子horizonの値が必ずtarget以上に戻るため、残るのはただ一つ、「target以上から出発した軌道が二度とtarget未満へ戻らない」可能性である。本モジュールはこの境界を明示的な命題として述べ、(1) downcross不在は「以後ずっとtarget以上」という恒久tailと同値であること、(2) 最小未出targetという仮想反例はまさにこの恒久tail挙動を強制するため、tail returnは局所補題ではなく予想の大域的核心であること、(3) それでもtail returnを仮定すればready crossingの局所全域stepが完成すること、の三点を証明する。

## 定理と証明

### `exists_futureDowncrossStep_between` (L20)

**主張:** `start ≤ finish`、`target ≤ a(start)`、`a(finish) < target`ならば、`start`以後のある時刻に`FutureDowncrossStep target start time`が存在する。すなわち、上から下へ渡る有限区間の中には隣接したdowncrossがある。

**証明:** `start`からの距離に関する帰納法である。距離0では両端の仮定が矛盾する。距離`d+1`では、一つ手前の値`a(start+d)`がtarget以上なら、その一歩`start+d → start+d+1`(端点はtarget未満)が求めるdowncrossである。target未満なら帰納法の仮定を距離`d`に適用する。`DowncrossBudgetGap`の上方横断存在定理の鏡像にあたる。

### `no_futureDowncross_iff_tail_atOrAbove` (L51)

**主張:** `target ≤ a(start)`のとき、「`start`以後にdowncrossが存在しない」ことは「すべての`time ≥ start`で`target ≤ a(time)`」と同値である。

**証明:** (⇒) ある将来時刻で値がtarget未満なら、前定理により途中に隣接downcrossが存在して仮定に反する。(⇐) tailが常にtarget以上なら、どのdowncross候補もその端点`a(time+1) < target`がtail条件に矛盾する。

### `LeastMissingTarget` (L69)

**構造:** `target`が最小の未出値であること、すなわち`target`が全軌道に一度も出現せず、かつそれより小さいすべての値が出現することを表す命題である。全射性予想の仮想的な最小反例を表す。

### `exists_historyHorizon_covering_below` (L75)

**主張:** target未満の各値に個別の出現証人があるなら、それらをまとめて一つの履歴horizonに収められる: ある`horizon`が存在して、target未満のすべての値が`valuesThrough horizon`に属する。

**証明:** targetに関する帰納法である。target = 0では空条件であり、horizon 0でよい。target+1では、帰納法の仮定でtarget未満を覆うhorizonを取り、値targetの出現時刻との最大値を新しいhorizonにする。履歴`valuesThrough`は時間について単調なので、両方の被覆が保たれる。

### `no_futureDowncross_of_belowCovered` (L103)

**主張:** target未満のすべての値がすでに時刻`start`までの履歴に含まれているなら、`start`以後にdowncrossは存在しない。

**証明:** downcrossがあったとする。その一歩は合法減算である(強制加算なら値が増え、端点がtarget未満であることに矛盾)。合法減算の着地値は定義により履歴に未出(fresh)でなければならない。しかし端点はtarget未満なので被覆仮定によりすでに`valuesThrough start ⊆ valuesThrough time`に含まれており、freshであることと矛盾する。つまり「downcrossの端点はfreshなbelow-target値」という`CrossingDowncrossRefined`の予算低下機構は、below-targetの値が尽きた瞬間に不可能になる。

### `LeastMissingTarget.eventually_strictlyAbove` (L128)

**主張:** 仮想的な最小未出targetに対し、ある開始時刻`start`が存在して、target未満のすべての値が`valuesThrough start`に含まれ、かつ`start`以後のすべての時刻で`target < a(time)`が成り立つ。すなわち軌道はいずれ残りすべてでtargetの真上に留まる。no-downcross枝が「欠けた局所crossing補題」ではなく予想の大域的核心である理由を示す定理である。

**証明:** targetは正である(0なら`a(0)=0`が出現に反する)。最小性から、target未満の値には各々出現証人があるので、`exists_historyHorizon_covering_below`で被覆horizonを取る。補助命題として「被覆されたtarget以上の開始点からのtailは厳密にtargetの上にある」ことを示す: 被覆により`no_futureDowncross_of_belowCovered`でdowncrossがなく、同値定理によりtailは常にtarget以上、さらにtargetは未出なので等号は起こらず厳密である。被覆horizon自身の値がtarget以上ならそこを開始点にすればよい。target未満なら`exists_weakUpcrossingStep_from_below`で次の上方横断を取り、その着地時刻`time+1`を開始点にする。被覆は後の時刻へ単調に引き継がれ、着地値はtarget以上なので、同じ補助命題が適用できる。

### `TargetTailReturnHypothesis` (L169)

**定義:** 残るcrossing枝が必要とする正確な長期軌道命題である: 「`target ≤ a(start)`なるすべての開始時刻について、targetがどこかに出現するか、または`start`以後のある時刻で値がtarget未満に戻る」。targetがすでに見つかった後のdowncrossまでは要求しない。

### `LeastMissingTarget.not_targetTailReturn` (L177)

**主張:** 最小未出targetはtail return仮説を反証する。したがって、すべての正のtargetについてtail returnを証明することは、仮想的な最小反例が強制するeventually-above挙動をちょうど排除することにあたる。

**証明:** `eventually_strictlyAbove`の開始点にtail return仮説を適用する。出現枝はtargetの未出性に矛盾し、下方復帰枝はtailが厳密に上に留まることに矛盾する。

### `all_targetTailReturn_implies_surjective` (L191)

**主張:** すべてのtargetについてtail return仮説が成り立つなら、すべてのtargetが軌道に出現する(全射性)。

**証明:** targetに関する強帰納法である。targetが出現しないと仮定すると、帰納法の仮定によりそれ未満の値はすべて出現するので、targetは`LeastMissingTarget`になる。前定理によりそのtargetのtail return仮説が破れ、仮定に矛盾する。

### `all_targetTailReturn_iff_surjective` (L210)

**主張:** tail return仮説の族は元のレカマン全射性予想と同値である:

```text
(∀ target, TargetTailReturnHypothesis target) ↔ ∀ target, ∃ time, a(time) = target
```

**証明:** 左から右は前定理である。右から左は、全射性があれば各tail return文は出現枝で直ちに成立する。この同値により、tail returnは「弱い局所補題」ではなく予想の言い換えであることが確定する。

### `ReadyCrossingTailDowncrossHypothesis` (L219)

**定義:** 同じtail境界のready crossing形である: horizonの値がtarget以上であるすべてのready crossingノードについて、targetの出現か、保存horizon以後の`FutureDowncrossStep`の存在を要求する。

### `readyCrossingTailDowncross_of_targetTailReturn` (L227)

**主張:** target-tail returnはcrossing recoveryが使うdowncross形を供給する。

**証明:** ノードのhorizonを開始点としてtail returnを適用する。出現枝はそのまま、下方復帰枝は`exists_futureDowncrossStep_between`で隣接downcrossに変換する。

### `ReadyCrossingSearchInvariant.refinedStep_of_tailDowncross` (L242)

**主張:** tail-downcross境界を仮定すれば、すべてのready crossingノードからの局所stepは全域である: targetが出現するか、refined domainの子へのランク進捗が存在する。

**証明:** horizonの値で二分する。

**horizonがtarget以上の場合。** 仮説をノードに適用する。出現ならば終了。downcrossが得られれば`CrossingDowncrossRefined`の`refinedStep_of_futureDowncross`で閉じる。

**horizonがtarget未満の場合。** `CrossingBelowRefined`の三分岐を適用する。出現枝と進捗枝はそのまま終わる。残るのは成長残余であり、続行の横断時刻`time`、ready crossing子`child = ⟨time+2, a(time), normal, a(time)⟩`、予算安定、anchor非減少、進捗不成立が与えられている。

まず子horizonの値`a(time+2)`がtarget以上であることを示す。そうでなければ、横断の着地`target ≤ a(time+1)`から一歩でtarget未満へ落ちる遷移`time+1 → time+2`が親horizon以後のdowncrossとなり、`FutureDowncrossStep.strict_budget_drop`が親に対する予算の厳密低下を与える。これは残余が記録する予算安定と矛盾する。つまり、予算が安定したままの成長残余では、拡大した子horizonは強制的にtargetの上へ戻っている。

そこでtail-downcross仮説を子に適用する。出現ならば終了。子horizon以後のdowncrossが得られれば、`CrossingDowncrossRefined`の強形`refinedStep_of_futureDowncross_withBudgetDrop`を子に適用し、次ノード`next`と子horizonに対する予算の厳密低下を得る。残余の予算安定`missingBelowCount(child.horizon) = missingBelowCount(node.horizon)`で書き換えると、この低下はそのまま元の親に対する予算低下になる。よって`next`は辞書式第一成分で元の親`node`へ直接進捗する。anchorが下がらなかった中間の子crossingは、ランク上は経由せずに飛び越えられる。

### `ReadyCrossingSearchInvariant.refinedStep_of_targetTailReturn` (L296)

**主張:** より軌道寄りの定式化であるtarget-tail returnからも、同じready crossing局所stepが閉じる。

**証明:** `readyCrossingTailDowncross_of_targetTailReturn`で仮説を変換し、前定理に渡す。

## 全体の中での位置づけ

証明地図の「crossing above tail」「tail returnの強さ」の二行に対応する。`RefinedOracleBoundary`が一点に絞った残余`CrossingRefinedStepHypothesis`は、`CrossingDowncrossRefined`・`CrossingBelowRefined`と本モジュールにより、`TargetTailReturnHypothesis`という単一の長期命題まで縮約された(仮説があれば`refinedStep_of_targetTailReturn`が`CrossingRefinedStepHypothesis`を与え、`crossingRefinedStepHypothesis_implies_occurs`で出現が従う)。同時に`all_targetTailReturn_iff_surjective`は、この命題の族が全射性予想の言い換えであることを示し、残る困難の正確な所在を確定する。この認識を受けて、`PermanentAboveTail`以降のモジュール群は同値性を仮定として使わず、最小未出targetが強制する恒久上方tail(`MissingPermanentAboveTail`)の内部構造をさらに解析していく。
