# DowncrossBudgetGap

**役割:** downcross再開ノードに残っていた履歴予算ギャップを、将来の弱上方crossingから作る`crossing_recovery`子で閉じる。

## このモジュールの役割

拡張履歴normalノード(過去の代表時刻の値を、より後の履歴時刻に載せたノード)に対する一般論では、履歴予算(history budget、`missingBelowCount`: その時刻までに未出であるtarget未満の値の個数)が代表時刻からhorizonまでの間にすでに真に減っていると、代表状態から得たランク下降を子ノードへ輸送できない。downcross再開(downcross restart: 軌道がtarget以上からtarget未満へ下向きに横断した後、その端点を新しい履歴horizonとして探索を再開する生成機構)は、まさにこの「悪い輸送」の場合そのものである。本モジュールは、この機構が一般証明書より多くの情報——horizonでの実際の軌道値がtarget未満であること——を保持している点を使い、将来の弱上方crossing(weak upcrossing: 強制加算によるtarget未満からtarget以上への一歩の横断)を経由して四成分ランクのanchor成分を真に下げ、この生成機構を完全に閉じる。ここで定義される`WeakUpcrossingStep`とその存在定理は、後続の`CrossingBelowRefined`や`CrossingTailRefined`でも横断の基本部品として再利用される。

## 主要な定義

### `WeakUpcrossingStep` (L25)

時刻`time`における一回の強制加算遷移で、`start ≤ time`、`a(time) < target ≤ a(time+1)`、かつ時刻`time+1`では減算が不可能(強制加算)であることを表す命題である。「start以後の将来に起きる、下から上への一歩の横断」を証明付きで記録する。

## 定理と証明

### `exists_weakUpcrossingStep_between` (L33)

**主張:** `start ≤ finish`、`a(start) < target`、`target ≤ a(finish)`ならば、`start`以後のある時刻`time`に`WeakUpcrossingStep target start time`が存在し、しかも`time + 1 ≤ finish`である。

**証明:** `start`から`finish`までの距離に関する帰納法である。距離0では仮定`a(start) < target`と`target ≤ a(start)`が矛盾する。距離`d+1`では、一つ手前の時刻`start+d`の値がすでにtarget以上なら帰納法の仮定を適用する。target未満なら、この一歩`start+d → start+d+1`が横断である。この一歩が合法減算だとすると次の値は現在値以下、すなわちtarget未満となり、`target ≤ a(start+d+1)`に矛盾する。よってこの一歩は強制加算であり、求める`WeakUpcrossingStep`が得られる。要するに「下から上へ渡る有限区間の中には、必ず隣接した強制加算の横断がある」——減算では値が増えないからである。

### `exists_weakUpcrossingStep_from_below` (L86)

**主張:** `0 < target`かつ`a(start) < target`ならば、`start`以後のある時刻に弱上方crossingが存在する。有限区間の両端を仮定しない、下側からの無条件の存在定理である。

**証明:** 二つに場合分けする。

1. 時計がすでにtarget-ready(`target ≤ start+1`)の場合。次の一歩で`start+1`を引くには`start+1 < a(start)`が必要だが、`a(start) < target ≤ start+1`なのでこれは不可能である。よって次の一歩は強制加算で、`a(start+1) = a(start) + (start+1) ≥ start+1 ≥ target`となり、時刻`start`自身が横断時刻になる。
2. まだtarget-readyでない場合。`InitialRegion`の定理により、時刻`target−1`または`target`にtarget-readyかつ値がtarget以上の正準状態が存在する。この時刻は`start`より後なので、`start`からそこまでの有限区間に前定理を適用して横断を得る。

### `DowncrossRestartNormalProvenance.representativeStep_or_budgetTransport` (L119)

**主張:** downcross再開の生成証明`h`に対し、履歴horizonと代表時刻の双方がtarget-readyならば、targetの出現か、または「代表時刻のノードに対してはランク進捗する子」と、この進捗を子ノードへ輸送できないことを記録した`budget_transport`残余が同時に得られる。

**証明:** 代表時刻の状態はtarget-readyなのでorbit-ready normalとみなせ、その局所全域step(`OrbitReadyNormalInvariant.phaseSemanticStep`)を適用する。得られる進捗は代表時刻ノードに対するものである。一方、downcross再開の定義には代表時刻からhorizonまでの厳密な予算低下が含まれるため、この進捗を後のhorizonを持つ子ノードへそのまま移すことはできない。この二つの事実をそのまま`ExtendedHistoryNormalResidual.budget_transport`として束ねる。この定理は一般論の限界を正確に述べるためのもので、次の定理が別経路でこの残余を回避する。

### `DowncrossRestartNormalProvenance.phaseSemanticStep` (L156)

**主張:** downcross再開の生成証明`h`から、無条件に、targetの出現か、または意味的domainに属し子ノードに対してランク進捗する次ノードが得られる。この機構に対する局所全域stepである。

**証明:** 子ノードのhorizonにおける軌道値はtarget未満である(downcrossの端点)。そこで`exists_weakUpcrossingStep_from_below`により、将来の弱上方crossing時刻`time`を取る。三分岐する。

- targetが時刻`time`までの履歴にすでに含まれるなら、その出現時刻が証人である。
- 横断の着地が正確に`a(time+1) = target`なら、`time+1`が証人である。
- それ以外なら横断は厳密(`target < a(time+1)`)である。強制加算の一歩なので`a(time+1) = a(time) + (time+1)`が成り立ち、`DebtCrossing`(厳密crossing)の証明が組める。次ノードを`⟨time+2, a(time), normal, a(time)⟩`とし、旧代表値`v = h.certificate.value`をanchor(アンカー: ランク比較の基準となる親の値)とする`CrossingRecoveryInvariant`を構成する。鍵となる不等式は`a(time) < target ≤ v`である。すなわちpre-crossing値はtarget未満、旧代表値はtarget以上なので、normal同士のanchor成分が真に下がる。horizonは`time+2`へ伸びるだけで縮まないから、履歴予算は増えず、四成分辞書式ランクはanchor成分で真に低下する(`phaseSearchProgress_of_horizonAndAnchor`)。

つまり、予算輸送の失敗という一般的障害を、この機構が保持する「target未満の実端点」からcrossing recoveryを作ることで迂回する。新しい位相もランクも必要ない。

### `DowncrossRestartNormalProvenance.phaseSemanticStep_from_source` (L207)

**主張:** 同じ回復は生成元(provenance source)の親ノードまで合成できる。すなわちtargetの出現か、親に対してランク進捗する意味的次ノードが得られる。

**証明:** 前定理の次ノードは子に対して進捗し、downcross再開の定義が持つ`rank_edge`(元の予算低下による子から親への進捗)と辞書式順序の推移性で合成する。

### `downcross_four_actual_crossingRecovery` (L222)

**主張:** 完成した機構は最小の実例で実現される。target 4に対し、親`⟨3, a(3), normal, a(3)⟩`(`a(3) = 6`)、子`⟨4, 6, normal, 6⟩`(horizonでは`a(4) = 2 < 4`)というdowncross再開が実在し、次ノード`⟨6, a(4), normal, a(4)⟩`は`CrossingSearchInvariant`を満たして子に対しランク進捗する。

**証明:** 実軌道`a(3)=6, a(4)=2, a(5)=7`について、時刻4での横断`2 < 4 < 7 = 2+5`、座標`a(5) = 5·1 + 2`、anchorの下降`2 < 6`などをすべてLeanカーネルの`decide`で検証する。旧anchor 6がpre-crossing値2へ真に下がることが確認できる。

## 全体の中での位置づけ

本モジュールは証明地図の「意味的探索domain」の行に属し、extended-history閉包の一角である「downcross由来の予算ギャップ」を`crossing_recovery`への接続で閉じた(PROOF_MAP: generic budget gapとearly representativeもcrossing recoveryへ接続)。`DowncrossRestartNormalProvenance`は`TypedNormalProvenance`で定義された5種類のhistorical生成機構の一つであり、その閉包がここで完成する。また、ここで導入した`WeakUpcrossingStep`と`exists_weakUpcrossingStep_from_below`は、`CrossingBelowRefined`のhorizon-below分類、`CrossingTailRefined`の最小未出target解析、さらに`PermanentAboveCanonical`のcanonical upcrossing構成など、下流のcrossing解析全体の基本部品になっている。
