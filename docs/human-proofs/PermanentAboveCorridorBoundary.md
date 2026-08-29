# PermanentAboveCorridorBoundary

**役割:** below-target sourceでの合法減算とその直後の強制加算は元の値`+1`へ着地するという二歩式を使い、targetが未出である限り、回廊内の合法減算endpointがcanonical return predecessorに一致することは不可能である(一致すれば正確にtargetを実現してしまう)ことを証明する。

## このモジュールの役割

`PermanentAboveCorridorSuffix.lean`の分類では、合法減算の子endpoint `time + 1`は`time + 1 ≤ returnTime`までしか言えず、endpointがreturn predecessorそのものに着地する境界ケースが残っていた。本モジュールはこの境界(legal return boundary)を排除する。鍵は`CoordinateDynamics.lean`の既存二歩式「合法減算の直後に強制加算が続くと`a(n+2) = a(n) + 1`」である。減算元の値がtarget未満で、二歩目がweak upcrossing(着地がtarget以上)なら、着地値は`a(n) + 1 ≤ target`かつ`≥ target`となり、正確に`target`に等しくなる。targetは未出という前提(missing-target provenance)の下ではこれは矛盾なので、すべてのlegal suffix childはreturnより厳密に前に留まる。この分離により、後続のlegal endpointが尽きたときの残余は純粋なall-forced suffixに限定される。

## 定理と証明

### `legalSubtraction_forcedAddition_crossing_hits_target` (L22)

**主張:** `a(time) < target`で、時刻`time+1`への一歩が合法減算、`time+2`への一歩が強制加算、かつ`target ≤ a(time+2)`なら、`a(time+2) = target`。

**証明:** 二歩式`a_sub_then_add_eq_succ`により`a(time+2) = a(time) + 1`。`a(time) < target`から`a(time+2) = a(time) + 1 ≤ target`であり、仮定`target ≤ a(time+2)`とあわせて等号になる。谷を降りて登り返すと元の値のちょうど1上に出るため、下からtargetを「飛び越える」ことができない、という算術的観察である。

### `CanonicalBelowCorridorSuffix.internalSubtraction_ne_return` (L34)

**主張:** targetが未出(`¬∃ witness, a(witness) = target`)なら、suffix内部の時刻`endpointTime ≤ time < returnTime`での合法減算の着地時刻はreturnに一致しない: `time + 1 ≠ returnTime`。

**証明:** 背理法で`time + 1 = returnTime`とする。回廊の下側性(`value_below_of_between`)により減算元`a(time) < target`。first return crossingの定義から、時刻`returnTime + 1 = time + 2`への一歩は強制加算であり、着地は`target ≤ a(time+2)`を満たす。するとL22により`a(time+2) = target`となり、targetの出現witnessができてmissing仮定に矛盾する。

### `CanonicalBelowCorridorSuffix.internalSubtraction_before_return` (L58)

**主張:** 強形: missing-target仮定の下で、すべてのlegal内部endpointはreturnより厳密に前にある: `time + 1 < returnTime`。

**証明:** `time < returnTime`から`time + 1 ≤ returnTime`であり、L34の不等号とあわせて厳密不等式になる。

### `CanonicalBelowCorridorSuffix.child_of_internalSubtraction_missing` (L74)

**主張:** missing-target回廊内のlegal childは、次の四点を同時に持つ: (1) 同じcanonical returnを持つ子suffix(endpoint `time + 1`)の存在、(2) 履歴予算`missingBelowCount`の厳密下降、(3) suffix cursor(`returnTime − endpointTime`)の厳密下降、(4) `time + 1 < returnTime`という厳密なendpoint分離、そして(5) 残りのsuffixの全域分類 — より後のlegal endpointが存在するか、子suffixがall-forcedであるか。

**証明:** (1)(2)(3)は`PermanentAboveCorridorSuffix.lean`の`child_of_internalSubtraction`から、(4)はL58から得る。(5)は「`time + 1 ≤ later < returnTime`で合法減算可能な`later`が存在するか」の排中律による場合分けで、存在しない側の否定は定義を展開するとそのまま子suffixの`AllForcedAdditionSuffix`である。

### `CanonicalReturnRebaseCertificate.legalSuffixChild_missingBoundary` (L104)

**主張:** 仮想的なpermanent tail(rebased stationary証明書)に適用すると、discharge回廊内の任意の合法減算(`downTime + 1 ≤ time < returnTime`)について、`time + 1 < returnTime`を満たす子suffixが存在し、履歴予算が厳密に下降し、残りは「より後のlegal endpointの存在」または「all-forced suffix」に分類される。

**証明:** discharge証明書から`exists_belowCorridor`で回廊を取り、`toSuffix`でfresh downcross endpointのsuffixに変換する。missing-target仮定は結合tail証明書の`target_missing`から供給され、L74をそのまま適用する。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「legal return boundary」(exact targetで排除済み)に対応する。上流は`PermanentAboveCorridorSuffix.lean`のsuffix構造と`CoordinateDynamics.lean`の二歩式である。下流では、`PermanentAboveCorridorWindow.lean`がL104の分類の「後続legal endpointなし」枝からterminal all-forced crossing windowを構成し、`PermanentAboveCorridorTerminal.lean`がsuffix cursorへの強帰納の各段でL104を使ってchildをreturnの厳密に手前へ送る。仮想反例(target未出)という大域仮定が、回廊内部の一致ケースを局所算術だけで消すという意味で、本モジュールはmissing-target provenanceが実際に仕事をする最初の場所である。
