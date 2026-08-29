# PermanentAboveCorridorSuffix

**役割:** return crossingを固定したまま、below corridorの後方のfresh endpointから始まる「canonical corridor suffix」を導入し、内部の合法減算ごとに履歴予算と`returnTime − endpointTime`のcursorが同時に厳密下降することを示して、legal endpointの消費を整礎rankで有限化する。

## このモジュールの役割

`PermanentAboveCorridor.lean`は回廊の第一歩と各内部遷移を局所的に分類したが、合法減算が起きた後の「残りの区間」を再び同じ形の解析対象として扱う枠組みがなかった。本モジュールの鍵は、first weak upcrossing(ある開始点以後で最初に起きる強制加算によるtarget未満→target以上の横断)が、開始点を同じ回廊内のより後のbelow-target点へ制限しても同じ時刻のままcanonicalであり続けるという観察である。これにより「fresh endpointとそのfirst return」という二点データ`CanonicalBelowCorridorSuffix`が、合法減算のたびに後方へ進む自己相似な証明書になる。endpointの移動は`missingBelowCount`(履歴予算)と`returnTime − endpointTime`(return までの残距離)を同時に厳密に下げ、後者は整礎なので、同じreturnに属するlegal endpointの消費は有限回で終わる。ただしreturn crossing自体は意図的に固定しており、外側のstationary cycleはこのrankでは動かない。

## 主要な定義

### `CanonicalBelowCorridorSuffix` (L47)

freshなbelow-target endpointとそのfirst return crossingの組: (1) `a(endpointTime)`の初出が時刻`endpointTime`にあること、(2) `a(endpointTime) < target`、(3) `FirstWeakUpcrossingStep target endpointTime returnTime`。

### `corridorSuffixRemaining` (L66)

suffix endpointから固定returnまでの残距離`returnTime − endpointTime`。

### `CorridorSuffixProgress` (L69)

固定した`returnTime`の下で、子endpointの残距離が親endpointの残距離より厳密に小さいという関係。

### `AllForcedAdditionSuffix` (L130)

suffix内部にもはや合法減算が残っていないこと: `endpointTime ≤ time < returnTime`の全時刻で減算不能。

## 定理と証明

### `FirstWeakUpcrossingStep.suffix` (L22)

**主張:** `FirstWeakUpcrossingStep target start returnTime`の開始点を、`start ≤ suffixStart ≤ returnTime`を満たす後方の点へ制限しても、同じ`returnTime`がcanonical first upcrossingのままである。

**証明:** crossing本体(時刻`returnTime`でのbelow値・強制加算・target以上への着地)は開始点に依存しない条件なのでそのまま流用でき、`start_le`だけを`suffixStart ≤ returnTime`に差し替える。最小性は、後方開始点からのより早いupcrossingが`start ≤ suffixStart`の推移律によりそのまま元の開始点からのupcrossingにもなるため、元のfirst性に矛盾することから従う。

### `CanonicalBelowCorridorCertificate.toSuffix` (L55)

**主張:** historical corridor証明書は、そのfresh downcross endpoint `downTime + 1`におけるcanonical suffixを与える。

**証明:** 回廊証明書の`endpoint_first`、downcrossの`endpoint_below`、`first_return`をそのまま束ねる。

### `corridorSuffixProgress_wellFounded` (L75)

**主張:** suffix endpoint cursorは整礎である(無限下降列が存在しない)。

**証明:** 自然数の整礎性のaccessibilityを、rank写像`corridorSuffixRemaining returnTime`に沿ってendpointへ引き戻す標準的な議論である。

### `corridorSuffixProgress_of_later` (L91)

**主張:** return以前(`childEndpoint ≤ returnTime`)でendpointを厳密に後方へ動かすと、cursorは厳密に下降する。

**証明:** `returnTime − childEndpoint < returnTime − parentEndpoint`の自然数算術(omega)。

### `CanonicalBelowCorridorSuffix.child_of_internalSubtraction` (L101)

**主張:** suffix内部の時刻`endpointTime ≤ time < returnTime`での合法減算は、同じcanonical returnを持つfreshな後方suffix(endpoint `time + 1`)を作り、履歴予算とendpoint cursorの両方を厳密に下げる。

**証明:** 着地値`a(time+1)`は、区間下側性(`FirstWeakUpcrossingStep.value_below_of_between`)によりtarget未満であり、合法減算の着地値は定義上未出なので初出が時刻`time+1`にある。L22により同じ`returnTime`が新endpointからのfirst returnのままなので、三条件を束ねて子suffixができる。below-target値の新初出は`missingBelowCount_strict_of_firstAt`により履歴予算を厳密に下げ、endpointの後退はL91によりcursorを厳密に下げる。

### `AllForcedAdditionSuffix.returnTime_lt_target` (L138)

**主張:** 空でない(`endpointTime < returnTime`)all-forced suffixでは、return時刻自体がtarget未満である: `returnTime < target`。

**証明:** 最後の内部時刻`returnTime − 1`も強制加算なので`a(returnTime) = a(returnTime−1) + returnTime ≥ returnTime`。一方crossingの`below`条件により`a(returnTime) < target`。両者から`returnTime < target`。すなわち、合法減算を一切含まない遅延returnは時計そのものがtargetで頭打ちになる。

### `CanonicalBelowCorridorSuffixOutcome` (L161)

suffixの全域的な三分類を表すinductive命題。

- `at_return`: `endpointTime = returnTime`(endpointがreturn predecessorそのもの)。
- `later_legal_endpoint`: 内部に合法減算があり、その子suffixと履歴予算・cursorの同時厳密下降を保持する。
- `all_forced`: 内部が全て強制加算で、`returnTime < target`のtarget有界residual。

### `CanonicalBelowCorridorSuffix.outcome` (L184)

**主張:** すべてのcanonical suffixは上の三分類のいずれかに入る。

**証明:** まず`endpointTime = returnTime`なら`at_return`。そうでなければ`start_le`から`endpointTime < returnTime`。内部の合法減算の存在で場合分けし、存在すればL101の子構成で`later_legal_endpoint`、存在しなければその否定が定義そのままに`AllForcedAdditionSuffix`であり、L138の境界とあわせて`all_forced`になる。

### `CanonicalReturnRebaseCertificate.suffixOutcome` (L209)

**主張:** rebased stationary証明書(`PermanentAboveCycleRebase.lean`)は、そのhistorical endpointにおけるsuffix outcomeを直接露出する。

**証明:** discharge証明書の`exists_belowCorridor`(`PermanentAboveCorridor.lean`)を`toSuffix`でsuffixに変換し、L184を適用するだけである。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「corridor suffix cursor」(有限化済み)に対応する。上流は`PermanentAboveCorridorRank.lean`(importの直接の親)と`PermanentAboveCorridor.lean`の回廊証明書である。下流では、`PermanentAboveCorridorBoundary.lean`がmissing-target仮定の下で`later_legal_endpoint`枝のendpointがreturnに一致し得ないことを示して分類を精密化し、`PermanentAboveCorridorWindow.lean`が`all_forced`枝を有限算術証明書へ変換し、`PermanentAboveCorridorTerminal.lean`が本モジュールのcursorに対する強帰納でlegal endpoint列全体を消費する。suffix cursorは固定return内の探索を有限化するが、return crossing自体を変えないため、外側の停留cycleの解消は後続モジュールの課題として残る。
