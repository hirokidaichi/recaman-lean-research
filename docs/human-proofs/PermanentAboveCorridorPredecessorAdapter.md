# PermanentAboveCorridorPredecessorAdapter

**役割:** terminal historical blockerの生成遷移から共通のpredecessor証明書を取り出し、そのpredecessorを既存の負potential normal domain、明示的なclock/sign残余、または最小のbelow-target historical domainの三つのsemantic outcomeへ完全分類する。

## このモジュールの役割

`PermanentAboveCorridorBlockerGeneration.lean`は、terminal historical blocker(終端crossingの最終減算を妨げた既出のbelow-target値`candidate`と、その初出時刻`firstTime`)の初出を作った実遷移が、合法減算か強制加算かのちょうど二形であることを示した。しかしblockerの着地値自体はtarget未満なので、target下界を要求する既存のnormal/debt探索domainには直接載らない。本モジュールは視点を一歩手前、すなわち初出直前の時刻`firstTime − 1`の軌道値(predecessor、直前値)へ移す。両生成枝はいずれも「predecessorの初出は`firstTime`より厳密に前にある」という共通のインターフェースを与えるので、これを`TerminalBlockerPredecessorCertificate`として統一する。その上でpredecessorの値をtargetと比較し、(1) target以上でclock ready(`target ≤ firstTime`)かつ負potentialなら既存の`NormalPhaseInvariantAt`(通常位相のnormal探索invariant)が成立、(2) target以上だがどちらかの条件が欠けるなら失敗条件をliteralに保持する残余、(3) target未満なら将来のcanonical return crossingを備えた最小のhistorical証明書、の三択に閉じる。

## 主要な定義

### `TerminalBlockerPredecessorCertificate` (L24)

生成枝に依存しない共通のpredecessor証明書。`a(firstTime − 1) = predecessor`、predecessorの初出`FirstAt a predecessor predecessorFirstTime`、`predecessorFirstTime < firstTime`(初出はblockerの初出より厳密に前)、targetとの位置の二分`predecessor < target ∨ target ≤ predecessor`、および生成分類`TerminalHistoricalBlockerGeneration`自体を保持する。

### `BelowTargetHistoricalPredecessorCertificate` (L76)

target未満のpredecessorに対する最小のsemantic domain。上記provenanceに加えて、`predecessor < target`、`firstTime − 1 < source.returnTime`(predecessor時刻はdischarge returnより前)、将来のweak upcrossing `WeakUpcrossingStep target (firstTime − 1) source.returnTime`、および「`firstTime − 1 = 0`(時刻0)か、正時刻なら商剰余座標`CoordinatesAt`が取れる」という分離を保持する。保持するcrossingが意図的に弱い(そのclockからの*最初*のcrossingとは限らない)ことに注意する: predecessorは元のdischarge endpointより前にあり得るためである。

### `AboveTargetPredecessorResidual` (L131)

target以上のpredecessorが負normal nodeとしてまだinstallできないときの正確な欠落条件。provenance、`target ≤ predecessor`、時刻`firstTime − 1`の座標に加えて、障害`firstTime < target`(clockがtarget-readyでない)または`0 ≤ potential quotient remainder`(potentialが非負)をliteralに保持する。

### `TerminalBlockerPredecessorSemanticOutcome` (L145)

predecessorの完全なsemantic分類を表す帰納型。`normal_ready`(既存の`NormalPhaseInvariantAt`がnode `⟨firstTime−1, predecessor, normal, a(firstTime−1)⟩`で成立)、`above_residual`、`below_historical`の三constructorを持つ。

## 定理と証明

### `TerminalOuterHistoricalBlockerCertificate.exists_predecessorCertificate` (L38)

**主張:** すべてのouter historical blocker(fresh endpoint証明書とblocker本体を束ねたもの)は共通のpredecessor証明書を持つ。

**証明:** blockerの生成分類で場合分けする。合法減算枝は、より大きいpredecessorとそのearlier初出、およびtarget位置の二分を生成データそのものとして保持しているので、そのまま詰め替える。強制加算枝では`candidate = a(firstTime−1) + firstTime`であり、生成データがpredecessor `a(firstTime−1)`の初出、`predecessorFirstTime < firstTime`、そして`a(firstTime−1) < target`を与えるので、位置の二分は左枝(target未満)で確定する。いずれの枝でも`predecessor_eq`は定義的に成り立つ。

### `TerminalBlockerPredecessorCertificate.toBelowTargetHistorical` (L93)

**主張:** predecessorがtarget未満なら、最小のbelow-target historical証明書(将来のcanonical return crossingを含む)へ持ち上げられる。

**証明:** 時刻については、blockerの`firstTime < source.returnTime`と`firstTime − 1 ≤ firstTime`から`firstTime − 1 < returnTime`。将来のcrossingは、discharge証明書が保持するreturn時のcanonical crossingの三成分(crossing直前値がtarget未満、着地値がtarget以上、強制加算であること)をそのまま流用し、開始時刻条件`firstTime − 1 ≤ returnTime`だけ差し替えて`WeakUpcrossingStep target (firstTime−1) returnTime`を組む。開始点が早まっただけなので「最初のcrossing」である保証は失われるが、weak形には十分である。座標は`firstTime − 1 = 0`かどうかで場合分けし、正時刻なら`exists_coordinatesAt`で商剰余を取る。

### `TerminalOuterHistoricalBlockerCertificate.predecessorSemanticOutcome` (L176)

**主張:** すべてのouter historical blockerは、既存の負normal domain、明示的なabove-target readiness/sign残余、最小のbelow-target historical domainのちょうどいずれか一つとしてsemantic的に利用できる。

**証明:** L38でpredecessor証明書を取り、target位置で場合分けする。

*target未満の枝。* L93を適用して`below_historical`。

*target以上の枝。* まず時刻`firstTime − 1`が正であることを確かめる: もし0なら`predecessor = a(0) = 0`だが、`target ≤ predecessor`かつ`0 < target`(tail証明書のtarget正値性)と矛盾する。よって座標`(quotient, remainder)`が取れる。次に二つの条件を順に検査する。

- `target ≤ firstTime`(clock ready)かつ`potential quotient remainder < 0`(負potential)なら、node `⟨firstTime−1, predecessor, normal, a(firstTime−1)⟩`について`NormalPhaseInvariantAt`の全フィールドを構成できる。時計条件`target ≤ (firstTime−1)+1`はblockerのbacktrack証明書が与える`0 < firstTime`と`target ≤ firstTime`から従い、値の条件は`predecessor_eq`の書き換えで`target ≤ a(firstTime−1) ≤ anchor`(anchorは自分自身なので等号)になる。`normal_ready`が成立。
- potentialが非負なら、その事実をliteralな障害`0 ≤ potential`として`above_residual`を返す。
- clockがreadyでないなら、`firstTime < target`を障害として`above_residual`を返す。

したがって三constructorで排他的かつ網羅的に閉じる。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「blocker predecessor adapter(三semantic outcomeへ分類済み)」に対応する。上流は`PermanentAboveCorridorBlockerGeneration.lean`(生成遷移の完全分類)と`PermanentAboveCorridorOuterHistory.lean`(backtrack証明書と`firstTime`の正値性)である。下流では、`below_historical`枝の証明書が`PermanentAboveCorridorPredecessorCrossing.lean`でready crossingの再選択へ接続され、`above_residual`枝は後に`PermanentAboveCorridorAboveClosure.lean`がorbit-ready/early representativeの完全定理で除去する。`normal_ready`枝は既存のnormal位相機構へ直接入る。「blockerの着地値ではなく、その直前値を意味的探索nodeに選ぶ」という`PermanentAboveCorridorOuterHistory.lean`末尾の未解決provenanceを、本モジュールが型として実装した形になる。
