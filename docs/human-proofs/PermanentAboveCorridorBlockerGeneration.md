# PermanentAboveCorridorBlockerGeneration

**役割:** terminal historical blocker(回廊終端の減算を妨げた既出値)の初出を作った実遷移を合法減算/強制加算へ完全分類し、同時に、その着地値がtarget未満であるため既存のnormal/debt意味的domainには直接載らないという境界を型として固定する。

## このモジュールの役割

`PermanentAboveCorridorBlocker.lean`は、回廊終端の最終減算を妨げた正の候補値`candidate`が、returnより前の時刻`firstTime`に初出するhistorical blocker(既出値による下降妨害)であることを示した。本モジュールはさらに一歩遡り、「その初出は誰が作ったのか」を問う。`candidate`は正なので初期状態`a(0) = 0`ではあり得ず、時刻`firstTime`への実遷移は合法減算(legal subtraction)か強制加算(forced addition)のどちらかである。合法減算枝ではより大きいpredecessor(直前値)`a(firstTime − 1)`とそのさらに早い初出時刻が得られ、強制加算枝ではpredecessorと時計`firstTime`がともにtarget未満に押さえられる。一方で、blockerの着地値そのものは`candidate < target`なので、通常探索のnormal状態(`NormalPhaseInvariantAt`)にもdebt状態(`DebtInvariant`)にも入れない。両invariantは値がtarget以上であることを要求するからである。この「数値的なrank辺は既にあるが、意味的な探索nodeとしての受け皿がない」という正確な境界を`TerminalHistoricalBlockerSemanticBoundary`として保存し、below-target専用のadapterが必要であることを明示する。証明地図の「blocker generation boundary」段階に対応する。

## 主要な定義

### `TerminalHistoricalBlockerGeneration` (L25)

blockerの初出`firstTime`を作った実遷移の型付き分類。二つの構成子を持つ。

- `legal_subtraction`枝: 時刻`firstTime`で減算可能であり、predecessor `predecessor = a(firstTime − 1)`、その初出`FirstAt a predecessor predecessorFirstTime`と`predecessorFirstTime < firstTime`、減算の算術`candidate + firstTime = predecessor`、着地前の未出性`candidate ∉ valuesThrough(firstTime − 1)`、`candidate < predecessor`、およびpredecessorとtargetの位置の選言(`predecessor < target ∨ target ≤ predecessor`)を保持する。
- `forced_addition`枝: 時刻`firstTime`で減算不能であり、`candidate = a(firstTime − 1) + firstTime`、predecessorの初出とその時刻`predecessorFirstTime < firstTime`、`a(firstTime − 1) < candidate`、`a(firstTime − 1) < target`、`firstTime < target`、および強制の理由(predecessorの減算候補が非正、または既出)を保持する。

### `TerminalHistoricalBlockerSemanticBoundary` (L140)

blocker証明書、その生成分類、および二つの不可能性(あらゆるnode・座標で`NormalPhaseInvariantAt`が成り立たないこと、あらゆるhorizon・anchorで`DebtInvariant`が成り立たないこと)を一つに束ねた構造。「生成のprovenanceは完全に判明しているが、既存domainには入れない」という状態を一証明書で表す。

## 定理と証明

### `TerminalHistoricalBlockerCertificate.generation` (L60)

**主張:** すべてのterminal historical blockerは`TerminalHistoricalBlockerGeneration`のいずれかの枝を与える。時刻0の枝は不可能である。

**証明:** 初出の最終遷移分類`firstAt_final_transition`(`DebtInvariant.lean`)は、初出時刻が0で値も0、合法減算による着地、強制加算による着地の三択を与える。

*初期状態枝の排除。* この枝では`candidate = a(0) = 0`となるが、blocker証明書は`0 < candidate`を保証するので矛盾。

*合法減算枝。* `firstTime`は正であり、`legalSubtraction_firstAt_predecessor`(`DebtSubtraction.lean`)がpredecessor `predecessor = a(firstTime − 1)`、その初出時刻`predecessorFirstTime < firstTime`、和の式`candidate + firstTime = predecessor`、着地前の`candidate`の未出性、`candidate < predecessor`を一括で与える。合法減算は「未出の値へ降りる」遷移なので、着地値の初出がまさに`firstTime`であることと整合し、predecessorはより大きい値のより早い初出として過去向き探索の次の候補になる。predecessorとtargetの位置は`Nat.lt_or_ge`による全域的な選言としてそのまま保持する(この選言の各枝を実際に処理するのは下流の`PermanentAboveCorridorPredecessorAdapter.lean`である)。

*強制加算枝。* `candidate = a(firstTime − 1) + firstTime`である。predecessorは履歴`valuesThrough(firstTime − 1)`の元なので初出時刻`predecessorFirstTime < firstTime`を持つ。加算の式から`a(firstTime − 1) < candidate`。`candidate < target`(blocker証明書)と合わせて`a(firstTime − 1) < target`、さらに`firstTime ≤ a(firstTime − 1) + firstTime = candidate < target`から`firstTime < target`。つまり強制加算枝では値も時計もすべてtargetで押さえられる。減算不能の理由(候補が非正、または既出)も定義の分解からそのまま保持する。

### `TerminalHistoricalBlockerCertificate.not_normalPhaseInvariantAt` (L115)

**主張:** blockerの着地は、その初出時計`firstTime`においていかなるnode・商剰余についても通常のnormal意味的状態`NormalPhaseInvariantAt`になれない。

**証明:** `NormalPhaseInvariantAt`は局所値がtarget以上であること(`target_le_value`)を要求する。しかし時刻`firstTime`の値は`candidate`であり、blocker証明書の`candidate_below_target`により`candidate < target`。矛盾。

### `TerminalHistoricalBlockerCertificate.not_debtInvariant` (L129)

**主張:** 同様に、blockerの着地値はhorizonとanchorの選び方に依らず`DebtInvariant`のdebt値になれない。

**証明:** `DebtInvariant`の`target_le`(debt値はtarget以上)が`candidate < target`と直接矛盾する。

### `TerminalHistoricalBlockerCertificate.semanticBoundary` (L153)

**主張:** すべてのterminal historical blockerは、生成分類と二つの不可能性を束ねた`TerminalHistoricalBlockerSemanticBoundary`に到達する。

**証明:** L60、L115、L129を構造体に詰めるだけである。

### `TerminalOuterHistoricalBlockerCertificate.semanticBoundary` (L167)

**主張:** outer historical枝(immediate valley枝とfinite window枝の共通provenance、`PermanentAboveCorridorOuterHistory.lean`)のどちらのblockerも、内蔵する共通のblocker証明書を通じて同じ生成分類と意味的境界を継承する。

**証明:** 内蔵する`blocker`成分にL153を適用する射影である。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「blocker generation boundary」(生成分類・no-go済み)に対応する。入力は`PermanentAboveCorridorBlocker.lean`のblocker証明書、`PermanentAboveCorridorOuterHistory.lean`のouter historical証明書、および`DebtInvariant.lean`/`DebtSubtraction.lean`の初出遷移補題である。ここで確立したno-go(着地値はnormal/debt domainに入らない)が、below-target専用の受け皿を作る`PermanentAboveCorridorPredecessorAdapter.lean`の直接の動機となる。同adapterは本モジュールの生成分類の両枝から共通のpredecessor証明書を取り出し、predecessorがtarget以上なら既存normal domainへ、target未満なら新しいhistorical certificateへ振り分ける。
