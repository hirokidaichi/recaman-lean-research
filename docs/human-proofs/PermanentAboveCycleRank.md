# PermanentAboveCycleRank

**役割:** zero-budget恒久tail専用に、crossing anchorを最外層とし`crossing → backtrack → discharge`を一方向phaseとする四成分整礎rankを定義し、historical探索の全内部stepを厳密下降で閉包する。dischargeからcrossingへ戻れることはstrict anchor dropと同値であり、停留cycleは進捗として排除される。

## このモジュールの役割

恒久上方tail(以後ずっとtargetより大きい軌道区間)の内部では履歴予算`missingBelowCount`(未出のtarget未満値の個数)が0で飽和しており、従来の位相探索rankの最外成分は動かない。さらに`PermanentAboveHistory.lean`は、任意のcrossing選択の下でchild = parentの停留残余が構成でき、`PermanentAboveCanonical.lean`はearliest選択でもそれが消えないことを示した。本モジュールはこの状況への構造的応答として、新しい四成分辞書式rankを与える。最外層にcrossing anchor(pre-crossing値)、その下に一方向のphase `crossing(2) → backtrack(1) → discharge(0)`、内層にdual budget `seenBelowCount`とtail最小値を置く。historical探索の内部step(backtrackへの進入、tail更新、downcross処理)はすべてこのrankで厳密に下降する。一方、dischargeからcrossingへ戻るrank辺はstrict anchor dropと必要十分であることを示し、同anchorの停留loopをrankの構造自体が拒否することを確定する。ただしanchor非減少のgrowth residualはこのrankでも退出障害として残り、それが現在の未証明点(exit anchor dropの構成)である。

## 主要な定義

### `TailCyclePhase` (L14)

cycle探索の三つのphase(探索モード)。`crossing`(crossing nodeに滞在)、`backtrack`(過去のtail最小値を遡る)、`discharge`(historical downcrossを処理する)からなり、rankの構造上`crossing → backtrack → discharge`の一方向にしか進めない。

### `TailCyclePhase.rank` (L20)

phaseを自然数へ写す: `discharge ↦ 0`、`backtrack ↦ 1`、`crossing ↦ 2`。辞書式rankの成分として使う。

### `TailCycleSearchNode` (L25)

cycle探索のノード: crossing anchor(探索の基準となるpre-crossing値)`anchor`、phase、履歴時刻`historyTime`、tail最小値`minimumValue`の四つ組。

### `tailCycleRank` (L32)

nodeに対する四成分rank

```text
(anchor, (phase.rank, (seenBelowCount target historyTime, minimumValue)))
```

anchorが最外層である点が本rankの核心で、内側の三成分がどう動いてもanchorの厳密下降がなければ外層は縮まない。

### `TailCycleProgress` (L38)

四成分rankの辞書式順序による厳密下降関係。

## 定理と証明

### `tailCycleProgress_wellFounded` (L44)

**主張:** permanent-tail cycle rankは整礎である(無限下降列が存在しない)。

**証明:** 自然数の四重辞書式順序の整礎性`natQuadLex_wellFounded`のaccessibility(到達可能性)を、rank写像`tailCycleRank`に沿ってnodeへ引き戻す。rank上の帰納法がそのままnode上のaccessibilityを与える、`PermanentAboveCanonical.lean`の三成分版と同じ標準的議論である。

### `tailCycleProgress_enterBacktrack` (L61)

**主張:** crossing anchorを変えずに、crossing phaseからbacktrack phaseへ進入することは常にrank下降である。

**証明:** anchor成分が等しく、phase rankが`2 → 1`と下がるので、辞書式順序の第二成分で決まる。

### `tailCycleProgress_backtrack_of_seenDrop` (L73)

**主張:** 同anchorのbacktrack同士では、dual seen予算`seenBelowCount`の厳密下降がrank下降になる。

**証明:** anchorとphaseが等しいので、第三成分の厳密下降として直接構成する。

### `tailCycleProgress_backtrack_of_seenLe_minimumDrop` (L84)

**主張:** 同anchorのbacktrack同士で、seen予算が非増加かつtail最小値が厳密下降するなら、rank下降になる。

**証明:** seenが厳密に下がるならL73。等しいなら第四成分`minimumValue`の厳密下降が辞書式下降を与える。

### `tailCycleProgress_enterDischarge` (L102)

**主張:** 実際のhistorical downcrossによるbacktrackからdischargeへの進入は、同anchorの下で常にrank下降である。

**証明:** phase rankが`1 → 0`と下がるので、第二成分で決まる。

### `tailCycle_exitCrossing_iff_anchorDrop` (L116)

**主張:** dischargeからcrossingへの復帰がこのrankで下降として成り立つことは、crossing anchorの厳密下降`childAnchor < parentAnchor`とちょうど同値である。時刻成分もどちらの履歴成分も、停留したanchorを隠すことはできない。

**証明:** (⇐)anchorの厳密下降は最外成分の下降なので直ちに辞書式下降。(⇒)辞書式下降を展開すると、最外のanchor成分で決まったか、anchor同値で内側が下降したかのいずれかである。しかし後者では第二成分のphase rankが`0`(discharge)から`2`(crossing)へと増加しており、phase同値もあり得ないので、内側で下降することは不可能。よってanchor成分の厳密下降しか残らない。この同値性が「phaseを一方向にし、anchorを最外層に置く」設計の要点であり、dischargeを終端phaseとすることで、crossingへ戻る唯一の道をanchor下降に限定している。

### `HistoricalPredecessorOutcome.tailCycleProgress` (L136)

**主張:** historical predecessor二分法(`PermanentAboveHistory.lean`)はanchorを固定したままcycle rankで全域的かつ厳密に下降する。親node `⟨anchor, backtrack, predecessorFirstTime, a(minimumTime)⟩`に対し、rank下降する子nodeが存在する。

**証明:** 二分法の場合分けに従う。downcross枝では子`⟨anchor, discharge, downTime + 1, a(minimumTime)⟩`がL102により下降する。renewed_tail枝では、新しい初出時刻は旧tail開始時刻以下なので`seenBelowCount`の単調性(`PermanentAboveCanonical.lean`)によりseenは非増加、新最小値は厳密に小さいので、子`⟨anchor, backtrack, newFirstTime, a(newMinimumTime)⟩`がL84により下降する。

### `PermanentTailCombinedCertificate.entersTailCycle` (L158)

**主張:** すべてのcombined permanent-tail障害は、anchorを固定したままcycle rankへ厳密に進入する。combined証明書からは、strict tail・最小値証明書・historical downcrossに加えて、crossing node `⟨parent.anchorParent, crossing, parent.horizon, …⟩`からbacktrack node `⟨parent.anchorParent, backtrack, historicalFirstTime, …⟩`への`TailCycleProgress`が得られる。

**証明:** `exists_historicalDowncrossCertificate`のwitnessを取り、L61の進入辺を使う。historical証明書を結論に保持しているのは、その局所的な二分法(L136)が続けて次の厳密stepを取れるようにするためである。

### `tailCycle_no_stationary_crossingExit` (L181)

**主張:** 停留するhistorical cycleは、新rankでは同じcrossing anchorへのdischarge退出になれない: 同anchorでのdischarge → crossingの`TailCycleProgress`は成り立たない。

**証明:** L116の同値性により、この退出は`anchor < anchor`を要求するが、これは自然数の非反射性に反する。`PermanentAboveHistory.lean`のchild = parent停留構成は、このrankでは「進捗」として数えられないことが確定する。

### `HistoricalCycleGrowthResidual.tailCycleExitObstruction` (L192)

**主張:** 旧来のhistorical growth residual(anchor非減少の停留残余)は、新しい一方向rankに対しても正確に退出障害である。残余からは、ready crossing子で`parent.anchorParent ≤ child.anchorParent`を満たし、かつdischarge node からそのcrossing nodeへの`TailCycleProgress`が成り立たないものが得られる。

**証明:** 残余のconstructorを展開してready crossing子とanchor非減少を取り出す。L116の同値性により、退出には`child.anchorParent < parent.anchorParent`が必要だが、これはanchor非減少と矛盾するので退出は不可能。

つまり、新rankは停留cycleを「偽の進捗」として受け入れることはなくなったが、growth residualそのものを消したわけではない。残余が生じたときにdischargeからcrossingへ戻るためのstrict anchor dropを実際に構成すること — これが証明地図における現在の未証明点である。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「permanent-tail cycle rank」(骨格証明済み)と「cycle discharge exit」(必要十分条件まで縮約)に対応し、permanent above-target tail解析の現在の最前線である。入力は`PermanentAboveCanonical.lean`の`seenBelowCount`と単調性定理、`PermanentAboveHistory.lean`の`HistoricalPredecessorOutcome`・combined証明書・`HistoricalCycleGrowthResidual`である。成果として、zero-budget領域のhistorical探索内部はすべて整礎rankの厳密下降で閉包され、停留選択はL116・L181によりrankの構造レベルで排除された。残る一点は、growth residualが現れた場合にstrict anchor dropを与えるexit構成(README末尾の「discharge exit anchor drop:未証明」)であり、これが閉じれば恒久tail仮説の矛盾導出、ひいてはready crossing局所totalityを経由した全射性予想本体へ接続する。
