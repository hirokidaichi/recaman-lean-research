# PermanentAboveCanonical

**役割:** 最初のfuture weak upcrossingを強帰納でcanonicalに構成して一意性を示し、履歴予算の双対`seenBelowCount`を導入して、zero-budget tail horizonからpositive-missingな過去の点へ戻る向きの厳密下降を証明する。

## このモジュールの役割

`PermanentAboveHistory.lean`は、任意のcrossing選択を許すとchild = parentの停留残余が必ず構成できることを示した。本モジュールはその曖昧さへの二つの独立した応答を形式化する。第一に、below-targetの開始点から最初(earliest)のweak upcrossing(target未満からtarget以上への強制加算横断)をcanonicalに選ぶ規則を構成し、その存在・一意性・最小性を証明する。ただし同じ開始点から再選択すれば一意性ゆえに同じ時刻へ戻るため、earliest規則単独では停留は解消されないことも定理として固定する。第二に、履歴予算(未出のtarget未満値の個数`missingBelowCount`)の双対`seenBelowCount = target − missingBelowCount`(発見済みのtarget未満値の個数)を導入する。時間が進む向きでは単調増加するこの量は、zero-budget tail horizonからmissingが正の過去の初出時刻へ戻るbacktracking(過去向き探索)では厳密に減少するため、過去向き探索のdual budgetとして使える。あわせて、phase・seen・minimumの三成分辞書式rank `TailHistoryProgress`を定義し、historical predecessor二分法の両枝がこのrankで厳密に下降することを示す。

## 主要な定義

### `FirstWeakUpcrossingStep` (L18)

選ばれたbelow-target開始点`start`以後で最初に起きるweak upcrossing。`WeakUpcrossingStep target start time`(`start ≤ time`、`a(time) < target ≤ a(time+1)`、強制加算)と、それより早い時刻ではupcrossingが起きないこと(`∀ earlier < time, ¬WeakUpcrossingStep`)を束ねる。

### `seenBelowCount` (L84)

`seenBelowCount target horizon = target − missingBelowCount target horizon`。時刻`horizon`までに既出となったtarget未満の値の個数に対応する双対予算である。

### `TailHistoryPhase` (L134)

historical探索の二つのphase(探索モード)。`backtrack`(過去のtail最小値を遡る段階)と`discharge`(downcrossを処理する終端段階)からなり、探索は`backtrack → discharge`の一方向に進む。

### `TailHistoryPhase.rank` (L139)

phaseを自然数へ写す: `discharge ↦ 0`、`backtrack ↦ 1`。辞書式rankの成分として使う。

### `TailHistorySearchNode` (L143)

historical探索のノード: 履歴時刻`historyTime`、tail最小値`minimumValue`、phaseの三つ組。

### `tailHistoryRank` (L149)

nodeに対する三成分rank `(phase.rank, (seenBelowCount target historyTime, minimumValue))`。

### `TailHistoryProgress` (L154)

三成分rankの辞書式順序による厳密下降関係。子のrankが親のrankより辞書式に小さいときに成り立つ。

## 定理と証明

### `exists_firstWeakUpcrossingStep_from_below` (L25)

**主張:** targetが正で`a(start) < target`なら、canonicalな最初のupcrossingが存在する: `∃ time, FirstWeakUpcrossingStep target start time`。

**証明:** まず`exists_weakUpcrossingStep_from_below`が何らかのupcrossing witness `bound`を与える。このwitness時刻を上界とする自然数の強帰納法で議論する: `bound`より早いupcrossingがあればそこへ降りて帰納法の仮定を使い、なければ`bound`自身が最小性条件を満たす。時刻は自然数なので有限回で最初のupcrossingに到達する。

### `FirstWeakUpcrossingStep.time_le` (L53)

**主張:** canonicalな最初のupcrossing時刻は、同じ開始点からの他のいかなる証明付きupcrossing時刻以下である。

**証明:** そうでなければ他のwitnessがより早いupcrossingとなり、最小性条件に反する。

### `FirstWeakUpcrossingStep.unique` (L63)

**主張:** 最初のupcrossing witnessは一意である。

**証明:** 二つのwitnessにL53を相互に適用すれば両向きの`≤`が得られ、等しい。

### `FirstWeakUpcrossingStep.endpoint_le_of_witness` (L74)

**主張:** どれかのupcrossingが有限のhorizon `finish`までに完了するなら(`witnessTime + 1 ≤ finish`)、canonicalな最初のupcrossingも同じhorizonまでに完了する。

**証明:** L53の最小性`firstTime ≤ witnessTime`から直ちに従う。

### `seenBelowCount_le` (L87)

**主張:** `seenBelowCount target horizon ≤ target`。

**証明:** 自然数の切り捨て減算の定義から明らか。

### `seenBelowCount_add_missingBelowCount` (L93)

**主張:** seen予算とmissing予算はtarget未満の有限区間を分割する: `seenBelowCount + missingBelowCount = target`。

**証明:** `missingBelowCount target horizon ≤ target`(各値の寄与は高々1)を使えば、切り捨て減算が通常の減算に一致し、算術的に閉じる。

### `seenBelowCount_eq_target_iff` (L102)

**主張:** dual予算の飽和`seenBelowCount = target`は、元のmissing予算が0であることとちょうど同値である。

**証明:** L93の分割等式から直ちに従う。恒久tailのhorizonはまさにこの飽和状態にある。

### `seenBelowCount_monotone` (L110)

**主張:** 実際の履歴が成長する向き(`earlier ≤ later`)で`seenBelowCount`は単調非減少である。

**証明:** `missingBelowCount`の時間についての単調非増加性(`missingBelowCount_antitone`)を分割等式で反転させる。

### `seenBelowCount_strict_of_missingBelowCount_strict` (L122)

**主張:** missing予算の厳密な下降は、dual seen予算の厳密な増加とちょうど対応する: `missingBelowCount(later) < missingBelowCount(earlier)`なら`seenBelowCount(earlier) < seenBelowCount(later)`。

**証明:** 両時刻での上界`missingBelowCount ≤ target`とあわせて算術で閉じる。読み替えると、探索が後の時刻(seenが大きい)から前の時刻(seenが小さい)へ戻るとき、`seenBelowCount`を子nodeの尺度に使えば厳密下降になる。これが過去向き探索のdual budgetという着想である。

### `tailHistoryProgress_wellFounded` (L160)

**主張:** 三成分辞書式順序`TailHistoryProgress`は整礎である(無限下降列が存在しない)。

**証明:** 自然数の三重辞書式順序の整礎性`natTripleLex_wellFounded`のaccessibility(到達可能性)を、rank写像`tailHistoryRank`に沿ってnodeへ引き戻す。rankが等しいnode同士は互いに関係しないので、rank上の帰納法がそのままnode上のaccessibilityを与える。

### `tailHistoryProgress_of_seenDrop` (L176)

**主張:** backtrack同士では、`seenBelowCount`の厳密下降がrank下降になる。

**証明:** phase成分が等しい(ともに1)ので、辞書式順序の第二成分の下降として直接構成する。

### `tailHistoryProgress_of_seenLe_minimumDrop` (L185)

**主張:** backtrack同士で、`seenBelowCount`が非増加かつtail最小値が厳密下降するなら、rank下降になる。

**証明:** seenが厳密に下がるならL176。等しいなら第三成分`minimumValue`の厳密下降が辞書式下降を与える。

### `tailHistoryProgress_enterDischarge` (L201)

**主張:** backtrackからdischargeへの進入は、他の成分によらず常にrank下降である。

**証明:** phase rankが`1 → 0`と下がるので、辞書式順序の第一成分で決まる。

### `HistoricalPredecessorOutcome.tailHistoryProgress` (L214)

**主張:** historical predecessor二分法(`PermanentAboveHistory.lean`)の両constructorは新rankで厳密である。親node `⟨predecessorFirstTime, a(minimumTime), backtrack⟩`に対し、rank下降する子nodeが存在する。

**証明:** 二分法の場合分けに従う。downcross枝では子`⟨downTime + 1, a(minimumTime), discharge⟩`がL201により下降する。renewed_tail枝では、新しい初出時刻は旧tailの開始前(`newFirstTime < predecessorFirstTime`の非厳密形)なので、seen予算はL110により非増加。新最小値は厳密に小さいので、子`⟨newFirstTime, a(newMinimumTime), backtrack⟩`がL185により下降する。`PermanentAboveHistory.lean`で「二つの枝が異なる尺度に住む」とされた分裂が、この三成分rankの中では単一の整礎下降に統合される。

### `PermanentTailCombinedCertificate.entersTailHistory` (L236)

**主張:** combined permanent-tail障害は、dual-history domainへ厳密に進入する。すなわちcombined証明書からは、strict tail・最小値証明書・downcrossに加えて、crossing horizonのnode `⟨parent.horizon, …, backtrack⟩`からhistorical初出時刻のnode `⟨historicalFirstTime, …, backtrack⟩`への`TailHistoryProgress`が得られる。

**証明:** `exists_historicalDowncrossCertificate`のwitnessを取る。選ばれたhistorical初出時刻は正のmissing予算を持ち(予算の厳密下降の始点なので)、一方crossing horizonの予算は0である。よって`missingBelowCount(parent.horizon) = 0 < missingBelowCount(historicalFirstTime)`であり、L122がseen予算の厳密下降を与え、L176がrank下降を与える。zero-budgetで飽和して動けなかった従来の外側予算に対し、過去へ戻る一歩そのものが進捗として測れるようになったことを意味する。

### `MissingPermanentAboveTail.exists_firstHistoricalUpcrossing` (L268)

**主張:** earliest規則はhistorical cycleの上で実際に構成可能で、更新されたstrict tailの開始前に完了する。すなわちstrict tail、historical downcross、`FirstWeakUpcrossingStep target (downTime+1) crossingTime`、および`crossingTime + 1 ≤ tailStart`を満たすwitnessが存在する。

**証明:** historical downcross証明書のendpoint `a(downTime + 1) < target`にL25を適用してcanonicalな最初のupcrossingを得る。一方、`exists_weakUpcrossingStep_between`はtailStartまでに完了する何らかのupcrossing witnessを与えるので、L74によりcanonicalなものも同じ境界までに完了する。

### `firstHistoricalUpcrossing_reselection_stationary` (L294)

**主張:** earliest選択はwitnessの曖昧さを除くが、停留性は除かない。同じhistorical downcross endpointからの二回目のearliest選択は、同一のcrossing時刻を返す。

**証明:** L63の一意性そのものである。したがって`PermanentAboveHistory.lean`のchild = parent停留残余は、canonical化だけでは解消されない。停留を排除するには、選択規則ではなくrank自体を変える必要がある。これが`PermanentAboveCycleRank.lean`の動機である。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「canonical upcrossing」(存在・一意性証明済み)と「dual history budget」(証明済み)に対応する。入力は`PermanentAboveHistory.lean`の`HistoricalPredecessorOutcome`とdowncross証明書である。出力のうち`seenBelowCount`とその単調性・厳密下降定理は、`PermanentAboveCycleRank.lean`が四成分cycle rank `(anchor, phase, seenBelowCount, tailMinimum)`の内層二成分として直接継承する。三成分rank `TailHistoryProgress`はそのanchorなし原型であり、L294の停留定理は「anchorを最外層に置き、dischargeからcrossingへの復帰にstrict anchor dropを要求する」という次モジュールの設計を必然にした否定的知見である。
