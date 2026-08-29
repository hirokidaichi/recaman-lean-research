# PermanentAboveCorridorLandingHorizon

**役割:** anchored interfaceのfresh landingに欠けていたhorizon境界を、permanent tailの被覆条件と初出の最小性から事後的に補い、landingとそのrestart crossingがparent historyの厳密な内側(`landing < start`、`crossing + 1 ≤ start < parent.horizon`)に住むことを証明する。

## このモジュールの役割

`PermanentAboveCorridorHistoryLanding.lean`のanchored interfaceは、history辺の背後にbelow-target値のfresh landing(初出)とそのcanonical restart crossing(landing以後の最初のweak upcrossing)を回収した。しかしその構成はmissing-count下降不等式だけから行われたため、landing時刻には何のhorizon上界も付いておらず、このままではparentのhistory node(installed crossing node `⟨parent.horizon, a(c), normal, a(c)⟩`)の上に搭載できない。本モジュールは、permanent-tailの文脈が事後的にこの上界を供給することを示す。missing targetの反例ではtarget未満の全値がtail開始`start`までに出現済みであり(被覆条件)、初出は最小の出現時刻なので、landingは`start`以前 — さらにtailが`start`から厳密にaboveであることから厳密に前 — に位置する。すると`landing`と`start`の間にweak upcrossingが存在し、canonicalなfirst crossingはそれ以前なので`crossing + 1 ≤ start`。tail開始はparent horizonより厳密に前なので、landingとrestart crossingはともにparentの履歴の厳密な内側に確定する。上流の定理はひとつも書き換えていない。

## 主要な定義

### `PermanentTailTerminalHorizonAnchoredOutcome` (L26)

horizon境界付きのanchored interface。`PermanentAboveCorridorHistoryLanding.lean`の三形と同じ骨格だが、parent nodeで添字づけられ、fresh landing枝に境界条件が加わる。

- `fresh_landing`: 従来のhistory progress(`TerminalChronologyHistoryProgress`、missing budgetの厳密下降)、landing値のbelow-target性、窓条件`parentTime < landingTime ≤ childTime`、landingの初出`FirstAt`、restart crossing(`FirstWeakUpcrossingStep`)に加えて、新たに三つの境界: `landingTime < start`(landingはtail開始前)、`nextCrossingTime + 1 ≤ start`(restart crossingもtail開始前に完結)、`nextCrossingTime + 1 < parent.horizon`(crossingはparent horizonの厳密な内側)。最後の形はまさにinstalled crossing nodeが要求する履歴内境界である。
- `semantic_progress`: 比較元node付きのsemantic位相辺(`PhaseSemanticInvariant`と`PhaseSearchProgress`)。従来のまま。
- `exact_replay`: replay固定点(descendantのdischarge証明書と`TerminalExactDischargeReplayCertificate`)。従来のまま。

## 定理と証明

### `PermanentTailCombinedCertificate.terminalHorizonAnchoredOutcome` (L57)

**主張:** combined permanent-tail証明書(仮想反例が強制するtail・zero-budget crossing・minimum blockerの三点セット、`PermanentAboveHistory.lean`)は、horizon境界付きanchored outcomeを持つ。permanent-tailのbelow被覆とstrict-above条件だけで、すべてのanchored landingがparent historyの内側に束縛される。

**証明:** `terminalAnchoredOutcome`(`PermanentAboveCorridorHistoryLanding.lean`)の三形を場合分けする。semantic枝とreplay枝はそのまま移送する。fresh landing枝では、境界を三段で獲得する。

*landingはtail開始以前にある。* landing値`value < target`なので、tail証明書の被覆条件`below_covered`により`value ∈ valuesThrough start`、すなわちある時刻`t ≤ start`で`a(t) = value`。landingの初出性(`FirstAt`)の最小性から、`t < landingTime`はあり得ない(初出より前の出現になる)。よって`landingTime ≤ t ≤ start`。

*厳密に前にある。* `a(landingTime) = value < target`である一方、tailは`start`で厳密にaboveなので`target < a(start)`。従って`landingTime = start`は値の比較で矛盾し、`landingTime < start`。

*restart crossingもtail開始・horizonの内側にある。* 区間`[landingTime, start]`はbelow-targetからstrictly-aboveへの有限区間なので、`exists_weakUpcrossingStep_between`によりある`witness`(`witness + 1 ≤ start`)でweak upcrossingが起きる。restart crossingはlanding以後の*最初の*upcrossingなので、その一意最小性(`FirstWeakUpcrossingStep.time_le`)により`nextCrossingTime ≤ witness`、従って`nextCrossingTime + 1 ≤ start`。最後に、crossing証明書の`tail_strictly_before_horizon`(`start < parent.horizon`)と連結して`nextCrossingTime + 1 < parent.horizon`を得る。

三つの境界を元のlandingデータに添えて`fresh_landing`を再構成すれば完了である。証明全体が既存フィールドの読み出しと初出最小性の算術だけで済む点が、この段階の軽さである。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「landing horizon bound」(landingをparent history内へ束縛済み)に対応する。上流は`PermanentAboveCorridorHistoryLanding.lean`(anchored interface)、`PermanentAboveTail.lean`(`MissingPermanentAboveTail`の被覆・strict-above条件と`PermanentTailCrossingCertificate`のhorizon条件)、`PermanentAboveCanonical.lean`(first upcrossingの最小性)である。下流では、直後の`PermanentAboveCorridorLandingMount.lean`が、この`nextCrossingTime + 1 < parent.horizon`という境界を唯一の入力として、restart crossingを実際のready crossing node(refined semantic domainの実object)として`⟨parent.horizon, a(c), normal, a(c)⟩`に搭載する。数値的なlandingデータとsemantic domainの間に残っていた「horizon境界の欠落」という一点を、仮想反例自身の性質で埋めた橋渡しのモジュールである。
