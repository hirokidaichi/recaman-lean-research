# PermanentAboveTail

**役割:** 仮想的な「最小未出target」が強制する恒久上方tail(以後ずっとtargetより大きい軌道区間)の内部構造を解析し、高々二遷移のCoverageStep、履歴予算0のready crossing、tail最小値直下のhistorical blockerを抽出する。

## このモジュールの役割

全射性予想を否定する最小の反例、すなわち「軌道に一度も現れない最小の目標値`target`」を仮想的に固定すると、`CrossingTailRefined.lean`の結果により、ある有限時刻`start`以後の軌道は恒久的に`target`より真に大きくなる(permanent above tail)。本モジュールはこの仮想的なtailの内部を直接解析する。得られる結果は三つある。第一に、tail内の任意の状態は高々二遷移で値を下げる`CoverageStep`(目標出現、または親より真に小さい値の初出を与える一段の証明)を返す。第二に、tail開始時点で`target`未満の値はすべて既出なので履歴予算(history budget、未出の`target`未満の値の個数`missingBelowCount`)は0であり、tail内部にはzero-budget ready crossingが実在し、そのrefined子はcrossingに留まってanchor(探索の基準となる親の値)を厳密に下げるしかない。第三に、tailの最小値では二連続の強制加算(forced addition)が起き、直下値`a(time) − 1`の初出がtail開始前にあるというhistorical blocker(既出値による下降妨害)を取り出せる。

## 主要な定義

### `MissingPermanentAboveTail` (L71)

仮想反例が強制する状態の証明書。`target start`について、(1) `0 < target`、(2) `target`は全軌道で未出(`¬∃ time, a(time) = target`)、(3) `target`未満の値はすべて時刻`start`までの履歴`valuesThrough start`に含まれる、(4) `start`以後の全時刻で`target < a(time)`、の四条件を束ねる。

### `MissingStrictAboveTail` (L81)

上記から条件(3)(below-target値の被覆完了)を落とした核。tail最小値の下降反復(`PermanentAboveHistory.lean`)では、新しい開始時刻で(3)が成り立つとは限らないため、この弱い形が再帰の対象になる。

### `PermanentTailCrossingCertificate` (L276)

恒久tailが強制するready crossing(target到達可能なclock条件`target ≤ horizon + 1`を持つcrossing状態)の完全な形。node(探索ノード)について、(1) `ReadyCrossingSearchInvariant`、(2) horizonがtail内(`start ≤ node.horizon`かつ`start < node.horizon`)、(3) 履歴予算0(`missingBelowCount target node.horizon = 0`)、(4) `target < a(node.horizon)`、(5) horizon以後にdowncross(target以上からtarget未満への実遷移)が存在しない、を保持する。

### `TailMinimumAt` (L366)

時刻`time`がtail(`start`以後)の最小値を実現すること: `start ≤ time`かつ`∀ later ≥ start, a(time) ≤ a(later)`。

### `PermanentTailMinimumCertificate` (L402)

tail最小値で強制される局所構造の証明書。時刻`time`での一歩目が強制加算(`a(time+1) = a(time) + (time+1)`)、続く二歩目の減算候補が`a(time+1) − (time+2) = a(time) − 1`でこれも強制加算、直下値`a(time) − 1`の初出`FirstAt`が時刻`firstTime < start`(tail開始前)にあり、さらに`target < a(time) − 1`を保持する。

## 定理と証明

### `forcedAddition_above_twoStep_coverage` (L20)

**主張:** `0 < target < a(n)`で、時刻`n`からの一歩が強制加算(減算不能)なら、`CoverageStep target (a n) n`が成り立つ。座標や商の仮定は一切不要である。

**証明:** 強制加算により`a(n+1) = a(n) + (n+1)`。次の時刻`n+2`での減算候補は

```text
a(n+1) − (n+2) = a(n) − 1 =: c
```

であり、`target < a(n)`から`target ≤ c < a(n)`。また`a(n) ≥ 2`(`target ≥ 1`より)なので`a(n+1) ≥ n+3 > n+2`、すなわち候補は常に正である。時刻`n+2`で場合分けする。

- 減算可能なら`a(n+2) = c`で、合法減算の着地値は定義上未出なので`c`の初出は時刻`n+2`。`target ≤ c < a(n)`とあわせて`CoverageStep`の第二選択肢(より小さい値の初出)を与える。
- 減算不能なら、候補が非正である可能性は上で排除済みなので、`c`はすでに履歴`valuesThrough(n+1)`にある。履歴の元は必ず初出時刻を持つので、その初出時刻とともにやはり第二選択肢を得る。

いずれの枝でも`y = a(n) − 1`が`target ≤ y < a(n)`を満たす初出値になる。

### `strictAboveTail_coverageStep` (L57)

**主張:** `target`が正で、`start`以後の全時刻で`target < a(time)`なら、tail内の任意の時刻`n ≥ start`で`CoverageStep target (a n) n`が成り立つ。

**証明:** 時刻`n+1`への一歩で場合分けする。合法減算なら着地値`a(n+1) = a(n) − (n+1)`は未出かつ`target ≤ a(n+1) < a(n)`なので、`subtraction_gives_coverageStep`により直ちに第二選択肢を得る。強制加算なら`forcedAddition_above_twoStep_coverage`が二歩先で同じ結論を与える。

### `MissingPermanentAboveTail.toStrictAboveTail` (L88)

**主張:** 完成履歴付き証明書からbelow-target被覆条件を忘れると`MissingStrictAboveTail`になる。

**証明:** 構造体の射影のみ。

### `LeastMissingTarget.exists_missingPermanentAboveTail` (L99)

**主張:** 最小未出target(`target`は未出だが、それ未満の値はすべて出現する)は、ある有限の`start`で`MissingPermanentAboveTail target start`証明書を持つ。

**証明:** `a(0) = 0`なので`target = 0`は未出になり得ず、`target`は正。`CrossingTailRefined.lean`の`LeastMissingTarget.eventually_strictlyAbove`が、below-target値の被覆と恒久的な厳密上方性を同時に満たす`start`を与える。あとは四条件を束ねるだけである。

### `MissingPermanentAboveTail.coverageStep_at` (L118)

**主張:** 証明書付きtail内の任意の時刻`n ≥ start`で`CoverageStep target (a n) n`。

**証明:** `strictAboveTail_coverageStep`の直接適用。

### `MissingPermanentAboveTail.readyCurrentOrDebtStep_at` (L129)

**主張:** さらにclock条件`target ≤ n + 1`が成り立てば、tail状態のCoverageStepは既存のready current/debt domain(target到達可能な時計を持つcurrent normalおよびstrong debt状態)へ入る。すなわち`ReadyCurrentOrDebtInvariant`を満たす子nodeと、開始node`targetStartNode n`に対する`PhaseSearchProgress`(四成分位相ランクの厳密下降)が存在する。

**証明:** `target`が正、`target ≤ n+1`、`target ≤ a(n)`(tail内なので)から`CurrentCoverageParentCertificate`を作り、`CoverageDebtBridge`の`coverageStep_readyCurrentOrDebt`をL118のCoverageStepに適用する。目標出現の枝は`target_missing`と矛盾するので、残るのはready子とrank下降の枝だけである。なおこれはtail状態での局所閉包であり、これ単独では過去のcrossing nodeへのrank辺を輸送しない。

### `missingBelowCount_eq_zero_of_belowCovered` (L148)

**主張:** `target`未満の値がすべて`valuesThrough horizon`に含まれるなら、`missingBelowCount target horizon = 0`。

**証明:** `target`についての帰納法。`target + 1`の場合、`target`未満の被覆から帰納法の仮定でカウントの下位部分は0、最上位の値`target`自身も既出なので加算項も0。

### `MissingPermanentAboveTail.budget_zero` (L166)

**主張:** 恒久tailの開始時点で履歴予算は完全に枯渇している: `missingBelowCount target start = 0`。

**証明:** 証明書の`below_covered`にL148を適用する。位相探索rankの最外成分がすでに絶対最小値に達していることを意味する。

### `crossing_zeroBudget_no_nonCrossing_progress` (L175)

**主張:** 履歴予算0のcrossing親からは、いかなる非crossing refined子(`RefinedNonCrossingInvariant`)へも`PhaseSearchProgress`は成り立たない。

**証明:** `CrossingRefinedBoundary.lean`の定理により、crossing親(anchorはtarget未満)から非crossing子(anchorはtarget以上)へのrank下降は必ずstrictな履歴予算下降を伴う。親の予算が0なら、自然数値の予算を0未満にすることになり矛盾。

### `crossing_zeroBudget_progress_forces_anchorDrop` (L189)

**主張:** 履歴予算0のcrossing親からcrossing子への`PhaseSearchProgress`が成り立つなら、子の予算も0のままで、子のanchorは親のanchorより真に小さい。

**証明:** 両nodeのcrossing証明書からanchorが実軌道値(`a parentTime`、`a childTime`)であることを取り出し、crossing間の数値的progress同値`crossingNumeric_progress_iff_budgetDrop_or_anchorDrop`を適用する。progressは「予算のstrict下降」または「予算同値かつanchorのstrict下降」のいずれかだが、前者は予算0で不可能。よって後者であり、子の予算は親と等しく0、anchorは真に下がる。

### `MissingPermanentAboveTail.crossing_refinedChild_is_crossing` (L227)

**主張:** 証明書付きtail内にhorizonを持つcrossing親(`start ≤ parent.horizon`)のrefined子(`OrbitReadyRefinedInvariant`)が`PhaseSearchProgress`を成すなら、その子は必ず自身もcrossingである。

**証明:** `missingBelowCount`は時間について単調非増加なので、`start`で予算0なら`parent.horizon`でも0。refined子は`crossing_refinedChild_budgetDrop_or_crossing`により「strictな予算下降」または「crossing」のいずれかを与えるが、予算0で前者は不可能。

### `MissingPermanentAboveTail.crossing_refinedChild_shape` (L250)

**主張:** 前定理の完全形: tail内crossing親のrefined子は、crossingであり、予算0を保ち、anchorを厳密に下げる。

**証明:** L227で子がcrossingであることを得て、L189を適用する。仮想反例の下では、rank下降はpre-crossing anchorの自然数下降という一本道に絞られる。

### `MissingPermanentAboveTail.exists_crossingCertificate` (L289)

**主張:** すべての恒久tailは、予算0のready crossingを実際に含む: `∃ node, PermanentTailCrossingCertificate target start node`。

**証明:** `a(0) = 0 < target`かつ`target < a(start)`なので、区間`[0, start]`のどこかでtarget未満からtarget以上への上向き横断が起きる。`exists_weakUpcrossingStep_between`が、時刻`crossingTime`(`crossingTime + 1 ≤ start`)での強制加算による弱いupcrossing(`a(crossingTime) < target ≤ a(crossingTime+1)`)を与える。`target`は未出なので着地値は実は`target`より真に大きく、また`target ∉ valuesThrough crossingTime`。着地時刻の商剰余座標を取り、horizonを`max(start+1, target)`に選んでnode

```text
node = ⟨horizon, a(crossingTime), normal, a(crossingTime)⟩
```

を作る。crossing時刻はhorizonより前なので`CrossingRecoveryInvariant`が成立し、`target ≤ horizon`からclock条件`target ≤ horizon + 1`も従い、ready crossingになる。予算は`start ≤ horizon`と単調性から0、horizonの値はtailにより`target`より真に大きく、以後の全時刻がtarget以上なのでfuture downcrossは存在しない(`no_futureDowncross_iff_tail_atOrAbove`)。

### `exists_tailMinimumAt` (L372)

**主張:** 任意の`start`について、tailの最小値を実現する時刻が存在する: `∃ time, TailMinimumAt start time`。

**証明:** 自然数値に対する強帰納法。tail上のある値`bound = a(time)`を固定し、それより真に小さいtail値があればその値へ降りて帰納法の仮定を使う。なければ`time`自身が最小値の witness である。開始点`a(start)`から始めれば有限回で必ず停止する。

### `MissingStrictAboveTail.exists_minimumCertificate` (L416)

**主張:** すべてのmissing strict-above tailは、tail最小値の直下にhistorical blockerを露出する: `∃ time firstTime, PermanentTailMinimumCertificate target start time firstTime`。below-target履歴の完備性はこの値下降には不要である。

**証明:** L372でtail最小時刻`time`を取る。tailにより`target < a(time)`、特に`a(time) ≥ 2`。

*一歩目が強制加算であること。* 時刻`time+1`で減算可能なら`a(time+1) = a(time) − (time+1) < a(time)`となるが、`time+1`もtail内なので最小性に反する。よって強制加算で`a(time+1) = a(time) + (time+1)`。

*二歩目も強制加算であること。* 続く減算候補は`a(time+1) − (time+2) = a(time) − 1`。減算可能なら`a(time+2) = a(time) − 1 < a(time)`でやはり最小性に反する。よって強制。候補は正(`time+2 < a(time+1)`)なので、減算不能の理由は「既出」しかない: `a(time) − 1 ∈ valuesThrough(time+1)`。

*初出がtail開始前であること。* 履歴の元として`a(time) − 1`の初出時刻`firstTime`を取る。もし`start ≤ firstTime`なら最小性から`a(time) ≤ a(firstTime) = a(time) − 1`となり矛盾。よって`firstTime < start`。

*targetとの分離。* `target < a(time)`から`target ≤ a(time) − 1`。等号なら`target`が時刻`firstTime`に出現してしまい`target_missing`に反する。よって`target < a(time) − 1`。

### `MissingPermanentAboveTail.exists_minimumCertificate` (L481)

**主張:** 完成履歴付き証明書についての同じ結論。

**証明:** L88でstrict形へ忘却してL416を適用する。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「permanent tail局所構造」および「zero-budget crossing境界」の段階(いずれも証明済み)に対応する。上流では`CrossingTailRefined.lean`の`LeastMissingTarget.eventually_strictlyAbove`と`ReadyCurrentDebt.lean`のcoverage橋を使う。下流では、`PermanentAbovePotential.lean`が最小値の二連続forced additionの座標候補を監査し、`PermanentAboveHistory.lean`が`PermanentTailCrossingCertificate`と`PermanentTailMinimumCertificate`を結合してhistorical blockerの反復と`crossing_zeroBudget_progress_forces_anchorDrop`によるanchor下降解析を行う。現在の研究最前線である「tail最小値のhistorical blockerをzero-budget crossingのanchor下降へ変換する」問題は、本モジュールが用意した二つの証明書の間の未証明の一歩である。
