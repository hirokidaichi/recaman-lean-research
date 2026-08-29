# LandingRevisitTransport

**役割:** discharge replay側で有効だった三種道具をlanding固定点へ移植し、再訪排除は無条件で移る一方、欠けているのはdowncross前置界ただ一つであることを確定する。

## このモジュールの役割

permanent tail解析の統合outcome `PermanentTailUnifiedOutcome`は三枝である。semantic位相child、discharge replay固定点、landing固定点。このうち数値的に攻撃されてきたのはreplay枝だけで、landing枝には武器が一つも届いていなかった。本モジュールはreplay枝で有効だった三種道具、すなわち**再訪排除**(tail最小値は既出値を遅く再訪できない)・**record排除**(固定点clockは走行最大値になれない)・**downcross前置界**(clockより真に前にtarget超の事象がある、という順序情報)を、landing枝へ一つずつ持ち込み、成否を確定する。

replay枝でこの三つが同時に効くのは一本の鎖のおかげである。discharge downcross(過去のdischargeサイクルを閉じるために消費される下向き交差)はtarget以上の値から始まり、格納された historical first timeを支配し(`horizon_le_time`)、replay clockは親の格納old crossingそのものであって`eligible`である(`time_eq`)。三段を繋ぐと「clockより真に前にtarget超の事象がある」が出る。landing枝にはこの鎖がない。landing固定点のclockは、tailより前に初出したtarget未満の値(landing)から取った最初の弱上向き交差 `FirstWeakUpcrossingStep`として定義されており、下からしか固定されていないからである。

用語を一つだけ補っておく。両枝が共有する数値核 `TailFixedPointCore target parent crossingTime`は、clockの値が親のanchor値に一致し(`anchor_eq`)、clock時点ではtarget未満だが次の時刻で強制加算によりtarget以上へ跳ね(`below`・`endpoint_ge`・`forced`)、そこから組み立てた探索ノードが親そのものを再現する(`node_reproduction`)、という四点セットである。三種道具はすべてこの核の上で語られる。

## 定理と証明

### `FirstWeakUpcrossingStep.window_below` (L48)

**主張:** landing時刻の値がtarget未満ならば、landingからその最初の弱上向き交差までの閉区間 `[landingTime, crossingTime]` は全区間でtarget未満である: `∀ time, landingTime ≤ time ≤ crossingTime → a(time) < target`。

**証明:** landingからのoffsetに関する帰納法。offset 0は仮定そのもの。帰納段で `a(landingTime+offset) < target` かつ `target ≤ a(landingTime+offset+1)` だったとすると、この一歩は減算ではあり得ない(減算なら値は減るのでtargetを超えない)から強制加算であり、`WeakUpcrossingStep target landingTime (landingTime+offset)` の四条件がすべて揃う。しかし `landingTime+offset < crossingTime` なので、これは `crossingTime` が最初の弱上向き交差であることに反する。よって breach は起こらない。

この一本が、以下すべての「窓の内側には何もない」という議論の土台である。

### `TailFixedPointCore.crossingTime_not_record_of_prefixAbove` (L85)

**主張:** record排除の共有核版。固定点clockより真に前の時刻にtarget以上の値があれば、clockは走行最大値ではない: `∃ time, time < crossingTime ∧ a(crossingTime) < a(time)`。

**証明:** 核の`below`によりclockの値はtarget未満、仮定によりwitnessの値はtarget以上。よってwitnessがclockの値を真に上回る。**この形は無条件かつ枝に依存しない**。replay枝でもlanding枝でも、「clock前のtarget超事象」さえ手に入れば即座に発火する。裏を返せば、landing枝に足りないのはこの入力データただ一つである。

### `PermanentTailCombinedCertificate.lowWitness_lt_start` (L101)

**主張:** target以下の値をとる時刻は、必ずpermanent tailの開始より前にある。

**証明:** tail成分の`strictly_above`は、tail開始以降の全時刻でtargetを真に上回ることを言っている。その対偶である。補助補題だが、以下でcutoffの位置を押さえるのに繰り返し使う。

### `PermanentTailCombinedCertificate.minimum_revisit_absurd` (L115)

**主張:** 再訪排除の移植版。`a(cutoff) ≤ target` なるcutoffをとる。時刻も値もcutoff以下のwitnessが tail最小値のpredecessor値の後続 `a(predecessorFirstTime) + 1` を実現していれば、矛盾する。

**証明:** minimum証明書は、tail最小値の直後に強制加算が二度起き、二度目の減算候補が `a(minimumTime) - 1` に確定すること、そしてその値の初出が `predecessorFirstTime` であることを保証している。したがって `a(minimumTime) = a(predecessorFirstTime) + 1 = a(witness)`、つまりtail最小値はwitnessの値の再訪である。ところが `lowWitness_lt_start` によりcutoffはtail開始より前にあり、witnessは時刻も値もcutoff以下だから、witnessの時刻もその値も `minimumTime` を真に下回る。既出値の遅い再訪を禁じる `value_no_late_recurrence`(小さい値は減算では新値要求に反し、加算では行き過ぎる)がそのまま適用でき、矛盾する。

**この定理はcrossing clockを一切参照しない。** 引数はcombined証明書とcutoff・witnessだけである。したがって三種道具のうち再訪排除は、landing枝へ**無条件で移植できた**。ただし発火には依然として四条件(cutoffの値がtarget以下・witness時刻がcutoff以下・witness値がcutoff以下・後続一致)が要る。

### `PermanentTailCombinedCertificate.impossible_of_prefixSuccessorCoverage` (L134)

**主張:** prefix-successor coverageエンジンは、**predecessorの初出がclockより前である**ような固定点核すべてへ移植できる。すなわち `predecessorFirstTime < crossingTime` と `ReplayPrefixSuccessorCoverage crossingTime cutoff` から矛盾。

**証明:** coverage条件は「clockより前にあってclock値を上回る全prefix値について、その数値的後続がcutoffまでに時刻・値ともにcutoff以下で既出」という命題である。核の`below`とminimum証明書の `target < a(predecessorFirstTime)` から `a(crossingTime) < a(predecessorFirstTime)`、また前置界より `predecessorFirstTime < crossingTime` なので、coverageが `predecessorFirstTime` に適用できてwitnessを吐く。そのwitnessを `minimum_revisit_absurd` に入れれば終わり。

### `PermanentTailCombinedCertificate.crossingTime_ge_of_prefixSuccessorCoverage` (L155)

**主張:** ある天井 `ceiling` 未満の全clockでcoverageが成り立てば、前置界のあるlanding clockは `ceiling` 以上である。

**証明:** 対偶。`crossingTime < ceiling` なら仮定からcoverageが得られ、L134で矛盾する。床上げをcoverage条件へ一括還元する定式化である。

### `PermanentTailCombinedCertificate.thirtytwo_le_crossingTime_of_prefixBound` (L178)

**主張:** 具体化。前置界 `predecessorFirstTime < crossingTime` を仮定すれば、landing固定点のclockは32以上である。しかも共有核の一般床 `18 ≤ crossingTime ∨ target = 19` にあった `target = 19` の逃げ道が残らない。

**証明:** まず核と `target_missing` から無条件の `19 ≤ target` を得る(`nineteen_le_target`)。minimum証明書の `target < a(predecessorFirstTime)` と合わせて `19 < a(predecessorFirstTime)` である。cutoffには時刻131をとる。`a(131) = 4` はkernel計算で確定し、`4 ≤ 19 ≤ target` なのでcutoffの資格を満たす。`crossingTime < 32` を仮定すると前置界より `predecessorFirstTime ≤ 30` なので、初出時刻を31通りに場合分けする。うち16通りはその時刻の値が19以下で `19 < a(predecessorFirstTime)` に反する。残る15通りについては、その値の数値的後続を実現する時刻131以下のwitnessを名指しで与える(たとえば `a(17) = 25` の後続26は時刻64に、`a(21) = 63` の後続64は時刻99に居る)。どの場合も `minimum_revisit_absurd` が発火して矛盾する。

数値の限界も記録しておく。ここでcutoffが131なのは、**target床19のもとで `a(t) ≤ 19` を満たす最大の時刻が131だから**である。そしてclock 32を超えられないのは `a(32) = 46` の後続47の初出が時刻222であり、cutoff 131の外側にあるためである。222をcutoffに使うにはまずtarget床を48以上へ上げる必要がある。**これらの数値は軌道の実測に基づく経験的事実であり、kernel証明として主張しているのは `a(131) = 4` などの有限個の等式と上の場合分けだけである。**射程と床が互いを要求し合うこの階段は、replay側の床上げと同じ構造をしている。

### `PermanentTailCombinedCertificate.exists_parentCrossing` (L253)

**主張:** 親ノードが格納しているcrossingの数値内容を取り出す。ある `oldTime` が存在して `parent.anchorParent = a(oldTime)` かつ `a(oldTime) < target < a(oldTime+1)` かつ `a(oldTime+1) = a(oldTime) + (oldTime+1)`。

**証明:** combined証明書のcrossing成分はready crossing不変量を含み、その内部にcrossing recoveryの三点(target未満・次でtarget超・強制加算)が入っている。格納ノードの等式からanchor値の一致を読み出すだけである。landing枝が持っている「clock以外の唯一のcrossingデータ」がこれである。

### `PermanentTailCombinedCertificate.aboveTarget_before_crossing_or_pinnedParent` (L272)

**主張:** 前置界の代替候補は親の格納crossingしかない。それはlanding clockに対して三通りにピン留めされる。すなわち「clockより前にtarget超の事象がある」か、あるいは `a(oldTime) = a(crossingTime)` なる `oldTime` が clock以降にあって、`oldTime = crossingTime` であるか `oldTime ≤ a(crossingTime)` であるかのいずれかである。

**証明:** 格納crossingの値もclockの値もどちらも `parent.anchorParent` に等しいので `a(oldTime) = a(crossingTime)`。ここで `oldTime + 1 = crossingTime` はあり得ない。もしそうなら `a(crossingTime) = a(oldTime+1) > target` だが、核の`below`はclock値がtarget未満だと言っている。したがって `oldTime < crossingTime` の場合は真に二歩以上前であり、`oldTime + 1` がclock前のtarget超事象、つまり**discharge downcrossが供給していたのとまったく同じデータ**になる。`crossingTime < oldTime` の場合は、同じ値の遅い再訪が禁じられることから `oldTime ≤ a(crossingTime)` が従う。

この三択が、landing枝に残された前置界の全在庫である。そして三択のうち有用なのは第一の場合だけで、どれが起きるかを決める情報はどこにもない。

### `landing_predecessorFirstTime_outside_window` (L305)

**主張:** tail最小値のpredecessorはlanding窓の内側では初出しない: `predecessorFirstTime < landingTime` または `crossingTime < predecessorFirstTime`。

**証明:** landing値はtarget未満なので `window_below` が適用でき、窓 `[landingTime, crossingTime]` は全区間target未満。一方predecessorの値はtargetを真に上回る。よって初出時刻は窓の外、二択のいずれかである。

**ここが本モジュールの結論の核心である。** 二択は無条件に出る。しかし**landing分岐はこの二択を決める情報を持たない**。replay側はdowncrossを通じて「clockより前」を決めるが、landing側のclockは fresh history landing によって下からしか固定されていない。dischargeで上界を与えていた三段連鎖のうち `eligible` はreplay固有のフィールドであり、combined証明書にもlanding分岐にも存在しないからである。

### `landing_crossingTime_not_record_or_gap` (L332)

**主張:** landing固定点についてのrecord排除は、残余を明示した形で成立する: 「clockより前の値がclock値を上回る」か、または `crossingTime < predecessorFirstTime`。

**証明:** L305の二択に分ける。前者(`predecessorFirstTime < landingTime`)なら、弱上向き交差の `start_le` により `landingTime ≤ crossingTime` なので `predecessorFirstTime < crossingTime` が言え、L85が発火する。後者はそのまま残余として返す。つまりrecord排除はlanding枝では**条件付き**に成立し、その条件は `predecessorFirstTime < landingTime` である。

### `landing_thirtytwo_le_crossingTime_or_gap` (L362)

**主張:** landing固定点は床 `32 ≤ crossingTime` を持つ。ただし `crossingTime < predecessorFirstTime` の場合を除く。

**証明:** L305の二択の前者からL178が発火する。後者はそのまま残余。残余の形は具体的で、「tail最小値のpredecessorがlanding交差より後に初出する」という一つの順序主張である。**この一事実さえ供給されれば、replay側の道具立てが丸ごとlanding側へ移る。**

### `PermanentTailUnifiedOutcome.semantic_or_thirtytwo_or_landingGap` (L386)

**主張:** 統合outcomeの精密化。「semantic位相child」「`32 ≤ crossingTime` かつ `19 ≤ target` を伴う固定点核」「landing gap(`crossingTime < predecessorFirstTime` かつ `target < a(predecessorFirstTime)`)」の三択。

**証明:** 統合outcomeの三枝を場合分けする。semantic枝はそのまま。replay枝は自前のkernel床 `112 ≤ crossingTime` を持つので第二枝へ落ちる。landing枝はL362でさらに二分し、床が取れれば第二枝、取れなければ第三枝へ入れる。`19 ≤ target` はどちらの枝でも核から無条件に出る。

**この定理の位置づけには重要な留保がある。** 第八十一ラウンドの敵対的再検査により、第一disjunctのsemantic枝は `0 < target` だけから捏造できる(`PhaseSearchProgress` は四成分lex順にすぎず、比較元の親が存在量化されているだけなので、anchorを一つ上げた親を常に作れる)ことが判明している。したがって**この三択そのものは論理的に情報量ゼロであり、`0 < target` から出る**。この定理の価値は選言の成立にではなく、第二・第三枝が実際に起きたときにそこへ載っている内容(床32、gapの具体形)にある。

## 全体の中での位置づけ

証明地図(docs/PROOF_MAP.md)の「landing側の再訪排除/record排除/downcross前置界/landing床」の4行がすべて本モジュールに対応する。上流は統合outcomeを与える `PermanentAboveCorridorLeastMissingSummit.lean` と、coverage条件を抽象化した `PermanentAboveCorridorPrefixSuccessorCoverage.lean` である。

移植の成績表は次の通りである。再訪排除は**無条件で移植できた**。record排除は共有核レベルの汎用形としては無条件だが、landing分岐で発火するのは `predecessorFirstTime < landingTime` のときに限る。downcross前置界は**移植できず、しかもlanding分岐には原理的に存在しない**ことを `window_below` と `landing_predecessorFirstTime_outside_window` が示している。

残された一点は後続ラウンドで、二択を決めることによってではなく、上流の型を変えることで埋められた。第八十二ラウンドは history枝の定義そのものを `TerminalHistoryBudgetDrop` と `TerminalHistoryCursor` の連言へ強化し、「clockより前のtarget超事象」というデータを生成点からsource-freeで運ぶようにした。その結果 `LandingFloorThirtytwo.lean` の `landing_thirtytwo_le_crossingTime` が無条件になっている。ただしこれは本モジュールが同定した二択を解決したのではなく、**同じデータを別ルートで供給し直した**ものである。そして床が32へ上がってもsemantic枝が空であるという事実は変わらないため、頂点定理の二択自体は依然 `0 < target` から出る。床の価値は枝の内容にあり、選言の形にはない。
