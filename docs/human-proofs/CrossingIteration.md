# CrossingIteration

**役割:** joint-growth crossing のエポック frontier を旧 debt anchor と比較して精密化し、残る二つの literal residual(coverage_growth / negative_growth)を分離した上で、その不可避性を実軌道でカーネル検証する。

## このモジュールの役割

`CrossingGrowth` が切り出した joint-growth 障害は、その内部にエポック frontier(即時被覆、後の負点、または後の局所被覆)を保持している。本モジュールは、この frontier が返す値を旧 debt の anchor(探索ランクの基準となる親の値)と突き合わせると、新しい仮定なしにどこまで進めるかを確定する。結果は三択で、目標出現・旧 debt 節点のランク子・そして二種類の正確な残余である。さらに、そのうち negative_growth 残余が実軌道(目標 5、遷移 7 → 13)で実際に生じ、既存のどの数値尺度も減らないことを示す。これにより、residual 型は弱い選言インターフェースの産物ではなく、最終的な意味的オラクルが表現しなければならない本物の状態であることが確定する。

## 主要な定義

### `CrossingIterationResidual` (L9)

joint-growth crossing の frontier を旧 anchor と比較したときに残る、ちょうど二つの状況を表す帰納命題。

- `coverage_growth`: frontier の `CoverageStep` が返した blocker 値 `value` が、その局所軌道値 `sourceValue` からは降下している(`value < sourceValue`)ものの、`target ≤ value` かつ `anchor ≤ value` で旧 anchor を下回らない場合。
- `negative_growth`: frontier が負ポテンシャル(`potential < 0`)の座標点に到達したが、その軌道値が `anchor ≤ a time` と旧 anchor 以上に成長している場合。

## 定理と証明

### `CrossingGrowthObstructionAt.refine_epoch_frontier` (L30)

**主張:** joint-growth 障害の frontier は、新しい仮定なしに次の三択へ精密化できる: (i) 目標が出現する、(ii) 旧 debt 節点 `⟨horizon, anchor, debt, debtTime⟩` の位相ランク子が存在する、(iii) `CrossingIterationResidual target anchor` が成り立つ。

**証明:** frontier の三分岐をそれぞれ処理する。即時被覆の場合、`CoverageStep` が目標出現なら (i)、blocker 値 `y` を返すなら `y < anchor` かどうかで分け、成り立てば anchor 降下による debt 脱出で (ii)、さもなくば `coverage_growth` 残余で (iii)。後の負点の場合、その軌道値 `a u` を anchor と比較し、`a u < anchor` なら (ii)、さもなくば `negative_growth` 残余。後の局所被覆の場合は即時被覆と同じ議論である。

ここで (ii) の子は意図的に「ランクのみ」である: 負ポテンシャルの端点は値が target 未満のこともあり、そのときは normal 探索の意味的不変量(`NormalSearchInvariant`)を満たさない。ランク降下と意味的資格を分離して記録することが、residual 型を「最終オラクルが追加で表現すべき意味的ケース」として正確に浮かび上がらせる。

### `crossingGrowth_negativeContinuation_actual_example` (L75)

**主張:** 目標 5 の実 joint-growth 障害(`CrossingGrowthObstruction 5 4 7 6 3`)の frontier 証人として、catch-up 点(時刻 5、値 7)の直後の時刻 6 が取れる: 座標は `CoordinatesAt 6 2 1`(`a 6 = 13 = 6·2 + 1`)、ポテンシャルは `1 − 3 = −2 < 0` と負であり、しかも値は `7 ≤ 13`、`a 5 = 7 < 13 = a 6` と成長し、normal 節点 `⟨4, 13, normal, 13⟩` は旧 debt 節点 `⟨4, 7, debt, 3⟩` の子にならない。

**証明:** 数列の有限区間 `a 0..6 = 0, 1, 3, 6, 2, 7, 13` の検査に帰着し、進捗不能は `exitDebt_to_normal_iff_anchorDrop` で `13 < 7` の否定へ落としてカーネルの `decide` で閉じる。つまり最初の joint-growth(値 7 = anchor)の直後に、二度目の同時成長(値 13 > anchor)が続けて起きる。

### `crossingIterationResidual_actual_example` (L90)

**主張:** 同じ具体的継続が、`refine_epoch_frontier` の要求する残余型をちょうど inhabit する: `CrossingIterationResidual 5 7` が `negative_growth 6 2 1` で成立する。

**証明:** 座標・負ポテンシャル・`7 ≤ a 6` をすべて `decide` で確認する。

### `crossingGrowth_negativeContinuation_no_standard_descent_example` (L98)

**主張:** この継続では既存の三つの数値的脱出尺度がどれも減らない: 履歴予算は不変 `missingBelowCount 5 6 = missingBelowCount 5 4`(どちらも未出値は 4 のみで 1)、軌道値は `a 5 < a 6` と増加、旧 anchor との比較も `7 ≤ a 6` と成長側にある。

**証明:** すべて有限計算(`decide`)である。予算・値・anchor 比較のどれを第一成分に選んでも、この一歩は下降にならないことの直接検証である。

### `negativeGrowth_not_oldDebtRank_example` (L107)

**主張:** 特に、負ポテンシャルという事実だけでは joint-growth frontier を旧 debt 節点の子に変換できない: `potential 2 1 < 0` かつ `7 ≤ a 6` でありながら、対応する normal 節点への `PhaseSearchProgress` は成立しない。

**証明:** 前掲の実例定理の最終成分をそのまま取り出す。結論として、全域的な意味的オラクルは `negative_growth` を証明付き状態として domain に加えるか、まさにこの状態からのさらなる降下定理を確立するかのいずれかを迫られる — この選択が次段の `CrossingFrontier` 以降の設計を規定する。

## 全体の中での位置づけ

証明地図の「負債局所解析」層で `CrossingGrowth` の直上にあり、joint-growth 障害の frontier を「ランク子が取れる部分」と「取れない literal residual」に完全分解する役割を担う。ここで分離された residual のうち coverage 側・negative 側の両方は、`CrossingFrontier` で `CrossingFrontierResidual` としてさらに精密化され、strong debt 証明書の self-exit により現行 semantic domain の中では安全に処理される。negative_growth の実例(遷移 7 → 13)は、後の `CrossingContinuationGrowthResidual`(target 19 の実例)と並んで、「同時成長は interface の弱さではなく実在する」という本研究の反例駆動の設計方針を代表する。
