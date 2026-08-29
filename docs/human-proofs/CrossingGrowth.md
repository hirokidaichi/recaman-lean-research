# CrossingGrowth

**役割:** catch-up 後に残る「値も anchor も同時に成長する」障害を `CrossingGrowthObstruction` として正確に切り出し、それ以外のすべての分岐が目標出現または位相ランク下降で閉じることを示す。

## このモジュールの役割

`CrossingGap` の有限 catch-up 定理は、crossing(target 未満から強制加算で target 以上へ横断する遷移)後の debt 状態に対し、値比較と anchor 比較という二つの独立な二択を残していた。本モジュールはまず、horizon(履歴予算を評価する履歴時刻)を固定したまま debt から normal へ戻る遷移のランク境界が「anchor の厳密降下」とちょうど一致することを同値として確定する。その上で、二つの二択の混合ケースがすべて閉じること、すなわち残るのは「catch-up 値が旧値以上かつ旧 anchor 以上」という一つの joint-growth 障害だけであることを証明する。この障害は仮想的な可能性ではなく、目標 5 の実軌道上で実際に生じることをカーネル検証で示す。

## 主要な定義

### `CrossingGrowthObstructionAt` (L36)

有限 catch-up が残す joint-growth 状況の完全な記録。catch-up 状態 `CrossingCatchup`、値の成長 `value ≤ a catchTime`、anchor(探索ランクの基準となる親の値)の成長 `anchor ≤ a catchTime`、catch-up 値を持つ自然な normal 節点が旧 debt 節点の位相ランク子になれないこと(`no_direct_phase_progress` — これは未証明の穴ではなく下の同値定理からの帰結)、および catch-up 点のエポック frontier(即時被覆または後の負点・局所被覆)を同時に保持する。

### `CrossingGrowthObstruction` (L52)

上の構造を catch-up 時刻・座標・初出時刻について存在量化した命題。

## 定理と証明

### `exitDebt_to_normal_iff_anchorDrop` (L9)

**主張:** horizon を固定したとき、debt 節点から normal 節点への遷移が `PhaseSearchProgress`(履歴予算・anchor・位相・局所量の四成分辞書式ランクの厳密下降)になるのは、`childAnchor < parentAnchor` のとき、かつそのときに限る。

**証明:** 十分性は既知の `phaseSearch_exitDebt_of_anchorDrop` である。必要性は辞書式順序の場合分けによる。第一成分の履歴予算 `missingBelowCount`(target 未満の未出値の個数)は同じ horizon で評価されるので厳密降下は不可能。第二成分が anchor であり、ここで降下すれば結論。第三成分の位相ランクは `normal = 1 > 0 = debt` と目的の向きと逆であり、第四成分に到達するには第三成分の等号が必要だが `1 = 0` は偽である。よって進捗は anchor 成分の降下しかあり得ない。位相成分が normal 側に不利に設計されている(debt への進入だけが位相で下がる)ことが、この境界を一点に絞っている。

### `debtCoverageStep_target_or_phaseProgress` (L61)

**主張:** debt 値 `value` に対する `CoverageStep` は、目標の出現を与えるか、または `target ≤ y < value` なる初出値 `y` から anchor 降下つきの normal 子への `PhaseSearchProgress` を与える。

**証明:** `CoverageStep` の第二分岐の値 `y` は `y < value` を満たし、debt 不変量の `value < anchor` と合わせて `y < anchor` が従うので、前段の anchor 降下脱出がそのまま使える。短い補題だが、「被覆 blocker は位相ランクと既に整合している」ことを明示する。

### `debtCrossing_finite_catchup_phaseOutcome` (L87)

**主張:** 時刻 `n+1` の debt 状態で `a n < target` なら、(i) 目標が出現する、(ii) 旧 debt 節点の位相ランク子が存在する、(iii) `CrossingGrowthObstruction` が成立する、の三択が成り立つ。これは有限 catch-up の位相水準での最強の無条件精密化である。

**証明:** `debtCrossing_finite_catchup` の四つ組(catch-up 状態、値比較、anchor 比較、frontier)を場合分けする。値比較が `CoverageStep` 側なら前定理で (i) または (ii)。値が成長し anchor 比較が進捗側なら (ii)。両方成長した場合のみ (iii) となり、`no_direct_phase_progress` フィールドは `exitDebt_to_normal_iff_anchorDrop` と `anchor ≤ a t` から算術的に埋まる。したがって catch-up の二つの比較は独立な残余課題ではなく、混合ケースはすべて閉じ、残るのは同時成長ただ一つである。

### `crossingGrowth_actual_example` (L122)

**主張:** 実軌道の strict crossing `3 → 6`(時刻 2→3、目標 5)に対し、catch-up は時刻 5・値 `a 5 = 7` に着地し(`CrossingCatchup 5 4 7 5 1 2 5`)、`6 ≤ 7` かつ `7 ≤ 7` が成り立ち、値 7 を持つ自然な normal 節点は旧 debt 節点 `⟨4, 7, debt, 3⟩` の位相ランク子にならない。

**証明:** 座標 `7 = 5·1 + 2`、値 7 の初出が時刻 5 であること(`a 0..4 = 0,1,3,6,2`)を有限検査で確かめ、進捗不能は `exitDebt_to_normal_iff_anchorDrop` により `7 < 7` の否定へ帰着してカーネルの `decide` で閉じる。catch-up 値が旧 anchor とちょうど等しくなる、joint-growth 障害の最小の実例である。

### `crossingGrowthObstruction_actual_example` (L147)

**主張:** 同じ実軌道区間で、エポック frontier まで含めた完全な障害パッケージ `CrossingGrowthObstruction 5 4 7 6 3` が成立する。

**証明:** 前定理の各成分をそのまま構造体に詰め、frontier は `crossingCatchup_epoch_frontier` で供給する。frontier フィールドが他のフィールドと矛盾する「空約束」ではないことの確認である。

## 全体の中での位置づけ

証明地図の「負債局所解析」層で `CrossingGap` の直上に立つ。ここで切り出された `CrossingGrowthObstruction` を、`CrossingIteration` が旧 anchor との比較でさらに二つの literal residual に分解し、`CrossingFrontier` が frontier 由来の子と strong debt の self-exit で意味的に閉包する。`exitDebt_to_normal_iff_anchorDrop` は同一 horizon での debt 脱出境界の基準定理として、horizon を進める場合の一般化(`CrossingHorizon`)の出発点にもなっている。
