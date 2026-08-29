# CrossingGap

**役割:** crossing の小さな相対ギャップを直接エポック定理に渡す代わりに、絶対時計が目標に追いつく有限の「catch-up」状態を構成し、そこから既存エポック API を無条件に呼べることを示す。

## このモジュールの役割

`CrossingRecovery` で確定したとおり、crossing(target 未満の値から強制加算で target 以上へ上向き横断する遷移)は正で歩幅以下の相対ギャップ `target − a n` を供給するが、エポック定理群が要求するのは絶対時刻条件 `target ≤ 時刻 + 1` である。本モジュールはこの不一致を、時刻 `target − 1` または `target` まで軌道を進めれば必ず「target-ready」な状態(時刻条件と `target ≤ a t` を同時に満たす状態)に到達するという事実で解消する。その状態を `CrossingCatchup` 構造にまとめ、あらゆる catch-up 状態が既存の負領域・undershoot・above-target 機構のいずれかに受理されることを証明する。最後に、相対ギャップの小ささが絶対時刻条件を含意しないことを実軌道の反例でカーネル検証し、この迂回が不可避であることを示す。

## 主要な定義

### `CrossingCatchup` (L9)

絶対時計が目標に追いついた後の target-ready 状態。時刻が `t = target − 1` または `t = target` であること、エポック時刻条件 `target ≤ t + 1`、値条件 `target ≤ a t`、座標 `CoordinatesAt t q r`、および値 `a t` の初出時刻 `f ≤ t`(`FirstAt a (a t) f`)を保持する。小さな crossing ギャップそのものをエポック定理に渡そうとする代わりに使う、意味的な置き換えである。

## 定理と証明

### `positiveQuotient_potential_aboveTarget_gives_coverageStep` (L22)

**主張:** 正の時刻 `n`、正の商 `q`、時刻条件 `target ≤ n + 1` のもとで、座標のポテンシャルが `target ≤ G(q,r)` を満たすなら、`CoverageStep target (a n) n` が成り立つ。

**証明:** ポテンシャルが非負なので `g = r − upperTri(q)` とおくと `G = g` かつ `target ≤ g` である。非負エポック定理 `nonnegative_epoch_records_level_or_coverage` により、被覆が直ちに得られるか、レベル `g` がある時刻までに履歴へ記録される。後者の場合、`g` の初出時刻 `fg` を取る。`g ≤ r` であり、`n·q > 0`(時刻・商とも正)だから座標式より `g ≤ r < n·q + r = a n`。したがって `y = g` が `target ≤ y`、初出、`y < a n` の三条件を満たし、`CoverageStep` の第二分岐(親値より真に小さい初出値)が成立する。正の商が「記録されたレベルは開始値より真に小さい」ことを保証する点が鍵である。

### `crossingCatchup_epoch_frontier` (L59)

**主張:** `0 < target` のとき、任意の catch-up 状態は既存エポック機構に受理される。すなわち `CoverageStep target (a t) t` が直ちに成り立つか、後の時刻 `u ≥ t` で負ポテンシャル座標または局所 `CoverageStep` に到達する。

**証明:** まず `t > 0` を確かめる(`t = 0` なら `a 0 = 0 < target` が `target ≤ a t` に反する)。次に `q > 0` を示す: `q = 0` なら `a t = r < t` だが、`t ≤ target ≤ a t` なので矛盾する(`time_eq` の両分岐とも同じ計算)。あとはポテンシャルの符号で三分する。`G < 0` なら負領域エポック定理 `negative_undershoot_cycle`、`G ≥ target` なら前定理による即時被覆、`0 ≤ G < target` なら undershoot 有限降下定理 `undershoot_eventually_negative_or_localCoverage` が、それぞれ catch-up 状態の時刻条件 `target ≤ t + 1` を使って結論を与える。

### `debtCrossing_finite_catchup` (L116)

**主張:** 時刻 `n+1` の debt 状態で `a n < target` なら、catch-up 状態 `(t, q, r, f)` が存在して次の三つが同時に成り立つ。(1) `CoverageStep target value (n+1)` が成立するか、または `value ≤ a t`(値が catch-up 値まで成長)。(2) catch-up 値を anchor とする normal 子への `PhaseSearchProgress` が成立するか、または `anchor ≤ a t`(anchor も成長)。(3) catch-up 状態のエポック frontier(前定理の結論)。

**証明:** `a n < target` から `target > 0` なので、`InitialRegion` の定理 `exists_targetReady_state_of_pos` により時刻 `target − 1` または `target` で target-ready 状態が存在する(レカマン数列はこの時刻までに必ず `target` 以上の値を取る)。これが `CrossingCatchup` の全フィールドを満たす。(1) は `a t < value` かどうかで分ける: 成り立てば `y = a t` が目標以上・初出・`value` 未満なので `CoverageStep`、さもなくば `value ≤ a t`。(2) も同様に `a t < anchor` なら `phaseSearch_exitDebt_of_anchorDrop` による debt 脱出、さもなくば `anchor ≤ a t`。(3) は `crossingCatchup_epoch_frontier` をそのまま適用する。したがって時計の catch-up は無条件かつ有限であり、残る困難は旧来の時刻条件の不一致ではなく、値と anchor が同時に成長する分岐だけである(この残余の正確な切り出しが `CrossingGrowth` の主題)。

### `diagonalDebt_strictCrossing_finite_forward` (L165)

**主張:** 対角由来の debt(目標 `horizon + 1`)で strict crossing が起きた場合、ギャップ上下界 `0 < (horizon+1) − a n ≤ n+1` が成り立ち、さらに catch-up 状態は crossing より真に後 `n + 1 < t` かつ `t ≤ horizon + 1` にあり、そのエポック frontier が得られる。

**証明:** 強制加算と `horizon + 1 < value` から `DebtCrossing (horizon+1) value n` を構成し、`debtCrossing_gap_bounds` でギャップの上下界を得る。catch-up 状態は前定理から取る。debt 不変量の `firstTime < horizon` は今の設定では `n + 1 < horizon` を意味し、`t = horizon` または `t = horizon + 1` のどちらの場合も `n + 1 < t ≤ horizon + 1` が従う。すなわち対角の場合、catch-up 構成は本当に前向き(crossing より未来)であり、小さな相対ギャップは局所的な上下界として保持したまま、絶対時計だけを追いつかせる形になっている。

### `crossingGap_does_not_imply_absolute_epoch_range` (L206)

**主張:** 相対ギャップが小さくても絶対エポック時刻条件は従わない。実際のレカマン crossing `3 → 6`(時刻 2→3)と対角型 horizon `4` について、`DebtInvariant 5 ⟨4, 7, debt, 3⟩ 6 3` と `DebtCrossing 5 6 2` が成立し、ギャップ `5 − a 2 = 2` は `0 < 2 ≤ 3` と歩幅内に収まるのに、`5 ≤ 2 + 2` は偽である。

**証明:** 数列の初期値 `a 0, …, a 3 = 0, 1, 3, 6` に対する有限検査で、debt 不変量の各フィールド(値 6 の初出が時刻 3、`3 < 4`、`6 < 7` など)と crossing の三条件をカーネルの `decide` で確認する。この反例が、本モジュールの catch-up 迂回が「あれば便利」ではなく必須であることを示している。

## 全体の中での位置づけ

証明地図の「負債局所解析」層で、`CrossingRecovery` の直後に位置する。`CrossingRecovery` が特定したインターフェース障害(対角 debt の crossing はエポック時刻範囲に入らない)を、絶対時計の有限 catch-up で解消するのが本モジュールである。`CrossingCatchup` と `debtCrossing_finite_catchup` は `CrossingGrowth` の joint-growth 障害の切り出しにそのまま使われ、`BoundaryAudit` は catch-up が履歴予算を変えないこと(`diagonalCrossingCatchup_budget_eq_horizon`)を監査する。
