# CrossingRecovery

**役割:** 負債終端の強制加算が目標を厳密に飛び越える「strict crossing」の直後状態を解析し、そのポテンシャルが必ず目標未満に落ちることと、既存エポック機構への接続条件・限界を確定する。

## このモジュールの役割

debt(負債: 対角分岐で得た早期blockerを処理する探索モード)の途中で強制加算が起きると、軌道値は目標 `m` 未満から一気に `m` を飛び越えることがある。この上向き横断を crossing と呼ぶ。本モジュールは、crossing 直後の商・剰余座標におけるポテンシャル `G(q,r) = r − upperTri(q)` が常に目標未満であること、すなわち着地点が負領域か undershoot 帯(`0 ≤ G < m` の帯)のどちらかに限られることを証明する。さらに、目標が時刻範囲内にあれば既存の負領域・undershoot エポック定理へそのまま接続できること、逆に対角由来の debt ではこの時刻条件が原理的に満たされないことを、それぞれ定理として固定する。crossing 状態そのものは `CrossingRecoveryInvariant` という証明付き構造にまとめられ、通常の normal 状態と混同されないようにする。

## 主要な定義

### `CrossingRecoveryInvariant` (L10)

strict crossing 直後の意味的状態を表す構造。目標 `target` が時刻 `n` までの履歴に未出であること、時刻 `n+1` の遷移が強制加算(減算不能)であること、`DebtCrossing target (a(n+1)) n`(`a n < target < a(n+1)` かつ `a(n+1) = a n + (n+1)`)、着地点の座標 `CoordinatesAt (n+1) q r`、crossing 時刻が horizon(履歴予算を評価する履歴時刻)より前であること、および前状態値が anchor(探索ランクの基準となる親の値)より小さいこと `a n < anchor` を同時に保持する。通常の normal 状態と違い、直前の値が target 未満だったという事実と、target がまだ未出であることを明示的に記録している点が本質である。

## 定理と証明

### `debtCrossing_gap_bounds` (L22)

**主張:** strict crossing `DebtCrossing target value n` において、残りギャップ `target − a n` は `0 < target − a n ≤ n + 1` を満たす。

**証明:** 定義から `a n < target < value = a n + (n+1)` である。左の不等式からギャップは正、右の不等式から `target < a n + (n+1)` すなわちギャップは加算歩幅 `n+1` 以下となる。crossing が供給する真に有限なパラメータはこの相対ギャップであり、絶対的な目標値が crossing 時刻以下である保証はない(この区別が後の `CrossingGap` の主題になる)。

### `debtCrossing_post_potential_lt_target` (L32)

**主張:** strict crossing の直後端点の座標 `(q, r)`(`CoordinatesAt (n+1) q r`)について、`potential q r < target` が成り立つ。すなわち着地点は above-target 領域(`G ≥ m`)には決して入らない。

**証明:** 強制加算より `a(n+1) = a n + (n+1)` であり、座標式は `a(n+1) = (n+1)·q + r`、`r < n+1` である。まず `q ≥ 1` を示す: もし `q = 0` なら `a(n+1) = r < n+1` だが、`a(n+1) = a n + (n+1) ≥ n+1` なので矛盾する。すると `(n+1)·q ≥ n+1` だから、座標式より `r ≤ a n` が従う。crossing の定義から `a n < target` なので `r < target`。ポテンシャルは `G = r − upperTri(q)` で、`q ≥ 1` より `upperTri(q) > 0` だから `G ≤ r < target` となる。したがって着地点は負領域(`G < 0`)か undershoot 帯(`0 ≤ G < target`)のいずれかに限られる。

### `debtCrossing_epoch_recovery` (L71)

**主張:** strict crossing の直後状態が、さらに時刻条件 `target ≤ n + 2` を満たすなら、`CoverageStep target (a(n+1)) (n+1)`(目標が出現するか、目標以上で親値より真に小さい初出値を得るという被覆一段)が直ちに成り立つか、または後の時刻 `t ≥ n+1` で負ポテンシャル座標か局所 `CoverageStep` に到達する。

**証明:** 前定理により `G < target` なので、符号で二分する。`G < 0` なら負領域エポック定理 `negative_undershoot_cycle` が、時刻条件 `target ≤ n+2` のもとで結論を与える。`0 ≤ G < target` なら undershoot 帯の有限降下定理 `undershoot_eventually_negative_or_localCoverage` が同じ形の結論を与える。時刻条件を仮定として明示している点が重要で、これは一般の debt crossing からは従わず、後述のとおり対角由来の debt とは実際に両立しない。

### `debtCrossing_enters_recovery` (L96)

**主張:** 時刻 `n+1` の debt 状態(`DebtInvariant`)で強制加算が起き、かつ `a n < target` なら、目標がすでに軌道に出現しているか、さもなくばある座標 `(q, r)` について `CrossingRecoveryInvariant target horizon anchor n q r` が成立し、同時に新しい normal 子(anchor を `a n` とする)への `PhaseSearchProgress`(四成分辞書式ランクの厳密下降)が得られる。

**証明:** まず `target = value`(debt が追跡する初出値)なら初出時刻が目標出現の証人になる。次に `target` が時刻 `n` までの履歴に既出なら、その出現時刻を取ればよい。残るのは target 未出の場合で、ここで crossing を構成する。debt 不変量から `target ≤ value` であり、`target ≠ value` なので `target < value`。強制加算より `value = a(n+1) = a n + (n+1)` だから `DebtCrossing target value n` が成り立つ。座標は正の時刻で常に取れる。anchor については、`a n < value` かつ debt 不変量の `value < anchor` から `a n < anchor` が従い、これが `phaseSearch_exitDebt_of_anchorDrop`(anchor の厳密降下による debt 脱出)を発火させる。得られる意味的状態は normal 不変量ではなく `CrossingRecoveryInvariant` であり、この定理は「形式的な anchor 減少を normal と誤ってラベル付けできない」ことを正確に述べている。

### `diagonalDebt_crossing_not_in_epoch_range` (L137)

**主張:** 対角由来の debt では目標が `horizon + 1` の形をとるが、crossing 時刻が `n + 1 < horizon` を満たす限り、エポック定理の時刻条件 `horizon + 1 ≤ n + 2` は成立しない。

**証明:** `n + 1 < horizon` から `n + 2 ≤ horizon < horizon + 1` なので直ちに従う。これは符号解析の欠落ではなく、既存エポック API とのインターフェース上の正確な障害であり、次モジュール `CrossingGap` の「時計の追いつき(catch-up)」構成が必要になる理由そのものである。

### `crossing_four_negative_example` (L143)

**主張・証明:** 最初の実 crossing、時刻 2→3 の遷移 `3 → 6`(目標 4 を横断)で、着地座標は `(q, r) = (2, 0)`、`G = 0 − 3 = −3 < 0` と負領域に入る。数列の有限区間に対するカーネル検証(`decide`)による。

### `crossing_four_nonnegative_example` (L154)

**主張・証明:** 実遷移 `2 → 7`(時刻 4→5、目標 4 を横断)は座標 `(1, 2)`、`G = 2 − 1 = 1`、`0 ≤ 1 < 4` となり、undershoot 帯のレベル 1 に着地する。同じく `decide` による。前例とあわせて、`debtCrossing_post_potential_lt_target` の二分岐(負・undershoot)がどちらも実軌道で実現され、負ポテンシャルが crossing の必然ではないことを示す。

## 全体の中での位置づけ

証明地図の「負債局所解析」層に属し、`DebtCrossing` と `Undershoot` の上に立つ crossing 解析チェーンの起点である。`debtCrossing_post_potential_lt_target` による符号の絞り込みと `diagonalDebt_crossing_not_in_epoch_range` によるインターフェース障害の特定を受けて、`CrossingGap` が絶対時計の catch-up を構成する。`CrossingRecoveryInvariant` は `PhaseSemantic` からも参照され、意味的探索 domain の crossing recovery 分岐の基礎データとなる。
