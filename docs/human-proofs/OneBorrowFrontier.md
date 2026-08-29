# OneBorrowFrontier

**役割:** 負エポックの終端を一つのフロンティア定理にまとめる: 高々 `⌊r/2⌋` 歩で実際の一段借り遷移が起こり、ポテンシャルは厳密に上昇し、着地は非負か商 4 以上である。

## このモジュールの役割

`Recovery.lean` は負ポテンシャル状態が有限時間で一段借りに達することを、`RecoveryBudget.lean` は実軌道の一段借りが `G` を厳密に増やすことを、`RecoveryFrontier.lean` は低商の一段借りが必ず非負に回復することを、それぞれ示した。本モジュールはこの三つを合成し、負エポック(負ポテンシャルから回復を追う有限区間)の出口の形を一度に記述するフロンティア(解析領域の境界で成立する定理)を与える。結論は、一段借りの前後の実座標・借りデータ・ポテンシャル上昇・出口の二分(非負着地または高商 4 以上)をすべて一つの存在文に束ねた形であり、下流のエポック解析がこの定理一つを引けば負領域の処理を始められるようにする。

## 定理と証明

### `eventually_oneBorrow_frontier` (L8)

**主張:** 実軌道の負ポテンシャル座標点 `CoordinatesAt n q r`, `G(q,r) < 0` から出発すると、時刻 `t`(`n ≤ t ≤ n + ⌊r/2⌋`)と座標 `q', r'`、新剰余 `s`、着地商 `k` が存在して、

1. `CoordinatesAt t q' r'` かつ `BorrowData t q' r' 1 s`(時刻 `t` で実際に一段借りが起こる)、
2. `CoordinatesAt (t+1) k s`(着地点も実軌道の座標である)、
3. `G(q', r') < G(k, s)`(ポテンシャルは厳密に上昇する)、
4. `0 ≤ G(k, s)` または `4 ≤ k`(非負に回復するか、高商障壁に当たるかの二択)。

**証明:** まず `Recovery.lean` の有限時間定理(`eventually_oneBorrow_of_negative_halfRemainder`)で、`⌊r/2⌋` 歩以内の一段借り時刻 `t` とその座標・借りデータを取る。あとは時刻 `t+1` の一歩が合法減算か強制加算かで場合分けする。

- **合法減算の場合。** 合法性から `t + 1 < a t`、よって `q' ≥ 2` となり、着地商は `k = q' − 2`(Lean 上は `q' − 1 − 1`)。減算の座標遷移(`coordinates_sub_borrowData`)が `CoordinatesAt (t+1) k s` を与え、`RecoveryBudget.lean` の単調性(`coordinates_sub_oneBorrow_potential_lt`)がポテンシャルの厳密上昇を与える。出口の二分は、`k ≤ 3` なら `RecoveryFrontier.lean` の低商回復(`coordinates_sub_oneBorrow_lowQuotient_nonnegative`)により着地は非負、そうでなければ `4 ≤ k` が自明に成り立つ。
- **強制加算の場合。** 着地商は `k = q'`(Lean 上は `q' + 1 − 1`)。加算の座標遷移(`coordinates_add_borrowData`)と加算側の単調性(`coordinates_add_oneBorrow_potential_lt`)を使い、二分は同様に `q' ≤ 3` なら低商回復(`coordinates_add_oneBorrow_lowQuotient_nonnegative`)、さもなくば `4 ≤ k`。

いずれの枝でも四つの結論が同時に揃う。

### `eventually_oneBorrow_potential_rise` (L49)

**主張:** 同じ設定で、出口の二分を落とした弱い形: `⌊r/2⌋` 歩以内に、ポテンシャルを厳密に上げる実際の一段借り遷移が存在する。

**証明:** L8 の結論から第 4 成分を捨てるだけである。「負エポックでは必ずポテンシャルが一度は上がる」という定性的事実だけが必要な場面のための射影。

## 全体の中での位置づけ

`RecoveryFrontier` を入力とする回復層の終端モジュールで、証明地図(docs/PROOF_MAP.md)の状況一覧では `RecoveryFrontier` とともに「高商障壁」の行に対応する。ここで確定した出口の二分「非負着地 or 商 4 以上」は、負エポックを undershoot 帯(`0 ≤ G < m` の非負ポテンシャル帯)への脱出と blocker 生成に振り分ける `NegativeEpoch.lean` の場合分けと同じ構造であり、本モジュールはそれを目標 `m` に依存しない純座標の形で単独に切り出したものである。現在の下流(`NegativeEpoch` 以降)は目標付きの精密版を直接構成するため、本定理は負エポックのフロンティア構造を示す独立の総括として置かれている。
