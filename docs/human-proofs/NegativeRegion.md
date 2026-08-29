# NegativeRegion

**役割:** 借りが2回以上(multi-borrow)の遷移は必ず負ポテンシャルに着地することを示し、負領域(`G < 0` の座標領域)の解析を一段借りだけに帰着させる。

## このモジュールの役割

レカマン数列の値を `a n = n·q + r` (`r < n`) と商・剰余座標で表すと、時刻の法が `n` から `n+1` に変わる際に「借り」(borrow、筆算の借りに相当する算術補正)が `b` 回発生し得る。一般の算術モデルでは `b` は任意だが、本モジュールは `b ≥ 2` の遷移(multi-borrow)の着地点のポテンシャル `G(q,r) = r − U(q)`(`U(q) = q(q+1)/2` は上三角数)が必ず負になることを証明する。したがって、負領域から非負領域への横断や目標面 `G = m` への直接着地は multi-borrow では起こり得ず、後続の `Recovery.lean` で「横断は一段借りに限る」という基本定理が得られる。実軌道では multi-borrow 自体が排除される(`OrbitBounds.lean`)が、本モジュールの結果は座標だけから従う算術的事実であり、その排除証明にも依存しない形で負領域の力学を単純化する。

## 定理と証明

### `self_le_upperTri` (L6)

**主張:** すべての `k` について `k ≤ U(k)`。

**証明:** `k` に関する帰納法。`U(k+1) = U(k) + k + 1` なので各段で右辺は少なくとも 1 増える。

### `two_mul_le_upperTri` (L14)

**主張:** `3 ≤ k` ならば `2k ≤ U(k)`。

**証明:** 帰納法。基底 `k = 3` は `6 ≤ U(3) = 6` を直接計算で確認する。帰納段では `U(k+1) = U(k) + k + 1 ≥ 2k + k + 1 ≥ 2(k+1)`。

### `add_multi_remainder_lt_upperTri` (L29)

**主張:** 借りデータ `BorrowData n q r b s`(すなわち `b(n+1) + r = q + s` かつ `s < n+1`)が `b ≥ 2` を満たすなら、加算側の着地商 `k = q + 1 − b` に対して `s < U(k)`。

**証明:** `b ≤ q + 1` より `q + 1 = b + k` と書ける。収支式に代入すると

```text
s = b·n + r − k + 1
```

を得る。`s ≤ n` と合わせると `(b−1)·n + r + 1 ≤ k` であり、`b ≥ 2` から `n + 1 ≤ k`、すなわち `n < k` が従う。よって `s < n + 1 ≤ k ≤ U(k)`(最後は `self_le_upperTri`)。直観的には、2回以上借りるには現在値が時刻に比べて非常に大きく、着地商 `k` が時刻 `n` を追い越すほど大きくなるため、剰余 `s < n+1` は三角数の閾値 `U(k)` に遠く及ばない。

### `add_multi_potential_neg` (L50)

**主張:** `b ≥ 2` の加算遷移の着地ポテンシャルは負: `G(q+1−b, s) < 0`。

**証明:** 前定理より `s < U(q+1−b)` なので `G = s − U(q+1−b) < 0`。

### `sub_multi_remainder_lt_upperTri` (L61)

**主張:** `b ≥ 2`、`b + 1 ≤ q`、`4 ≤ n` のとき、減算側の着地商 `k = q − 1 − b` に対して `s < U(k)`。

**証明:** `q = b + k + 1` と書けるので収支式から

```text
s = b·n + r − k − 1
```

となる。`s ≤ n` と `b ≥ 2` から `n ≤ k + 1` が従い、`n ≥ 4` と合わせて `k ≥ 3`。よって `s < n + 1 ≤ k + 2 ≤ 2k ≤ U(k)`(最後は `two_mul_le_upperTri`)。減算側は着地商が加算側より小さいため、`k ≤ U(k)` では足りず、`n ≥ 4` を仮定して `2k ≤ U(k)` を使う点が加算側との違いである。

### `sub_multi_potential_neg` (L81)

**主張:** 同じ仮定のもとで `G(q−1−b, s) < 0`。

**証明:** 前定理から直ちに従う。

### `actual_multi_time_ge_four` (L94)

**主張:** 実軌道の座標 `CoordinatesAt n q r`(すなわち `a n = n·q + r`, `r < n`)が `b ≥ 2` の借りデータを持つなら `4 ≤ n`。

**証明:** `b ≥ 2` は multi-borrow 領域の特徴づけにより `n + 1 + r < q` と同値である。`n ≤ 3` の各場合を実際の値で棄却する: `n = 0` は `r < 0` となり不可能。`n = 1, 2, 3` では `a 1 = 1`, `a 2 = 3`, `a 3 = 6`(Lean カーネルの `decide` で検証)を `a n = n·q + r` に代入すると、`q` が `n + 1 + r < q` を満たすほど大きくなれないことが `r < n` との連立で分かる。

### `coordinates_sub_multi_potential_neg` (L123)

**主張:** 実軌道上で合法減算(`CanSubtract`)が multi-borrow 座標更新を伴うなら、着地ポテンシャルは負。

**証明:** 合法減算からは `n + 1 < a n` が従い、これと座標の等式から `b + 1 ≤ q` が得られる。`actual_multi_time_ge_four` で `n ≥ 4` を確保し、`sub_multi_potential_neg` を適用する。

### `add_multi_ne_targetSurface` (L134)

**主張:** multi-borrow 加算は目標面 `G = m`(`m` は非負整数)に直接着地できない。

**証明:** 着地ポテンシャルは負(`add_multi_potential_neg`)であり、`Int.ofNat m ≥ 0` と矛盾する。

### `coordinates_sub_multi_ne_targetSurface` (L149)

**主張:** 実軌道上の合法 multi-borrow 減算も目標面 `G = m` に直接着地できない。

**証明:** `coordinates_sub_multi_potential_neg` から同様。

## 全体の中での位置づけ

本モジュールは `LandingSurfaces` の上に立ち、`Recovery.lean` から直接使われる。証明地図(docs/PROOF_MAP.md)の「実多段借り排除」から「負エポック有限化」への橋にあたり、`Recovery.lean` の「負から非負への横断は必ず一段借り」(`add_crosses_nonnegative_only_oneBorrow` など)の場合分けで、`b ≥ 2` の枝を潰す役を担う。`OrbitBounds.lean` が実軌道上の multi-borrow を排除するのとは独立に、座標算術だけで multi-borrow の行き先を負領域に閉じ込める点が特徴である。
