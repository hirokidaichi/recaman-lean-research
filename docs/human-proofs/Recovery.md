# Recovery

**役割:** 負ポテンシャル状態は有限時間(高々 `⌊r/2⌋` 歩)で必ず一段借りに到達し、負から非負への横断はその一段借りに限られることを証明する。

## このモジュールの役割

負領域(`G(q,r) = r − U(q) < 0` の座標領域)に入った実軌道がどう振る舞うかを解析する「回復」(recovery: 負ポテンシャルから非負着地または被覆証明へ進む有限過程)の中核である。まず、借りが 0 回(zero-borrow)の遷移は負領域から抜け出せないこと、そして負領域での zero-borrow は剰余を毎回 2 以上減らすことを示す。剰余は非負整数なので、この降下は無限には続かず、有限時間で一段借り(one-borrow)が必ず起こる。さらに `NegativeRegion.lean` の「multi-borrow は負に着地する」と合わせ、負から非負への横断・目標面への直接着地が起こるとすればその借り回数は正確に 1 であることを結論する。これにより、負領域の脱出問題は `RecoveryBudget.lean` 以降の一段借りの精密解析に完全に帰着する。

## 定理と証明

### `add_zeroBorrow_potential_eq` (L7)

**主張:** zero-borrow 加算では `G(q+1, s) = G(q,r) − (2q+1)`。

**証明:** `b = 0` の収支式 `r = q + s` から通常領域の条件 `q ≤ r` と `s = r − q` が従い、通常加算のポテンシャル公式 `potential_add_regular` に帰着する。加算で商が 1 増えると三角数の閾値が `2q+1` 増えるため、その分だけ `G` が下がる。

### `sub_zeroBorrow_potential_eq` (L22)

**主張:** `1 ≤ q` のとき、zero-borrow 減算では `G(q−1, s) = G(q,r)`(ポテンシャル保存)。

**証明:** 同様に `q ≤ r`、`s = r − q` に帰着し、通常減算の保存則 `potential_sub_regular` を使う。減算では剰余が `q` 減り、三角数の閾値もちょうど `q` 減るため `G` は変わらない。

### `add_zeroBorrow_preserves_negative` (L38)

**主張:** zero-borrow 加算は負ポテンシャルを保つ(負領域から脱出できない)。

**証明:** `G` が `2q+1 ≥ 0` だけ下がるので、負ならさらに負になる。

### `sub_zeroBorrow_preserves_negative` (L50)

**主張:** zero-borrow 減算も負ポテンシャルを保つ。

**証明:** `G` が保存されるので明らか。

### `two_le_quotient_of_negative_zeroBorrow` (L59)

**主張:** 負ポテンシャルの zero-borrow 状態(通常領域)では `2 ≤ q`。

**証明:** zero-borrow から `q ≤ r`。`q = 0` なら `G = r ≥ 0`、`q = 1` なら `r ≥ 1` かつ `U(1) = 1` より `G = r − 1 ≥ 0` で、いずれも負に反する。

### `zeroBorrow_remainder_drop` (L81)

**主張:** 負領域での zero-borrow 遷移は剰余を毎回 2 以上減らす: `s + 2 ≤ r`。

**証明:** `s = r − q` と前定理の `q ≥ 2` から直ちに従う。この不等式が次の有限時間定理の降下尺度になる。

### `eventually_oneBorrow_of_negative_halfRemainder` (L98)

**主張:** 実軌道の負ポテンシャル座標点 `CoordinatesAt n q r`, `G(q,r) < 0` から出発すると、ある時刻 `t`(`n ≤ t ≤ n + ⌊r/2⌋`)で一段借りが起こる。すなわち `CoordinatesAt t q' r'` かつ `BorrowData t q' r' 1 s` となる `t, q', r', s` が存在する。

**証明:** 剰余 `r` に関する強帰納法。現在の状態の借りデータを取ると、実軌道では借り回数は 0 か 1 に限られる(`OrbitBounds` 由来の `eq_zero_or_one_of_coordinatesAt`)。

- 借りが 1 なら、`t = n` 自身が求める一段借りの時刻であり、歩数 0 で終わる。
- 借りが 0 なら、次の一歩(合法減算か強制加算かを問わず)は負ポテンシャルに留まり(L38, L50)、新しい剰余 `s` は `s + 2 ≤ r` を満たす(L81)。よって帰納法の仮定が `s` に適用でき、そこから高々 `⌊s/2⌋` 歩で一段借りに達する。歩数の合計は `1 + ⌊s/2⌋ ≤ 1 + ⌊r/2⌋ − 1 = ⌊r/2⌋` に収まる。

剰余は 1 歩ごとに 2 以上減る非負整数なので、この降下は無条件に停止する。仮定は「現在負である」ことだけであり、履歴や目標に関する条件は一切要らない。

### `eventually_oneBorrow_of_negative` (L134)

**主張:** 同じ結論を粗い上界 `t ≤ n + r` で述べた便宜形。

**証明:** `⌊r/2⌋ ≤ r` から直ちに従う。

### `add_crosses_nonnegative_only_oneBorrow` (L146)

**主張:** 加算が `G < 0` から `G ≥ 0` へ横断するなら、その借り回数は正確に 1。

**証明:** `b` に関する場合分け。`b = 0` は負を保つ(L38)ので横断できない。`b ≥ 2` は着地が必ず負(`NegativeRegion` の `add_multi_potential_neg`)なのでやはり横断できない。残るのは `b = 1` のみ。

### `sub_crosses_nonnegative_only_oneBorrow` (L164)

**主張:** 実軌道上の合法減算による横断も借り回数は正確に 1。

**証明:** 合法減算から `n + 1 < a n`、したがって `b + 1 ≤ q` が得られ、`b = 0` は保存(L50)、`b ≥ 2` は `coordinates_sub_multi_potential_neg` で負着地となり、いずれも横断と矛盾する。

### `add_crossing_oneBorrow_chamber` (L189)

**主張:** 加算側の横断では `b = 1` に加えて、一段借りの領域条件 `r < q ≤ n + 1 + r` が成り立つ。

**証明:** 前定理で `b = 1` を得て、`BorrowData` の特徴づけ `eq_one_iff`(借り 1 回であることと領域条件の同値)を適用する。

### `sub_crossing_oneBorrow_chamber` (L199)

**主張:** 減算側の横断についても同じ領域条件が成り立つ。

**証明:** 同様。

### `add_negative_to_target_only_oneBorrow` (L211)

**主張:** 負ポテンシャルから目標面 `G = m`(`m ≥ 0`)へ加算で直接着地するなら `b = 1`。

**証明:** 着地値 `Int.ofNat m` は非負なので、これは非負横断の特別な場合であり L146 に帰着する。

### `sub_negative_to_target_only_oneBorrow` (L223)

**主張:** 減算による目標面への直接着地も `b = 1`。

**証明:** 同様に L164 に帰着する。

## 全体の中での位置づけ

`NegativeRegion` と `OrbitBounds` を入力とし、`RecoveryBudget.lean` から使われる。証明地図(docs/PROOF_MAP.md)の「負エポック有限化」の第一段であり、状況一覧の「負領域 — 有限時間で一段借り」の前半を担う。ここで得た「有限時間で必ず一段借り」(L98)は `OneBorrowFrontier.lean` と `NegativeEpoch.lean` の帰納法の骨格にそのまま再利用され、「横断は一段借りのみ」という結論は、一段借りの収支・時計を精密に計算する `RecoveryBudget.lean` の解析対象を正当化する。
