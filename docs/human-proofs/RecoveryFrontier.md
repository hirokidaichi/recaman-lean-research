# RecoveryFrontier

**役割:** 低商の一段借りは必ず非負に回復すること、回復に失敗する一段借りは商 4 以上の高商に限られ、その失敗自体が blocker(下降を妨げる既出値)と `CoverageStep` を生むことを証明する。

## このモジュールの役割

`RecoveryBudget.lean` は一段借りの非負着地条件を三角数の閾値式に翻訳した。本モジュールはその閾値を実軌道の商上界 `2q ≤ n + 1` と初期時刻の具体計算で評価し、着地商が 3 以下の一段借りは常に非負へ回復することを示す。対偶として、回復に失敗する一段借りは着地商 4 以上の「高商」障壁でしか起こらない。さらに、失敗する一段借り加算は強制加算であることから、減算候補 `a n − (n+1)` がすでに履歴に存在する。この既出値は現在値より小さくかつ `2(n+1)` 以上なので、十分小さい目標 `m` すべてに対して値下降型の `CoverageStep`(目標到達か、より小さい初出値の発見かの一段証明)を与える。つまり「回復の失敗」がそのまま大域探索の進捗に変換される。

## 定理と証明

### `coordinates_add_oneBorrow_lowQuotient_nonnegative` (L8)

**主張:** 実軌道上で強制加算(減算不能)となる一段借りは、旧商 `q ≤ 3`(着地商も `q`)なら必ず非負に着地する: `0 ≤ G(q, s)`。

**証明:** 判定式 `U(q) + q ≤ n + 1 + r`(`add_oneBorrow_nonnegative_iff`)を `q = 1, 2, 3` について検証する。

- `q = 1`: 閾値は `2` で、商上界 `2q ≤ n + 1` から `n ≥ 1` なので常に成立。
- `q = 2`: 閾値は `U(2) + 2 = 5`。失敗するなら `n + 1 + r ≤ 4` で、`n ≥ 3` と合わせると `n = 3, r = 0` に限られる。しかし時刻 3 では `a 3 = 6` から `6 − 4 = 2` は未出であり、`CanSubtract 4 (stateAt 3)` が成り立つ(`decide` で検証)。これは強制加算の仮定と矛盾する。
- `q = 3`: 閾値は `U(3) + 3 = 9`。失敗するなら `n + 1 + r ≤ 8` で、`n ≥ 5` から `n ∈ {5, 6, 7}`。ところが `a 5 = 7`, `a 6 = 13`, `a 7 = 20`(`decide` で検証)はいずれも `a n = 3n + r`(`r < n`)を満たせない。

いずれの場合も例外は実在せず、閾値が成立する。

### `coordinates_sub_oneBorrow_lowQuotient_nonnegative` (L56)

**主張:** 合法減算の一段借りで着地商 `q − 2 ≤ 3`(すなわち旧商 `q ≤ 5`)なら必ず非負に着地する。

**証明:** 合法性から `q ≥ 2`。判定式 `U(q−2) + q ≤ n + 1 + r` を `q = 2, 3, 4, 5` で検証する。`q = 2, 3, 4` は商上界 `2q ≤ n + 1` から直ちに成立。`q = 5` では閾値 `U(3) + 5 = 11` の失敗候補が `n = 9, r = 0` に絞られるが、そのとき `a 9 = 45` が必要になる一方、実際は `a 9 = 21`(`decide`)なので矛盾する。

### `coordinates_add_oneBorrow_negative_highQuotient` (L94)

**主張:** 一段借り加算の回復が失敗する(着地が負)なら、着地商は 4 以上: `4 ≤ q + 1 − b = q`。

**証明:** L8 の対偶。`q ≤ 3` なら非負に着地するはずだからである。

### `coordinates_add_oneBorrow_negative_blocker_data` (L111)

**主張:** 高商で失敗した一段借り強制加算からは、目標に依存しない blocker データが取り出せる。すなわち `y = a n − (n + 1)` と時刻 `fy` が存在して、`2(n+1) ≤ y`、`FirstAt a y fy`(`y` は時刻 `fy` に初出)、かつ `⟨y, fy⟩` は `⟨a n, n⟩` より値も初出時刻も小さい(`EarlierSmaller`)。前状態の初出性は仮定しない。

**証明:** これが本モジュールの中心である。

まず L94 により着地商は `q ≥ 4`。一段借りの収支 `n + 1 + r = q + s` を `a n = n·q + r` に代入すると

```text
a n = (n+1)·q + s − (n+1),
y = a n − (n+1) = (n+1)·q + s − 2(n+1) ≥ 4(n+1) + s − 2(n+1) = 2(n+1) + s ≥ 2(n+1)
```

を得る。特に `a n ≥ 3(n+1) > n + 1` なので減算候補 `y` は正の位置にある。ここで強制加算の仮定が効く: もし `y` が履歴 `valuesThrough n` に無ければ、減算は合法になってしまうから、`y` は既出である。履歴の元は必ず初出時刻を持つ(`history_member_has_firstAt`)ので `FirstAt a y fy`, `fy ≤ n` を取れる。`fy = n` なら `a n = y < a n` となり矛盾するから `fy < n`。`y < a n` は定義から明らかであり、`EarlierSmaller` の両条件が揃う。

直観的には、高商状態からの強制加算は「大きく引こうとしたら引き先がすでに使われていた」状況であり、その引き先 `y` こそが過去に現れた小さい値、すなわち blocker である。

### `coordinates_add_oneBorrow_negative_gives_coverageStep_exact` (L166)

**主張:** `m ≤ a n − (n + 1)` を満たすすべての目標 `m` に対し、失敗した高商一段借り加算は `CoverageStep m (a n) n` を与える。

**証明:** L111 の blocker `⟨y, fy⟩` は `m ≤ y`、`y` は初出、`y < a n` を満たすので、`CoverageStep` の値下降枝(より小さい初出値の発見)がそのまま成立する。

### `coordinates_add_oneBorrow_negative_gives_coverageStep_below_doubleTime` (L183)

**主張:** 目標の範囲を時刻だけで述べた形: `m ≤ 2(n + 1)` なら `CoverageStep m (a n) n`。

**証明:** blocker の下界 `2(n+1) ≤ y` を経由して L166 と同じ議論を適用する。

### `coordinates_add_oneBorrow_negative_gives_coverageStep_below_time` (L198)

**主張:** 後方互換形: `m ≤ n` でも同じ結論。前状態の初出仮定は引数にあるが実際には使われない。

**証明:** `m ≤ n ≤ 2(n+1)` として L183 に帰着する。

### `coordinates_sub_oneBorrow_negative_highQuotient` (L215)

**主張:** 合法減算の一段借り回復が失敗するなら、着地商は 4 以上: `4 ≤ q − 1 − b`。

**証明:** L56 の対偶。

## 全体の中での位置づけ

`RecoveryBudget` と `PrestateCoverage` を入力とし、`OneBorrowFrontier.lean` と `NegativeEpoch.lean` から使われる。証明地図(docs/PROOF_MAP.md)の状況一覧「高商障壁 — 高商失敗を blocker へ変換」に対応する。低商回復(L8, L56)は `OneBorrowFrontier` のフロンティア定理の「非負または商 4 以上」という二分に、blocker からの `CoverageStep`(L166〜L198)は `NegativeEpoch` の主帰納法で一段借り強制加算が負に留まる枝を閉じるのに、それぞれ使われる。回復の失敗を大域探索の進捗証明書へ変換するこの機構が、負エポック全体を「undershoot 脱出または CoverageStep」の二択に落とす鍵である。
