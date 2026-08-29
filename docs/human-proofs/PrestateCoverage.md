# PrestateCoverage

**役割:** 借りターゲットチャートを遷移前(pre-state)の値へ引き戻し、加算・減算どちらの遷移でも遷移前状態から `CoverageStep` を取り出す。

## このモジュールの役割

`LandingSurfaces.lean` のチャートは「遷移後の状態が目標面 `G = m` 上にある」ことを
遷移前の座標で特徴付けたが、`CoverageStep` を返すべき探索ノードは遷移前の値
`a n` である。このモジュールは、チャートの方程式を遷移前の値の明示式へ解き直し、

- 減算側では借り回数が完全に消去されて遷移前の目標方程式が直接得られること、
- 加算側では低い着地商(`k = 0, 1`)なら無条件の出現、高い着地商(`k ≥ 2`)なら
  「減算できなかったこと」自体が履歴blockerになること

を示す。その結果、目標面へ着地するすべての実遷移について、freshness仮定なしで
遷移前状態からの `CoverageStep` が得られる。末尾では商が大きい強制加算一般に
ついても、時刻以下のすべての目標を一挙に処理するblocker枝を与える。

## 定理と証明

### `sub_borrowTarget_prestate_targetEquation` (L8)

**主張:** 減算側の借りチャートは、遷移前ですでに目標方程式を与える。借り回数は
完全に相殺する: `CoordinatesAt n q r`、`BorrowData n q r b s`、`q = b + k + 1`、
`BorrowTargetPreimage n q r b k m` のもとで `TargetEquation n (a n) m (k+1)`。
つまり「遷移後に商 `k` で `G = m` に着地する」ことは、「旧値から `k+1` 回の減算を
予定する」ことと同じである。

**証明:** 座標の等式 `a n = n·q + r = n(b + k + 1) + r` に、遷移前方程式から解いた
`r = (b + k + 1) + upperTri k + m − b(n+1)` を代入する。展開すると `b` を含む項
`n·b` と `−n·b` が打ち消し合い、

```text
a n = (k+1)·n + (upperTri k + k + 1) + m = m + descentDrop n (k+1)
```

を得る(`upperTri (k+1) = upperTri k + k + 1`)。これは実行する一歩(減算)と
残り `k` 歩の予定を合わせた `k+1` 歩の目標方程式である。

### `add_borrowTarget_prestate_value` (L32)

**主張:** 加算側で正の商 `k` に着地する場合、遷移前の値の厳密な公式:
`k > 0`、`q + 1 = b + k`、遷移前方程式のもとで

```text
a n = (k−1)·(n+1) + upperTri k + m
```

**証明:** `k = p + 1` と書けば `q = b + p` である。`a n = n(b + p) + r` に遷移前方程式
から解いた `r` を代入すると、減算側と同様に `b` の項が相殺し
`a n = p(n+1) + upperTri k + m` が残る。補助的だが、以下のblocker構成の土台になる。

### `add_borrowTarget_prestate_blocker` (L59)

**主張:** 実際の加算が `(p+2, G = m)` に着地するなら、遷移前で阻止された減算候補は
値が `m` 以上の具体的な `ActualBlocker` である: `a n` の初出が時刻 `n`、座標・借り
データ・減算不能・`q + 1 = b + (p+2)`・遷移前方程式のもとで、
`∃ y, m ≤ y ∧ ActualBlocker n (a n) 0 y`。

**証明:** 候補は `y = p(n+1) + upperTri (p+2) + m` と置く。値公式より
`a n = (p+1)(n+1) + upperTri (p+2) + m` なので、`a n − (n+1) = y` である。
`upperTri (p+2) ≥ 3` から `n + 1 < a n`(候補の正値性)が出る。もし `y` が履歴に
未出なら減算は合法になってしまい、減算不能の仮定に反する。よって `y` は既出であり、
長さ0の下降列(自明)とともに `ActualBlocker n (a n) 0 y` のすべてのフィールドが
そろう。`m ≤ y` は `y` の定義から明らかである。要点は、「加算が強制された」という
力学的事実そのものが、blockerに必要な既出性の証明を無償で与えることである。

### `add_borrowTarget_gives_coverageStep` (L108)

**主張:** 遷移後の初出時刻において、加算側チャートは `CoverageStep m (a (n+1)) (n+1)`
を与える(`m > 0` と `FirstAt a (a (n+1)) (n+1)` を仮定)。

**証明:** `LandingSurfaces.lean` の `add_borrowTarget_gives_targetEquation` で
遷移後の目標方程式を作り、`targetEquation_gives_coverageStep` に渡す。補助補題。

### `sub_borrowTarget_gives_coverageStep` (L120)

**主張:** 減算側の同型の遷移後版。

**証明:** `sub_borrowTarget_gives_targetEquation` との合成である。補助補題。

### `sub_borrowTarget_prestate_gives_coverageStep` (L134)

**主張:** 減算チャートのより強い遷移前接続。遷移後の定理と違い、減算の合法性も
時刻 `n+1` での初出仮定も要らない: `FirstAt a (a n) n` とチャートの算術仮定だけで
`CoverageStep m (a n) n`。

**証明:** `m = 0` なら `a 0 = 0` が出現枝である。`m > 0` なら
`sub_borrowTarget_prestate_targetEquation` の遷移前目標方程式を
`targetEquation_gives_coverageStep` に渡す。目標方程式は純粋に算術的な条件なので、
その後の下降が実際に実行されるかどうかは有限下降二分法が引き受ける。

### `add_borrowTarget_prestate_gives_coverageStep_high` (L150)

**主張:** 着地商が2以上の加算チャートも遷移前 `CoverageStep m (a n) n` を与える。
減算の失敗自体が要求される履歴blockerなので、ゲート型のfreshness仮定は不要である。
初出仮定さえ要らない。

**証明:** blocker定理と同じ計算で、候補 `y = p(n+1) + upperTri (p+2) + m` が
既出であることを示す(未出なら減算が合法になり矛盾)。履歴の要素は初出時刻を
持つので `y` の初出時刻 `fy` を取り、`m ≤ y`(定義から)と `y < a n`(候補は
現在値から正の数を引いた値)により降下枝
`⟨y, fy, m ≤ y, FirstAt a y fy, y < a n⟩` が直接構成できる。

### `add_borrowTarget_prestate_gives_coverageStep` (L192)

**主張:** 加算側遷移前接続の完成形。着地商 `k` で場合分けし、`k = 0, 1` は実際の
加算の後の無条件出現、`k ≥ 2` は上のblocker枝により、いずれも
`CoverageStep m (a n) n` が成り立つ。

**証明:** `k = 0` の場合、`coordinates_add_enters_borrowTarget` で遷移後が商0の
目標面に入ることを示せば、`targetSurface_zero_occurs` により `a (n+1) = m` そのもの
である。`k = 1` の場合も同様に遷移後が商1の面に入り、`targetSurface_one_occurs`
(既出なら過去に出現済み、未出なら次の減算で着地)により無条件に出現する。
`k = p + 2` の場合は前定理の降下枝である。三分岐とも出現枝または降下枝なので
`CoverageStep` が閉じる。

### `coordinates_add_target_prestate_gives_coverageStep` (L218)

**主張:** 利用者向けの加算定理。実際の強制加算遷移の借り座標が `G = m` に着地する
(`potential (q + 1 − b) s = m`)ならば、それだけで `CoverageStep m (a n) n`。

**証明:** 着地商を `k = q + 1 − b` と置けば、借りデータから `b ≤ q + 1` が出て
商条件が整い、ポテンシャル条件は `potential_eq_iff_borrowTargetPreimage` で
遷移前方程式に翻訳される。あとは前定理である。

### `coordinates_sub_target_prestate_gives_coverageStep` (L235)

**主張:** 利用者向けの減算定理。合法減算遷移の借り座標が `G = m` に着地する
(`potential (q − 1 − b) s = m`)ならば、遷移前 `CoverageStep m (a n) n` が直ちに
得られる。

**証明:** ここではチャートを経由せず、遷移そのものを使う。借り付き減算則により
遷移後座標は `(q − 1 − b, s)` で、`s = upperTri (q−1−b) + m` だから
`a (n+1) = (n+1)(q−1−b) + s ≥ m` である。合法減算は必ず新しい真に小さい値に
着地するので(`Mechanisms.lean` の `subtraction_gives_coverageStep`)、着地値
`a (n+1)` 自身が降下枝の証人になる。

### `add_highQuotient_prestate_blocker` (L254)

**主張:** 商3以上からの強制加算では、阻止された減算候補は正で、かつ現在時刻以上の
値を持つ。初出時刻においてこれは長さ0の実blockerである: `FirstAt a (a n) n`、
`CoordinatesAt n q r`、減算不能、`q ≥ 3` のもとで
`∃ y, n ≤ y ∧ ActualBlocker n (a n) 0 y`。

**証明:** 剰余条件 `r < n` から `n > 0` である。`a n = n·q + r ≥ 3n` なので、候補
`y = a n − (n+1)` は `y ≥ 3n − (n+1) = 2n − 1 ≥ n` を満たし、特に正である。
`y` が未出なら減算が合法になって矛盾するから `y` は既出であり、長さ0の下降列と
合わせて `ActualBlocker` が構成できる。目標面への着地仮定は不要で、商の大きさだけが
効いている点がこの定理の一般性である。

### `coordinates_add_oneBorrow_highQuotient_gives_coverageStep_below_time` (L299)

**主張:** 一段借り(`b = 1`)で着地商が4以上の強制加算は、現在時刻以下のすべての
目標をblocker枝で一挙に処理する: 前定理の仮定に `b = 1`、`4 ≤ q + 1 − b`、
`m ≤ n` を加えると `CoverageStep m (a n) n`。

**証明:** `b = 1` と着地商の下界から `q ≥ 4 ≥ 3` となるので、前定理のblocker
`y ≥ n` が得られる。その二重降下(`ActualBlocker.doubleDescent`)から `y < a n` と
`y` の初出時刻を取り、`m ≤ n ≤ y` により降下枝が成立する。目標 `m` はblockerの
構成に一切関与しないので、`m ≤ n` を満たす限り同じblockerがすべての目標に使える。

## 全体の中での位置づけ

証明地図の「目標面」層の出口であり、状況一覧の「目標面: 証明済み」の後半、
すなわち借り付き遷移から `CoverageStep` への接続を完結させる。上流は
`LandingSurfaces.lean`(チャート)、`Mechanisms.lean`(変換定理)、
`ActualDescent.lean`(blocker構成)である。下流では、負領域からの回復解析
(`RecoveryFrontier.lean`)が高商の強制加算を処理する際に
`add_highQuotient_prestate_blocker` 系の議論を引き継ぎ、負債局所解析の
`DebtCrossing.lean` も本モジュールの遷移前接続を利用する。「遷移前の値のまま
`CoverageStep` を返せる」ことは、探索ノードを動かさずに局所機構を適用できることを
意味し、後段の意味的探索domainの設計を単純にしている。
