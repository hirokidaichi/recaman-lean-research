# ActualDescent

**役割:** 実軌道上の連続減算区間(下降列)と、その直後に起きる具体的blockerを定義し、抽象blocker証明書への橋渡しと二重降下を証明する。

## このモジュールの役割

`Blocker.lean` の証明書は抽象数列に対する仮定の束であり、そのままではレカマン軌道に
ついて何も言わない。このモジュールは、実際のレカマン軌道 `a` 上で合法減算が連続する
区間を `DescentRun` として証明付きで定式化し、各時点の値を三角数の厳密な式で表す。
さらに、下降の直後に減算候補が既出で加算を強制される配置を `ActualBlocker` として
捉え、そこから抽象証明書 `BlockerCertificate` を実際に構成する。結果として、実軌道の
blockerが値と初出時刻の二重降下を与えることが確定し、大域帰納の再帰辺が実現される。

## 主要な定義

### `descentDrop` (L7)

`descentDrop f j = j·f + upperTri j`。時刻 `f` の直後から `j` 回連続で減算したときに
値から取り除かれる総量である。実際、引かれる数は `f+1, f+2, …, f+j` なので、その和は
`j·f + (1+2+…+j) = j·f + U(j)` になる(`U` は上三角数 `upperTri`)。

### `DescentRun` (L56)

`DescentRun f v length` は、実軌道上の連続減算区間の証明書である。

- `start_value : a f = v`(開始時刻 `f` の値が `v`)
- `subtracts : ∀ i < length, CanSubtract (f+i+1) (stateAt (f+i))`
  (区間内の各歩で減算が合法である)

### `ActualBlocker` (L127)

下降列の直後で最初に減算が阻止された配置の証明書である。

- `first_v : FirstAt a v f`(`v` は時刻 `f` が初出)
- `run : DescentRun f v length`(そこまでの下降列)
- `blocker_positive : f + length + 1 < a (f + length)`(減算候補は正)
- `blocker_candidate : a (f + length) − (f + length + 1) = y`(候補値が `y`)
- `blocker_seen : y ∈ valuesThrough (f + length)`(`y` はすでに履歴にある)

つまり「引けるのに、引き先 `y` が既出だから加算を強制される」瞬間を捉えている。

## 定理と証明

### `descentDrop_succ` (L9)

**主張:** `descentDrop f (j+1) = descentDrop f j + (f + j + 1)`。

**証明:** `(j+1)·f = j·f + f` と `U(j+1) = U(j) + j + 1` を展開すればよい。補助補題。

### `upperTri_mono` (L14)

**主張:** `i ≤ j` ならば `upperTri i ≤ upperTri j`。

**証明:** `j` に関する帰納法。各段で `U(j+1) = U(j) + j + 1 ≥ U(j)`。補助補題。

### `descentDrop_mono` (L29)

**主張:** `i ≤ j` ならば `descentDrop f i ≤ descentDrop f j`。

**証明:** 乗算部分と三角数部分がそれぞれ単調であることから従う。補助補題。

### `a_succ_of_canSubtract` (L36)

**主張:** 時刻 `n+1` で減算が合法なら `a (n+1) = a n − (n+1)`。

**証明:** レカマンの一歩 `step` の定義で減算枝を選ぶだけである。補助補題。

### `firstAt_succ_of_canSubtract` (L43)

**主張:** 合法減算の着地値は必ず新値である。すなわち `CanSubtract (n+1) (stateAt n)`
ならば `FirstAt a (a (n+1)) (n+1)`。

**証明:** 減算の合法性の定義そのものに「引き先が履歴 `valuesThrough n` に含まれない」
ことが入っている。もし `u < n+1` で `a u = a (n+1)` なら、`a (n+1)` は時刻 `n` までの
履歴に属することになり合法性に反する。よって時刻 `n+1` が初出である。

### `DescentRun.prepend` (L63)

**主張:** 下降列の直前の一歩も合法減算なら、下降列は後方に一歩延長できる:
`DescentRun f (a f) length` と `CanSubtract f (stateAt (f−1))` から
`DescentRun (f−1) (a (f−1)) (length+1)` が得られる。

**証明:** 新しい列の第0歩は仮定の減算そのもの、第 `i+1` 歩は元の列の第 `i` 歩である。
添字の付け替えだけで済む。

### `DescentRun.maximal_backward_extension` (L85)

**主張:** すべての有限下降列は、同じ終端時刻を持つ極大な後方延長を持つ。すなわち
`DescentRun f (a f) length` に対し、`start + totalLength = f + length` かつ
`length ≤ totalLength` なる `DescentRun start (a start) totalLength` が存在し、しかも
`start = 0` であるか、または時刻 `start` への直前の一歩が減算不能である。

**証明:** 開始時刻 `f` に関する強帰納法。`f = 0` なら現在の列がすでに極大である。
`f > 0` で直前の一歩が合法減算なら `prepend` で一歩延長し、開始時刻が真に減った列に
帰納法の仮定を適用する。直前が減算不能ならその事実が極大性の証人である。開始時刻は
自然数なので、この後方延長は必ず有限回で止まる。

### `DescentRun.equation_at` (L107)

**主張:** 下降列の任意の途中時点で厳密な三角数公式が成り立つ:
`i ≤ length` ならば `a (f + i) + descentDrop f i = v`。

**証明:** `i` に関する帰納法。`i = 0` は `a f = v` そのもの。帰納段では、第 `i` 歩の
合法減算から `a (f+i+1) = a (f+i) − (f+i+1)` であり、減算候補の正値性から切り捨ては
起きない。`descentDrop_succ` により取り除かれる総量がちょうど `f+i+1` だけ増えるので、
両辺の和は保存される。これで「下降 `j` 歩後の値は `v − j·f − U(j)`」という予定表が、
実軌道上で正確に実現されていることになる。

### `ActualBlocker.y_pos` (L134)

**主張:** blocker値は正である: `0 < y`。

**証明:** `blocker_positive` より減算候補 `a (f+length) − (f+length+1)` は正であり、
それが `y` に等しい。補助補題。

### `ActualBlocker.blocker_eq_drop` (L142)

**主張:** `y + descentDrop f (length + 1) = v`。すなわち抽象blocker方程式は、独立に
仮定されるのではなく、実際の連続減算から導出される。

**証明:** `equation_at` を `i = length` に適用して
`a (f+length) + descentDrop f length = v` を得る。`y` は次の一歩の候補
`a (f+length) − (f+length+1)` だから、`descentDrop_succ` と合わせて
`y + descentDrop f (length+1) = v` になる。

### `ActualBlocker.above_during_descent` (L153)

**主張:** 下降区間 `f ≤ t < f + (length+1)` の各時点で `y < a t`。

**証明:** `t = f + i`(`i ≤ length`)と書く。`equation_at` より
`a (f+i) = v − descentDrop f i` であり、`descentDrop` の単調性から区間内の値は
最終時点の値 `a (f+length)` 以上である。一方 `y` は最終値から正の数 `f+length+1` を
引いた値なので `y < a (f+length)` である。よって区間内のすべての値は `y` を真に上回る。

### `ActualBlocker.seen_before_block` (L176)

**主張:** `SeenBefore a y (f + (length+1))`。すなわち `y` は阻止が起きる時刻より前に
出現済みである。

**証明:** `blocker_seen` は `y` が時刻 `f+length` までの履歴に属することを言っており、
履歴への所属は「その時刻以前のどこかで出現した」ことと同値である。補助補題。

### `ActualBlocker.forces_addition` (L184)

**主張:** 証明されたblockerは実際に次の一歩で加算枝を強制する:
`a (f + (length+1)) = a (f+length) + (f+length+1)`。

**証明:** 減算候補が履歴に属する(`blocker_candidate` と `blocker_seen`)ので、
レカマンの更新則の「既出なら加算」の枝が発火する。定義の展開である。

### `ActualBlocker.exists_certificate` (L201)

**主張:** 橋渡しの主定理。すべての `ActualBlocker` 配置から、抽象証明書
`BlockerCertificate a` が構成でき、その成分は `v, y, f` に一致し `k = length + 1` となる。

**証明:** `y` は履歴に属するので、履歴の要素は必ず初出時刻を持つという事実
(`history_member_has_firstAt`)から初出時刻 `fy` を取る。証明書の各フィールドは
本モジュールの定理をそのまま当てはめる: blocker方程式は `blocker_eq_drop`
(`descentDrop f (length+1) = (length+1)·f + U(length+1)` と展開)、既出性は
`seen_before_block`、区間内優位は `above_during_descent`、正値性は `y_pos` である。

### `ActualBlocker.doubleDescent` (L226)

**主張:** 実軌道上の具体的な二重降下。`ActualBlocker f v length y` から
`y < v` かつ、ある `fy` で `FirstAt a y fy` かつ `fy < f`。

**証明:** `exists_certificate` で抽象証明書に持ち上げ、`Blocker.lean` の
`value_decreases` と `first_time_decreases` を適用して戻すだけである。

## 全体の中での位置づけ

証明地図の「下降・blocker」層の中核である。`descentDrop`、`DescentRun`、
`ActualBlocker` はこのモジュールで定義され、`TargetDescent.lean` の有限下降二分法
(`targetDescent_dichotomy`)が下降の失敗枝で `ActualBlocker` を返す。その二重降下
(`doubleDescent`)が `Coverage.lean` の値に関する強帰納法の降下辺になる。また
`a_succ_of_canSubtract` と `firstAt_succ_of_canSubtract` は座標力学
(`CoordinateDynamics.lean`)を含む多くの後続モジュールで使われる基礎補題であり、
`maximal_backward_extension` は対角分岐(`Diagonal.lean`)の極大後方鎖の原型である。
