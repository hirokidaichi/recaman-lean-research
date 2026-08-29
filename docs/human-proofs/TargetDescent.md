# TargetDescent

**役割:** 目標方程式を満たす下降の試みが「目標に着地する」か「途中で具体的blockerに阻まれる」かの完全な二分法を証明する。

## このモジュールの役割

`ActualDescent.lean` は下降列とblockerの語彙を与えたが、「そもそも下降が目標 `m` を
狙える配置とは何か」を定めるのが本モジュールの目標方程式 `TargetEquation` である。
主定理 `targetDescent_dichotomy` は、目標方程式が成り立つとき、実軌道が予定どおり
`k` 歩の連続減算をすべて実行して `m` に着地するか、さもなくば予定より前に最初の
blockerが現れることを、`k` に関する帰納法で示す。着地枝は目標の出現そのもの、
阻止枝は値と初出時刻の二重降下を与えるので、この二分法が大域帰納の一歩分の中身になる。

## 主要な定義

### `TargetEquation` (L7)

`TargetEquation f v m k` は算術条件 `m + descentDrop f k = v`、すなわち
`v = m + k·f + upperTri k` を表す。時刻 `f` に値 `v` から `k` 回連続で減算できたと
すれば、その着地値がちょうど正の目標 `m` になる、という到達予定の方程式である。

### `TargetOutcome` (L11)

目標へ向けた有限下降の試みの完全な結果を表す帰納命題で、二つの構成子を持つ。

- `lands`: 長さ `k` の下降列 `DescentRun f v k` が実在し、`a (f + k) = m` と着地する。
- `blocked`: ある `length < k` と値 `y` について、具体的blocker配置
  `ActualBlocker f v length y` が存在する(下降が予定より前に阻止された)。

## 定理と証明

### `DescentRun.extend` (L20)

**主張:** 長さ `length` の下降列の直後の一歩が合法減算なら、下降列は前方に一歩
延長でき、長さ `length + 1` の下降列になる。

**証明:** 新しい列の最後の歩は仮定の減算、それ以前の歩は元の列のものをそのまま使う。
補助補題。

### `descentDrop_strict` (L33)

**主張:** `i < j` ならば `descentDrop f i < descentDrop f j`(下降量の狭義単調性)。

**証明:** 一歩分の増分は `f + i + 1 > 0` であり(`descentDrop_succ`)、残りは
単調性 `descentDrop_mono` で埋める。補助補題。

### `targetDescent_dichotomy` (L48)

**主張:** 有限目標下降の二分法。`v` の初出が時刻 `f` であり、`m > 0` かつ
`TargetEquation f v m k` が成り立つならば、`TargetOutcome f v m k` が成り立つ。
すなわち実軌道は `k` 歩すべての減算を実行して `m` に着地するか、着地前に最初の
正の既出blockerを持つ。

**証明:** `k` に関する帰納法で示す。

`k = 0` のとき、目標方程式は `m = v` を意味し(`descentDrop f 0 = 0`)、`a f = v = m`
なので長さ0の下降列とともに直ちに着地枝が成立する。

`k + 1` のとき、中間目標 `intermediate = m + (f + k + 1)` を導入する。これは
「最後の一歩を除いた `k` 歩後に通過すべき値」であり、`descentDrop_succ` より
`TargetEquation f v intermediate k` が成り立つ。帰納法の仮定をこの中間目標に適用する。

- 帰納段が阻止枝を返す場合: その blocker は `length < k < k + 1` を満たすので、
  そのまま元の主張の阻止枝になる。
- 帰納段が着地枝を返す場合: `a (f + k) = intermediate = m + (f + k + 1)` である。
  したがって次の減算候補は正で、その値は `a (f + k) − (f + k + 1) = m` である。
  ここで最後の一歩について場合分けする。
  - 減算が合法なら、下降列を `DescentRun.extend` で延長し、`a (f + k + 1) = m` と
    なって着地枝が成立する。
  - 減算が非合法なら、候補は正なのだから、非合法の理由は候補 `m` がすでに履歴に
    あることに限られる。このとき `⟨初出証明, k 歩の下降列, 候補の正値性, 候補 = m,
    m の既出性⟩` が `ActualBlocker f v k m` を構成し、`k < k + 1` とともに阻止枝が
    成立する。

この場合、blockerの値はちょうど目標 `m` 自身であることに注意する。つまり最終歩での
阻止は「`m` はすでに出現していた」ことを意味し、これも実質的には目標の解決である。

### `targetBlocker_bounds` (L116)

**主張:** 目標下降の途中で得られたblockerの値は目標と開始値の間に挟まれる:
`TargetEquation f v m k`、`length < k`、`ActualBlocker f v length y` のもとで

1. `m ≤ y` かつ `y < v`、
2. `length + 1 = k`(最終歩での阻止)ならば `y = m`、
3. `length + 1 < k`(それより早い阻止)ならば `m < y`。

**証明:** blocker方程式 `y + descentDrop f (length+1) = v` と目標方程式
`m + descentDrop f k = v` を比較する。`length + 1 ≤ k` だから下降量の単調性より
`descentDrop f (length+1) ≤ descentDrop f k`、したがって `y ≥ m`。等号の場合分けは
狭義単調性 `descentDrop_strict` で決まる: `length + 1 = k` なら下降量が一致して
`y = m`、`length + 1 < k` なら下降量が真に小さいので `y > m`。`y < v` は
`ActualBlocker.doubleDescent` の値降下である。

### `targetDescent_lands_or_doubleDescent` (L141)

**主張:** 利用者向けの帰結。`v` の初出が時刻 `f`、`m > 0`、`TargetEquation f v m k`
ならば、`a (f + k) = m`(着地)か、または `length < k`、`m ≤ y < v`、
`FirstAt a y fy`、`fy < f` を満たす `length, y, fy` が存在する(二重降下)。

**証明:** `targetDescent_dichotomy` の二分法に、阻止枝では
`ActualBlocker.doubleDescent`(値降下と初出時刻降下)と `targetBlocker_bounds`
(下界 `m ≤ y`)を合成する。

## 全体の中での位置づけ

証明地図の「下降・blocker」層の頂点であり、`ActualDescent.lean`(下降列・blocker)を
入力、`Coverage.lean`(大域値帰納)を出力とする。`Coverage.lean` の
`targetResolvable_reaches_from` と `targetResolvable_implies_coverageOracle` は
`targetDescent_lands_or_doubleDescent` を直接呼び、`Mechanisms.lean` の
`targetEquation_gives_coverageStep` は同じ定理を `CoverageStep` の形に包み直す。
また目標方程式 `TargetEquation` は、座標側の目標面 `potential q r = m` と
`Mechanisms.lean` の `targetEquation_of_quotRem_potential` で同一視され、
`LandingSurfaces.lean` 以降の借り付き解析の共通言語になる。
