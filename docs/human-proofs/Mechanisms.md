# Mechanisms

**役割:** 完全ゲート・局所脱出・直接下降・合法減算という各局所機構を実軌道に特殊化し、すべてを共通通貨 `CoverageStep` と目標面 `G = m` の言葉に統一する。

## このモジュールの役割

`Gate.lean`(完全ゲート)と `Oracle.lean`(+−−− 局所脱出)の結果は抽象状態に
対するものであり、`TargetDescent.lean` の下降二分法は目標方程式を仮定する。
このモジュールは三者を実軌道 `a` の上で接続する変換層である。中心となるのは
「目標面 `potential q r = m` への所属は、`q` 歩の減算予定がちょうど `m` に届く
目標方程式と同じものである」という同一視(`targetEquation_of_quotRem_potential`)
であり、これにより座標側の解析と下降側の解析が同じ `CoverageStep` を生成できる。
さらに商 `q ≤ 1` の目標面は無条件に、`q = 2` は完全ゲートとして、`q = 3` は
局所脱出として目標の出現に落ちることを示す。

## 定理と証明

### `exactGate_at_occurs` (L10)

**主張:** 完全ゲート(2歩の連続減算で目標に正確に着地できる局所配置)の実軌道版。
`m > 0`、時刻 `u` の値が `2u + m + 3`、中間値 `gateIntermediate u m = u + m + 2` と
`m` がともに未出ならば、`∃ t, a t = m`。

**証明:** `Gate.lean` の `exactGate_sufficient` を状態 `stateAt u` に適用すると、
2歩後の状態の値が `m` になる。`stateAt (u+2) = step (u+2) (step (u+1) (stateAt u))`
という展開により、その2歩後の状態はまさに `stateAt (u+2)` なので、`t = u + 2` が
出現の証人である。

### `localEscape_at_occurs` (L29)

**主張:** +−−− 局所脱出族の実軌道版。`EscapeAssumptions s m (stateAt (s−1))` ならば
`∃ t, a t = m`。

**証明:** `Oracle.lean` の `localEscape_lands` により、`stateAt (s−1)` から4歩進んだ
状態の値は `m` である。`s = 0` はサイズ条件 `m + 9 < s` に反するので除外され、
`s = u + 1` と書けば4歩後の状態は `stateAt (u + 4)`、すなわち `t = s + 3` が証人である。

### `targetEquation_gives_coverageStep` (L43)

**主張:** 妥当な直接目標方程式は一段の `CoverageStep` を供給する。`m > 0`、
`FirstAt a v f`、`TargetEquation f v m k` ならば `CoverageStep m v f`。

**証明:** 有限下降二分法 `targetDescent_lands_or_doubleDescent` を適用する。
着地枝 `a (f+k) = m` は出現枝、阻止枝の `m ≤ y < v` なる初出値 `y` は降下枝に
そのまま対応する。

### `subtraction_gives_coverageStep` (L56)

**主張:** すべての合法減算は新しい真に小さい値に着地する。したがって着地値が
目標以上に留まるなら、その遷移自体が `CoverageStep m (a n) n` であり、blockerは
不要である。

**証明:** `firstAt_succ_of_canSubtract` により `a (n+1)` は時刻 `n+1` が初出、
`a_succ_of_canSubtract` により `a (n+1) = a n − (n+1) < a n` である。仮定
`m ≤ a (n+1)` と合わせて降下枝の証人 `y = a (n+1)` が得られる。

### `occurrence_gives_coverageStep` (L68)

**主張:** どちらの局所着地機構であれ、出現証明 `∃ t, a t = m` はどんな探索ノード
`(v, f)` に対しても直ちに `CoverageStep m v f` である。

**証明:** `CoverageStep` の出現枝そのものである。補助補題。

### `targetEquation_of_quotRem_potential` (L74)

**主張:** 等位面 `G = m` は目標方程式にほかならない: `QuotRem f v q r`(すなわち
`v = f·q + r`, `r < f`)かつ `potential q r = m` ならば `TargetEquation f v m q`、
すなわち時刻 `f` の値 `v` からの `q` 歩の減算予定の終点が `m` である。

**証明:** `potential q r = m` は `r = upperTri q + m` と同値である。これを
`v = f·q + r` に代入すると `v = q·f + upperTri q + m = m + descentDrop f q` となり、
これが目標方程式の定義である。座標のポテンシャルと下降算術を結ぶ、本モジュールの
要の同一視である。

### `targetSurface_gives_coverageStep` (L87)

**主張:** 初出時刻において目標面 `G = m` に属することは、直ちに `CoverageStep` の
下降枝を供給する: `m > 0`、`FirstAt a v f`、`CoordinatesAt f q r`、
`potential q r = m` ならば `CoverageStep m v f`。

**証明:** `CoordinatesAt f q r` は `QuotRem f (a f) q r` であり、初出の等式
`a f = v` で書き換えれば前定理から目標方程式を得る。あとは
`targetEquation_gives_coverageStep` に渡す。

### `targetSurface_zero_occurs` (L98)

**主張:** 商0の目標面所属は出現そのものである: `CoordinatesAt u 0 r` かつ
`potential 0 r = m` ならば `∃ t, a t = m`。

**証明:** `potential 0 r = r − upperTri 0 = r` なので `r = m`、また
`a u = u·0 + r = m` である。`t = u` が証人。

### `targetSurface_one_occurs` (L112)

**主張:** 商1はfreshness仮定を必要としない: `CoordinatesAt u 1 r` かつ
`potential 1 r = m` ならば `∃ t, a t = m`。

**証明:** `r = m + 1` であり `a u = u + m + 1` である。`m = 0` なら `a 0 = 0` が証人。
`m > 0` のときは `m` の既出性で場合分けする。

- `m` が履歴 `valuesThrough u` に既出なら、履歴の意味からある時刻 `t ≤ u` で
  `a t = m` であり、それが証人である。
- `m` が未出なら、時刻 `u + 1` の減算候補は `a u − (u+1) = m` であり、`m > 0` より
  正、未出性より合法である。よって減算が実行され `a (u+1) = m` となる。

「既出なら過去に出現済み、未出なら次の一歩で着地」という両にらみの議論であり、
どちらの枝でも追加仮定なしに目標が出現する。

### `targetSurface_lowQuotient_occurs` (L147)

**主張:** したがって商が高々1の目標面の点は、無条件に目標を解決する。

**証明:** `q = 0` と `q = 1` の場合分けで前二定理を適用する。補助補題。

### `exactGate_targetSurface` (L159)

**主張:** 完全ゲートの値 `2u + m + 3` は、まさに目標面 `G = m` の `q = 2` 部分である:
`m + 3 < u` のもとで `QuotRem u (2u+m+3) 2 (m+3)` かつ `potential 2 (m+3) = m`。

**証明:** `2u + m + 3 = u·2 + (m+3)` の分解と剰余条件 `m + 3 < u`、および
`G(2, m+3) = (m+3) − 3 = m` の計算である。補助補題。

### `exactGate_targetEquation` (L166)

**主張:** 同じ配置は目標方程式 `TargetEquation u (2u+m+3) m 2` を満たす。

**証明:** 前補題を `targetEquation_of_quotRem_potential` に通すだけである。補助補題。

### `localEscape_postAddition_targetEquation` (L173)

**主張:** +−−− 族の加算直後の状態は `q = 3` の目標面上にあり、残る3歩の減算は
正確に目標下降である: `m + 9 < s` のもとで
`TargetEquation s (escapeAfterAddition s m) m 3`。

**証明:** `Coordinates.lean` の `postAddition_quotRem`(`3s+m+6 = s·3 + (m+6)`)と
`postAddition_potential`(`G(3, m+6) = m`)を要の同一視に通す。

### `regularAddition_enters_targetSurface` (L180)

**主張:** 面 `G = m + (2q+1)` からの強制通常加算は目標面 `G = m` に入る:
`CoordinatesAt n q r`、通常領域条件 `q ≤ r`、減算不能、
`potential q r = m + (2q+1)` ならば、`CoordinatesAt (n+1) (q+1) (r−q)` かつ
`potential (q+1) (r−q) = m`。

**証明:** 座標力学の通常加算則(`coordinates_add_regular`)により、加算後の座標は
`(q+1, r−q)` でありポテンシャルはちょうど `2q+1` だけ低下する。仮定の値
`m + (2q+1)` から `2q+1` を引けば `m` である。強制加算が一段でポテンシャルを
目標へ近づける、というポテンシャル解析の基本遷移である。

## 全体の中での位置づけ

証明地図の「目標面」層(`Gate`, `Mechanisms`, `LandingSurfaces`, `PrestateCoverage`)の
中心にあり、状況一覧の「目標面: 証明済み」の一角を占める。上流は `Coverage.lean`
(`CoverageStep` の定義)、`Gate.lean`、`Oracle.lean`、`TargetDescent.lean` であり、
下流では `LandingSurfaces.lean` が本モジュールの `targetEquation_of_quotRem_potential`
と `targetSurface_*` 群を借り付き遷移へ一般化し、`DebtSubtraction.lean` などの
負債局所解析も `subtraction_gives_coverageStep` 型の変換を再利用する。低商
(`q ≤ 1` 無条件、`q = 2` ゲート、`q = 3` 脱出)の分類は、canonical閉包
(`CanonicalLevelZero/One/Two`)におけるレベル分けの原型でもある。
