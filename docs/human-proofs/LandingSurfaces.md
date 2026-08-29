# LandingSurfaces

**役割:** 借り(borrow)を伴う一歩の遷移が目標面 `G = m` のどこに着地するかを、遷移前の座標だけで書ける完全な逆像チャートとして与える。

## このモジュールの役割

時刻の法が `n` から `n+1` に変わる遷移では、更新後の値を正規化された商・剰余に直す
ための算術的な「借り」が生じる(回数 `b` と補正後剰余 `s` を `BorrowData` が保持する)。
このモジュールは、「遷移後に商 `k`・ポテンシャル `G = m` の点へ着地する」という条件を、
補正後剰余 `s` を消去して遷移前の座標 `(q, r)` と借り回数 `b` だけの一次方程式
`BorrowTargetPreimage` に翻訳する。加算・減算の両側について着地商とこの方程式の同値
(逆像チャート)を証明し、実際の遷移に適用して目標方程式へ接続する。さらに目標面の
`k = 2`, `k = 3` 部分が完全ゲート・局所脱出の値形と正確に一致することを示し、
座標解析と局所機構解析を同じ面の上で結び付ける。

## 主要な定義

### `BorrowTargetPreimage` (L8)

`BorrowTargetPreimage n q r b k m` は方程式

```text
b·(n+1) + r = q + upperTri k + m
```

である。借りデータ `(b, s)` を持つ遷移が商 `k` で目標面 `G = m` に着地するための
遷移前(pre-state)方程式であり、補正後剰余 `s` を消去した形になっている。

## 定理と証明

### `potential_eq_iff_borrowTargetPreimage` (L13)

**主張:** 妥当な借りデータ `BorrowData n q r b s`(収支 `b·(n+1) + r = q + s` と
`s < n+1`)のもとで、`potential k s = m` は `BorrowTargetPreimage n q r b k m` と
同値である。

**証明:** `potential k s = m` は `s = upperTri k + m` と同値である。これを収支の式に
代入すれば `b·(n+1) + r = q + upperTri k + m` となり、逆も同じ代入で戻る。
補正後剰余 `s` が消去できることが、以後すべてのチャートの基礎になる。

### `BorrowData.targetPreimage_bound` (L23)

**主張:** 非負の目標面への着地は、三角数込みの剰余が新しい法に収まることを強制する:
`upperTri k + m < n + 1`。

**証明:** 前定理より `s = upperTri k + m` であり、借りデータの剰余条件 `s < n+1` を
そのまま読み替える。目標面上に居られる商 `k` の大きさが時刻で頭打ちになる、
という時刻下界の原型である。

### `add_borrowQuotient_eq_iff` (L34)

**主張:** 加算側の着地商の同値: `b ≤ q + 1` のもとで `q + 1 − b = k ⟺ q + 1 = b + k`。

**証明:** 切り捨て減算を通常の等式に直すだけの算術である。補助補題。

### `sub_borrowQuotient_eq_iff` (L39)

**主張:** 減算側の着地商の同値: `b + 1 ≤ q` のもとで `q − 1 − b = k ⟺ q = b + k + 1`。

**証明:** 同上の算術。補助補題。

### `add_borrowTarget_chart` (L44)

**主張:** 加算枝が `(k, G = m)` に着地するための完全な逆像チャート:
借りデータのもとで

```text
(q + 1 − b = k ∧ potential k s = m) ⟺ (q + 1 = b + k ∧ BorrowTargetPreimage n q r b k m)
```

**証明:** 左辺の第一成分は `add_borrowQuotient_eq_iff`、第二成分は
`potential_eq_iff_borrowTargetPreimage` でそれぞれ右辺の成分と同値である。
左辺は遷移後の量(着地商と補正後剰余のポテンシャル)、右辺は遷移前の量だけで
書かれている点がチャートの意味である。

### `sub_borrowTarget_chart` (L57)

**主張:** 合法減算枝の同型のチャート:

```text
(q − 1 − b = k ∧ potential k s = m) ⟺ (q = b + k + 1 ∧ BorrowTargetPreimage n q r b k m)
```

**証明:** 加算側と同様に、二つの成分ごとの同値を合成する。

### `zeroBorrow_targetPreimage_iff` (L71)

**主張:** 借り0のとき、一般の遷移前方程式は既知の通常加算面をそのまま回復する:

```text
BorrowTargetPreimage n q r 0 (q+1) m ⟺ potential q r = m + (2q + 1)
```

**証明:** `b = 0`, `k = q + 1` を代入すると方程式は `r = q + upperTri (q+1) + m` と
なり、`upperTri (q+1) = upperTri q + q + 1` を使えば
`r − upperTri q = m + (2q + 1)`、すなわち左辺のポテンシャルの式になる。
通常加算で `G` が `2q+1` 下がるという `Mechanisms.lean` の遷移則と整合する検算である。

### `add_exactGate_chart` (L78)

**主張:** 加算側チャートの完全ゲート特殊化(`k = 2`):

```text
(q + 1 − b = 2 ∧ potential 2 s = m) ⟺ (q = b + 1 ∧ b·(n+1) + r = q + m + 3)
```

**証明:** 一般チャートに `k = 2` を代入し、`upperTri 2 = 3` を展開する。補助補題。

### `add_localEscape_chart` (L87)

**主張:** 加算側チャートの局所脱出特殊化(`k = 3`): 右辺は
`q = b + 2 ∧ b·(n+1) + r = q + m + 6`。

**証明:** `k = 3`、`upperTri 3 = 6` の代入である。補助補題。

### `sub_exactGate_chart` (L96)

**主張:** 減算側の `k = 2` 特殊化: 右辺は `q = b + 3 ∧ b·(n+1) + r = q + m + 3`。

**証明:** 同様の代入である。補助補題。

### `sub_localEscape_chart` (L105)

**主張:** 減算側の `k = 3` 特殊化: 右辺は `q = b + 4 ∧ b·(n+1) + r = q + m + 6`。

**証明:** 同様の代入である。補助補題。

### `coordinates_add_enters_borrowTarget` (L114)

**主張:** チャートを満たす実際の強制加算は本当に `(k, G = m)` へ入る:
`CoordinatesAt n q r`、借りデータ、減算不能、`q + 1 = b + k`、遷移前方程式のもとで
`CoordinatesAt (n+1) k s` かつ `potential k s = m`。

**証明:** 借り回数の上界 `b ≤ q + 1` は借りデータ自身から従う。座標力学の
借り付き加算則(`coordinates_add_borrowData`)により遷移後座標は
`(q + 1 − b, s)` であり、チャートの商条件でこれが `(k, s)` に一致する。
ポテンシャル条件は `potential_eq_iff_borrowTargetPreimage` の逆向きである。

### `coordinates_sub_enters_borrowTarget` (L129)

**主張:** チャートを満たす実際の合法減算も `(k, G = m)` へ入る: 仮定は加算版の
減算不能を `CanSubtract` に、商条件を `q = b + k + 1` に替えたもの。

**証明:** 減算の合法性から値の正値性 `n + 1 < a n` が出て、そこから減算側で必要な
下界 `b + 1 ≤ q` が従う。あとは借り付き減算則(`coordinates_sub_borrowData`)と
チャートで加算側と同様に閉じる。

### `add_borrowTarget_gives_targetEquation` (L146)

**主張:** 借りターゲットチャートを通る加算は、次時刻の目標方程式
`TargetEquation (n+1) (a (n+1)) m k` を供給する。

**証明:** 前々定理で遷移後が目標面上にあることを示し、`Mechanisms.lean` の同一視
`targetEquation_of_quotRem_potential` で目標方程式に読み替える。

### `sub_borrowTarget_gives_targetEquation` (L157)

**主張:** 減算側も同様に `TargetEquation (n+1) (a (n+1)) m k` を供給する。

**証明:** 減算版の進入定理と同じ同一視の合成である。

### `targetSurface_time_bound` (L169)

**主張:** 実軌道上の目標面の点はすべて鋭い時刻下界を満たす:
`CoordinatesAt f k r` かつ `potential k r = m` ならば `upperTri k + m < f`。

**証明:** ポテンシャル条件から `r = upperTri k + m`、座標の剰余条件から `r < f`。
両者を合わせるだけである。目標面上に立てるのは十分遅い時刻に限る、という事実で、
以下の値形定理のサイズ条件の出所になる。

### `targetSurface_two_value` (L180)

**主張:** `k = 2` の目標面は単なる目標方程式ではない: そこに立つ実状態は、二歩の
完全ゲートが要求する値形を正確に持つ。`CoordinatesAt u 2 r` かつ
`potential 2 r = m` ならば `(stateAt u).value = 2u + m + 3` かつ `m + 3 < u`。

**証明:** `r = upperTri 2 + m = m + 3` を座標の等式 `a u = u·2 + r` に代入すると
値形が出る。サイズ条件は `targetSurface_time_bound` の `k = 2` の場合である。

### `targetSurface_two_occurs` (L193)

**主張:** freshness(未出性)を加えると、`k = 2, G = m` の目標面の点は完全ゲートを
経由して実際の出現になる: `m > 0`、前定理の座標仮定に加えて中間値
`gateIntermediate u m` と `m` が未出ならば `∃ t, a t = m`。

**証明:** `targetSurface_two_value` で値形 `2u + m + 3` を得て、`Mechanisms.lean` の
`exactGate_at_occurs` に渡す。二歩の連続減算がそれぞれ合法であることは未出性仮定が
保証し、`t = u + 2` で `m` に着地する。

### `targetSurface_three_value` (L205)

**主張:** `k = 3` の目標面は、+−−− 局所脱出族の加算直後の値形を正確に持つ:
`CoordinatesAt u 3 r` かつ `potential 3 r = m` ならば
`(stateAt u).value = 3u + m + 6` かつ `m + 6 < u`。ただし局所脱出に必要な追加の
履歴freshness仮定は別立てのままである。

**証明:** `r = upperTri 3 + m = m + 6` を `a u = u·3 + r` に代入する。サイズ条件は
時刻下界の `k = 3` の場合である。

## 全体の中での位置づけ

証明地図の「目標面」層に属し、状況一覧では `PrestateCoverage` とともに
「目標面: 証明済み(`G=m` と目標方程式の接続)」を担う。上流は `MultiBorrow.lean`
(借りデータと借り付き遷移則)と `Mechanisms.lean`(目標方程式との同一視、
完全ゲート)である。下流では `PrestateCoverage.lean` が本モジュールのチャートを使って
遷移前状態からの `CoverageStep` を構成し、`NegativeRegion.lean` は負領域からの
一段借り着地の解析に、`Examples.lean` は具体例の検証に本モジュールを用いる。
借り回数が実軌道では `b = 0, 1` に限られること(`OrbitBounds.lean`)と合わせると、
このチャートは実際に起こりうるすべての着地を覆う。
