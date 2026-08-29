# Oracle

**役割:** 局所的な履歴条件のもとで符号列 +−−− が強制され4歩で目標 `m` に着地する「局所脱出(local escape)」の族を、逐歩の状態計算で証明する。

## このモジュールの役割

完全ゲート(2歩の連続減算で目標に届く配置)より一段広い局所機構として、
「一度の強制加算のあと3歩の連続減算で目標に届く」+−−− 型の脱出族を定式化する。
必要な履歴条件をまとめた `EscapeAssumptions` を仮定すれば、次の4歩の符号と
中間値がすべて一意に決まり、4歩目でちょうど `m` に着地する。このモジュールの
議論は抽象的な状態 `state` に対する `step` の計算であり、実軌道の `stateAt` への
特殊化と座標(目標面)への接続は `Mechanisms.lean` が行う。モジュール名の
「Oracle」は、この族が `CoverageOracle` の義務を果たす局所機構のひとつの候補で
あることに由来する。

## 主要な定義

### `escapeBlocker` (L6)

`escapeBlocker s m = s + m + 6`。時刻 `s` での減算候補となる値であり、これが既出で
あることが最初の加算を強制する。ここでのblocker(妨害値)は、減算先がすでに履歴に
あるため減算を阻む既出値を指す。

### `escapeX1` (L7)

`escapeX1 s m = 2s + m + 5`。加算後の最初の減算(時刻 `s+1`)の着地値である。

### `escapeX2` (L8)

`escapeX2 s m = s + m + 3`。二番目の減算(時刻 `s+2`)の着地値である。
`escapeX2 − (s+3) = m` なので、ここから最後の一歩で目標に届く。

### `escapeAfterAddition` (L9)

`escapeAfterAddition s m = 3s + m + 6`。強制加算直後の値である。

### `EscapeAssumptions` (L12)

+−−− パターンを強制する局所的な履歴仮定の束である。状態 `state` について

- `m_pos : 0 < m`、`s_large : m + 9 < s`(サイズ条件)
- `value_eq : state.value = 2s + m + 6`(現在値の形)
- `blocker_seen : escapeBlocker s m ∈ state.seen`(減算候補が既出)
- `x1_fresh`, `x2_fresh`, `m_fresh`(以後の3つの着地値がすべて未出)

を仮定する。

## 定理と証明

### `localEscape_trace` (L23)

**主張:** `EscapeAssumptions s m state` のもとで、時刻 `s, s+1, s+2, s+3` の4歩は
符号 +−−− をとり、値は順に

```text
2s+m+6 → 3s+m+6 → 2s+m+5 → s+m+3 → m
```

と遷移する。すなわち `step s state` の値は `escapeAfterAddition s m`、以下順に
`escapeX1 s m`、`escapeX2 s m`、最後が `m` である。

**証明:** 各歩を減算可能性の判定つきで逐次計算する。

第1歩(時刻 `s`): 減算候補は `(2s+m+6) − s = s+m+6 = escapeBlocker s m` であり、
仮定によりこれは既出である。よってレカマンの規則は加算を選び、値は
`2s+m+6 + s = 3s+m+6` になる。履歴には新値が積まれる。

第2歩(時刻 `s+1`): 候補は `3s+m+6 − (s+1) = 2s+m+5 = escapeX1 s m`。
`s_large` より候補は正であり、履歴に対する未出性は、直前に積まれた `3s+m+6` とは
値が異なること(`s` が十分大きいため)と、元の履歴に対する `x1_fresh` から従う。
よって減算が合法で、値は `2s+m+5` になる。

第3歩(時刻 `s+2`): 候補は `2s+m+5 − (s+2) = s+m+3 = escapeX2 s m`。同様に正で、
新しく積まれた2値 `3s+m+6`, `2s+m+5` のいずれとも異なり、元の履歴には `x2_fresh` で
未出である。減算が合法で、値は `s+m+3` になる。

第4歩(時刻 `s+3`): 候補は `(s+m+3) − (s+3) = m`。`m_pos` より正で、積まれた3値の
いずれとも異なり(サイズ比較)、元の履歴には `m_fresh` で未出である。減算が合法で、
値はちょうど `m` になる。

各段の「積まれた新値と候補が異なる」比較はすべて `m + 9 < s` のもとでの一次不等式で
あり、機械的に確認できる。

### `localEscape_lands` (L124)

**主張:** 終端形。`EscapeAssumptions s m state` ならば、4歩後の状態の値は `m` である。

**証明:** `localEscape_trace` の最後の成分を取り出すだけである。

### `localEscape_coordinate_jump` (L131)

**主張:** 同じ局所族に付随する座標のジャンプ。仮定のもとで

1. 加算前: `QuotRem (s−1) state.value 2 (m+8)` かつ `potential 2 (m+8) = m+5`、
2. 加算後: `QuotRem s (3s+m+6) 3 (m+6)` かつ `potential 3 (m+6) = m`。

すなわち強制加算は、商 `q = 2` の面 `G = m+5` から商 `q = 3` の目標面 `G = m` へ
軌道を移す。

**証明:** 加算前の値 `2s+m+6` は `(s−1)·2 + (m+8)` と分解でき、`m + 9 < s` から
剰余条件 `m+8 < s−1` が出る。ポテンシャルは `G(2, m+8) = (m+8) − upperTri 2 =
(m+8) − 3 = m+5`。加算後の値 `3s+m+6 = s·3 + (m+6)` についても同様に
`m+6 < s` と `G(3, m+6) = (m+6) − upperTri 3 = (m+6) − 6 = m` を計算する。
これらは `Coordinates.lean` の `preEscape_*`, `postAddition_*` 補題の組合せである。

## 全体の中での位置づけ

`Gate.lean`(完全ゲート)と並ぶ、目標面の低商部分を直接目標の出現に変換する
局所機構の層に属する。`Mechanisms.lean` の `localEscape_at_occurs` が本モジュールの
`localEscape_lands` を実軌道 `stateAt (s−1)` に特殊化して出現証明 `∃ t, a t = m` を
作り、`localEscape_postAddition_targetEquation` が `localEscape_coordinate_jump` の
加算後座標を目標方程式に読み替える。証明地図では、`k = 3`(商3)の目標面を
freshness仮定つきで処理する具体機構として、`LandingSurfaces.lean` の
`targetSurface_three_value` と対をなす。
