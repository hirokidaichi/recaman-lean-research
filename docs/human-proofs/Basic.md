# Basic

**役割:** レカマン数列を状態機械として実行可能な形で定義し、履歴と一歩更新の基本補題を与える。

## このモジュールの役割

プロジェクト全体の出発点である。レカマン数列 `a` (a(0)=0、時刻 n+1 で「引けて未出現なら減算、さもなくば加算」) を、現在値と既出値リストを持つ状態 `State` の逐次更新として定義する。レカマン数列では「減算先が過去に出現したか」が力学を決めるため、値だけでなく履歴そのものを状態に含めるのがこの定式化の要点である。以降のすべてのモジュール (座標力学、blocker 解析、大域探索) はここで定義された `a`、`valuesThrough`、`CanSubtract` の上に構築される。

## 主要な定義

### `State` (L7)

現在値 `value : Nat` と、これまでに出現した値のリスト `seen : List Nat` の組。リストは新しい値が先頭に来る逆時系列順で、重複は許す (重複しても以降の議論に害はない)。`Repr` と決定可能な等号を備え、具体例を計算で検証できる。

### `initial` (L13)

初期状態 `⟨0, [0]⟩`。すなわち a(0) = 0 であり、値 0 はすでに履歴に含まれる。

### `CanSubtract` (L17)

時刻 `n` の状態 `state` で減算が許される条件:

```text
n < state.value  かつ  state.value − n ∉ state.seen
```

つまり減算結果が正に留まり、かつ未出現であること。この命題は決定可能であり (L20 のインスタンス)、`decide` による具体例の検証を可能にする。

### `nextValue` (L26)

一歩の数値部分。`CanSubtract n state` なら `state.value − n`、さもなくば `state.value + n`。

### `step` (L30)

一歩の状態更新。`nextValue` で新しい値を計算し、それを履歴の先頭に積む。

### `stateAt` (L35)

`n` 歩後の状態。`stateAt 0 = initial`、`stateAt (n+1) = step (n+1) (stateAt n)` という再帰で定義する。

### `a` (L40)

レカマン数列そのもの: `a n = (stateAt n).value`。

### `valuesThrough` (L43)

時刻 `n` までの履歴: `valuesThrough n = (stateAt n).seen`。a(0), …, a(n) を逆時系列順に並べたリストである。

## 定理と証明

### `recurrence` (L48)

**主張:** すべての `n` について

```text
a(n+1) = if CanSubtract (n+1) (stateAt n) then a(n) − (n+1) else a(n) + (n+1)
```

**証明:** `a`、`stateAt`、`step`、`nextValue` の定義を展開すれば両辺は定義的に等しい。レカマン数列の教科書的な再帰式が、状態機械による定義と一致することを確認する定理である。

### `old_seen_mem_step_seen` (L62)

**主張:** `x ∈ state.seen` ならば `x ∈ (step n state).seen`。

**証明:** `step` は履歴の先頭に新値を積むだけなので、既存の要素はそのまま残る。

### `current_mem_valuesThrough` (L71)

**主張:** 現在値は常に履歴に含まれる: `a n ∈ valuesThrough n`。

**証明:** n = 0 では初期状態の定義から 0 ∈ [0]。n = k+1 では `step` が新値を履歴先頭へ積むことから直ちに従う。

### `valuesThrough_persist` (L78)

**主張:** 履歴は単調である: `x ∈ valuesThrough n` ならば `x ∈ valuesThrough (n+1)`。

**証明:** `old_seen_mem_step_seen` を `stateAt n` に適用するだけである。一度出現した値が永久に「既出」であり続けることは、blocker (妨害値: 減算先が既出のため合法減算を妨げる値) 解析全体の基礎になる。

### `step_of_subtract` (L83)

**主張:** `CanSubtract n state` のとき、`step n state = ⟨state.value − n, (state.value − n) :: state.seen⟩`。

**証明:** 定義の展開。減算分岐の明示形を与える。

### `step_of_seen` (L88)

**主張:** 減算先 `state.value − n` がすでに履歴にあれば、一歩は必ず加算になる: `step n state = ⟨state.value + n, (state.value + n) :: state.seen⟩`。

**証明:** 減算先が既出なら `CanSubtract` の第二条件が破れるため、`nextValue` は加算分岐を取る。

### `step_of_nonpositive` (L96)

**主張:** `n < state.value` が成り立たなければ一歩は必ず加算になる (結論は `step_of_seen` と同形)。

**証明:** `CanSubtract` の第一条件が破れることから同様である。

### 補助補題

`stateAt_succ` (L45)、`initial_value` (L56)、`initial_seen` (L57)、`step_seen` (L59)、`step_value_mem_seen` (L67) は、いずれも定義の展開を `simp` 用に登録した書き換え補題である。また L105 の無名 `example` は、a(0)〜a(15) が標準的な初期値列 `0, 1, 3, 6, 2, 7, 13, 20, 12, 21, 11, 22, 10, 23, 9, 24` と一致することを Lean カーネルの `decide` で検証する実行可能な健全性チェックである。

## 全体の中での位置づけ

証明地図 (docs/PROOF_MAP.md) のモジュール層で最下層の「基礎」に当たる。`History` が履歴リストと初出時刻 (`FirstAt`) の橋渡しをする際に本モジュールの `valuesThrough` 補題群を使い、`CoordinateDynamics` の実軌道遷移定理は `recurrence` と `step_of_*` 系列を通じて分岐を制御する。事実上、リポジトリ内の全モジュールが本モジュールに (直接または間接に) 依存する。
