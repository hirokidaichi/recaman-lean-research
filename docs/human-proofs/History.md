# History

**役割:** 実装上の履歴リストと「数列としての出現・初出」を同値な述語として結び付ける。

## このモジュールの役割

`Basic` の `valuesThrough n` は状態機械が保持するリストであり、一方で大域的な議論では「ある時刻 `t ≤ n` に `a t = x` が成り立つ」「`x` の初出 (`FirstAt`: その時刻に値を取り、それより前には取らない) が時刻 `f` にある」という数列に関する述語を使いたい。本モジュールはこの二つの見方が同値であることを証明し、さらに「出現する値には必ず初出時刻がある」という最小時刻原理を構成的に与える。blocker (妨害値) の解析や履歴予算 (`missingBelowCount`: 未出の目標未満値の個数) の議論は、すべてこの橋渡しの上に成り立つ。

## 定理と証明

### `mem_valuesThrough_iff` (L12)

**主張:** `x ∈ valuesThrough n ↔ ∃ t, t ≤ n ∧ a t = x`。すなわち、格納された履歴のメンバーシップは、実際の数列で時刻 `n` 以前に出現したことと正確に一致する。

**証明:** `n` に関する帰納法。n = 0 では履歴は `[0]` のみで、`a 0 = 0` と対応する。帰納段階では `valuesThrough (n+1) = a(n+1) :: valuesThrough n` (L6 の `valuesThrough_succ`) を使う。左から右へは、先頭要素なら `t = n+1` を取り、残りの要素なら帰納法の仮定から得た時刻をそのまま使う。右から左へは、`t = n+1` なら先頭要素に、`t ≤ n` なら帰納法の仮定によりリストの残り部分に対応する。

### `seenBefore_succ_iff` (L44)

**主張:** `SeenBefore a x (n+1) ↔ x ∈ valuesThrough n`。ここで `SeenBefore seq x t` は「時刻 `t` より真に前に `x` が出現した」を表す。

**証明:** `t < n+1` と `t ≤ n` が同値であることに注意すれば、`mem_valuesThrough_iff` の言い換えにすぎない。減算可能性 `CanSubtract` の「未出現」条件を数列の言葉に翻訳するときに使う基本辞書である。

### `exists_firstAt_bounded` (L55)

**主張:** 任意の数列 `seq` について、`x` が時刻 `n` までに出現するなら、`x` の初出時刻 `f ≤ n` が存在する: `∃ f, f ≤ n ∧ FirstAt seq x f`。

**証明:** `n` に関する帰納法による最小時刻原理の構成的証明である。n = 0 では出現時刻は 0 しかなく、それより前の時刻は存在しないので自動的に初出である。帰納段階では「`x` が時刻 `n` までに出現するか」で場合分けする。出現するなら帰納法の仮定が `f ≤ n ≤ n+1` の初出を与える。出現しないなら、仮定の出現時刻は `n+1` そのものでなければならず、しかも `n+1` より前の出現はまさに今否定した事実なので、`n+1` が初出になる。

### `exists_firstAt` (L85)

**主張:** 出現する値には初出がある: `(∃ t, seq t = x)` ならば `∃ f, FirstAt seq x f`。

**証明:** 出現時刻 `t` を上界として `exists_firstAt_bounded` を適用する。

### `history_member_has_firstAt` (L94)

**主張:** `x ∈ valuesThrough n` ならば、`x` の実際の初出時刻 `f ≤ n` が存在する: `∃ f, f ≤ n ∧ FirstAt a x f`。

**証明:** `mem_valuesThrough_iff` で履歴メンバーシップを出現命題に変換し、`exists_firstAt_bounded` を適用する。

### 補助補題

`valuesThrough_succ` (L6) は `valuesThrough (n+1) = a(n+1) :: valuesThrough n` という履歴の一歩展開で、`simp` 補題として登録されている。

## 全体の中での位置づけ

証明地図のモジュール層「基礎」に属する。下降解析 (`ActualDescent`) は blocker 候補が既出であることを初出時刻付きの証明書に変換する際に `history_member_has_firstAt` を使い、履歴予算ランク (`HistoryBudget`) は `mem_valuesThrough_iff` を通じて未出値の個数を数列の言葉で数える。初出時刻を進行度として使う大域探索 (証明地図の「三成分履歴ランク」以降) の基盤である。
