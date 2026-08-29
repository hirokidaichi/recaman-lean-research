# AnchorBoundary

**役割:** `DebtBackward`の三分法が残した等式境界 `anchor = y+1` の局所形を完全に決定し、着地値からの脱出でこの境界を意味的に閉じる。

## このモジュールの役割

合法減算枝の後方三分法(`legalSubtraction_maximalBackward_trichotomy`)は、鎖長1かつ直前値が正確にanchorに一致する等式境界 `anchor = y+1` だけを未処理で残した。本モジュールはまず、この境界の軌道形状が「`anchor` → `anchor + start` → `y`」という剛直な二歩(強制加算の直後に減算)に一意に決まることを示す。するとこの境界は、無制約な合法減算の問題ではなく、単一の強制加算の障害に還元される。その上で、着地値`y`自身を新anchorに選べば脱出できること、境界における商・剰余座標が完全に明示的であること、強制加算の理由が「非正のくさび領域 `anchor ≤ start`」と「目標未満の既消費履歴」に帰着することを証明し、くさび領域が実軌道で実現することも検証する。

## 定理と証明

### `anchorBoundary_exact_local_shape` (L11)

**主張:** `anchor = y+1` のもとで、鎖長1の境界データ(時刻`start`への強制加算、`a(start) = y + descentDrop(start,1)`)から、軌道の三点が正確に決まる:

`a(start−1) = anchor`, `a(start) = anchor + start`, `a(start+1) = y`。

**証明:** `descentDrop(start,1) = start + 1` なので `a(start) = y + start + 1`。時刻`start`の遷移は強制加算だから `a(start) = a(start−1) + start`、これを解いて `a(start−1) = y + 1 = anchor`。鎖の1回の減算は `a(start+1) = a(start) − (start+1) = y` を与える。軌道は目標圏のすぐ上 `anchor` にいて、`start`だけ跳ね上げられ、直後に`start+1`を引いて`y = anchor − 1`へ着地する — 幅1だけ下へずれた往復である。

### `anchorBoundary_exitNormal_at_landing` (L44)

**主張:** 等式境界では、着地値`y`自身が、先行値 `y+1` には供給できなかった狭義のanchor下降を供給する。すなわち `m ≤ y` と初出 `FirstAt a y fy` のもとで、通常ノード `⟨horizon, y, normal, y⟩` への `PhaseSearchProgress` が成り立つ。

**証明:** `y < y + 1 = anchor` は定義そのものであり、`phaseSearch_exitDebt_of_anchorDrop` が直ちに適用できる。つまり三分法の等式枝はランクの障害ではない — 通常ノードを初出の着地値から再開することを許しさえすればよい。

### `anchorBoundary_target_or_exitNormal` (L59)

**主張:** 等式境界の意味的閉包。目標`m`が着地値に等しければ`m`はすでに出現しており、そうでなければ(`m < y`)着地値での通常再開が狭義のanchor下降になる。

**証明:** `m ≤ y` を等号と狭義で分ける。等号なら `a(fy) = y = m` が出現の証人。狭義なら前定理の脱出がそのまま使え、しかも新anchor `y` は目標より真に大きいので通常探索の下界不変量も保たれる。

### `anchorBoundary_nonpositive_coordinates` (L79)

**主張:** 非正候補のくさび領域 `anchor ≤ start` では座標幾何が完全に明示的である。着地点は商0: `CoordinatesAt (start+1) 0 y`。中間のスパイクでは、`anchor < start` なら商1・剰余`anchor`(`CoordinatesAt start 1 anchor`)、鋭い対角 `anchor = start` 上では商2・剰余0(`CoordinatesAt start 2 0`)である。

**証明:** 局所形状の定理から `a(start+1) = y = anchor − 1 ≤ start − 1 < start + 1` なので、着地点の商・剰余は `(0, y)` である。スパイクでは `a(start) = anchor + start`。`anchor < start` なら `1·start + anchor` で剰余条件 `anchor < start` を満たし、`anchor = start` なら `2·start + 0` で剰余0となる。商が2に跳ねる対角の場合が、後続のポテンシャル解析で特別扱いを要する点である。

### `anchorBoundary_forced_reason` (L120)

**主張:** 境界の強制加算(`fy = start+1`、`start ≤ horizon`)の理由は三通りに分類され、実質的な残余は二つに縮む。

1. 減算候補が非正、すなわち `anchor ≤ start`(くさび領域)。
2. 正の候補 `x = anchor − start` が目標未満(`x < m`)で、しかもhorizon履歴にすでに含まれる — 目標未満の履歴が既に消費されている場合。
3. 候補が目標以上(`m ≤ x`)なら、その初出が `⟨horizon, x, normal, x⟩` への狭義anchor下降の通常子を与え、障害ではない。

**証明:** `start < anchor` かどうかで分ける。成り立つ場合、局所形状から `a(start−1) = anchor` なので減算候補は `x = anchor − start > 0`。減算が強制加算になった以上、`x`は時刻`start−1`までに既出でなければならず(さもなければ`CanSubtract`が成立して矛盾)、初出時刻 `fx ≤ start−1 < fy` を持つ。また `x = anchor − start < anchor`。あとは`x`と`m`の比較で第2枝と第3枝に分かれ、第2枝では履歴の単調性(`start−1 ≤ horizon`)から `x ∈ valuesThrough horizon`、第3枝では `phaseSearch_exitDebt_of_anchorDrop` がランク進捗を与える。`start < anchor` が成り立たなければ第1枝である。結局、ランク下降で処理できない配置は「非正のくさび」と「既消費の目標未満履歴」だけである。

### `anchorBoundary_nonpositive_wedge_example` (L191)

**主張:** 残余のくさび領域は空ではない。着地値 `y = 2` の境界(実軌道 `0, 1, 3, 6, 2, …`)は `anchor = start = 3` を実現する。したがって境界仮定から `anchor < start` も `start < anchor` も導けない。

**証明:** `a(2) = 3`、時刻3の遷移が強制加算(候補 `3 − 3 = 0` は既出)、時刻4で `6 − 4 = 2` へ減算する長さ1の下降列、および `a(3) = 6 = 2 + descentDrop(3,1)` を、すべて`decide`でカーネル検証する。これは鋭い対角 `anchor = start`(前定理の商2の場合)の実例でもある。

## 全体の中での位置づけ

証明地図の「負債・crossing閉包」段階の仕上げにあたる。`DebtBackward`を直接importして三分法の等式枝を引き取り、それがランクの障害ではないことを示して合法減算側を完全に閉じる。本モジュールは`PhaseSemantic`からimportされ、そこでdebt局所解析全体が意味的探索domainへ統合される。残余として明示された「非正くさび」と「既消費履歴」は、いずれも目標未満の値の履歴的既出に根差すもので、後の`HistoricalDebtBridge`や履歴予算・crossing系の解析が扱う問題圏へ引き渡される。
