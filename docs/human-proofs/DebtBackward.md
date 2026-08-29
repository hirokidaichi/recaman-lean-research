# DebtBackward

**役割:** 合法減算で生まれた初出値を極大後方減算鎖へ延長し、鎖長2以上ならblockerを露出、鎖長1なら鋭いanchor境界 `anchor = y+1` だけが残るという三分法を証明する。

## このモジュールの役割

`DebtSubtraction`は初出の一歩後方だけを見たが、本モジュールは合法減算が後方へどこまで連続するかを極大に取り、下降列(descent run: 合法減算が連続する軌道区間)の長さで場合分けする。鎖が長ければ、鎖の直前の強制加算を阻んだ既出値(blocker: 減算先がすでに履歴にあるため下降を止める妨害値)が目標以上に留まり、値の強帰納法の一段 `CoverageStep` が得られる。鎖長がちょうど1のときは、直前値が着地値`y`のちょうど`y+1`になるという剛直な形が現れ、debtからの脱出を阻み得るのは等式 `anchor = y+1` の一点だけになる。この境界が実軌道で実際に起こることも`decide`で検証する。

## 定理と証明

### `legalSubtraction_firstAt_maximalBackward` (L9)

**主張:** `y`が正の時刻`fy`に合法減算で初出したなら、`start + length = fy`、`1 ≤ length`、`0 < start` を満たす極大な後方減算鎖が存在する。すなわち `DescentRun start (a(start)) length`(時刻`start`から`length`回の連続合法減算)が成り立ち、時刻`start`への遷移自体は強制加算(`¬ CanSubtract start`)であり、鎖の開始値は

`a(start) = y + descentDrop(start, length)`, ここで `descentDrop(f, j) = j·f + U(j)`(`U`は上三角数 `U(j) = j(j+1)/2`)

を満たす。

**証明:** 最終遷移そのものが長さ1の下降列 `DescentRun (fy−1) (a(fy−1)) 1` なので、下降列の極大後方延長(`DescentRun.maximal_backward_extension`)を適用する。延長が時刻0まで届くことはない: レカマン数列の最初の一歩(時刻1)は `a(0) = 0` から減算できず合法減算ではないからである。ゆえに `0 < start` で、極大性から`start`への遷移は強制加算である。開始値の等式は、下降列の各段で `a` が `start + i` ずつ減ることを積算した下降方程式(`DescentRun.equation_at`)を端点 `a(fy) = y` で評価して得る。

### `maximalBackward_long_exposes_blocker` (L56)

**主張:** 極大鎖の長さが2以上なら、鎖直前の強制加算の減算候補 `z = a(start−1) − start` は、`m ≤ y` を満たす任意の目標`m`に対して `m ≤ z`、ある `fz < start` で初出、`z < a(start)` を満たし、`CoverageStep m (a(start)) start` を与える。

**証明:** `start = u+1` と書く。強制加算より `a(start) = a(u) + start` なので `z = a(u) − start = a(start) − 2·start` である。鍵となる不等式は開始値の下降方程式から来る:

`a(start) = y + length·start + U(length) ≥ y + 2·start + 3`(`length ≥ 2`、`U(2) = 3`)。

したがって `z = a(start) − 2·start ≥ y + 3`、特に `m ≤ y < z` かつ `z > 0`。`z`が正なのに減算が強制加算になったのだから、`z`は既出でなければならず(`not_canSubtract`の分析)、履歴所属から初出時刻 `fz ≤ u < start` を得る。また `z = a(start) − 2·start < a(start)`。よって`z`は「親値 `a(start)` より真に小さい目標以上の初出値」であり、`CoverageStep`の第二枝の証人になる。直観的には、2回分の減算幅 `2·start + 3` が、blockerを着地値`y`より確実に3以上高い位置に押し上げるのである。

### `maximalBackward_one_predecessor_boundary` (L114)

**主張:** 鎖長がちょうど1のとき、強制加算の直前値`p`は正確に `p = y + 1` であり、ある `fp < start` で初出し、`m ≤ p` を満たす。`y < anchor` のもとでは `p < anchor` または `p = anchor` である。等式の可能性はこの仮定からは除去できない。

**証明:** `descentDrop(start, 1) = start + 1` なので `a(start) = y + start + 1`。強制加算 `a(start) = a(start−1) + start` から `a(start−1) = y + 1` が正確に決まる。直前値は履歴の元なので初出時刻 `fp ≤ start−1` を持つ。`y < anchor` は `y + 1 ≤ anchor` しか意味しないので、結論は `p < anchor ∨ p = anchor` の弱い形に留まる。

### `legalSubtraction_maximalBackward_trichotomy` (L153)

**主張:** 合法減算枝の完全な後方三分法。`m ≤ y < anchor` のもとで、次のいずれかが成り立つ。

1. 鎖長2以上: 目標以上のblocker `z`(初出 `fz < fy`)と `CoverageStep m (a(start)) start`、およびdebt時刻を`fy`から`fz`へ下げる `PhaseSearchProgress`。
2. 鎖長1で `p = y+1 < anchor`: `p`を新anchorとする通常ノードへの、anchor下降による `PhaseSearchProgress` 付き脱出。
3. 残余は等式 `anchor = y + 1` のみ。

**証明:** 極大後方延長を取り、長さで二分する。長さ2以上なら`maximalBackward_long_exposes_blocker`の`z`がすべてを与える(`fz < start ≤ fy` よりdebt時刻下降)。長さ1なら`maximalBackward_one_predecessor_boundary`の`p = y+1`を使い、`p < anchor` なら `phaseSearch_exitDebt_of_anchorDrop` で脱出、`p = anchor` なら第三の等式枝である。第三枝が本物の残余である理由は、`y < anchor` が保証するのは `y+1 ≤ anchor` までで、anchor下降に必要な狭義不等式 `p < anchor` には届かないからである。

### `legalSubtraction_anchor_boundary_example` (L202)

**主張:** 等式境界は実軌道で実現する。値`2`は時刻4に合法減算 `6 − 4` で初出し、その極大鎖は時刻3から始まり(時刻3への遷移は強制加算)、強制加算の直前値は `a(2) = 3 = 2 + 1` である。

**証明:** 軌道の冒頭は `0, 1, 3, 6, 2, …` である。`FirstAt a 2 4` は、`a(4) = 2` と時刻0〜3の各値が2でないことをすべて`decide`で確認する。減算可能性・不可能性(時刻3では候補 `3 − 3 = 0` が既出)と `a(2) = 3` も`decide`によるカーネル検証である。

## 全体の中での位置づけ

証明地図の「負債・crossing閉包」段階で、`DebtStep`の分類が残す合法減算側の障害(`legal_reaches_anchor`)を実質的に解消する定理群である。`DebtSubtraction`と`DebtInvariant`をimportして構築され、唯一の残余である等式境界 `anchor = y+1` は、直接importする`AnchorBoundary`が引き継いで完全に閉じる(着地値`y`自身をanchorにすれば `y < y+1 = anchor` で脱出できる、等)。鎖長2以上の枝が返す`CoverageStep`は、大域の値帰納(`Coverage`)へ接続する出口である。
