# EventualHighCorridorSupply

**役割:** A枝corridorの燃料供給を追跡し、pre-cutoffの包絡を超えるforced additionの供給者がcorridor内部の着地に限られること(自給自足性)を示す。

## このモジュールの役割

`EventualHighCorridorStructure` は、corridor(あるcutoff以後すべての減算候補が
targetを厳密に超える回廊)内部のforced addition(強制加算)が履歴によってのみ
ブロックされることを示した。ブロックするには候補値がすでに軌道上に出現して
いなければならない。本モジュールはその「供給者」— 候補値を最初に軌道へ
置いた着地 — がどこに住めるかを追う。第一にvalue law: cutoffより後の全軌道値は
`target + clock + 1` を超える。第二に、corridorはforced additionを無限に再発させる。
第三に、候補がpre-cutoff hull(包絡)`upperTri cutoff` を超えるforced additionの
供給者はcorridor内部の着地に限られ、その着地自身もvalue lawに従う。第四に、
clock相対の精密化として、候補が `upperTri (max cutoff T)` を超えれば供給者は
`T` より後に押し出される。まとめると、無限のcanonical corridorは有限seedを
除いて自分自身を燃料にする閉じた系である。

## 定理と証明

### `corridor_value_law` (L26)

**主張(value law):** corridor条件「∀ m ≥ cutoff, target < a (m+1) − (m+2)」の
もとで、`cutoff < n` ならば `target + (n+1) < a n`。

**証明:** corridor条件を `m = n−1` に適用すると
`target < nextSubtractionCandidate n = a n − (n+1)`。自然数減算がここで正の値を
返す以上 `n+1 < a n` であり、移項して主張を得る。∎

系として、corridor内の全軌道値は自分の次のclockより `target + 1` 以上高い。
特に `CanSubtract` のclock条件はcorridor内で常に満たされている。

### `corridor_infinitely_many_forcedAdditions` (L41)

**主張:** corridor条件のもと、任意の `M` に対し `M ≤ n` で時刻 `n+1` の減算が
不能となる `n` が存在する。すなわちforced additionはcorridor内で無限に再発する。

**証明:** 存在しないと仮定すると、`M` 以後のすべてのステップで減算が合法である
(排中律による言い換え)。`N = M + cutoff + 2` と置くと `cutoff < N` である。
`k` に関する帰納法で

`a (N+k) + 2k ≤ a N`

を示す。実際、value lawより `target + (N+k+1) < a (N+k)` なので時刻 `N+k+1` の
減算は真の(切り捨てのない)減算であり、その減算量はclock
`N+k+1 ≥ cutoff + 2 ≥ 2` である。よって値は1ステップに2以上ずつ下がり続ける。

ここで `k = a N` と取ると `a (N + a N) + 2·(a N) ≤ a N`、左辺第1項は非負なので
`2·(a N) ≤ a N`、すなわち `a N = 0`。しかしvalue lawは
`target + (N+1) < a N`、特に `a N > 0` を保証する。矛盾。∎

直感的には、corridor内では値が高すぎて減算はいつでも許されそうに見えるが、
もし減算が永久に続けば値は毎ステップ2以上落ちて有限時間で尽きる。value lawが
値を下から支えているため、これは不可能であり、履歴によるブロック=forced
additionが必ず何度でも戻ってくる。`EventualHighCorridorStructure` の
「forced additionは永久に続かない」と対になり、corridor内では減算と強制加算が
どちらも無限回交代することが確定する。

### `corridor_forcedAddition_supplier` (L76)

**主張(供給者の窓):** corridor条件、`cutoff + 1 ≤ n`、時刻 `n+1` の減算不能、
さらに候補 `c = nextSubtractionCandidate n` がpre-cutoff包絡を超える
(`upperTri cutoff < c`)とする。このとき時刻 `t` が存在して

`cutoff < t ≤ n`、`a t = c`、`t + 1 + target < c`、`c ≤ upperTri t`。

**証明:** ブロック則 `corridor_forcedAddition_candidate_seen` より `c` は履歴に
属するので、`a t = c` となる `t ≤ n` が取れる。もし `t ≤ cutoff` なら一般則
`a t ≤ upperTri t` と三角数の単調性から `a t ≤ upperTri cutoff < c = a t` となり
矛盾。よって `cutoff < t`。すると `t` にvalue lawが適用でき
`target + (t+1) < a t = c`。最後に包絡そのものから `c = a t ≤ upperTri t`。∎

解釈: 時刻cutoff以前の値の在庫はすべて `upperTri cutoff` 以下という有限の棚に
収まる。候補がこの棚を超えた瞬間、それをブロックできる既出値はcorridor内部
(cutoffより後)の着地しかあり得ない。しかもその着地自身がcorridorのvalue lawに
従い、包絡不等式 `c ≤ upperTri t` は供給時刻 `t` を下から押し上げる
(`upperTri t ≥ c` となる程度に `t` は大きい)。corridorの燃料はcorridor自身が
生産している。

### `EventualHighCandidateTail.late_forcedAdditions_are_self_fueled` (L102)

**主張:** `EventualHighCandidateTail target tailStart`(A枝corridor)のもとで、
`tailStart ≤ cutoff` なるcutoffが存在し、cutoffより後のすべてのforced addition
について、候補が `upperTri cutoff` を超えるならその供給者はcorridor内部にある
(前定理の結論がそのまま成り立つ)。

**証明:** corridorの定義からcutoffを取り出し、各 `n` に
`corridor_forcedAddition_supplier` を適用するだけの包装である。A枝の利用者は
この一つの証明書で自給自足性を受け取れる。

### `corridor_supplier_clock_lower_bound` (L121)

**主張(供給者clock下界):** 前々定理と同じ仮定で、包絡条件を
`upperTri (max cutoff T) < c` に強めると、供給者は追加で `T < t` を満たす:

`T < t`、`cutoff < t ≤ n`、`a t = c`、`t + 1 + target < c`。

**証明:** `upperTri cutoff ≤ upperTri (max cutoff T) < c` なので
`corridor_forcedAddition_supplier` が適用でき、供給者 `t` と `c ≤ upperTri t` を
得る。もし `t ≤ max cutoff T` なら包絡の単調性より
`upperTri t ≤ upperTri (max cutoff T) < c ≤ upperTri t` となり矛盾。よって
`t > max cutoff T ≥ T`。∎

解釈: 候補が高いほど、その供給者は遅い時刻のcorridor着地でなければならない。
時間の閾値 `T` は任意なので、十分高い候補の供給者はいくらでも後方へ押し込める。
「古い在庫の使い回し」では高い候補をブロックできず、燃料の生成(generation)と
再利用(reuse)の時系列を追跡する道が開く。

## 全体の中での位置づけ

入力は `EventualHighCorridorStructure` のブロック則
`corridor_forcedAddition_candidate_seen` である。出力側では
`SharpResidualKernel.lean` のcorridor束 `SharpCorridor` の三つのfield —
`value_law`、`forced_additions`、`self_fueled` — がそれぞれ本モジュールの
`corridor_value_law`、`corridor_infinitely_many_forcedAdditions`、
`corridor_forcedAddition_supplier` で満たされ、A枝の既知構造が一つの
証明書に束ねられる。

`SeededHighCorridorNoGo` は任意有限長のseeded high corridorが構成できることを
示し、局所符号や有限履歴合法性だけではA枝を閉じられないという境界を引いた。
本モジュールの自給自足性は、有限seedのcorridor(外部から与えた履歴を燃料に
できる)と無限のcanonical corridor(いずれ自分の着地しか燃料にできない)を
分ける最初の大域的性質であり、`corridor_supplier_clock_lower_bound` による
供給時刻の押し上げとあわせて、generation-vs-reuse chronology路線の土台になる。
