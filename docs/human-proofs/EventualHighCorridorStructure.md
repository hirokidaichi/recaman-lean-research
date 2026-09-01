# EventualHighCorridorStructure

**役割:** 仮想反例A枝(eventual-high candidate corridor)の構造定理群。無条件定理「forced additionは永久には続かない」を核に、corridorがfreshな高位着地を無限個強制することを示す。

## このモジュールの役割

仮想反例(missing permanent tail: 最小の未出targetが恒久的に軌道の下に取り残される状態)は
`TargetTailResidualKernel` により二分されている。A枝は eventual high-candidate corridor、
すなわち「あるcutoff以後、すべての減算候補(subtraction candidate) `a n - (n+1)` が
targetを厳密に超える回廊」であり(`EventualHighCandidateTail`、
`TargetTailResidualKernel.lean` で定義)、B枝は固定rootの右側を走るunbounded
right-terminal streamである。本モジュールはA枝の内部構造を三段階で削る。
第一に、corridor内で取られたlegal subtraction(合法減算)は `target + clock + 2` を
超えるfreshな(未出の)値に着地する。第二に、corridorとは無関係の無条件定理として、
canonical Recamán軌道はforced addition(強制加算: 減算が不能で加算が強制されるステップ)を
永久に続けることができない。第三に、両者を合成して、corridorはfreshな高位着地を
無限個強制する。最後に、corridor内部のforced additionは履歴によってのみブロックされる
(clock不足では起こらない)ことを記録する。

## 定理と証明

### `corridor_subtraction_lands_above_clock` (L26)

**主張:** corridor条件「∀ m ≥ cutoff, target < a (m+1) − (m+2)」のもとで、
`cutoff ≤ n` かつ時刻 `n+1` の減算が合法ならば、着地値について

`target + (n+2) < a (n+1)` かつ `FirstAt a (a (n+1)) (n+1)`

が成り立つ。すなわちcorridor内のlegal subtractionは、targetの上に次のclockを
載せてもまだ超えない高さの、初出値に着地する。

**証明:** corridor条件を `m = n` に適用すると `target < a (n+1) − (n+2)`。
自然数減算がここで正の値を返す以上 `n+2 < a (n+1)` であり、移項して
`target + (n+2) < a (n+1)` を得る。着地のfresh性は一般則
`firstAt_succ_of_canSubtract` そのものである: 合法減算は定義上、履歴にない値に
しか降りられないので、時刻 `n+1` はその値の初出である。

### `ray_step_value` (L38)

**主張:** 時刻 `M` 以後のすべてのステップが強制加算である(以下これをrayと呼ぶ)
とき、`∀ n ≥ M, a (n+1) = a n + (n+1)`。

**証明:** 漸化式の加算枝を読むだけである。補助補題。

### `ray_growth_linear` (L44)

**主張:** ray上では `∀ s ≥ M, ∀ d, a s + d ≤ a (s+d)`(1ステップあたり1以上の成長)。

**証明:** `d` に関する帰納法。各ステップの増分はclock `s+i+1 ≥ 1` である。補助補題。

### `ray_growth_double` (L60)

**主張:** ray上で `M ≤ s` かつ `1 ≤ s` ならば `a s + 2d ≤ a (s+d)`
(1ステップあたり2以上の成長)。

**証明:** `s ≥ 1` なら各ステップのclock `s+i+1` は2以上である。`d` の帰納法。
補助補題。この「隣接するray値は2以上離れる」という歩幅が、次の主定理で候補の
fresh性を導く鍵になる。

### `no_perpetual_forcedAddition_ray` (L80)

**主張(無条件):** どの `M` についても、「時刻 `M` 以後のすべてのステップが
強制加算」は不可能である(False)。

**証明:** そのようなrayが存在したとして矛盾を導く。`p = M + (upperTri M + M + 2)`
と置く。ここで `upperTri M = M(M+1)/2` はpre-ray hull(包絡)、すなわち一般則
`a t ≤ upperTri t`(`a_le_upperTri`)と三角数の単調性により、時刻 `M` 以前の
全軌道値を上から押さえる定数である。

(1) *ray値は包絡を追い越す。* 線形成長 `ray_growth_linear` より
`a M + (upperTri M + M + 2) ≤ a p`、特に `upperTri M + M + 2 ≤ a p`。
つまり `a p` はpre-ray履歴のどの値よりも `M + 2` 以上高い。

(2) *露出する候補は `a p − 1`。* ステップ `p+1` は加算なので
`a (p+1) = a p + (p+1)`。よって時刻 `p+2` の減算候補は
`a (p+1) − (p+2) = a p − 1` であり、clock条件 `p+2 < a (p+1)` は
`a (p+1) ≥ p + 1 + (upperTri M + M + 2) ≥ p + 3` から成り立つ。

(3) *候補 `a p − 1` はfreshである。* `a t = a p − 1` となる `t ≤ p+1` が
あったとして、`t` の位置で場合分けする。

- `t ≤ M` のとき: `a t ≤ upperTri t ≤ upperTri M < a p − 1`(ステップ(1))。矛盾。
- `M < t < p` のとき: `t ≥ 1` なので二倍成長 `ray_growth_double` を `s = t`,
  `d = p − t ≥ 1` に適用して `a t + 2(p−t) ≤ a p`、ゆえに
  `a t ≤ a p − 2 < a p − 1`。矛盾。ray値は歩幅2以上で `a p − 1` を飛び越すので、
  ray自身がこの候補を踏むことはできない。
- `t = p` のとき: `a p = a p − 1` は `a p ≥ 2` に反する。
- `t = p+1` のとき: `a (p+1) = a p + p + 1 > a p − 1`。矛盾。

(4) 以上より時刻 `p+2` の減算は合法である(clock条件とfresh性の両方が成立)。
これは `p+1 ≥ M` がray上にあり減算不能のはずだったことと矛盾する。∎

直感的には、永久のforced additionは値を爆発的に成長させるが、その成長自身が
「一つ前のray値の1下」という候補を有限履歴とまばらなray値の両方の外へ
押し出してしまい、legal subtractionが必ず解禁される。

### `exists_canSubtract_of_ray` (L125)

**主張(無条件):** 任意の `M` に対し、`M ≤ n` かつ時刻 `n+1` の減算が合法となる
`n` が存在する。すなわちcanonical軌道ではlegal subtractionが無限回起こる。

**証明:** 存在しなければ `M` 以後は永久にforced additionとなり(排中律による
言い換え)、`no_perpetual_forcedAddition_ray` に矛盾する。

### `EventualHighCandidateTail.infinitely_many_high_fresh_landings` (L138)

**主張:** `EventualHighCandidateTail target tailStart`(A枝corridor)のもとで、
任意の `M` に対し `n ≥ M` が存在して

`target + (n+2) < a (n+1)` かつ `FirstAt a (a (n+1)) (n+1)`。

つまりcorridorは、targetをclock幅で超えるfreshな着地を無限個強制する。

**証明:** corridorの定義からcutoffを取り出す。`exists_canSubtract_of_ray` を
`max M cutoff` に適用して、legal subtractionが起こる時刻 `n ≥ max M cutoff` を得る。
`cutoff ≤ n` なので着地則 `corridor_subtraction_lands_above_clock` が適用でき、
高位性とfresh性の両方が従う。

### `corridor_forcedAddition_candidate_seen` (L154)

**主張:** corridor条件のもと、`cutoff + 1 ≤ n` で時刻 `n+1` の減算が不能ならば、
その候補 `nextSubtractionCandidate n = a n − (n+1)` は履歴 `valuesThrough n` に属する。

**証明:** corridor条件を `m = n−1` に適用すると
`target < nextSubtractionCandidate n`、特に候補は正なので `n+1 < a n` であり、
`CanSubtract` のclock半分は満たされている。減算不能の理由の二分
`not_canSubtract_cases`(候補が非正、または候補が既出)のうち第一枝は排除される
ので、既出枝しか残らない。∎

系として、corridor内部のforced additionはすべて「候補値がすでに軌道上に
出現していた」という履歴的理由によるものであり、この事実が次モジュール
(`EventualHighCorridorSupply`)の供給者追跡の入口になる。

## 全体の中での位置づけ

`TargetTailResidualKernel` のA枝 `EventualHighCandidateTail` が本モジュールの入力で
ある。出力側では `SharpResidualKernel.lean` のcorridor束 `SharpCorridor` の
`fresh_landings` fieldが `infinitely_many_high_fresh_landings` で満たされ、
ブロック則 `corridor_forcedAddition_candidate_seen` は
`EventualHighCorridorSupply.lean` の供給者定理群の基礎になる。

`no_perpetual_forcedAddition_ray` と `exists_canSubtract_of_ray` はcorridor仮定に
依存しない無条件の恒久資産であり、任意の文脈で「減算は無限回起こる」として
再利用できる。A枝はこれまで `SeededHighCorridorNoGo`(任意有限長のseeded high
corridorが構成できるという no-go)により、局所論だけでは討ち取れないことが
知られていた。本モジュールは、有限seedと違って無限のcanonical corridorは
freshな高位着地を自ら生産し続けなければならないという大域的構造を与え、
generation-vs-reuse chronology路線の最初のレンガとなる。
