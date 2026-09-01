# EventualHighCorridorRecurrence

**役割:** corridor内でcandidate walkの値 `c` が遅い時計で再訪し床を持つとき、各use clockが「合法減算で対角値に入り、forced additionで出て、後続値は既訪問」というrigid eventに強制されることを示す。有界再訪から単一再訪値を抽出するK帰納法で締める。

## このモジュールの役割

A枝corridor(あるcutoff以後すべての減算候補がtargetを厳密に超える回廊)の内部で、
candidate walk(候補の軌跡)`d m = nextSubtractionCandidate m = a m − (m+1)` を
追跡する。紙上ではA枝は「`d` の発散」∨「liminfが有限で、最小再訪候補 `c` が
限りなく遅い時計で再訪する」という二分法に縮約されており、本モジュールは後者の
recurrence側を明示仮定の下でLean化する。仮定は二つ: corridor条件と、候補の床
「∀ k ≥ M₁, c ≤ d k」(`c` が遅い候補の最小値であることの言い換え)である。
結論は、`d m = c` となる各use clock(使用時計)`m` が三点のrigidパターン —
(i) `m` からの一歩はforced addition(強制加算: 減算不能で加算が強制される
ステップ)、(ii) `m` への一歩は合法減算で対角値 `c + m + 1` にfresh着地、
(iii) 後続値 `c + m` は既訪問 — に強制されることである。最後の抽出定理が
「有界な再訪」から「単一値の非有界な再訪」を取り出し、二分法のrecurrence枝へ
仮定を接続する。

以下、`d m = a m − (m+1)`(自然数減算)と略記する。使用時計とは `d m = c` と
なる時刻 `m` のことである。

## 定理と証明

### `corridor_recurringCandidate_forcedAddition` (L34)

**主張(use clockからの一歩はforced addition):** corridor条件
「∀ k ≥ cutoff, target < d (k+1)」のもと、`cutoff ≤ m`、`d m = c`、`c ≤ m`
ならば、時刻 `m+1` の減算は不能である(`¬ CanSubtract (m+1) (stateAt m)`)。

**証明:** 減算が合法だったとして矛盾を導く。clock条件 `m+1 < a m` により減算は
切り捨てなしで `a (m+1) = a m − (m+1) = c` に着地する。corridor条件を `k = m` に
適用すると `target < d (m+1) = a (m+1) − (m+2) = c − (m+2)`。しかし `c ≤ m < m+2`
なので自然数減算は 0 を返し、`target < 0` となって不可能である。∎

直感的には、use clockから減算すると着地値は候補 `c` そのもので、時計はすでに
`c` を追い越しているから、次に露出する候補は切り捨ての 0 である。corridorの
high-candidate lawは候補が常にtargetを超えることを要求するので、この一歩は
回廊を壊す。ゆえに `c` を候補として「使う」時計は必ず加算で抜ける。

### `corridor_recurringCandidate_entry_subtraction` (L54)

**主張(use clockへの一歩は合法減算でfreshに対角着地):** corridor条件のもと、
`cutoff + 2 ≤ m`、`d m = c`、`c + 1 ≤ m` ならば、

`CanSubtract m (stateAt (m−1))` かつ `a m = c + m + 1` かつ `FirstAt a (a m) m`。

すなわち時刻 `m` へは合法減算で入り、その値は対角値 `c + m + 1`(use clockを
動かすと時刻に対し傾き1の直線上を走るのでこう呼ぶ)であり、時刻 `m` はこの値の
初出である。

**証明:** `cutoff < m` なのでvalue law(`corridor_value_law`)より
`target + (m+1) < a m`、特に `m+1 < a m`。よって `d m = c` は切り捨てのない
等式であり `a m = c + m + 1` を得る。

時刻 `m` への一歩(clock `m`、状態 `stateAt (m−1)`)で場合分けする。合法減算
ならば、一般則 `firstAt_succ_of_canSubtract`(合法減算は履歴にない値にしか
降りられないので着地は初出)からfresh性が従い、三結論がそろう。加算だったと
すると `a m = a (m−1) + m`、すなわち `a (m−1) = c + 1`。しかし `cutoff < m − 1`
なのでvalue lawは時刻 `m−1` にも適用でき `target + m < a (m−1) = c + 1 ≤ m`。
これは `target + m < m` を意味し不可能である。∎

前の値 `c + 1` は回廊の床(value lawの下界)を割ってしまうので、加算で対角値に
乗ることはできない。`c` が使用されるたびに、その直前で軌道は対角値
`c + m + 1` を新品として生産していなければならない。

### `corridor_recurringCandidate_successor_seen` (L84)

**主張(後続値の需要):** corridor条件と床「∀ k ≥ M₁, c ≤ d k」のもと、
`cutoff ≤ m`、`M₁ ≤ m + 2`、`d m = c`、`c ≤ m`、`0 < c` ならば

`c + m ∈ valuesThrough (m+1)`。

すなわち後続値 `c + m` は時刻 `m+1` までに既訪問でなければならない。

**証明:** 前々定理より時刻 `m+1` はforced additionであり
`a (m+1) = a m + (m+1)`。`0 < c` と `d m = c` から `a m = c + m + 1`
(切り捨てなし)、よって `a (m+1) = c + 2m + 2`。

`c + m` が時刻 `m+1` までに未訪問だったと仮定する。時刻 `m+2` の減算候補は
`a (m+1) − (m+2) = c + m` であり、clock条件 `m+2 < c + 2m + 2` は `0 < c + m`
から成り立ち、fresh性も仮定そのものである。よって減算は合法で
`a (m+2) = c + m`。すると次の候補は `d (m+2) = (c + m) − (m+3)` であり、これは
高々 `c − 3`(`c < 3` なら切り捨てで 0)、いずれにせよ `c` 未満である。床を
`k = m+2` に適用すると `c ≤ d (m+2)` のはずだから矛盾。∎

これが本モジュールの核心の需要である: `c` の使用のたびに、forced additionの
出力 `c + 2m + 2` が候補 `c + m` を露出し、履歴がこの値を事前に持っていなければ
軌道は一歩で `c` の床を割ってしまう。「各use clockごとに `c + m` が既訪問」
というper-use需要は、pre-corridor履歴(有限)では賄いきれない新しい
supply/demand対象である。

### `corridor_recurringCandidate_event` (L120)

**主張(束ねたrigid event):** corridor条件と床のもと、`cutoff + 2 ≤ m`、
`M₁ ≤ m + 2`、`d m = c`、`c + 1 ≤ m`、`0 < c` ならば、次の六点が同時に成り立つ:

1. `CanSubtract m (stateAt (m−1))` — 入りは合法減算、
2. `FirstAt a (a m) m` — 着地は初出、
3. `a m = c + m + 1` — 着地値は対角値、
4. `¬ CanSubtract (m+1) (stateAt m)` — 出はforced addition、
5. `a (m+1) = c + 2m + 2` — 加算出力、
6. `c + m ∈ valuesThrough (m+1)` — 後続値は既訪問。

**証明:** 前三定理の合成である。加算出力の等式5は漸化式の加算枝と等式3から
従う。使う側はこの一本で、use clock一回分のrigid eventの全payloadを受け取れる。

### `corridor_candidate_bounded_recurrence` (L145)

**主張(有界再訪からの抽出):** 固定された上界 `K` について
「∀ M, ∃ m ≥ M, d m ≤ K」ならば、単一の値 `c ≤ K` が存在して
「∀ M, ∃ m ≥ M, d m = c」。すなわちcandidate walkが限りなく遅い時計で `K` 以下に
戻るなら、ある一つの値がちょうどの候補として限りなく遅く再訪する。

**証明:** `K` に関する帰納法(鳩ノ巣論法の無限版)。`K = 0` のとき、候補が
0 以下とは 0 に等しいことだから `c = 0` でよい。`K + 1` のとき、
「ある `N` 以後 `d m = K + 1` が二度と起きない」か否かで場合分けする(排中律)。
起きないなら、任意の `M` に対し `max M N` 以後で `d m ≤ K + 1` となる時刻を
取れば `d m ≠ K + 1` でもあるので `d m ≤ K`、つまり有界再訪の上界が `K` に
下がり、帰納法の仮定が `c ≤ K` を返す。起きるなら `K + 1` 自身が限りなく遅く
再訪するので `c = K + 1` とすればよい。∎

この定理はcorridor仮定もtargetも使わない無条件の抽出補題であり、二分法の
非発散枝「`d` が有界に戻り続ける」を、rigid event群が要求する形
「単一の値 `c` がちょうどの候補として再訪し続ける」へ変換する。

## 全体の中での位置づけ

紙上分析(docs/CORRIDOR_SUPPLY_ANALYSIS_2026-09-01.md §1.2、
docs/PARALLEL_SPRINT_2026-09-01_AFTERNOON.md §6.1, §7b)はA枝を
「candidate walkの発散」∨「最小再訪候補でのrigid recurrence」へ縮約した。
本モジュールはそのrecurrence側の三点パターン(P-a, P-b, P-c)を、2026-09-01午後の
sharp-kernelスプリントRound 4でLean化したものである。入力は
`EventualHighCorridorSupply` の `corridor_value_law` と基本力学
(`a_succ_of_canSubtract`、`a_succ_of_not_canSubtract`、
`firstAt_succ_of_canSubtract`)である。

床仮定「∀ k ≥ M₁, c ≤ d k」の構成 — `corridor_candidate_bounded_recurrence` の
再訪値のうち最小のものを選び、それ未満の各値の再訪が有界であることから `M₁` を
取る段 — は本モジュールでは明示仮定のままであり、次の形式化対象である。また
発散側の残余 `a m − m → ∞` は自由事実ではない(実軌道は `a 99734 = 19` のように
低い値へ遅れて着地する)。出力側では、per-use需要「`c + m ∈ 履歴`」が
`EventualHighCorridorSupply` の供給者定理群・`EventualHighCorridorBirth` の
birth分類と同じ土俵に載る新しい需要であり、generation-vs-reuse chronology路線の
次の攻撃対象になる。姉妹モジュール `EventualHighCorridorSecondMissing` は同じ
縮約のもう一方の前提(第二欠損値)をLean化している。
