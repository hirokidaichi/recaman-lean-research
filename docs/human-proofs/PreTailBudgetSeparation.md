# PreTailBudgetSeparation

**役割:** 履歴の被覆数 `coveredBelowCount` と鳩の巣原理だけで、replay証明書に**無条件の `target < tailStart`** を課す。ただし計数は矛盾には届かないことも同時に確定させる。

## このモジュールの役割

permanent tail(仮想的な最小未出値 `target` の周りで、ある時刻 `tailStart` 以降ずっと
`target < a t` が続く領域)の解析には構造的な欠落があった。discharge証明書
(tail内部のcycleを閉じる証明データ)が軌道に下界を課すのは `tailStart` 以降だけで、
それより前の時刻について語る枝——とりわけ `ReplayDoubleSubtractDescent` の二連減算枝——は
どうやっても落とせない。本モジュールはその pre-tail 領域に、力学ではなく**計数**で
初めて制約を入れる。`missingBelowCount`(時刻 `n` の履歴にまだ無い `k` 未満の値の個数)の
厳密な補数 `coveredBelowCount` を定義し、鳩の巣 `coveredBelowCount k n ≤ n + 1` を
replay 証明書へ適用すると、kernel 計算ゼロ・条件なしの `target < tailStart` が出る。
副産物として `target + 2 < a m` の残余(`m` は tail 最小値の時刻)を単一の pinned 配置へ
釘付けし、tail 最小値の局所解析が原理的に何を出せないかを明示する。

## 主要な定義

### `coveredBelowCount` (L37)

`coveredBelowCount k n` は「時刻 `n` までの履歴 `valuesThrough n` に既に現れている
`k` 未満の値の個数」である。`k` に関する再帰で
`coveredBelowCount 0 n = 0`、`coveredBelowCount (k+1) n = coveredBelowCount k n + (k ∈ 履歴 ? 1 : 0)`
と定める。既存の `missingBelowCount`(欠損数)と同じ形の再帰で、`if` の分岐だけが逆である。

## 定理と証明

### `coveredBelowCount_add_missingBelowCount` (L52)

**主張:** 任意の `k, n` について `coveredBelowCount k n + missingBelowCount k n = k`。

**証明:** `k` に関する帰納法。各段で `k` が履歴に入っているかで場合分けすると、
被覆側と欠損側のちょうど一方だけが 1 増える。つまり両者は `k` 未満の水準の分割である。
この等式があるので、既存の budget 議論(欠損数の下降)と本モジュールの計数は
同じ量の裏表として自由に往復できる。

### `coveredBelowCount_initial` (L66)

**主張:** `coveredBelowCount k 0 ≤ 1`。

**証明:** 時刻 0 の履歴は値 `0` ただ一つである。`k` の帰納で、`k = 0` の水準だけが
被覆に寄与し、他の水準 `k ≠ 0` は履歴に属さない。

### `coveredBelowCount_step_of_above` (L89)

**主張:** `k ≤ a (n+1)` ならば `coveredBelowCount k (n+1) ≤ coveredBelowCount k n`。
すなわち「値が `k` 以上の一歩」は `k` 未満の水準を一つも埋めない。

**証明:** `k` の帰納。水準 `k' < k ≤ a (n+1)` については `k' ≠ a (n+1)` なので、
`valuesThrough (n+1) = a (n+1) :: valuesThrough n` の先頭は無関係であり、
`k'` の所属は一歩前と同値である。よって各水準の寄与が変わらない。

### `coveredBelowCount_step_le` (L119)

**主張:** `coveredBelowCount k (n+1) ≤ coveredBelowCount k n + 1`。一歩は高々一つの水準しか埋めない。

**証明:** `k` の帰納。水準 `k'` が `a (n+1)` に等しい場合だけ 1 増え得て、それ未満の水準は
前補題により全く増えない。`k' ≠ a (n+1)` なら所属が一歩前と同値なので寄与は不変である。

### `coveredBelowCount_le_time` (L162)

**主張(鳩の巣):** `coveredBelowCount k n ≤ n + 1`。

**証明:** `n` の帰納。基底は `coveredBelowCount_initial`、帰納段は `coveredBelowCount_step_le`。
時刻 `n` までに置ける値は高々 `n+1` 個、という当たり前の事実だが、これが本モジュールの
唯一の推進力である。Mathlib の有限集合機構を使わず標準ライブラリだけの二重帰納で済んでいる。

### `coveredBelowCount_mono_level` (L172)、`coveredBelowCount_eq_of_covered` (L195)

**主張:** 前者は `k ≤ k'` ならば `coveredBelowCount k n ≤ coveredBelowCount k' n`(水準に関する単調性)。
後者は `k` 未満の値がすべて時刻 `n` までに現れていれば `coveredBelowCount k n = k`(完全被覆なら計数は厳密)。

**証明:** どちらも `k'`(あるいは `k`)に関する帰納で、各段の寄与が 0 以上/ちょうど 1 であることによる。補助補題。

### `coveredBelowCount_le_of_above` (L211)

**主張:** 時刻区間 `s < t ≤ n` の値がすべて `k` 以上ならば
`coveredBelowCount k n ≤ coveredBelowCount k s`。

**証明:** `n` の帰納で `coveredBelowCount_step_of_above` を繰り返す。「`k` を下回らない
時間帯は `k` 未満の予算を一切消費しない」という区間版である。tail の最小値より下の水準が
tail 内で埋まらないことを言うのに使う。

---

以下は replay 証明書 `TerminalExactDischargeReplayCertificate source` への適用である。
記号を固定する。`T = source.tailStart`(permanent tail の開始時刻)、
`m = source.historicalMinimumTime`(tail 最小値の時刻)、`M = a m`(tail 最小値)、
`f = source.historicalFirstTime`(最小値の一つ下の値 `M - 1` の初出時刻。`f < T` が証明書に
入っている)。証明書は `target < M - 1` と「`t ≥ T` なら `target < a t`」を持つ。

### `tailStart_pos` (L240)、`firstTime_pos` (L247)、`two_le_minimumTime` (L261)

**主張:** 順に `0 < T`、`0 < f`、`2 ≤ m`。

**証明:** `f < T` から `0 < T`。`a f = M - 1` かつ `3 ≤ M` なので `a f ≥ 2`、
一方 `a 0 = 0` だから `f ≠ 0`。`f < T ≤ m` と `0 < f` を合わせて `2 ≤ m`。補助補題だが、
後の減算・鳩の巣の議論が退化しないための下限として要る。

### `belowTarget_covered_preTail` (L271)

**主張:** `target` 未満のすべての値は時刻 `T - 1` までに現れている。

**証明:** combined 証明書の `below_covered`(target 未満の値は tail 開始時の履歴に
すべて揃っている)から、`v < target` はある時刻 `t` で現れる。
もし `t ≥ T` なら tail の性質 `target < a t` により `a t > target > v` となり矛盾。
よって `t < T`、すなわち `t ≤ T - 1`。ここが「tail は target より上」という定性的事実を
「pre-tail 区間に押し込まれる値の個数」へ翻訳する箇所である。

### `predecessor_covered_preTail` (L286)

**主張:** 最小値前駆の値 `a f = M - 1` も時刻 `T - 1` までに現れている。

**証明:** その初出時刻が `f` であり `f < T` だから。補助補題。

### `target_lt_tailStart` (L297)

**主張(本モジュールの主結果):** `target < source.tailStart`。**無条件**である。

**証明:** `target` 未満の値はすべて時刻 `T - 1` までに埋まっているので、
`coveredBelowCount_eq_of_covered` より `coveredBelowCount target (T-1) = target`。
一方 `a f = M - 1 > target` であり、この値もまた時刻 `T - 1` までに現れている。
よって水準 `a f` は `target` 以上の位置にある被覆済み水準であり、
単調性と定義の一段展開から
`coveredBelowCount (a f + 1) (T-1) = coveredBelowCount (a f) (T-1) + 1 ≥ target + 1`。
ここへ鳩の巣 `coveredBelowCount (a f + 1) (T-1) ≤ (T-1) + 1 = T` を当てると
`target + 1 ≤ T`、すなわち `target < T` を得る。

意義を正確に述べておく。従来 `tailStart` の下界はすべて `a 222 = 47` のような
**条件付きの kernel 計算**(特定の clock での軌道値を計算機で評価する)に依存していた。
本定理は計算を一切使わず、どの replay に対しても成り立つ。強さ(`target < T` の `+1` 分)を
担っているのは前駆 `a f` の一水準だけで、`target` 水準までの計数だけなら `target ≤ T` しか出ない。

### `coveredBelowCount_tailMinimum_bound` (L323)

**主張:** 任意の時刻 `n` について `coveredBelowCount M n ≤ T`。

**証明:** `n ≤ T - 1` なら鳩の巣で `≤ n + 1 ≤ T`。`n ≥ T - 1` の場合は、
`T - 1 < t ≤ n` なる時刻はすべて `t ≥ T` なので tail 最小値の最小性 `M ≤ a t` が効き、
`coveredBelowCount_le_of_above` により `T - 1` 以降は `M` 未満の水準が一つも増えない。
すなわち `M` 未満の予算は pre-tail 区間の長さで永久に頭打ちになる。

### `tailMinimum_gap_or_pinned` (L349)

**主張:** 最小値前駆に関する順序条件 `f + 1 < m` と `f + 2 < m` の下で、次のいずれかが成り立つ。

1. `target + 2 < M`(tail 最小値が target を 3 以上引き離す)、または
2. 配置が完全に釘付けされる: `M = target + 2`、`a f = target + 1`、
   `a (f+1) = target - f`、`a (f+2) = target - 2f - 2`、`2f + 2 < target`、`target < T`。

**証明:** 1 が偽と仮定する。`target < M - 1` と `3 ≤ M` から `M = target + 2`、
したがって `a f = M - 1 = target + 1` が確定する。ここで
`ReplayDoubleSubtractDescent` の精密二分法 `minimum_predecessor_followUp_refined` を適用する。
blocked 枝はその場で `target + 2 < M` を吐くので仮定に矛盾し、残るのは二連減算枝だけである。
二連減算枝は時刻 `f` の初出から二回続けて合法減算するので、
`a (f+1) = (target+1) - (f+1) = target - f`、
`a (f+2) = a (f+1) - (f+2) = target - 2f - 2` が公式から出る。二回の減算候補がともに
正であることから clock 条件 `2f + 3 < a f = target + 1`、すなわち `2f + 2 < target`。
最後の `target < T` は `target_lt_tailStart` である。

これで残余は「一つの配置」に縮む。ただし後続の `PinnedConfigurationAttack` によれば、
この pinned 配置は `f` だけで完全に決まり実軌道上で判定できるものの、`f` の候補は
`target` とともに広がり上限の兆候がない。すなわち**列挙では落ちない**。

### `tailMinimum_transition_subtracts` (L385)

**主張:** `T < m`(最小値が tail 開始より真に後で達成される)ならば、`m` への一歩は必ず減算である:
`a (m-1) = M + m` かつ `FirstAt a M m`(時刻 `m` が値 `M` の初出)。

**証明:** 背理法。`m-1 → m` が強制加算なら `a (m-1) = M - m < M` だが、
`T ≤ m - 1` なので最小性 `M ≤ a (m-1)` に矛盾する(`2 ≤ m` を使う)。よって減算であり、
合法減算の着地は常に新値なので `M` の初出は `m` である。tail 最小値が fresh であるという
情報は、後の初出降下の議論に必要な足場である。

### `tailMinimum_firstForced_cases` (L412)

**主張:** `M ≤ m + 1`(最小値が clock 以下)であるか、または値 `M - (m+1)` の出現時刻が存在する。

**証明:** 証明書の `first_forced`(時刻 `m` からの一歩が減算できない)に
`not_canSubtract_cases` を当てる。減算が失敗する原因は定義上二つしかない——
候補が非正(`M ≤ m + 1`)か、候補 `M - (m+1)` が既出か——ので、後者の場合はその履歴要素の
出現時刻を取り出せばよい。

### `tailMinimum_local_witnesses_miss_gap` (L427)

**主張(否定的結果):** `m + 1 < M` の下で、`(M - 2) + 1 = M - 1` かつ `M - (m+1) < M - 2`。

**証明:** `3 ≤ M` と `2 ≤ m` から算術で従う。

この定理の意味は「できないことの証明」である。`target + 2 < M` を無条件へ格上げするには
`M - 2` の出現 witness が一つ要る(`tailMinimum_gap_of_attainment`)。tail 最小値の
局所解析が生む witness はちょうど二つ、前駆 `M - 1` と blocked 枝の欠損 `M - (m+1)` であるが、
前者は `M - 2` の**ちょうど一つ上**、後者は `m - 1 ≥ 1` だけ**下**にあり、どちらも当たらない。
したがって `target + k < M` の一般化は `k = 2` で止まる。blocked 枝が `k = 2` を出せたのは、
強制加算の次の減算候補がちょうど `M - 2` になるという一回限りの偶然であって、機構としては伸びない。

## 計数枠組みの射程と限界

誠実に記録しておくべき負の側面がある。**計数だけでは矛盾に届かない。**
計数が生む不等式は常に「`tailStart` は十分大きい」という向きであり、
`target < T` も `coveredBelowCount M n ≤ T` も `T` の**下界**を強める形にしかならない。
一方、証明書が `T` に課す上界は `tailStart ≤ start`(そして crossing 経由の
`oldCrossingTime + 1 < parent.horizon`)だけで、`start` も `parent.horizon` も
無制限に大きく取れる。上界と下界が衝突しないので、この枠組み単独では矛盾は出ない。

「pre-tail に fresh な初出が3連発で並ぶから budget を食い尽くす」という路線も検討され、
消費が3水準にとどまり無視できる量であることが判明している。矛盾へ変えるには、
`start` または `parent.horizon` に上界を与える**別機構**が必要である。
本モジュールが提供したのは、その別機構を載せるための土台(pre-tail 領域に効く唯一の
無条件不等式)であって、閉じた議論ではない。

## 全体の中での位置づけ

証明地図(`docs/PROOF_MAP.md`)の「prefix successor coverage」層に属し、直接の上流は
`ReplayDoubleSubtractDescent`(pre-tail 制約の欠落を同定したモジュール)である。
`coveredBelowCount` はここで新規に定義された基盤であり、既存の `HistoryBudget` の
`missingBelowCount` と `coveredBelowCount_add_missingBelowCount` で結ばれている。
下流では `PinnedConfigurationAttack` が `tailMinimum_gap_or_pinned` の pinned 枝を
実軌道上で調べ、列挙では落ちないという否定的決着を与える。
主結果 `target_lt_tailStart` は、replay 固定点枝に対する数値的挟撃(corridor band、
kernel floor)のうち「下から」を担う唯一の無条件成分として、以降の攻略線に供給される。
