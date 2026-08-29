# ReplayDoubleSubtractDescent

**役割:** replay固定点における「最小値前駆が二回連続で減算する」枝を`DoubleSubtractStep`として完全に構造化し、同時にこの枝の排除がpre-tail領域への下界なしには原理的に不可能であることを確定する（no-go）。

## このモジュールの役割

`PermanentAboveCorridorMinimumFollowUp.lean`の`minimum_predecessor_followUp`は、
仮想反例(最小未出target)のpermanent tail(以後ずっとtargetを上回り続ける区間)の
最小値`a m`の一つ下の値`a m - 1`について、その初出時刻`f`の直後の挙動を
二つに分けた。すなわち「履歴に阻まれて即座に加算する(blocked枝)」か
「二回連続で減算する(二連減算枝)」かである。blocked枝は
`ReplayWitnessDescent.lean`で別途処理され、整礎順序`EarlierSmaller`の辺を
一本供給し、副産物として分離`target + 2 < a m`を与えた。

本モジュールは残るもう一方、二連減算枝を扱う。結論を先に述べる。
**この枝は構造としては完全に記述できるが、排除はできない。しかもできない理由が
偶発的ではなく原理的である。** 証明書が軌道に下界を課すのは
`MissingStrictAboveTail.strictly_above`(tail開始以降はtargetより上)と
`TailMinimumAt.minimal`(tail開始以降は`a m`以上)の二本だけで、どちらも
tail開始以降にしか効かない。ところが二連減算枝が語る時刻`f`・`f+1`・`f+2`は
`doubleSubtract_before_tailStart` によりすべてtail開始より厳密に前にある。
pre-tail領域へ届く大域フックは恒等式`a f = a m - 1`とtargetの欠損の二本しかなく、
本モジュールの各定理はその両方をすでに使い切っている。したがって
「この枝を落とす」には、pre-tail領域に下界を持つ**新しい証明書フィールド**が要る。
現在のdischarge証明書はそれを持っていない。

代償として無条件の数値的強化が三本得られた(`f + 2 < target`、`f + 3 < a f`、
`f + 4 < a m`)。これらはclock床上げの探索範囲を直接削るという意味で有用だが、
枝の排除には寄与しない。

## 主要な定義

### `DoubleSubtractStep` (L56)

初出から二回連続で合法減算が起きる配置の証明書。三つのフィールドを持つ。

- `first : FirstAt a value time` — 時刻`time`が値`value`の初出である。
- `subtract_one : CanSubtract (time + 1) (stateAt time)` — 次の一歩の減算が合法。
- `subtract_two : CanSubtract (time + 2) (stateAt (time + 1))` — その次も合法。

`value`と`time`だけで添字付けされており、replay証明書には依存しない。
実軌道上のどこにでも適用できる汎用の配置である。

## 定理と証明

以下、`DoubleSubtractStep`の名前空間では`value`を`v`、`time`を`f`と略記する。

### `DoubleSubtractStep.first_value` (L70)

**主張:** `a (f+1) = v - (f+1)`。

**証明:** 合法減算の一歩は`a (n+1) = a n - (n+1)`を与える
(`a_succ_of_canSubtract`)。`a f = v`で書き換えるだけである。

### `DoubleSubtractStep.second_value` (L77)

**主張:** `a (f+2) = v - (f+1) - (f+2)`。

**証明:** 同じ一歩の公式を時刻`f+1`に適用し、`first_value`と合成する。

### `DoubleSubtractStep.clock_bound` (L88)

**主張:** `2f + 3 < v`。

**証明:** 減算の合法性には「引く数より値が真に大きい」という条件が含まれる。
第一歩から`f + 1 < a f = v`、第二歩から`f + 2 < a (f+1) = v - (f+1)`である。
後者を移項すれば`(f+1) + (f+2) < v`、すなわち`2f + 3 < v`。ここが重要なのは、
自然数の切り捨て減算が起きないことを保証する点で、以降の等式はすべてこの
不等式に支えられている。

### `DoubleSubtractStep.time_pos` (L99)

**主張:** `0 < f`。

**証明:** 背理法。`f = 0`なら`v = a 0 = 0`だが、`clock_bound`は`3 < v`を要求する。
矛盾。この一行が後の`doubleSubtract_values_below_predecessorGap`で決定的に効く。

### `DoubleSubtractStep.exact_drop` (L116)

**主張:** `a (f+2) + (2f + 3) = v`。

**証明:** 二歩で引かれる総量はちょうど`(f+1) + (f+2) = 2f + 3`であり、
`clock_bound`が切り捨てを排除するので、切り捨て減算の等式が厳密な加法等式に
変換できる。

**補助補題。** `value_eq` (L66) は`a f = v`(初出性の第一成分そのもの)、
`second_pos` (L109) は`0 < a (f+2)`、`strict_drop` (L124) は
`a (f+2) < a (f+1) < v`。いずれも上の等式群からの算術で、単独の内容はない。

### `DoubleSubtractStep.first_fresh` (L133) / `DoubleSubtractStep.second_fresh` (L138)

**主張:** 二つの着地値はいずれも初出である:
`FirstAt a (a (f+1)) (f+1)` および `FirstAt a (a (f+2)) (f+2)`。

**証明:** 合法減算の着地は必ず新値である(`firstAt_succ_of_canSubtract`)。
`strict_drop`と合わせると、`f`・`f+1`・`f+2`は相異なる値の相異なる初出時刻である。

### `DoubleSubtractStep.no_earlierSmaller_landings` (L145)

**主張:** どちらの着地も整礎順序の辺ではない:
`¬ EarlierSmaller ⟨a (f+1), f+1⟩ ⟨v, f⟩` かつ `¬ EarlierSmaller ⟨a (f+2), f+2⟩ ⟨v, f⟩`。

**証明:** 中身は自明である。`EarlierSmaller`は「値が小さく**かつ**時刻が早い」を
要求するが、`f+1`も`f+2`も`f`より遅いので時刻条件が破れる。証明は`omega`一行で、
`DoubleSubtractStep`の仮定すら使っていない(引数が`_h`とアンダースコア付きで
束縛されている)。

**この定理の意義は証明の難しさではなく、記録の内容にある。** blocked枝は
値も時刻も下げる辺を供給したが、二連減算枝は値だけを下げ時刻は上げる。
witness下降の向きと逆であり、同じ整礎性の議論をこの枝に流用する道は
構造的に閉ざされている、という事実を型として固定したものである。

## replay証明書への接続

以下は`TerminalExactDischargeReplayCertificate`(replay固定点、すなわち
discharge反復のrankが下がらず同じcycleを閉じる配置)の名前空間である。
`f = source.historicalFirstTime`、`m = source.historicalMinimumTime`と書く。
`source.historical_minimum.predecessor_first`により`a f = a m - 1`である。

### `minimum_predecessor_clock_below_target` (L166)

**主張:** `f + 2 < target`。

**証明:** corridorデータの連鎖である。corridorとは、replay証明書が閉じるcycleの
時刻とanchorを閉じ込める帯のことで、四つの事実がここで繋がる:
downcross(targetを上から下へ跨ぐ遷移)は初出`f`以降に起こる
(`downcross.horizon_le_time`: `f ≤ downTime`)、eligibility条件は
downcross終端が古いcrossingより前だと言う(`downTime + 1 ≤ oldCrossingTime`)、
replayの`time_eq`は`crossingTime = oldCrossingTime`、そしてcorridorの
`crossingTime_lt_target`は`crossingTime + 1 < target`。四つを繋げば
`f + 2 < target`が出る。**無条件で、kernel計算を一切使わない。**

### `minimum_predecessor_value_above_clock_sharp` (L178)

**主張:** `f + 3 < a f`。

**証明:** `a f = a m - 1`と`target < a m - 1`(証明書の`target_lt_predecessor`)を
使う。`a f = a m - 1 > target > f + 2`なので`f + 3 ≤ a f`、厳密には
`f + 3 < a f`まで出る。既存の`minimum_predecessor_value_above_clock`
(`f + 1 < a f`)を2段強化したものである。

### `tailMinimum_above_clock` (L190)

**主張:** `f + 4 < a m`。**両枝で成り立つ無条件の分離。**

**証明:** 上の`f + 3 < a f`に`a f = a m - 1`を代入するだけ。`a m ≥ 3`
(`tailMinimum_ge_three`)が自然数減算の切り捨てを防ぐ。

### `minimum_predecessor_doubleSubtract` (L202)

**主張:** 二連減算枝の仮定(二本の`CanSubtract`)の下で、最小値前駆は
本モジュールの意味での`DoubleSubtractStep (a f) f`である。

**証明:** 初出性フィールドを`a f = a m - 1`で書き換えて証明書の
`predecessor_first`をそのまま当てる。以下の定理はすべてこの橋を経由する。

### `doubleSubtract_clock_bound` (L218)

**主張:** `2f + 4 < a m`。

**証明:** `DoubleSubtractStep.clock_bound`(`2f + 3 < a f`)に`a f = a m - 1`。
`tailMinimum_above_clock`の`f + 4 < a m`より、`f`が大きいときは真に強い。

### `doubleSubtract_exact_gap` (L235)

**主張:** 厳密等式 `a (f+2) + (2f + 4) = a m`。

**証明:** `exact_drop`(`a (f+2) + (2f+3) = a f`)に`a f = a m - 1`を代入し、
切り捨てが起きないことを`clock_bound`と`a m ≥ 3`で保証する。
枝が語る三時刻の値がすべて`a m`と`f`だけで書き切れることを意味する。

### `doubleSubtract_below_tailMinimum` (L254)

**主張:** `a (f+1) < a m` かつ `a (f+2) < a m`。

**証明:** 上の等式群からの算術。二つの着地は tail 最小値より真に低い。

### `doubleSubtract_before_tailStart` (L276)

**主張:** `f + 2 < tailStart`。**枝全体がpermanent tailの開始より前で起こる。**

**証明:** 背理法。`tailStart ≤ f + 2`と仮定すると、tail最小性
`TailMinimumAt.minimal`が`a m ≤ a (f+2)`を強制する。これは
`doubleSubtract_below_tailMinimum`に反する。

**この定理が本モジュールのno-goの本体である。** tail最小性は「tail開始以降は
`a m`以上」としか言わない。二連減算の着地はそれを下回るので、着地は
tail開始前に押し出される。ところが押し出された先(pre-tail領域)には、
証明書が課す下界が一つもない。すなわちこの定理は同時に、枝を局在させる成果で
あり、局在させた先が手つかずであるという限界の宣言でもある。

### `doubleSubtract_landings_off_tail` (L292)

**主張:** tail開始以降のどの時刻`t`についても`a t ≠ a (f+1)` かつ `a t ≠ a (f+2)`。

**証明:** tail最小性から`a m ≤ a t`、着地は`a m`未満。値が異なる。

### `doubleSubtract_landings_ne_target` (L307)

**主張:** `a (f+1) ≠ target` かつ `a (f+2) ≠ target`。

**証明:** 着地は実際に軌道上に現れる値であり、targetは軌道上に現れない
(`historical_tail.target_missing`)。

**内容量について正直に書く。** この定理はreplay証明書も二本の`CanSubtract`仮定も
使っていない(いずれも`_`付きで束縛されている)。実質は「実現された任意の値は
欠損値と異なる」という一般命題の特殊化であり、二連減算枝に固有の情報はない。
下流での取り回しのために形を揃えた補題である。

### `doubleSubtract_values_below_predecessorGap` (L323)

**主張:** `0 < f` かつ
`a (f+1) + f = a m - 2` かつ `a (f+2) + (2f + 2) = a m - 2`。

**証明:** `time_pos`、`first_value`、`second_value`、`clock_bound`、
`a f = a m - 1`、`a m ≥ 3`を並べて算術で閉じる。

**これがblocked枝の分離が輸送されない理由の正確な形である。**
blocked枝が`target + 2 < a m`を得られたのは、強制加算の直後の減算候補が
ちょうど`a m - 2`になり、その値の実現witnessが手に入ったからである。
二連減算枝の二つの実現値は`a m - 2`をそれぞれ`f`と`2f + 2`だけ**下回る**。
`0 < f`なので下回り量は正であり、どちらも`a m - 2`のwitnessにはなれない。
つまり分離`target + 2 < a m`はこの枝では**成り立たない**のではなく、
**現在の材料からは導けない**。

### `tailMinimum_gap_of_attainment` (L351)

**主張:** `a m - 2`という値が軌道上のどこかで実現されているなら
(枝を問わず)、`target + 2 < a m`が従う。

**証明:** `target < a m - 1`と`a m ≥ 3`から`target + 2 ≤ a m`。もし
`target + 2 = a m`なら`a m - 2 = target`となり、実現witnessがそのまま
targetの出現witnessになって`target_missing`に矛盾する。よって
`target + 2 < a m`。

**残余義務の正確な切り出しである。** 分離の無条件化に必要なのは、枝ごとの
複雑な議論ではなく「`a m - 2`の実現witnessを枝に依らず一本取る」ことだけである。
blocked枝はそれを供給し、二連減算枝は供給しない。

### `minimum_predecessor_followUp_refined` (L367)

**主張:** 二つの順序仮定(`a f + 1 < m` と `f + 2 < m`)の下で、
follow-up二分法は各枝の収穫を付けた形に精密化できる:

- blocked枝: `BlockedFirstOccurrence (a f) f` かつ `target + 2 < a m`
- 二連減算枝: `DoubleSubtractStep (a f) f` かつ `f + 2 < tailStart` かつ
  `2f + 4 < a m` かつ `a (f+2) + (2f + 4) = a m`

**証明:** `minimum_predecessor_followUp`で場合分けし、各枝で本モジュールと
`ReplayWitnessDescent.lean`の定理を貼るだけである。

**依然として二本枝であることを明記する。** この定理は枝を減らしていない。
減らしたのは各枝の未整理さだけである。また二つの順序仮定は`minimum_predecessor_shape`
から引き継がれた未解消の側条件であり、無条件化されていない。

### `doubleSubtract_tailMinimum_above_twice_clock` (L395)

**主張:** 二連減算枝では`2f + 4 < a m`と`f + 4 < a m`が同時に成り立つ。

**証明:** 既出の二本の連言。二連減算枝では最小値がclockを二重に上回る、という
形にまとめた提示用の系である。

## 全体の中での位置づけ

証明地図(docs/PROOF_MAP.md)の「二連減算枝の構造」および「二連減算枝の排除」の
二行に対応する。上流は`ReplayWitnessDescent.lean`(blocked枝、`BlockedFirstOccurrence`、
`EarlierSmaller`降下)、および`PermanentAboveCorridorMinimumFollowUp.lean`
(二分法本体)、corridor側の`PermanentAboveCorridorReplayCorridor.lean`
(`crossingTime_lt_target`)である。

下流への提供物は二種類ある。第一に、無条件の数値的強化`f + 2 < target`・
`f + 3 < a f`・`f + 4 < a m`は、clock床上げ路線の探索範囲を削る形で
`PinnedConfigurationAttack.lean`や`LandingFloorThirtytwo.lean`の側へ効く。
第二に、`tailMinimum_gap_of_attainment`が残余義務を一点(「`a m - 2`の実現」)へ
切り出し、`PreTailBudgetSeparation.lean`がこの残余の破れる配置をさらに一つの
pinned配置へ釘付けする。

**成果の性格を最後にもう一度明示する。** 本モジュールの主結果は前進ではなく
no-goである。二連減算枝は完全に記述されたが排除されていない。しかも
「まだ排除できていない」のではなく、「現在の証明書の情報量では排除できない」
ことが構造的な理由(下界がtail開始以降にしかない／pre-tail領域への大域フックが
二本しかなくどちらも消費済み)とともに確定した。これを覆すには、pre-tail領域に
下界を持つ証明書フィールドの新設か、clock非依存に`a m - 2`の実現を取る新しい
議論のいずれかが要る。
