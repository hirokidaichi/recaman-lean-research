# PinnedConfigurationAttack

**役割:** 分離`target + 2 < a m`が破れる唯一の配置を`PinnedTailMinimumConfiguration`として独立の型に切り出し、それが強制するものを尽くしたうえで、**この枝はkernel列挙では落ちないと否定的に決着させる**。

## このモジュールの役割

`PreTailBudgetSeparation.lean`の計数分離は、tail最小値`a m`がtargetを三つ以上
上回らない可能性をただ一つの配置に絞り込んだ。すなわち「`a m = target + 2`、
最小値前駆`a f = target + 1`、follow-upは二連減算に強制され、
`a (f+1) = target - f`・`a (f+2) = target - 2f - 2`」という配置である。
本モジュールはこの配置を周囲のdischarge証明書から切り離して独立の構造にし、
二つのことを行う。

第一に、tail最小値`a m`が真の初出であることを示す。最小値への遷移は
「減算(着地はfresh初出)」か「強制加算(そのとき`m = tailStart`)」の
**無条件二分法**であり、pinned配置では計数下界`target < tailStart`が
`a (m-1) ≤ 1`まで押し込むので後者が死ぬ。値`1`は時刻`1`以降二度と現れないからである。
これで`FirstAt a (a m) m`が取れ、最小値の先三歩まで軌道が完全に決定する。

第二に、そして**本モジュールの主結果として、この配置がclock列挙では
排除できないことを確定する。** `target = a f - 1`により配置はclock `f`だけで
完全に決まり、`elim_of_predecessor_witness`という一撃必殺の排除フックも用意できる。
にもかかわらず落ちない。clockの窓が`2f + 2 < target`かつ`target + 1 ≤ upperTri f`
であり、下端が`f ≳ √(2·target)`、上端が`f ≲ target/2`と、targetとともに
**閉じるのではなく広がる**からである。**kernel列挙は床上げ路線と同じ
無限トレッドミルであり、pinned枝は構造的議論でしか落ちない。**

## 主要な定義

### `PinnedTailMinimumConfiguration` (L45)

分離が破れる唯一の配置。targetとclockの二つの自然数だけで述べられており、
周囲のreplay証明書に依存しない。だから証明書と切り離して攻撃できる。

- `predecessor_first : FirstAt a (target + 1) clock` — 時刻`clock`が値`target+1`の初出。
- `subtract_one : CanSubtract (clock + 1) (stateAt clock)` — 直後の減算が合法。
- `subtract_two : CanSubtract (clock + 2) (stateAt (clock + 1))` — その次も合法。
- `clock_bound : 2·clock + 2 < target` — clockはtargetに比べて十分小さい。
- `target_missing : ¬ ∃ time, a time = target` — targetは軌道上に現れない。

**実軌道上で判定可能な述語である点が重要である。** 五つのフィールドはすべて
有限時刻の軌道値だけで確認できる(targetは`a clock - 1`として決まるので
`target_missing`だけが無限の主張だが、それも「有限の初出表で`a clock - 1`が
出ていない」ことで反証できる)。だからこそ列挙攻撃が原理的には可能であり、
それでも通らない、というのが本モジュールの結論になる。

## 定理と証明

### `PinnedTailMinimumConfiguration.target_eq` (L62)

**主張:** `target = a clock - 1`。

**証明:** `value_eq` (L57、`a clock = target + 1`は初出性の第一成分)から算術。

**この一行が列挙攻撃の入口である。** targetがclockから決まるので、
配置は`(target, clock)`の二次元ではなく`clock`の一次元でしか動かない。
具体的なclockを一つ選べば、対応するtargetも一意に決まる。

### `PinnedTailMinimumConfiguration.toDoubleSubtractStep` (L68)

**主張:** pinned配置は`DoubleSubtractStep (a clock) clock`である。

**証明:** 初出性フィールドを`a clock = target + 1`で書き換えて三成分を並べるだけ。
これにより`ReplayDoubleSubtractDescent.lean`の二連減算枝の結果一式が
そのまま使えるようになる。

### `PinnedTailMinimumConfiguration.first_landing` (L74) / `second_landing` (L81)

**主張:** `a (clock+1) = target - clock` かつ `a (clock+2) = target - 2·clock - 2`。

**証明:** `DoubleSubtractStep.first_value`・`second_value`に`a clock = target + 1`を
代入する。`clock_bound`が自然数減算の切り捨てを防ぐ。
配置の周囲三時刻の軌道値がtargetとclockだけで書き切れることを意味する。

### `PinnedTailMinimumConfiguration.clock_pos` (L88)

**主張:** `0 < clock`。

**証明:** `DoubleSubtractStep.time_pos`をそのまま。補助補題。

### `PinnedTailMinimumConfiguration.upperTri_bound` (L93)

**主張:** `target + 1 ≤ upperTri clock`。

**証明:** 軌道の大域上界`a n ≤ upperTri n`(`upperTri n = n(n+1)/2`)を
`clock`に適用し、`a clock = target + 1`を代入する。

### `PinnedTailMinimumConfiguration.clock_window` (L102)

**主張:** clockの動ける窓は `2·clock + 2 < target` かつ `target + 1 ≤ upperTri clock`。

**証明:** 上の二本の連言である。証明としては自明。

**この定理が本モジュールの否定的結論の数学的核心である。** 二本の不等式を
targetについて解くと、上端は`clock < (target - 2)/2 ≈ target/2`、下端は
`upperTri clock ≥ target + 1`すなわち`clock ≳ √(2·target)`となる。
窓の幅は`target/2 - √(2·target)`で、targetが大きくなるほど**広がる**。
targetを固定するごとにclockの候補は減るのではなく増えていく。列挙で全滅させる、
という戦略が成立するには窓が閉じねばならないが、この窓は開いていく一方である。

### `PinnedTailMinimumConfiguration.elim_of_predecessor_witness` (L108)

**主張:** ある時刻`witness`で`a witness + 1 = a clock`となれば、配置は矛盾する。

**証明:** `a clock = target + 1`なので`a witness = target`となり、
`target_missing`に直接矛盾する。

**理想的な排除フックである。** 具体的なclockを固定すれば、
`a clock - 1`が軌道上に一度でも現れることを有限計算で確認するだけで、
そのclockは死ぬ。それでも全体が落ちないのは、上の窓が広がり続けるためであって、
フックの弱さのためではない。

### `one_no_late_occurrence` (L117)

**主張:** `1 < time` ならば `a time ≠ 1`。すなわち値`1`は時刻`1`以降二度と現れない。

**証明:** `a 1 = 1`なので`1`は時刻`1`までの履歴に属し、単調性で時刻`time - 1`
までの履歴にも属する。一方`1 < time`より`1 < (time-1) + 1`なので、
「既出の値`v`が`v < n+1`を満たすなら`a (n+1) ≠ v`」という一般補題
(`a_succ_ne_of_seen`)が`n = time - 1`で適用できる。減算枝では引き先が
新値でなければならず、加算枝では値が増えるので、どちらの枝も`1`を再訪できない。

## 実軌道への接続

以下は`TerminalExactDischargeReplayCertificate`(replay固定点)の名前空間である。
`m = source.historicalMinimumTime`(tail最小値の時刻)、
`f = source.historicalFirstTime`(最小値前駆`a m - 1`の初出時刻)と書く。

### `five_le_minimumTime` (L138)

**主張:** `5 ≤ m`。

**証明:** 四本の下界を連鎖させる。`firstTime_pos`で`0 < f`、
`minimum_predecessor_clock_below_target`(corridor由来)で`f + 2 < target`、
計数分離の`target_lt_tailStart`で`target < tailStart`、そしてtail最小性の
`start_le_time`で`tailStart ≤ m`。合わせて`m ≥ 5`。
**kernel計算を使わない無条件の下界である。**

### `tailMinimum_transition` (L150)

**主張:** tail最小値への遷移についての**無条件二分法**。次のいずれかが成り立つ:

- 減算枝: `a (m-1) = a m + m` かつ `FirstAt a (a m) m`(最小値は初出)、または
- 強制加算枝: `m = tailStart` かつ `a (m-1) + m = a m`。

**証明:** `m ≥ 5`なので`m = k + 1`と書ける。時刻`k`から時刻`m`への一歩で
場合分けする。減算が合法なら`a m = a k - m`かつ着地はfresh
(`firstAt_succ_of_canSubtract`)、正値性から`a k = a m + m`が厳密に成り立つ。
減算が非合法なら加算が強制され`a m = a k + m`である。このとき
`tailStart < m`と仮定すると`tailStart ≤ k`なので、tail最小性が`a m ≤ a k`を
要求するが、`a m = a k + m > a k`(`m ≥ 5`)に反する。よって`m = tailStart`。

**加算枝に`m = tailStart`が付くのが効く。** 「最小値が加算で到達される」ことは
「最小値がtail区間の先頭にある」ことを強制する。これがなければ後段の絞り込みは
できない。

### `tailMinimum_firstAt_of_small_value` (L190)

**主張:** `a m ≤ m + 1` ならば加算枝は不可能で、`a (m-1) = a m + m` かつ
`FirstAt a (a m) m`。

**証明:** 二分法の加算枝を潰す。加算枝なら`a (m-1) = a m - m ≤ 1`である。
一方`m ≥ 5`なので`m - 1 ≥ 4 > 0`、よって`a (m-1) > 0`(`a_pos_of_pos_time`)。
残る可能性は`a (m-1) = 1`だが、`m - 1 > 1`なので`one_no_late_occurrence`が
これを禁じる。矛盾。

### `tailMinimum_firstAt_or_blockedWitness` (L212)

**主張:** 仮定なしで、次のいずれかが成り立つ:

- `FirstAt a (a m) m`(tail最小値は初出)、または
- `m + 1 < a m` かつ、値`a m - (m+1)`が軌道上のどこかで実現されている。

**証明:** `a m ≤ m + 1`かどうかで場合分けする。成り立てば前者。成り立たなければ
`m + 1 < a m`であり、証明書の`first_forced`(最小値の直後で減算が阻まれる)を
`not_canSubtract_cases`で分解すると、「値が小さすぎる」ケースは今の仮定に反するので、
「減算欠損`a m - (m+1)`が既出」のケースだけが残る。既出なら実現時刻が取れる。

**これが遷移解析の残す正確な残余である。** tail最小値の初出性は、この定理により
**残り一点**、`m + 1 < a m`という不等式だけに縮約された。しかもその場合には
`a m - (m+1)`の実現witnessという別の材料が手に入る。無条件化はできていないが、
穴の形は完全に特定されている。

### `pinned_tailMinimum_firstAt` (L233)

**主張:** pinned配置(`a m = target + 2`)では、`a (m-1) = a m + m` かつ
`FirstAt a (a m) m`。

**証明:** 計数下界`target < tailStart`とtail最小性`tailStart ≤ m`から
`target + 1 ≤ m`、したがって`a m = target + 2 ≤ m + 1`。あとは
`tailMinimum_firstAt_of_small_value`である。

**pinned配置では上の残り一点が閉じる。** 一般には`m + 1 < a m`の穴が残るが、
`a m`がtargetにぴったり釘付けされている配置では、pre-tail計数の下界が
その穴をちょうど塞ぐ。

### `pinned_forward_orbit` (L248)

**主張:** pinned配置では最小値の先三歩まで軌道が完全に決定する:

- `a (m+1) = target + m + 3`
- `a (m+2) = target + 2m + 5`
- `a (m+3) = target + 3m + 8`

**証明:** 第一歩と第二歩は証明書が直接持っている。`first_addition`から
`a (m+1) = a m + (m+1)`、`followup_forced`(第二歩の減算も阻まれる)から
`a (m+2) = a (m+1) + (m+2)`である。

第三歩が本題である。時刻`m+2`からの減算候補は
`a (m+2) - (m+3) = target + m + 2`だが、これはちょうど
`a (m-1)`に等しい(`pinned_tailMinimum_firstAt`の第一成分が
`a (m-1) = a m + m = target + m + 2`を与える)。`m - 1 ≤ m + 2`なので
この値は既出であり、減算は阻まれて加算が強制される。よって
`a (m+3) = a (m+2) + (m+3)`。

**第三歩の障害witnessが`a (m-1)`であるのは、pinned配置で後方一歩が
確定していたおかげである。** 前方の決定性が後方の決定性を消費している、
という構造がここで見える。

### `tailMinimum_gap_or_pinnedConfiguration` (L294)

**主張:** 二つの順序仮定(`a f + 1 < m` と `f + 2 < m`)の下で、
`target + 2 < a m` が成り立つか、さもなくば
`PinnedTailMinimumConfiguration target f` が成り立ち、かつ`a m = target + 2`。

**証明:** `target + 2 < a m`でないと仮定する。証明書の`target < a m - 1`と
`a m ≥ 3`から`target + 2 ≤ a m`なので、`a m = target + 2`が確定する。
このとき`a f = a m - 1 = target + 1`である。
`ReplayDoubleSubtractDescent.lean`の`minimum_predecessor_followUp_refined`で
二枝に分けると、blocked枝は`target + 2 < a m`を直接与えるので今の仮定に反する。
残る二連減算枝の`DoubleSubtractStep`から、初出性を`a f = target + 1`で書き換え、
二本の`CanSubtract`と`clock_bound`(`2f + 3 < a f = target + 1`)、
証明書の`target_missing`を並べれば、pinned配置の五フィールドがそろう。

**残余の完全な釘付けである。** 分離の破れ方はこの一配置に限る。

### `tailMinimum_gap_or_missing_predecessor` (L327)

**主張:** 同じ二つの順序仮定の下で、`target + 2 < a m` が成り立つか、
さもなくば `¬ ∃ time, a time + 1 = a f`、すなわち`a f - 1`は軌道上に
一度も現れない。

**証明:** 上の二分法でpinned配置が出た枝に`elim_of_predecessor_witness`を
適用するだけである。

**攻撃可能な形への最終変形である。** 右枝は具体的なclock `f`について
「`a f - 1`が軌道上に決して現れない」という、実軌道上で検証を試みられる主張になった。
そして次節で述べるとおり、その検証は完了しない。

## kernel列挙による排除は不可能である

本モジュールのdocstringは、実軌道上でpinned配置の候補clockを探索した結果を
記録している。「初出を担い、二連減算が二回とも合法で、clock boundと
現行のtarget床を満たす」clockは、**`f < 10³`で25個、`f < 10⁵`で423個、
`f < 3×10⁶`で2438個**である。密度は薄まるが累積個数は増え続け、
上限の兆候はまったくない。

**これらの数値は経験的測定であり、Leanの証明には一切使用していない。**
本モジュールで型検査されているのは、上に列挙した定理群だけである。数値は
「列挙路線に投資すべきか」という研究上の判断材料としてのみ記録されている。

**この数え方の意味を誤読しないよう、第八十六ラウンドの訂正を明記しておく。**
2438という数は`target_missing`(targetが軌道上に現れない)を**含まない**
四つの列挙可能条件だけを満たす候補の個数であって、pinned配置の
「住人」の個数ではない。実際、より細かい数値調査(`f < 60000`)では、
四条件を満たす候補310個のうち232個がtargetの**実出現**によって直ちに排除され、
残る78個も400k項の範囲でwitnessが見つからないというだけである。
つまり各候補は出現witness一つで落ちる。真の障害は
「候補が生き残ること」ではなく、**witness時刻に一様上界がないこと**である。
配置そのものの居住性は、全射性予想と同じ深さで開いたままである。

判断の結論は否定である。理由は`clock_window` (L102) が数学的に述べている
とおりで、窓`√(2·target) ≲ f ≲ target/2`はtargetとともに広がる。
targetを一つ固定して候補clockを全滅させても、より大きなtargetでは
より多くの候補が現れる。**これは床上げ路線が第七十五ラウンドで測定した
無限トレッドミルとまったく同じ構造である。** したがって
**pinned枝は構造的議論でしか落ちない**というのが本モジュールの確定した結論であり、
これ自体を(前進ではなく)成果として記録する。

## 全体の中での位置づけ

証明地図(docs/PROOF_MAP.md)の「pinned配置の列挙可能性(**kernel列挙では落ちないと確定**)」
および「tail最小値の初出(残り1点へ縮約済み)」の二行に対応する。

上流は`PreTailBudgetSeparation.lean`(無条件の`target < tailStart`、
残余配置の釘付け、`firstTime_pos`)と、`ReplayDoubleSubtractDescent.lean`
(`DoubleSubtractStep`と精密二分法、corridor由来の`f + 2 < target`)である。

下流への提供物は二つある。ひとつは`tailMinimum_firstAt_or_blockedWitness`
(L212)が残した一点の穴`m + 1 < a m`で、これは第八十四ラウンドでさらに
一枝(`m = tailStart` かつ `a (m-1) + m = a m` かつ `m + 2 ≤ a m` かつ
`target < m` かつ `a m ≠ target + m`)まで記述され、計数では閉じないことが
分かっている。もうひとつは本モジュールの否定的判定そのもので、これは
研究資源の配分(kernel列挙・射程延長への追加投資を行わない)を根拠づける。

**成果の性格を明示する。** 本モジュールはpinned枝を排除していない。
排除できたのは「kernel列挙で排除する」という**方法**のほうであり、
主結果は方法についてのno-goである。加えてtail最小値の初出性は無条件化されておらず、
無条件に得られているのは二分法(L150)と残余の形(L212)までである。
