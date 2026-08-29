# ReplayWitnessDescent

**役割:** blocked配置からclock列挙なしに`(値, 初出)`のearlier-smaller辺が取れることを示し、それでも整礎性が発火しないというno-go(できないことの確定)を主成果として記録する。

## このモジュールの役割

replay枝(過去のdischargeサイクルを再生する終端固定点)の床上げは、clockを一つずつ潰す有限反復であり、原理的には無限トレッドミルである。それを卒業する候補として検討されたのが、clockに一切言及しない一般排除、すなわち「配置そのものが整礎順序に沿って無限下降するので存在し得ない」型の議論だった。本モジュールはその候補経路を最後まで実装して検証し、**否定的に決着させたものである。判定: この経路は床上げの卒業には効かない。**

出発点はwitness付き二分法である。replay証明書のtail最小値の直前(minimum predecessor、時刻 `f`)では、その次の一歩が「合法減算」か「履歴による阻止(blocked)」かに分かれる。blocked枝では減算欠損 `a(f) - (f+1)` が既に履歴に格納されているので、その値は真に小さく、初出も真に早い。つまり `(値, 初出)` の対を頂点とする整礎順序 `EarlierSmaller` の辺が、clockの列挙を一切使わずに手に入る。尺度 `値 - 時刻` も真に減る。

**しかし整礎性は発火しない。** blocked配置の三条件のうちwitnessへ輸送されるのは初出性のみで、`clock < 値`とblocked性が落ちるからである。連鎖の停止点(欠損の値が自分の時刻以下、あるいはそこで合法減算ができる)は実軌道に無数に存在し、tail側から輸送される情報(witnessがtail最小値未満・その初出がtail開始前)はそれらと何も矛盾しない。連鎖は一段で止まり得る。

**さらに重要な訂正がある。** 第七十ラウンドは残余義務を `regenerate` の二条件として型で固定し、`blockedFirstOccurrence_impossible_of_regeneration` を「それさえ埋まれば全blocked配置が一括で死ぬ」定理として提出した。第八十一ラウンドの敵対的再検査により、**この仮定は偽であることが判明した**。詳細は該当定理の節に書く。

## 主要な定義

### `BlockedFirstOccurrence` (L50)

blocked配置を自己完結した概念として切り出したもの。三条件からなる。

- `first : FirstAt a value time` — `value` は時刻 `time` が初出である。
- `clock_below_value : time + 1 < value` — 時計が値より十分小さい。つまり減算候補 `value - (time+1)` は正であり、**大きさの上では減算する余地がある**。
- `blocked : ¬ CanSubtract (time + 1) (stateAt time)` — それでも減算できない。

三つ合わせると「初出したばかりの値であり、引ける大きさもあるのに、引き先が既出だから加算を強いられる」配置になる。減算不能の理由が純粋に履歴的であることが要点である。

## 定理と証明

### `value_eq` (L60)

**主張:** 記録された値は記録された時刻の軌道値である。初出条件の第一成分そのもの。補助補題。

### `defect_seen` (L64)

**主張:** 阻止は履歴的である: 減算欠損 `value - (time+1)` は時刻 `time` までの履歴に属する。

**証明:** 減算不能には「候補が非正」と「候補が既出」の二つの理由しかない(`not_canSubtract_cases`)。前者は `clock_below_value` が排除する。**ここで clock 条件が消費される**ことに注意したい。この消費が、後で witness 側に clock 条件を再生できないことと表裏の関係にある。

### `defect_pos` (L74) と `defect_lt` (L80)

**主張:** 欠損は正であり(`0 < value - (time+1)`)、かつ元の値より真に小さい。どちらも `time + 1 < value` からの算術。補助補題。

### `next_value` (L86)

**主張:** 阻止された時計での強制加算の値: `a(time+1) = value + (time+1)`。

**証明:** 減算できないときレカマンの一歩は加算枝を選ぶ。補助補題。

### `second_candidate` (L94)

**主張:** 強制加算の後、次の減算候補はちょうど元の値より1小さい: `a(time+1) - (time+2) = value - 1`。

**証明:** `value + (time+1) - (time+2) = value - 1`。この式が後の局所未来解析と副産物の強化を生む。

### `defect_firstTime_lt` (L102)

**主張:** 欠損の初出は阻止時刻より真に早い。

**証明:** `defect_seen` より欠損はある `u ≤ time` で実現されているので、初出は `u` 以下、したがって `time` 以下である。等号 `earlier = time` は起こり得ない。時刻 `time` の値は `value` であり、欠損は `value` より真に小さいからである。

### `exists_defect_firstAt` (L122)

**主張:** 欠損には阻止時刻より真に早い真正の初出があり、その時刻自体も正である。

**証明:** 履歴の要素は必ず初出時刻を持つ(`history_member_has_firstAt`)。時刻が正であるのは、`a(0) = 0` である一方で欠損が正だからである。時刻の正値性は、下降連鎖を組むときに「まだ下がれる」ことを言うために取ってある。

### `earlierSmaller` (L138)

**主張:** blocked枝は整礎順序 `EarlierSmaller` の辺を一本供給する: `⟨value - (time+1), earlier⟩` から `⟨value, time⟩` へ、値も時刻も真に小さい。

**証明:** 値の減少は `defect_lt`、時刻の減少は `defect_firstTime_lt`。**この辺の取得にclockの列挙も床の情報も一切使っていない。** ここが当初この経路に期待されていた点である。

### `gap_drop` (L150)

**主張:** アフィンな尺度 `値 - 時刻` も辺に沿って真に減る。

**証明:** 値は少なくとも `time + 1` 減り、時刻も減るので、差は真に減る。連鎖が整礎であるだけでなく短いことを示すつもりの補題である。

### `regenerate` (L160)

**主張:** 残余義務の明示。witness側で改めて `earlier + 1 < value - (time+1)`(clock条件)と `earlier` での減算不能性(blocked性)が成り立てば、blocked配置が再生する。

**証明:** 三条件を並べるだけである。定理としての内容はほぼない。この補題の役割は**何が輸送されないかを型で名指しすること**にある。輸送されるのは初出性だけで、他の二条件は blocked 枝のどこからも出てこない。`clock_below_value` は上で `defect_seen` を出すために使い切られており、blocked 性は元の時刻 `time` での履歴状態についての主張であって、はるかに早い `earlier` については何も言わない。

### `predecessor_dichotomy` (L170)

**主張:** blocked配置の局所未来。値 `value - 1` は、二歩後の時刻 `time+2` にまさに初出するか、あるいは阻止時刻より真に前に既に現れているかのいずれかである。

**証明:** `second_candidate` により時刻 `time+2` の減算候補は `value - 1` である。そこで減算が合法なら、合法減算の着地値は必ず新値なので `time+2` が初出になる。合法でないなら、候補が非正である可能性は `clock_below_value` が排除するので、`value - 1` は既出であり、その初出時刻を取ればよい。初出時刻が `time` や `time+1` に一致しないことは、それらの時刻の値がそれぞれ `value` と `value + (time+1)` であることから分かる。

### `no_earlierSmaller_descent` (L210)

**主張:** 整礎性の梱包。出現対の性質 `S` が、どの節点からも `EarlierSmaller` でより小さい `S` の節点へ進めるならば、`S` はどこにも成り立たない。

**証明:** `EarlierSmaller` は値で測った尺度の部分関係なので整礎である(`Blocker.lean`)。その整礎帰納法をそのまま回す。

### `blockedFirstOccurrence_impossible_of_regeneration` (L224)

**主張:** 条件付き一般排除。blocked配置が自分の欠損witnessで必ず再生するならば、blocked first occurrenceは一つも存在しない。仮定は `regenerate` が名指しした二つの義務そのものであり、結論にはclock床への言及が一切ない。

**証明:** 各blocked節点から `exists_defect_firstAt` で欠損の初出を取り、仮定で子もblockedにし、`earlierSmaller` で辺を作る。`no_earlierSmaller_descent` を適用すれば終わる。

**訂正(第八十一ラウンド): この定理の仮定は偽である。** 実軌道にblocked first occurrenceが存在するからである。具体的には `a(6) = 13` が13の初出であり、減算欠損は `13 - 7 = 6` で、これは `a(3) = 6` として既出であり、`7 < 13` なのでclock条件も満たす。つまり `BlockedFirstOccurrence 13 6` が実際に成立する。ところが上の定理の結論は `∀ value time, ¬ BlockedFirstOccurrence value time` であり、これはいま反証された。含意が成り立っている以上、仮定 `hregen` の方が偽でなければならない。反証は `TrivialityProbe.lean` の `probe_blockedFirstOccurrence_thirteen` と `probe_not_blockedFirstOccurrence_regeneration` に機械的に記録されている。

したがって**この定理は空虚に真な含意にすぎず、第七十ラウンドが与えた「残余義務を型で固定した」という位置づけは撤回済みである**。`regenerate` 経路は死んでいる。仮定を満たす道を探すこと自体が無意味であり、この形の一般排除は放棄された。

### `tailMinimum_ge_three` (L247)

**主張:** 生き残ったreplayのtail最小値は3以上である。

**証明:** minimum predecessorの値が正のtargetを既に上回っているので、tail最小値はそれよりさらに1大きい。補助補題。

### `minimum_predecessor_blocked` (L256)

**主張:** replay設定への接続。blocked枝では、minimum predecessorが本モジュールの意味でのblocked first occurrenceである。

**証明:** 初出性はminimum証明書の `predecessor_first`(tail最小値より1小さい値の初出が `historicalFirstTime`)。clock条件 `historicalFirstTime + 1 < a(historicalFirstTime)` は既存の `minimum_predecessor_value_above_clock` が与える。これはcorridorデータの三段連鎖(downcrossの `horizon_le_time` → replayの `eligible` → `time_eq`)から出るもので、**replay固有のフィールドに依存している**。blocked性は仮定である。

### `minimum_predecessor_blocked_descent` (L272)

**主張:** blocked枝は、真に小さい値と真に早く正の初出を返す。すなわちearlier-smaller順序の辺一本を、**clock列挙を一切使わずに**得る。

**証明:** L256でblocked配置に翻訳し、L122とL138をそのまま適用する。この定理が当初の期待の到達点であり、同時に到達できた限界でもある。

### `minimum_predecessor_blocked_witness_belowTail` (L289)

**主張:** 下降に沿って輸送されるもの: witnessの値はtail最小値より真に小さく、その初出はpermanent tail開始より真に前にある。

**証明:** 値については、witnessはminimum predecessorの値よりさらに小さく、その値はtail最小値より1小さい。時刻については、minimum証明書の `firstTime_before_tail` と `defect_firstTime_lt` を繋ぐ。

### `minimum_predecessor_blocked_witness_off_tail` (L310)

**主張:** したがって下降したwitnessの値はpermanent tail内には二度と現れない。

**証明:** tail内の値はすべてtail最小値以上だが、witnessはそれより小さい。

L289とL310が、tail構造から下降連鎖へ輸送できる情報のすべてである。**そしてこれらは連鎖の停止と何も矛盾しない。** 連鎖が止まるのは、witnessの値がその初出時刻を上回らなくなるか、その時刻で合法減算ができるときである。どちらの停止点も実軌道に無数に存在し、しかも「値がtail最小値未満」「初出がtail開始前」という二条件はそういう停止点でも普通に成り立つ。tail側から情報を輸送しても、停止を禁じることはできない。これが no-go の実質的な理由である。

### `minimum_predecessor_blocked_second_step` (L328)

**主張:** blocked枝の局所未来。tail最小値より2小さい値は、minimum predecessorの二歩後にまさに初出する(その場合permanent tailはまだ始まっていない)か、あるいはminimum predecessorより真に前に既出であるかのいずれかである。

**証明:** L170をreplay設定へ移送し、`a(historicalFirstTime) = a(historicalMinimumTime) - 1` で値を書き換える。前者の枝でtailがまだ始まっていないと言えるのは、もし時刻 `historicalFirstTime + 2` がtail内にあれば、その値がtail最小値以上でなければならないのに、実際にはtail最小値より2小さいからである。

### `tailMinimum_gap_of_blocked` (L366)

**主張:** 副産物。blocked枝では `target + 2 < a(historicalMinimumTime)`。すなわちtail最小値はtargetを2ではなく3以上引き離す。

**証明:** L328のどちらの枝でも「tail最小値より2小さい値」は実際に軌道上で実現されている。targetは実現されないと仮定されている(`target_missing`)ので、その値はtargetと異なる。tail最小値はtargetより2以上大きいことは既に分かっているので、差が2ちょうどである可能性が消え、3以上になる。

**この一本は空虚でない実質的な成果である。** 証明書自身が持つ `target + 1 < a m`(`target_lt_predecessor`)の真の強化であり、clock非依存に成り立つ。ただし第七十四ラウンドで、この強化は二分法のもう一方(二連減算枝)へは輸送されないことが確定している。二連減算枝の実現値はどちらも `a m - 2` を真に下回るからである。

### `minimum_predecessor_canSubtract_of_regeneration` (L388)

**主張:** 再生仮定のもとでは、生き残ったreplayはminimum predecessorで必ず即時減算する。

**証明:** blocked枝ならL224で矛盾する。

**注記: 仮定が偽であるため、この定理は空虚に真である。** 得られる情報は何もない。

### `minimum_predecessor_doubleSubtract_of_regeneration` (L404)

**主張:** 同じ仮定のもとでwitness付き二分法は二連減算枝へ潰れる。

**証明:** L388で第一歩の減算を得て、`minimum_predecessor_shape` の二択の残る側を取る。

**注記: これも同じ理由で空虚に真である。**

## 全体の中での位置づけ

証明地図(docs/PROOF_MAP.md)の「witness descent (blocked枝)」行、および「`regenerate`仮定の空虚性」行に対応する。上流は二分法を与える `PermanentAboveCorridorMinimumFollowUp.lean` と `PermanentAboveCorridorMinimumShape.lean`、整礎順序 `EarlierSmaller` は最初期の `Blocker.lean` に由来する。

本モジュールの成果を正確に分けると次のようになる。**確定した否定的結果**が主成果である。blocked枝はclock非依存のearlier-smaller辺と減少する尺度を供給するが、blocked性とclock条件がwitnessへ輸送されないため整礎性は発火せず、この経路単独ではclock非依存の一般排除に届かない。**撤回された主張**が一つある。`regenerate` の二条件として残余義務を型で固定したという位置づけは、仮定が偽である以上成立しない。この定理と、それに依存する二つの系は空虚に真な含意である。**残る正の成果**は `tailMinimum_gap_of_blocked` の無条件強化 `target + 2 < a m` ただ一つである。

no-go判定を受けて次に試されたのは二分法のもう一方、二連減算枝(`ReplayDoubleSubtractDescent.lean`)だが、そちらも第七十四ラウンドで「pre-tail領域への下界なしには原理的に排除不能」と決着している。証明書が軌道に下界を課すのはtail開始以降だけなのに対し、二連減算枝が語る時刻はすべてtail開始前だからである。二つの枝の否定的決着を合わせると、witness付き二分法をclock非依存に閉じる道は、いまの証明書のフィールド構成では塞がっている。開けるには「pre-tail領域に下界を持つ証明書フィールドの新設」のような、型そのものの再設計が要る。
