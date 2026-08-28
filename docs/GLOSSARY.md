# 用語集

本リポジトリでは、Lean・数学の標準用語、レカマン数列の問題設定から自然に出る語、
本研究で導入した解析用語を併用している。本書では各用語の出自と役割を区別する。

## 分類

| 表記 | 意味 |
|---|---|
| 標準 | Lean、論理学、または一般的な数学で確立している用語 |
| 問題由来 | レカマン数列の定義から直接生じる概念 |
| 研究固有 | 本研究が導入した定義、証明インターフェース、または比喩 |
| 整理用 | 単独のLean定義ではなく、定理群や軌道区間をまとめる呼称 |

「研究固有」は未証明の仮定を意味しない。独自に定義した対象について、Lean内で定理を
証明しているという意味である。

## 基礎となる語

### レカマン数列 `a` — 問題由来

初項を `a 0 = 0` とし、時刻`n+1`では現在値から`n+1`を引いた値が正で未出なら減算し、
それ以外では加算する数列である。`Basic.lean`では現在値と既出値の履歴を持つ`State`、
減算可能性`CanSubtract`、一歩の更新`step`から実行可能な形で定義している。

### 履歴 `valuesThrough` — 問題由来

時刻`n`までに出現した`a 0, ..., a n`を保持するリストである。実装上は新しい値から並ぶ。
レカマン数列では「減算先が未出か」を判定するため、値だけでなく履歴が力学の一部になる。

### 初出 `FirstAt` — 問題由来

`FirstAt seq x t`は、`seq t = x`であり、かつ`t`より前には`x`が出現していないことを表す。
大域探索では、ある値だけでなくその初出時刻も進行度として利用する。

### 商・剰余座標 `QuotRem`, `CoordinatesAt` — 標準＋研究固有

商と剰余そのものは標準的である。本研究では正の時刻`n`における実軌道の値を

```text
a n = n * q + r,    r < n
```

と表し、`q`と`r`を軌道解析の座標として使う。`CoordinatesAt n q r`は、この関係が実際の
レカマン値について成り立つことを表す。

### 三角数 `lowerTri`, `upperTri` — 標準

```text
lowerTri q = q(q-1)/2
upperTri q = q(q+1)/2
```

に対応する。Leanでは除算に関する余分な証明を避けるため、再帰式で定義している。

### ポテンシャル `potential`、`G` — 研究固有

座標`(q,r)`に対して導入した符号付き整数

```text
G(q,r) = r - upperTri(q)
```

である。「ポテンシャル」という発想は数学で一般的だが、この式とレカマン数列への適用は
本研究固有である。局所遷移で`G`が保存、増加、減少する量を追跡し、有限降下の尺度にする。

## 局所座標力学

### regular chamber / 通常領域 — 研究固有

座標が`q <= r`を満たす領域である。この領域では、時刻を一つ進めたときの商・剰余更新を
追加の借りなしで記述できる。

### borrow / 借り — 研究固有

時刻の法が`n`から`n+1`へ変わる際、更新後の値を正規化された商・剰余に直すために行う
算術的な借りを指す。筆算の「借り」を使った比喩であり、`BorrowData`が回数`b`と更新後の
剰余`s`を証明付きで保持する。

- `zeroBorrow`: 借りが0回の遷移
- `oneBorrow`: 借りが1回の遷移
- `multiBorrow`: 一般の複数回の借りを許した算術モデル

一般の算術モデルでは複数回を扱うが、実際のレカマン軌道では`b = 0`または`b = 1`しか
起こらないことを`OrbitBounds.lean`で証明している。

### regular addition/subtraction、borrow addition/subtraction — 研究固有

加算・減算という分岐はレカマン数列由来である。`regular`と`borrow`は座標更新の型を表す。
たとえば通常減算では`G`が保存され、通常加算では`G`が`2q+1`だけ低下する。

## 目標到達の機構

### target / 目標 `m` — 一般語

軌道上に出現することを証明したい非負整数である。最終目標はすべての`m`について
`exists t, a t = m`を示すことである。

### exact gate / 完全ゲート — 研究固有

二回の連続した合法減算で目標`m`へ正確に着地できる局所配置である。時刻`u`の値が
`2u+m+3`で、中間値と`m`が未出なら、次の二歩で`m`に到達する。
「ゲート」は必要な局所条件がそろった入口という比喩である。

### target equation / 目標方程式 — 研究固有

下降開始時刻・値・目標・歩数の間に、三角数を含む到達方程式が成り立つことを表す。
減算が予定どおり続けば目標へ着地し、途中で止まればblockerを取り出すための算術条件である。

### target surface / 目標面 — 研究固有・整理用

座標空間で

```text
potential q r = Int.ofNat m
```

を満たす状態の呼称である。コード上では独立した`TargetSurface`構造ではなく、この等式を
仮定する`targetSurface_*`定理群として現れる。「面」は座標空間内の等位集合という比喩である。

### blocker / 妨害値 — 研究固有

下降中の減算先がすでに履歴にあるため、合法減算を続けられなくする既出値である。
`BlockerCertificate`は、現在値`v`、妨害値`y`、それぞれの初出時刻、下降長などを保持する。
証明書から`y < v`と、`y`の初出時刻が`v`の初出時刻より早いことが従う。

### descent run / 下降列 — 研究固有

実軌道上で合法減算が連続する区間を、開始時刻・開始値・長さとともに証明付きで表す。
途中で下降が止まる場合、その理由をactual blockerへ変換する。

### landing / 着地、escape / 脱出 — 整理用

`landing`は目標または目標面への到達、`escape`は現在の局所配置から強制加算などを経て
別の解析可能な配置へ移ることを表す。どちらも定理群を読みやすくする説明的な名称である。

## 符号領域と有限区間

### negative region / 負領域 — 研究固有

`potential q r < 0`を満たす座標領域である。負領域に入った実軌道がどのように一段借りの
境界へ到達するかを`Recovery*.lean`で解析する。

### recovery / 回復 — 整理用

負ポテンシャル状態から、一段借りによる非負着地または被覆証明へ進む有限過程の呼称である。
単独の`Recovery`データ型ではなく、関連定理とモジュールをまとめる名前として使う。

### epoch / エポック — 整理用

同じ符号条件や局所条件のもとで追跡する有限な軌道区間を指す。

- negative epoch: 負ポテンシャルから始めて回復を追う区間
- nonnegative epoch: 非負ポテンシャルから始めて低い商またはポテンシャル低下まで追う区間

確率論などの厳密な標準概念を流用したものではなく、本研究における区間整理の名称である。

### undershoot / アンダーシュート — 研究固有

目標`m`に対して

```text
0 <= G < m
```

となる非負ポテンシャル帯である。この帯では、有限時間内に被覆、負領域への復帰、または
同じ帯のより低いポテンシャルへ進む三分岐を証明している。

### frontier / フロンティア — 整理用

高い商、借りの回数、履歴条件など、解析領域の境界で成立する定理群の名称である。
`RecoveryFrontier`、`OneBorrowFrontier`、`HistoryFrontier`は共通のデータ型を指すのではなく、
それぞれ異なる境界問題をまとめたモジュール名である。

## 大域探索

### coverage / 被覆 — 一般語＋研究固有

一般には目標値が軌道に含まれることを指す。本研究では、全射性を値に関する整礎帰納へ
落とすため、次の証明インターフェースを定義している。

### `CoverageStep` — 研究固有

親の値`v`から見て、次のいずれかを与える一段の証明である。

1. 目標`m`が実際に出現する。
2. `m <= y < v`を満たす、より小さい値`y`とその初出時刻を得る。

第二の場合は親の値が真に小さくなるため、自然数上の強帰納法を適用できる。

### oracle / オラクル — 研究固有の証明インターフェース

このリポジトリでのoracleは、外部プログラム、探索アルゴリズム、計算上の神託ではない。
「各探索ノードで、目標到達または真に小さい次ノードを構成できる」という命題を抽象化した
証明義務である。

- `CoverageOracle`: 各初出値から`CoverageStep`を供給する。
- `HistorySearchOracle`: 三成分の履歴探索ランクを下げる。
- `PhaseSearchOracle`: 位相を含む四成分ランクを下げる。

oracleを仮定した停止証明は完成しているが、必要なoracleをすべての局所状態について構成する
部分は未証明である。したがって、oracleから全射性が従う定理は条件付き定理であり、全射性
そのものを仮定しているわけではない。

### history budget / 履歴予算 — 研究固有

`missingBelowCount m n`、すなわち時刻`n`までに未出である`m`未満の値の個数である。
履歴が増えるとこの個数は増えず、新しい`m`未満の値が初出すると真に減る。有限な探索ランクの
第一成分として使うため「予算」と呼ぶ。

### well-founded rank / 整礎ランク — 標準＋研究固有

整礎関係と辞書式順序は標準数学・Leanの概念である。どの量をランクに選ぶかは本研究固有である。

- 履歴予算ランク: 未出値数と親の値
- 履歴探索ランク: 未出値数、anchor parent、局所軌道値
- 位相探索ランク: 未出値数、anchor parent、位相、局所量

いずれも各証明ステップで辞書式に真に減るため、無限下降がないことをLeanで証明する。

### diagonal / 対角状態 — 研究固有

時刻と軌道値が一致する形の状態である。主要な対角補題では`a (n+2) = n+2`を仮定し、
次の値の出現または極大な後方減算鎖と早期blockerを抽出する。

### anchor parent / アンカー親 — 研究固有

局所的な探索中に基準として固定する親の値である。debt状態から通常探索へ戻るときは、
位相成分が増えても、その前に比較されるanchor parentが真に減ることで全体ランクが低下する。

### phase / 位相、normal / 通常、debt / 負債 — 研究固有

`PhaseSearchNode`が持つ探索モードである。

- `normal`: 通常の値・履歴探索を行う。
- `debt`: 対角分岐で得た早期blockerを処理し、初出時刻の下降を追う。

`debt`は金銭的意味ではなく、「通常探索へ戻る前に解消すべき局所的な証明義務」の比喩である。
debtへの進入、debt中の初出時刻低下、anchor低下後のnormalへの復帰は、いずれも四成分ランクを
真に下げるよう設計されている。

### semantic domain / 意味的domain — 研究固有

数値tupleとして作れる全`PhaseSearchNode`ではなく、実軌道・履歴・座標に関する証明を伴う
nodeだけを探索対象にするためのproof-carrying domainである。`PhaseSemanticInvariant`は
canonical、normal、debt、crossing recoveryを統合する。現在のweak normal constructorは
過去の初出値と後のhorizonを組み合わせられるため、total oracle用にはさらに精密化が必要である。

### orbit-ready normal — 研究固有

normal nodeのlocal valueが実際に`a time`であり、目標時刻条件、目標下界、anchor上界、
`CoordinatesAt time q r`を同時に持つ状態である。`OrbitReadyNormalCertificate`はこの条件を
証明付きで保持し、現在horizonからepoch定理を適用できることを明示する。

### provenance / 生成元証明 — 標準的発想＋研究固有の用途

あるnormal childがparent-drop、CoverageStep、frontierなど、どの局所定理から生成されたかを
保持する証明データである。一般語としてのprovenanceは標準的だが、本研究ではcurrent-stateでない
historical childを安全に再帰探索へ戻すためのdomain constructorとして用いる。
`ProvenancedNormalInvariant`はcurrent nodeとrank edge付きhistorical nodeを区別する基礎APIを
実装している。total oracleには、parent-dropやdowncrossingなど生成機構別の追加データが必要である。

### representative time / history horizon — 研究固有

historical normal nodeで分離する二つの時刻である。`representative time`はanchor値と座標を
実際に取る軌道時刻、`history horizon`は`missingBelowCount`を評価する後の履歴時刻である。
両者が一致するのがcurrent nodeであり、前者が小さい場合をextended-history nodeと呼ぶ。
代表時刻からhorizonまでに履歴予算が下がると、representative stateからのrank下降を単純には
輸送できないため、この差は単なる実装詳細ではない。

### crossing recovery / crossing回復 — 研究固有

target未満の値から強制加算でtarget以上へ上向き横断した実遷移を保持するnormal状態である。
pre-crossing値を新anchorにするため、旧anchorがtarget以上ならanchorを厳密に下げられる。
extended-historyのearly representativeとhistory-budget gapはいずれも、below-target実出現から
将来のcrossing recoveryを構成することで閉じる。

### horizon-ready debt / 時刻準備済み負債 — 研究固有

strong `DebtInvariant`に`target ≤ node.horizon+1`を追加した状態で、Leanでは
`ReadyDebtInvariant`として表す。通常のdebt継続はhorizonを固定するためこの条件を保存する。
一方、旧`CoverageDebtChildCertificate`は親のclock条件を保持していないので、certificate単独から
horizon readinessは導けない。

### ready crossing / 時刻準備済みcrossing — 研究固有

`CrossingSearchInvariant`に`target ≤ node.horizon+1`を追加した状態で、Leanでは
`ReadyCrossingSearchInvariant`として表す。horizonの軌道値がtarget未満なら次の強制加算で
weak upcrossingを作れ、horizon以後にdowncrossがあればfresh below-target値による
history-budget下降を作れる。

### crossing continuation growth residual — 研究固有

horizon-below ready crossingから次のcrossingへ進んだとき、history budgetが不変で、
pre-crossing anchorも下がらない残余である。Leanの
`CrossingContinuationGrowthResidual`は新crossing、budget同値、anchor非減少、および
`PhaseSearchProgress`不成立を同時に保持する。target 19の実軌道に実例があるため、
単なinterfaceの弱さではない。

### target tail return / 目標tail復帰 — 研究固有

at-or-above targetの軌道点から、目標がすでに出現するか、将来below-targetの軌道点へ
戻るという長期命題で、`TargetTailReturnHypothesis`として切り出す。future downcrossが
存在しないことは、その開始点以降ずっとtarget以上に留まることと同値である。
これは現在のready crossing局所totalityに残る数学的境界である。ただし、全targetに対する
tail returnは`all_targetTailReturn_iff_surjective`により元の全射性予想と同値であり、弱い局所補題ではない。

### missing permanent-above tail / 未出目標の恒久上方tail — 研究固有

正のtargetが全軌道で未出、target未満の値があるhorizonまでにすべて既出、かつそのhorizon以後の
軌道値が常にtargetより大きい状態を`MissingPermanentAboveTail`として表す。仮想的な最小未出targetは
この証明書を持つ。tailの最小値では二連続forced additionが起き、直下値`a n - 1`の初出がtail開始前にある。

### zero-budget crossing / 履歴予算0のcrossing — 研究固有

`missingBelowCount target horizon = 0`を持つcrossingである。target未満の全値が既出なので、
noncrossing refined子に必要なstrict budget dropは不可能になる。refined子が存在する場合はcrossingに
留まり、pre-crossing anchorが厳密に下がる。`PermanentTailCrossingCertificate`は仮想反例から、
tail内horizon、ready crossing、zero budget、future downcross不在をまとめて抽出する。

### tail minimum historical blocker / tail最小値の履歴blocker — 研究固有

恒久上方tailの最小値`a n`に対する直下値`a n - 1`と、そのtail開始前の初出証明である。
`PermanentTailMinimumCertificate`は最小性、二連続forced addition、候補式、初出時刻、target下界を保持する。
zero-budget crossingのanchor下降へこのblockerを接続することが現在の未証明点である。

### historical predecessor outcome / 履歴predecessor分岐 — 研究固有

tail最小値直下の初出時刻以後にdowncrossがあるかを分類する`HistoricalPredecessorOutcome`である。
downcross枝はfresh below-target endpointとstrict history-budget dropを返す。no-downcross枝は初出時刻から
新しいstrict-above tailを作り、その最小値を厳密に下げる。後者は自然数下降なので有限回しか続かない。

### historical cycle growth residual / 履歴cycle成長残余 — 研究固有

historical downcross後のupcrossingをzero-budget crossing親と同じhorizonへ載せた際、pre-crossing anchorが
下がらない残余である。`HistoricalCycleGrowthResidual`はdowncross、upcross、ready crossing子、same horizon、
anchor非減少、rank進捗不成立を保持する。親をそのupcrossing自身に選ぶとchild=parentの停留例を常に
構成できるため、単なる型情報不足ではなく、任意crossing選択を許す現行domainの本質的境界である。

### first weak upcrossing / 最初の弱上方crossing — 研究固有

below-target開始点以後で最初に起きる`WeakUpcrossingStep`を`FirstWeakUpcrossingStep`として表す。
既知witness時刻を上界にした自然数強帰納で存在し、任意の他witness以下なので一意である。
ただし同じ開始点から再選択すれば同じ時刻へ戻るため、canonical化だけではstationary cycleを除けない。

### seen-below count / 発見済み下側値数 — 研究固有

`seenBelowCount target horizon = target - missingBelowCount target horizon`である。target未満の発見済み値数に
対応し、missing countとの和はtargetになる。時間の進行では増加し、tail horizonからhistorical時刻へ
戻るbacktrackingでは減少し得るため、過去向き探索のdual budgetとして使う。

### permanent-tail cycle rank / 恒久tail cycleランク — 研究固有

zero-budget領域で使う`(anchor, phase, seenBelowCount, tailMinimum)`の四成分辞書式rankである。
phaseは`crossing > backtrack > discharge`の一方向。historical探索内部はすべてstrictに下降する。
dischargeからcrossingへ戻るにはstrict anchor dropが必要十分であり、同anchor stationary loopを拒否する。

### crossing-time cursor / crossing時刻cursor — 研究固有

permanent-tail cycleの外側比較をanchor単体から`(anchor, crossingTime)`へ精密化した辞書式量である。
anchorが下がればもちろん進捗し、anchorが等しくてもcanonical returnの時刻が旧crossingより早ければ
進捗する。phase、seen-below count、tail minimumと合わせた五成分rankもwell-foundedである。

### canonical discharge kernel residual / canonical排出kernel残余 — 研究固有

historical downcrossからcanonical upcrossingで戻ってもcrossing-time cursorが下がらない場合の最小分類である。
`CanonicalDischargeKernelResidual`は、strict anchor growth、旧crossingがdowncross endpointより前にある
chronology mismatch、anchorと時刻が同一のliteral stationaryの三constructorだけを持つ。

## Leanと証明監査の語

### `Prop`, `def`, `structure`, `inductive`, `theorem` — Lean標準

- `Prop`: 命題の型
- `def`: 定義
- `structure`: 複数のデータや証明を持つ構造
- `inductive`: 帰納型
- `theorem`: 証明済み命題

### `Decidable`、`decide` — Lean標準

命題を計算で判定できること、およびその判定手続きを使って小さな具体例を証明する機構である。
本リポジトリの`Examples.lean`ではLeanカーネルが確認できる`decide`を使用する。

### `WellFounded`、強帰納法、辞書式順序 — 数学・Lean標準

無限下降列が存在しない関係と、それに基づく帰納法である。本研究の大域探索は、複数の自然数を
辞書式に並べたランクが毎回低下することを示して停止性を得る。

### 公理監査 `#print axioms` — Lean標準の検査機能

ある定理がどの公理に依存するかを表示する。`Audit.lean`では主要定理を監査し、`sorryAx`、
ユーザー定義公理、`native_decide`由来の公理に依存していないことを検査する。

## 読む順序

初めて読む場合は、次の順序を推奨する。

1. `Basic.lean`: 数列と履歴
2. `Coordinates.lean`: 商・剰余とポテンシャル
3. `CoordinateDynamics.lean`: 通常遷移と一段借り
4. `Coverage.lean`: 全射性へつなぐ証明インターフェース
5. `PROOF_MAP.md`: 各局所定理が大域探索のどこに位置するか
6. `PhaseSearch.lean`: 現在の最終的な整礎探索骨格
