# ExtendedHistoryBudgetClosure

**役割:** extended-history nodeのbudget輸送残余を、履歴予算下降の原因である「新しいbelow-target出現」から将来のcrossing recoveryを構成して閉じる。

## このモジュールの役割

`ExtendedHistoryNormal` の完全分類には、代表時刻は準備済みだが履歴予算(`missingBelowCount`、目標未満の未出値数)がhorizonまでに真に落ちているため、代表nodeの局所下降を輸送できない `budget_transport` 残余が残っていた。本モジュールはこの残余を、局所childの輸送では**なく**、まったく別の辺で閉じる。すなわち、予算の真の下降には必ず具体的な原因、「代表時刻には未出でhorizonまでに出現した目標未満の値」があることを示し、その出現点から将来の**弱上方crossing**(target未満の値から強制加算でtarget以上へ跳ぶ遷移)を取り、既存のcrossing recovery semantic状態へ移る。pre-crossing値はtarget未満なので旧anchorより真に小さく、既存の四成分rankがanchor成分で下降する。

## 定理と証明

### `exists_newBelow_of_missingBelowCount_strict` (L18)

**主張:** `earlier ≤ later` かつ `missingBelowCount target later < missingBelowCount target earlier` ならば、ある値 `value < target` が存在して、時刻`earlier`の履歴には属さず、時刻`later`の履歴には属する。つまり予算の真の下降には必ず「新しく見えた目標未満の値」という証人がある(既知の順方向補題 `missingBelowCount_strict_of_new` の、実際の単調な履歴に沿った逆向き)。

**証明:** `target` に関する帰納法。`missingBelowCount` は `target` 未満の各値について未出なら1を数える和なので、最上位の値 `target`(帰納段階で新たに数える値)の出現状況で三分する。

1. `target` がすでに`earlier`で既出なら、履歴の単調性より`later`でも既出であり、両辺の計数からこの値の寄与は消える。残る真の不等式は `target` 未満の範囲の予算に関するものなので帰納法の仮定が証人を与える。
2. `earlier`では未出だが`later`では既出なら、この `target` 自身が求める証人である。
3. 両時刻で未出なら、両辺から1ずつ引いても真の不等式が保たれ、帰納法の仮定に帰着する。

### `exists_newBelow_occurrence_of_missingBelowCount_strict` (L45)

**主張:** 前定理の証人を実際の出現時刻に具体化する: 予算gapがあれば、ある値 `value < target` と時刻 `occurrenceTime` が存在して、`代表時刻 < occurrenceTime ≤ historyHorizon`、`a(occurrenceTime) = value`、かつ `value` は代表時刻の履歴に属さずhorizonの履歴に属する。

**証明:** 証人 `value` がhorizonの履歴に属するから、その出現時刻 `occurrenceTime ≤ historyHorizon` が取れる。もし `occurrenceTime ≤ 代表時刻` なら `value` は代表時刻の履歴に属してしまい、未出性に矛盾する。よって出現は代表時刻より真に後である。

### `ExtendedHistoryNormalCertificate.phaseSemanticStep_of_budgetGap` (L75)

**主張:** budget gap付きのextended-history nodeは、目標の出現、またはsemantic不変量を持つchildへの真のrank下降を持つ。これがbudget残余の本体の閉包である。

**証明:** 前定理で得た出現点では `a(occurrenceTime) = value < target` である。target未満の軌道値から出発すると、将来必ず弱上方crossingが存在する(`exists_weakUpcrossingStep_from_below`): ある時刻 `crossingTime` で `a(crossingTime) < target ≤ a(crossingTime + 1)` かつ時刻 `crossingTime + 1` の遷移は強制加算である。ここで場合分けする。

- 目標がすでに時刻 `crossingTime` までの履歴に出現していれば、その証人を返す。
- `a(crossingTime + 1) = target` なら、それ自身が証人である。
- 残るのは真の横断 `target < a(crossingTime + 1)` の場合である。強制加算の値の式と合わせて `DebtCrossing`(下から上への真の横断データ)が成り立ち、post-state `crossingTime + 1` の商・剰余座標も取れる。childを

  `next = ⟨max(node.horizon, crossingTime + 2), a(crossingTime), normal, a(crossingTime)⟩`

  と定める。horizonを `max` で拡張することで旧履歴をすべて保ち、crossingが新horizonより真に前にあることを保証する。anchor条件は `a(crossingTime) < target ≤ a(代表時刻)` から従い、これらが `CrossingRecoveryInvariant` の全フィールドを満たすので、childはsemantic不変量の `crossing_recovery` 枝に入る。rank下降は次の通り: 第一成分の履歴予算はhorizonの拡大により非増加(単調性)、第二成分のanchorは `a(crossingTime) < a(代表時刻)` で真に下降する。よって四成分辞書式rankで `next` は `node` より真に小さい。

代表時刻の局所childを予算gapを越えて輸送するのではなく、gapの**原因そのもの**を新しい下降辺に変換している点が本質である。

### `extendedHistory_budgetTransportResidual_phaseSemanticStep` (L141)

**主張:** constructor形の包み: `phaseSemanticStep_or_residual` が返す文字通りの `budget_transport` 残余(格納された局所child・局所下降を含む)は、その局所childとは無関係にすべて閉じる。

**証明:** 格納データのうちgapだけを取り出して前定理を適用する。局所child・局所semantic・局所progressの引数は使用しない(アンダースコア付き引数)。

### `ExtendedHistoryReadinessResidual` (L161)

**主張(定義):** budget輸送を閉じた後に残る唯一の残余。constructorは `representative_not_ready` のみで、代表時刻でのtarget readinessの失敗(`代表時刻 + 1 < target`)と値の真の超過(`target < a(代表時刻)`)を保持する。

### `ExtendedHistoryNormalCertificate.phaseSemanticStep_or_readiness` (L174)

**主張:** extended-history nodeの強化された全域分類: 目標の出現、semantic childへの真の下降、または readiness残余の三択。旧分類の `budget_transport` 枝は消えている。

**証明:** `phaseSemanticStep_or_residual` を実行し、`representative_not_ready` はそのまま新残余へ写す。`budget_transport` は `phaseSemanticStep_of_budgetGap` で出現または下降に置き換える。

## 全体の中での位置づけ

証明地図の「意味的探索domain: generic budget gapのcrossing recovery接続」に対応する。`DowncrossBudgetGap` の弱上方crossing存在定理と `CrossingRecovery` のsemantic状態を接続する要のモジュールであり、本モジュールと `EarlyRepresentativeComplete`(readiness残余の閉包)を合流させた `ExtendedHistoryComplete` が、extended-history normal nodeの残余なしの完全なsemantic stepを与える。同じ構成をrefined domain上で直接行うのが `ExtendedHistoryDirectRefined` の `refinedStep_of_budgetGap` である。
