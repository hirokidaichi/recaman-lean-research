# HistoryFrontier

**役割:** 非負・負の各エポックの終端を三成分履歴ランクの厳密下降へ変換し、残る例外を対角状態の一点に絞る。

## このモジュールの役割

`Undershoot` と `Recovery` 系のモジュールは、実軌道が有限時間内に「低商状態」や「一段借りの境界」へ到達することを示すが、それだけでは大域探索は停止しない。本モジュールは、それらのエポック(同じ符号条件で追跡する有限な軌道区間)の終端状態を `HistoryBudget` の探索ランクの言葉に翻訳する。鍵は商 1(`q = 1`)の低商フロンティアであり、そこでの二歩の場合分けがすべて「予算下降・親下降・軌道値下降・被覆」のいずれかに落ちることを示す。最終的に、負エポック全体の結果をランクに変換したとき唯一残る例外分岐が、対角状態 `a t = t` から目標 `t+1` を要求する `DiagonalSuccessorProperty` の一点であることを明示する。この一点が次モジュール `Diagonal` の主題になる。

以下で **blocker(妨害値)** とは、減算先がすでに履歴にあるため合法減算を止める既出値、**CoverageStep** とは「目標 `m` が出現する、または `m ≤ y <`(親の値) なる既出値 `y` とその初出時刻を与える」一段の被覆証明を指す。

## 定理と証明

### `zeroQuotient_firstAt` (L7)

**主張:** 正の時刻 `n` で座標が `(q, r) = (0, r)`、すなわち `a n = r < n` ならば、`r` は時刻 `n` が初出である(`FirstAt a r n`)。

**証明:** 直前の一歩が加算だったとすると `a n = a(n−1) + n ≥ n` となり `r < n` に矛盾する。よって直前は合法減算であり、レカマン数列の合法減算は定義上「未出の値」にしか着地しないので、`a n = r` はこの時刻が初出である。

### `later_zeroQuotient_historyBudgetProgress` (L32)

**主張:** `n < t`、`r < m` で時刻 `t` に商 0 の着地 `CoordinatesAt t 0 r` があれば、`⟨a t, t⟩` は `⟨a n, n⟩` に対して `HistoryBudgetProgress m` を満たす。

**証明:** 前定理により `r` は時刻 `t` が初出。`r < m` なので `missingBelowCount_strict_of_firstAt` により履歴予算が厳密に減り、ランクの左分岐が成立する。これは後述の `nonnegative_epoch_historyFrontier` に残る唯一の境界例外(商 0)を、先行する負エポック側で吸収するための橋である。

### `qOne_historyBudgetProgress_or_coverage` (L57)

**主張:** `m ≤ n+1`、レベル `3 ≤ g < m` で時刻 `n` の座標が `(1, r)`、ポテンシャル(`potential q r = r − q(q+1)/2`)が `g` のとき、次のいずれかが成り立つ。

1. `CoverageStep m (a n) n` が既に得られる。
2. ある時刻 `t`(`n < t ≤ n+2`)に座標 `(k, s)` があり、レベルは `g−1` または `g−3`、かつ `⟨a t, t⟩` が `⟨a n, n⟩` より履歴予算ランクで真に小さい。

**証明:** `q = 1` では `potential 1 r = r − 1` なので `r = g + 1`、すなわち `a n = n + 1 + g` である。時刻 `n+1` の減算候補は `a n − (n+1) = g` であり、二歩の場合分けを行う。

- **一歩目の減算が合法な場合。** `a(n+1) = g` は商 0 の着地であり(`g < m ≤ n+1`)、合法減算による着地なので `g` の初出である。`g < m` だから履歴予算は時刻 `n+1` で厳密に下がり、antitone 性により `n+2` でも下がったままである。続く一歩は `g < n+2` により必ず加算で、`a(n+2) = (n+2) + g`、すなわち座標 `(1, g)`・レベル `g−1` の状態になる。予算下降によりランクは左分岐で減少する(分岐 2、レベル `g−1`)。
- **一歩目が阻止され加算になる場合。** `a(n+1) = a n + (n+1) = 2(n+1) + g`、座標 `(2, g)`・レベル `g−3`。二歩目の減算候補は `a(n+1) − (n+2) = a n − 1` である。
  - 二歩目の減算が合法なら `a(n+2) = a n − 1`(強制加算直後の合法減算はちょうど 1 の値下降になるという `a_add_then_sub_eq_pred`)。座標は `(1, g−2)`・レベル `g−3` で、値下降によりランクが減る(分岐 2、レベル `g−3`)。
  - 二歩目も阻止される場合、候補 `y = a n − 1` は正で候補式も成り立つので、阻止の理由は「既出」しかない。`y = n + g ≥ n + 1 ≥ m` かつ `y < a n` なので、`y` とその初出時刻が親 `a n` に対する CoverageStep の blocker 分岐を与える(分岐 1)。

いずれの枝でもレベルは `g` から `g−1` または `g−3` へ下がることが明示され、ポテンシャルの有限降下とランクの下降が同時に追跡される。

### `qOne_historySearchProgress_or_coverage` (L164)

**主張:** 前定理の三成分ランク版。アクティブ親 `activeParent` を固定したまま、同じ二分岐が `HistorySearchProgress` で成り立つ。

**証明:** `HistoryBudgetProgress.toHistorySearchProgress` により、局所の二成分進捗を親成分固定の三成分進捗へ埋め込むだけである。

### `coverageStep_occurs_or_historySearchParentProgress` (L192)

**主張:** `CoverageStep m v f` からは、目標の出現か、あるいは `m ≤ y < v` なる blocker `y` によるアクティブ親成分の厳密下降(horizon と軌道値は固定)が得られる。

**証明:** CoverageStep の定義の場合分け。blocker 分岐では `historySearchProgress_of_parentDrop` を horizon 不変で適用する。blocker の初出時刻は証拠として保持するが、**意図的に horizon としては使わない**。初出時刻を horizon に代入すると履歴が過去へ戻り、予算成分が増加しうるからである。

### `forcedAddition_followup_historySearchProgress` (L212)

**主張:** 時刻 `n` で減算が阻止され(強制加算)、`a n ≤ activeParent` かつ `m ≤ a n − 1` とする。このとき次のいずれかが成り立つ。

1. `y = a n − 1` が `m ≤ y < activeParent` を満たす既出値であり、親成分が厳密に下がる。
2. 軌道値成分が厳密に下がる(`a(n+2) < a n`)。

**証明:** 強制加算の次の減算候補はちょうど `a(n+1) − (n+2) = a n − 1` である。この減算が合法なら `a(n+2) = a n − 1 < a n` で軌道値下降(分岐 2)。阻止されるなら、候補は正なので理由は既出しかなく、`y = a n − 1` は履歴にあり初出時刻を持つ。仮定 `m ≤ a n − 1` と `y < a n ≤ activeParent` により親下降(分岐 1)。つまり強制加算という「一時的な値の上昇」は、一歩以内に必ずランクの下降として返済される。

### `CoordinatesAt.target_le_pred_of_two_le_quotient` (L262)

**主張:** `m ≤ n+1`、座標 `(q, r)` で `q ≥ 2` ならば `m ≤ a n − 1`。

**証明:** 実軌道の商上界 `2q ≤ n+1`(`OrbitBounds` 由来)から `n ≥ 3` が従い、`a n = nq + r ≥ 2n ≥ n + 3` なので `a n − 1 ≥ n + 2 ≥ m + 1 > m − 1`、すなわち `m ≤ a n − 1` が成り立つ。

### `coordinates_forcedAddition_twoQuotient_historySearchProgress` (L277)

**主張:** 商 2 以上からの強制加算は、現在値がアクティブ親以下である限り、高々もう一歩で三成分ランクの厳密下降(親下降または軌道値下降)として解消される。

**証明:** 前補題により候補下界 `m ≤ a n − 1` が自動的に満たされるので、`forcedAddition_followup_historySearchProgress` をそのまま適用する。

### `qOne_historySearchOutcome` (L302)

**主張:** 商 1 フロンティアの完全なランク解釈。`a n ≤ activeParent` のもとで、目標の出現、blocker による親下降(`y < activeParent`)、または前進する探索ステップ(レベル `g−1` か `g−3`)のいずれかが成り立つ。

**証明:** `qOne_historySearchProgress_or_coverage` の CoverageStep 分岐を `coverageStep_occurs_or_historySearchParentProgress` 型の場合分けで開き、blocker の `y < a n` を輸送条件 `a n ≤ activeParent` で `y < activeParent` に持ち上げる。

### `nonnegative_epoch_historyFrontier` (L348)

**主張:** レベル `3 ≤ g < m` の任意の非負エポック(座標 `(q, r)`、ポテンシャル `g`)について、次のいずれかが成り立つ。

1. `CoverageStep m (a n) n`。
2. `q = 0`(先行する負エポックに請求すべき唯一の境界例外)。
3. ある時刻 `t`(`n < t ≤ n + q + 2`)にレベル `g`, `g−1`, `g−3` のいずれかの座標状態があり、履歴予算ランクが厳密に下がる。

**証明:** `Undershoot` の定理により、非負エポックは通常減算の前置区間を経て有限歩で商 `p ≤ 1` の状態(時刻 `u`、ポテンシャル `g` は不変、値は `u = n` でない限り厳密減少)か CoverageStep に到達する。

- `p = 0` の場合: `u = n` なら元の状態自身が商 0 であり分岐 2。`u > n` なら値が厳密に減っているので `historyBudgetProgress_of_valueDrop` によりランク下降(レベル `g` のまま、分岐 3)。
- `p = 1` の場合: 時刻 `u` に `qOne_historyBudgetProgress_or_coverage` を適用する。得られた CoverageStep は、前置区間で値が下がっていれば `CoverageStep.mono_parent` で元の親 `a n` へ持ち上がる(分岐 1)。得られた進捗は、前置区間の値下降による進捗と `HistoryBudgetProgress.trans` で合成して時刻 `n` からの進捗にする(分岐 3、レベル `g−1` か `g−3`)。

商 0 の例外だけがランクに変換できないが、これは `later_zeroQuotient_historyBudgetProgress` により「その状態が負エポックから入ってきたときには予算が既に下がっている」ことで別途吸収される。

### `nonnegative_epoch_historySearchOutcome` (L418)

**主張:** 前定理の三成分ランク版。エポックの開始値がアクティブ親以下なら、目標の出現、親下降、`q = 0` の境界、または前進する探索ステップのいずれかになる。

**証明:** `nonnegative_epoch_historyFrontier` の CoverageStep 分岐を親下降へ、進捗分岐を `toHistorySearchProgress` で三成分へ埋め込む。

### `negative_epoch_historySearchOutcome_or_qOneDebt` (L470)

**主張:** 負のポテンシャルから始まる完全な負エポックについて、次のいずれかが成り立つ。

1. 目標の出現。
2. blocker による親成分の厳密下降。
3. 後の時刻での軌道成分の厳密下降。
4. **商 1 の負債チャンバー:** ある時刻 `t ≥ n`(`a t ≤ a n`)で座標 `(1, r′)`、一段借り(borrow: 時刻の法が変わる際の商・剰余の繰り下がり)`BorrowData t 1 r′ 1 s` が起き、減算は阻止され、着地 `CoordinatesAt (t+1) 1 s` のポテンシャルが `0 ≤ potential 1 s < m` を満たす。

**証明:** `Recovery` 系の定理により、負状態は有限歩(値は増えない)で一段借りの境界時刻 `t` に到達し、そこで CoverageStep が既に得られているか、境界遷移が分類される。前置区間の値下降による進捗は `liftProgress`(`HistorySearchProgress.trans`)で時刻 `n` からの進捗に合成する。

- 境界で減算が合法なら `a(t+1) < a t` で軌道値下降(分岐 3)。
- 強制加算で、境界前の商 `q′ ≥ 2` なら `coordinates_forcedAddition_twoQuotient_historySearchProgress` により一歩以内に親下降(分岐 2)か軌道値下降(分岐 3)。
- 強制加算で `q′ = 1` の場合だけは、意図的にランクへ変換せず、そのままの証明データ(分岐 4)として次のエポックへ引き渡す。これが負債チャンバーである。
- 境界前に CoverageStep が得られていた場合は、目標出現(分岐 1)か親下降(分岐 2)。

### `qOneDebt_target_or_diagonalSuccessor` (L564)

**主張:** 商 1 の負債チャンバーの算術は完全に固定される。その前状態は対角状態 `a t = t` であり、目標の範囲は `m = t`(既に出現)または `m = t+1` かつ `n = t` に限られる。

**証明:** 一段借りが商 1 で起こる条件(`BorrowData.eq_one_iff`)は `r = 0` を強制し、借りの収支(`balance`)から着地剰余は `s = t` になる。したがって `a t = t·1 + 0 = t` で、着地レベルは `potential 1 t = t − 1` である。仮定 `potential 1 s < m` から `t ≤ m`、`m ≤ n+1 ≤ t+1` から `m ≤ t+1`。よって `m ∈ {t, t+1}` の二択で、`m = t` なら `a t = t = m` が目標の出現を直接与える。`m = t+1` なら `m ≤ n+1` と `n ≤ t` から `n = t` が従う。

### `DiagonalSuccessorProperty` (L598)

**定義:** 「すべての正の対角状態 `a t = t` について、その次の値 `t+1` が実軌道上のどこかに出現する」という命題。負エポックの解析で唯一残った履歴的命題を、この一点に分離して名付けたものである。

### `negative_epoch_historySearchOutcome` (L604)

**主張:** `DiagonalSuccessorProperty` を仮定すれば、負債チャンバーの例外分岐は消え、すべての負エポックは目標の出現・親下降・軌道値下降のいずれかで三成分探索を厳密に前進させる。

**証明:** `negative_epoch_historySearchOutcome_or_qOneDebt` の分岐 4 に `qOneDebt_target_or_diagonalSuccessor` を適用する。`m = t` なら出現。`m = t+1` の場合、仮定した対角性質が `a u = t+1 = m` の出現を直接与える。

## 全体の中での位置づけ

証明地図の「三成分履歴ランク」から「対角負債分岐」への橋であり、状況一覧の「履歴探索帰納」「高商障壁」行の中核をなす。`Undershoot`(非負帯有限化)と `Recovery` 系(負領域有限化)の軌道定理を消費し、`HistoryBudget` のランク補題へ変換する。ここで分離された `DiagonalSuccessorProperty` は `Diagonal` が極大後方減算鎖の解析で CoverageStep へ縮約し、さらに `PhaseSearch` / `PhaseEpoch` が四成分位相ランクを導入することで、この仮定自体をランクの厳密下降(debt 進入)に置き換える。`qOneDebt_target_or_diagonalSuccessor` は `PhaseEpoch.qOneDebt_target_or_phaseSearchProgress` から直接再利用される。
