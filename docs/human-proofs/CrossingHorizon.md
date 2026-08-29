# CrossingHorizon

**役割:** 履歴 horizon を進めながら debt から normal へ戻る遷移の位相ランク境界を、「履歴予算の厳密降下または anchor の厳密降下」という必要十分条件として確定する。

## このモジュールの役割

`CrossingGrowth` は horizon(履歴予算 `missingBelowCount` を評価する履歴時刻)を固定した場合の debt 脱出境界が anchor 降下と同値であることを示した。本モジュールはその一般化として、子節点の horizon を親より進める場合を扱う。horizon を進めることが意味的に正当なのは実際の軌道履歴を通じてだけであり、それが位相ランクに効くのは、追加の履歴が target 未満の未出値をちょうど消費するとき(履歴予算が真に減るとき)に限る — この直観を正確な同値定理の族として固定する。特に対角 crossing の catch-up 時刻へ horizon を更新しても予算分岐は開かないこと、逆に旧 horizon より後に target 未満の値が初出していれば予算分岐が開くことを、それぞれ証明する。

## 定理と証明

### `exitDebt_advancingHorizon_iff_budgetDrop_or_anchorDrop` (L20)

**主張:** `parentHorizon ≤ childHorizon` のとき、debt 親 `⟨parentHorizon, parentAnchor, debt, parentTime⟩` から normal 子 `⟨childHorizon, childAnchor, normal, childLocal⟩` への `PhaseSearchProgress` は、次と同値である: 履歴予算が真に減る(`missingBelowCount target childHorizon < missingBelowCount target parentHorizon`)、または予算が等しくかつ `childAnchor < parentAnchor`。

**証明:** 履歴予算は horizon について単調非増加(`missingBelowCount_antitone` — 履歴が増えても未出値の個数は増えない)なので、予算は「真に減る」か「等しい」かのちょうど二通りである。真に減れば辞書式順序の第一成分で進捗する(十分性の片側)。等しい場合、四成分辞書式順序の場合分けにより、第一成分では進捗できず、第三成分の位相ランクは `normal = 1 > 0 = debt` と逆向きで、第四成分にも到達できないから、進捗は第二成分 anchor の厳密降下と同値になる — これは固定 horizon の場合(`exitDebt_to_normal_iff_anchorDrop`)と同じ議論である。horizon の順序仮定が予算比較を排反な二分法に変えるところが、この同値の要である。

### `exitDebt_advancingHorizon_of_budgetDrop` (L67)

**主張:** 履歴予算の厳密降下は単独で位相の一段に十分であり、そのとき新しい normal 子の anchor と局所座標には何の制約もいらない。

**証明:** 辞書式順序の第一成分の厳密降下がそのまま `PhaseSearchProgress` である。1 行の補題だが、「予算が減るなら子は自由に選べる」という探索設計上の自由度を明示する。

### `exitDebt_anchorGrowth_iff_budgetDrop` (L79)

**主張:** さらに `parentAnchor ≤ childAnchor`(anchor が降下しない)と仮定すると、遷移の成立は履歴予算の厳密降下と同値になる。すなわち anchor 成長分岐では予算消費は十分条件であるだけでなく必要条件である。

**証明:** 前の同値定理で右辺の第二選択肢(予算等号 + anchor 降下)が仮定 `parentAnchor ≤ childAnchor` と矛盾して消えるので、予算降下だけが残る。

### `diagonalCrossingCatchup_exitDebt_iff_anchorDrop` (L99)

**主張:** 対角 crossing の catch-up 状態(目標 `horizon + 1`)に対し、子の horizon を catch-up 時刻 `catchTime` へ更新しても予算分岐は開かない。この遷移の進捗境界は依然としてちょうど `childAnchor < parentAnchor` である。

**証明:** `catchTime` は `horizon` または `horizon + 1` なので `horizon ≤ catchTime` であり、一般同値定理が適用できる。鍵は `BoundaryAudit` の監査定理 `diagonalCrossingCatchup_budget_eq_horizon`: catch-up までの一歩で新たに見える値は target 以上なので、`missingBelowCount (horizon+1) catchTime = missingBelowCount (horizon+1) horizon` が成り立つ。予算が等しい以上、同値の右辺は anchor 降下だけに簡約される。

### `diagonalCrossingCatchup_anchorGrowth_no_progress` (L117)

**主張:** したがって `parentAnchor ≤ childAnchor` の(anchor が成長する)場合、catch-up horizon への更新では進捗は不可能である。すなわち実際の catch-up horizon は `CrossingGrowth` の joint-growth 障害を閉じない。

**証明:** 前定理の同値に anchor の仮定を代入するだけである。horizon 更新という「見かけの前進」がランク上は無力であることの確定であり、`CrossingIteration` 以降で frontier 由来の新情報が必要になる理由を与える。

### `exitDebt_at_laterEpoch_of_newFirstBelowTarget` (L133)

**主張:** 後のエポック時刻 `epochTime` が、旧 horizon より真に後に初出した target 未満の値 `g`(`g < target`、`parentHorizon < firstTime ≤ epochTime`、`FirstAt a g firstTime`)を含むなら、`⟨epochTime, childAnchor, normal, childLocal⟩` への遷移は無条件に `PhaseSearchProgress` である。

**証明:** 初出補題 `missingBelowCount_strict_of_firstAt` により、`firstTime` の時点で履歴予算は旧 horizon の値より真に小さい。予算の単調性で `epochTime` まで運べば `missingBelowCount target epochTime < missingBelowCount target parentHorizon` となり、`exitDebt_advancingHorizon_of_budgetDrop` が適用できる。これが「予算を第一ランク成分として使うための標準的な十分条件」である。

### `exitDebt_at_laterEpoch_anchorGrowth_iff` (L152)

**主張:** anchor 成長分岐における後のエポックでの正確な残余義務: `parentHorizon ≤ epochTime` かつ `parentAnchor ≤ childAnchor` のとき、遷移が成立することと、拡張された実履歴が予算を真に下げることは同値である。

**証明:** `exitDebt_anchorGrowth_iff_budgetDrop` の epoch 時刻への言い換えそのものである。この定理が、joint-growth 状況で残る証明義務を「後の実履歴に target 未満の新しい初出があるか」という一点に還元する。

## 全体の中での位置づけ

証明地図の「負債局所解析」層に属し、`BoundaryAudit` の監査結果を入力として、`CrossingGrowth` の固定 horizon 境界を advancing-horizon の場合へ拡張する。他モジュールから直接 import はされないが、ここで確定した「budget drop ∨ anchor drop」の必要十分境界は、`CrossingFrontier` の horizon-safe exit(`phaseSearch_exitDebt_of_extendedHorizonAndAnchor`)や、後の `CrossingRefinedBoundary`・`CrossingDowncrossRefined` における「非 crossing 子には strict budget drop が必須」という境界解析の概念的な基準線である。
