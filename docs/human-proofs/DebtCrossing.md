# DebtCrossing

**役割:** 目標を下から上へ厳密にまたぐ強制加算(crossing)を定義し、既存の着地機構では処理できないこと、履歴予算を動かさないこと、しかし形式的なanchor下降のランク進捗は与えることを証明する。

## このモジュールの役割

`DebtStep`の分類が残す最も手強い障害は、直前値が目標未満なのに、強制加算の着地値が目標を超えて初出する配置である。本モジュールはこれを `DebtCrossing` として定義し、まず否定的な事実を積み上げる: この配置は目標方程式・目標面・完全ゲートのいずれの着地機構にも乗らず、履歴予算(`missingBelowCount`)も変化させない。次に肯定的な事実として、直前値が固定anchorより必ず小さいことから、形式的には位相ランクを下げてdebtを脱出できることを示す。ただしその着地先の値は目標未満であり、通常探索の下界不変量を破る — この「ランクは下がるが意味的不変量が壊れる」緊張関係が、後のcrossing recovery系モジュール群の出発点になる。最後に、crossingが起きても目標が既出とは限らないことを実軌道の反例で確定する。

## 主要な定義

### `DebtCrossing` (L8)

`DebtCrossing target value n` は、時刻`n+1`の強制加算が目標を厳密にまたぐこと:

`a(n) < target ∧ target < value ∧ value = a(n) + (n+1)`

を表す。ジャンプの幅は `n+1` であり、目標はその内部に真に含まれる。

## 定理と証明

### `debtCrossing_not_targetEquation` (L14)

**主張:** 厳密なcrossingの着地点を起点とする目標方程式 `TargetEquation (n+1) value target k`(`target + descentDrop(n+1, k) = value`、すなわち`k`回の予定減算で`value`から`target`へ着地する算術条件)は、どの歩数`k`でも成り立たない。

**証明:** `k = 0` なら `target = value` となり `target < value` に矛盾。`k ≥ 1` なら、予定減算1回分だけでも `descentDrop(n+1, 1) = n+2` を取り除くが、着地点から直前値までの全ギャップは `value − a(n) = n+1` しかない。したがって `target = value − descentDrop ≤ value − (n+2) = a(n) − 1 < a(n)` となり、`a(n) < target` に矛盾する。一回の減算が、またいだ距離全体よりすでに大きいのである。

### `debtCrossing_not_targetSurface` (L35)

**主張:** 着地状態のどんな商・剰余表示 `QuotRem (n+1) value q r` についても、ポテンシャル `G(q,r) = r − U(q)` が目標に等しい(目標面に乗る)ことはない。

**証明:** 目標面の等式は目標方程式に翻訳できる(`targetEquation_of_quotRem_potential`)ので、前定理に帰着する。

### `debtCrossing_not_exactGate_post` (L46)

**主張:** 着地値が完全ゲート(二連続減算で目標へ正確に着地する配置)の値 `2(n+1) + target + 3` になることもない。

**証明:** `value = a(n) + (n+1)` をゲート値の等式に代入すると `a(n) = n + target + 4 > target` となり、`a(n) < target` に矛盾する。

### `debtCrossing_not_exactGate_pre` (L55)

**主張:** 目標未満の直前値がゲート値 `2n + target + 3` を取ることもない。

**証明:** ゲート値は明らかに`target`以上なので `a(n) < target` に矛盾する。

### `missingBelowCount_succ_of_new_ge` (L64)

**主張:** 時刻`n+1`に加わる値が `target ≤ a(n+1)` を満たすなら、`missingBelowCount target (n+1) = missingBelowCount target n`。目標以上の値の追加は、`target`未満の未出スロットを一つも埋めない。

**証明:** `target`に関する帰納法。各スロット `t < target` について、新しい履歴は `a(n+1)` を先頭に足しただけであり、`t ≠ a(n+1)`(`t < target ≤ a(n+1)`)なので`t`の所属は変わらない。よって各段の指示関数が保たれ、総和も等しい。

### `debtCrossing_budget_unchanged` (L82)

**主張:** 厳密なcrossingは履歴予算成分を変えない。

**証明:** 着地値は初出だから `a(n+1) = value > target`。前補題を適用する。`DebtStep`の否定補題と合わせ、crossingでは四成分ランクの第一成分による進捗が原理的に不可能であることが確定する。

### `debtCrossing_phaseProgress` (L95)

**主張:** 有効なdebtノードで時刻`n+1`の遷移が強制加算であり直前値が目標未満なら、直前値を新anchorとする通常ノード `⟨horizon, a(n), normal, a(n)⟩` への形式的な `PhaseSearchProgress` が成り立つ。

**証明:** 強制加算より `a(n) < value` であり、debt不変量の `value < anchorParent` と合わせて `a(n) < anchor`。よってanchor成分の狭義下降でdebtを脱出できる(`phaseSearch_exitDebt_of_anchorDrop`)。ただしこれは純粋にランクに関する事実である。着地先のanchor `a(n)` は目標未満なので、通常探索が保つべき下界不変量 `target ≤ anchor` は成り立たない。

### `debt_forcedAddition_crossing_outcome` (L115)

**主張:** 直前値が目標未満の強制加算(弱いcrossing)の完全な結果: 着地値が目標に等しければその初出時刻が目標出現を証言し、目標が真に内部にあれば前定理の形式的ランク進捗が無条件に成り立つ。

**証明:** debt不変量の `target ≤ value` を等号か狭義かで分けるだけである。

### `debtCrossing_occursBefore_or_phaseProgress` (L135)

**主張:** 厳密なcrossingの枝で現在得られる最強の無条件結論: 目標がすでに時刻`n`までに出現しているか、または形式的なanchor下降のランク進捗が取れる。

**証明:** `target ∈ valuesThrough n` の決定可能な場合分け。既出なら出現時刻を取り出し、未出なら`debtCrossing_phaseProgress`を使う。

### `debtCrossing_four_local_counterexample` (L154)

**主張:** 「crossingが起きれば目標は既出」という強い主張は偽である。実軌道の時刻3の遷移は `a(2) = 3` から `a(3) = 6` へ目標`4`をまたぐが、`4`は時刻3までの完全な履歴 `{0, 1, 3, 6}` に現れない。しかもこの配置は `DebtInvariant 4 ⟨4, 7, debt, 3⟩ 6 3` を満たす正真正銘のdebt状態である。

**証明:** すべての数値事実(`a(3) = 6`、時刻0〜2に6が出ないこと、減算不可能性、各不等式)を`decide`でカーネル検証する。

## 全体の中での位置づけ

証明地図の「負債・crossing閉包」段階の核心であり、`DebtInvariant`と`PrestateCoverage`をimportし、`CrossingRecovery`から直接importされる。本モジュールの否定的結果群は、crossingを既存の着地・予算機構で処理する道をすべて塞ぎ、`debtCrossing_phaseProgress`の「ランクは下がるが下界が壊れる」出口だけを残す。この出口を意味的に修復する仕事 — pre-crossing値を新anchorとするcrossing recovery(用語集参照)の構築 — が、`CrossingRecovery`から`CrossingTailRefined`に至る後続モジュール群の主題である。
