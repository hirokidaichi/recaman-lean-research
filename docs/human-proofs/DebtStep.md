# DebtStep

**役割:** 有効なdebtノードの一歩を完全分類し、ランク下降しない残余を三種類の明示的なcrossing(障害)として切り出す。

## このモジュールの役割

`DebtInvariant`が与える強い不変量のもとで、debtノードから一歩進むと何が起こり得るかを余すところなく分類するのが本モジュールである。結論は帰納型 `DebtStepOutcome` にまとめられ、「目標出現」「通常位相への復帰」「debt継続」の三つのランク下降的な結果か、さもなければ `DebtStepObstruction` として明示された三種類の障害(いずれも目標をまたぐ、または境界に達する配置)に必ず落ちる。あわせて、debtの処理中には履歴予算(`missingBelowCount`: horizonまでに未出である`target`未満の値の個数)成分を下降させられないという二つの否定的事実も証明し、ランク下降が他の成分に頼らざるを得ないことを明確にする。

## 主要な定義

### `DebtStepObstruction` (L12)

現在のdebt不変量では解消できない配置を、証拠付きで列挙した帰納型。三つの構成子を持つ。

- `legal_reaches_anchor`: 最終遷移が合法減算だが、先行値が `anchor ≤ a(n)` と固定anchorに達してしまう場合。debt継続に必要な「anchor未満」が失われる。
- `addition_nonpositive`: 最終遷移が強制加算で、先行値が目標未満(`a(n) < target`)、かつ減算候補が非正(`a(n) ≤ n+1`)の場合。取り出すべき先行候補が存在しない。
- `addition_seen_below_target`: 最終遷移が強制加算で先行値が目標未満、減算候補 `x = a(n) − (n+1)` は正で既出、その初出時刻はdebt時刻より早いが、`x < target` かつ `x`はhorizon履歴にすでに含まれる場合。候補は目標下界を満たさず、履歴予算も減らせない。

後二者は、まさに目標を下から上へまたぐ強制加算(crossing)の周辺で生じる。

### `DebtStepOutcome` (L48)

一歩の結果の帰納型。`target_occurs`(目標の出現証人)、`exit_normal`(初出値を新anchorとする通常ノードへの`PhaseSearchProgress`付き復帰)、`continue_debt`(強い不変量を保ったままdebt時刻を下げる継続)、`crossing`(上記障害)の四構成子から成る。

## 定理と証明

### `debt_earlier_firstAt_mem_horizon` (L78)

**主張:** debtが保持する、より早い初出値(`fx < firstTime < horizon`)は、固定horizonの履歴 `valuesThrough horizon` にすでに含まれる。したがってその値はhorizon時点で新たに消費される未出値ではない。

**証明:** 初出時刻`fx`は`horizon`以下なので、履歴所属の特徴づけ(`mem_valuesThrough_iff`)から直ちに従う。

### `debt_fixed_horizon_has_no_budget_drop` (L89)

**主張:** debtのhorizonを固定したままでは、履歴予算成分 `missingBelowCount target horizon` は自分自身より小さくなれない(自明な非反射性)。

**証明:** `<`の非反射性そのものである。自明だが、「horizon固定のdebt処理では第一成分は動かない」という設計上の事実を明文化する。

### `debt_earlier_horizon_cannot_drop_budget` (L97)

**主張:** horizonを取り出した早い時刻`earlierTime ≤ horizon`に付け替えても、履歴予算は下がらない。早い時刻の未出数は同じか多いだけである。

**証明:** `missingBelowCount`は時刻に関して反単調(履歴が増えると未出数は増えない)なので、`missingBelowCount target horizon ≤ missingBelowCount target earlierTime` となり、狭義の逆向き不等式はあり得ない。二つの否定的補題を合わせると、debt処理のランク下降は履歴予算では実現できず、anchor・位相・debt時刻の下位成分で実現するしかないと分かる。

### `debtStep_classify` (L108)

**主張:** 目標が正で、`DebtInvariant target ⟨horizon, anchor, debt, firstTime⟩ value firstTime` が成り立つならば、`DebtStepOutcome`のいずれかが成立する。すなわち、目標が出現するか、ランク下降的に通常復帰またはdebt継続ができるか、三種類の明示的crossingのいずれかが起きている。

**証明:** まず `target = value` なら初出時刻`firstTime`が目標出現の証人である(`target_occurs`)。以下 `target < value` とする。目標が正なので`firstTime`は正であり(`debt_firstTime_pos`)、`firstTime = n+1` と書ける。初出の最終遷移(`firstAt_succ_transition`)で場合分けする。

*合法減算の場合。* 先行値 `a(n)` はより早い初出時刻を持ち `value < a(n)` である(`debt_legalSubtraction_earlierPredecessor`)。`a(n) < anchor` ならば不変量が先行値へ引き継がれ(`debt_legalSubtraction_preservesInvariant`)、debt時刻下降付きの `continue_debt`。そうでなければ先行値がanchorに達しており、`legal_reaches_anchor` のcrossingである。

*強制加算の場合。* 先行値は自動的に `a(n) < anchor` を満たす(`debt_forcedAddition_predecessor`)。目標との比較で二分する。

- `target ≤ a(n)` なら、先行値を新anchorとする通常復帰がanchor下降のランク進捗になる(`debt_forcedAddition_exitProgress`)ので `exit_normal`。
- `a(n) < target` なら、この強制加算は目標を下から上へまたいでいる。減算候補の二分法(`firstAt_forcedAddition_dichotomy`、`DebtAddition`参照)により、候補が非正なら `addition_nonpositive`。候補 `x = a(n) − (n+1)` が正で既出なら、`x < a(n) < target` より候補は目標未満で、初出時刻 `fx < firstTime < horizon` から `x` はhorizon履歴に含まれる(`debt_earlier_firstAt_mem_horizon`)。これは `addition_seen_below_target` のcrossingである。

いずれの枝も網羅されているので分類は完全である。

## 全体の中での位置づけ

証明地図の「負債・crossing閉包」段階の中心的な分類定理を提供する。`debtStep_classify`が切り出した三つの障害のうち、目標をまたぐ強制加算は`DebtCrossing`でさらに解析され、anchor境界は`DebtBackward`と`AnchorBoundary`で解消される。本モジュールは`HistoricalDebtBridge`から直接importされ、そこでは`exit_normal`構成子を使わない強化版 `debtStep_classify_without_normalExit` が同じ場合分けの骨格の上に構築される。二つの予算否定補題は、後の`CrossingRefinedBoundary`などで「非crossing子には履歴予算の狭義下降が必須」という境界定理群が現れる伏線でもある。
