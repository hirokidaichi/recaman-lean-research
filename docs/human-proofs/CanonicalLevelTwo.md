# CanonicalLevelTwo

**役割:** canonical開始点のポテンシャル水準 2 の残余を一段の実遷移で解析し、閉じ残る状態を「商 1・`a(n) = n + 3`・減算候補 2 が既出」という強制加算チェンバーに固定し、その次状態の剛性(成長・負ポテンシャル・履歴予算不変)も証明する。

## このモジュールの役割

`CanonicalOracle` が切り出した低水準残余のうち、ポテンシャル水準 2(`potential q r = 2`)を扱う。合法減算の枝は被覆または履歴予算下降で閉じ、商 2 以上の強制加算の枝は減算候補自身が目標以上の既出値(blocker)になることを算術評価で示して被覆に落とす。唯一残るのは商 1 の強制加算であり、そのとき `r = 3`、`a(n) = n + 3`、候補は `2 = a(4)` で既出になる。さらに、この残余の次の実状態が座標 `(2,2)`・負ポテンシャルへと厳密に成長し、履歴予算を消費しないことを示して、「通常の下降 normal 子として黙って扱うことはできない」構造的理由を明示する。

## 主要な定義

### `CanonicalLevelTwoForcedResidual` (L15)

水準 2 で最初の実遷移により閉じられなかった正確な境界である。構成子 `forced` は、canonical 証明書、座標 `CoordinatesAt orbitTime 1 remainder`、`potential 1 remainder = 2`、減算不可能性、`remainder = 3`、値の等式 `a(orbitTime) = orbitTime + 3`、阻止された候補 `2 ∈ valuesThrough orbitTime`、`2` の初出が時刻 4 であること(`FirstAt a 2 4`)、`4 ≤ orbitTime`、`2 < target` を保持する。

## 定理と証明

### 補助補題 `canonicalLevelTwo_firstAt_two` (L5)

`FirstAt a 2 4`、すなわち値 2 の初出時刻が 4 であることを有限検査(`decide`)で確かめる private 補題である(実際 `a(0..4) = 0,1,3,6,2`)。残余の構成と時刻下界 `4 ≤ n` の導出に使う。

### `CanonicalLevelTwoForcedResidual.growth_negative` (L39)

**主張:** 残余の次の実状態は完全に剛的である。すなわちある `n` について `parent = targetStartNode n` であり、

```text
a(n+1) = 2n + 4,  CoordinatesAt (n+1) 2 2,  potential 2 2 < 0,
a(n) < a(n+1),  missingBelowCount target (n+1) = missingBelowCount target n
```

がすべて成り立つ。

**証明:** 減算が阻止されているので強制加算で `a(n+1) = a(n) + (n+1) = (n+3) + (n+1) = 2n + 4` となる。これは `(n+1)·2 + 2` なので座標は `(2,2)` であり、`potential 2 2 = 2 − upperTri(2) = 2 − 3 = −1 < 0`。値は明らかに増加する。新しい値は証明書の `time_ready` から `target ≤ a(n+1)` を満たすため、目標未満の新しい値は現れず、履歴予算 `missingBelowCount`(目標未満の未出値数)は変化しない。この「anchor が増え、予算も減らない」という組合せが、位相探索ランクをそのままでは下げられない理由である。

### `canonicalLevelTwo_phaseSemanticStep_or_forcedQOne` (L70)

**主張:** 水準 2 の canonical 残余(`potential q r = 2`、`q > 0`、`target < a(n)`、`2 < target`)は、(1) 目標の出現、(2) 位相探索ランクを厳密に下げる意味的子ノード、(3) `CanonicalLevelTwoForcedResidual` のいずれかに帰着する。

**証明:** ポテンシャル等式から `r = upperTri(q) + 2` である。次の一歩で場合分けする。

*合法減算の場合。* `a(n+1) = a(n) − (n+1) < a(n)` は fresh である。
  - `target ≤ a(n+1)` ならば、これは `target ≤ y < a(n)` の値とその初出を与えるので `CoverageStep`(被覆の一段証明)になり、`canonicalCoverage_phaseSemantic` で (1) または (2)。
  - `a(n+1) < target` ならば下方横断であり、`orbit_downcrossing_occurs_or_budgetDrop` により目標出現か履歴予算の厳密下降。後者では旧値 `a(n)` を horizon `n+1` で再利用した子でランクが第一成分で下がる。

*強制加算・`q = 1` の場合。* `r = upperTri(1) + 2 = 3`、座標方程式から `a(n) = n + 3`、減算候補は `a(n) − (n+1) = 2`。候補は正なので阻止の理由は既出しかなく `2 ∈ valuesThrough n`。値 2 の初出は時刻 4 だから(補助補題)、2 が履歴に入っている以上 `n ≥ 4` である。証拠一式を `forced` に詰めて (3)。

*強制加算・`q ≥ 2` の場合。* 候補 `y = a(n) − (n+1)` を評価する。`upperTri(q) ≥ 3` から `r ≥ 5`、座標方程式と `q ≥ 2` から `a(n) ≥ 2n + 5`、よって `y ≥ n + 4`。一方 near-target 条件から `n ≥ target − 1`、したがって `y ≥ target` である。候補は正なので阻止の理由は既出であり、`y` は履歴から初出時刻を持つ。`y < a(n)` と合わせてこれは `CoverageStep` の blocker 枝そのものであり、`canonicalCoverage_phaseSemantic` で (1) または (2) に落ちる。

## 全体の中での位置づけ

証明地図の「canonical開始 — 局所閉包」の水準 2 担当である。主分類定理は `CanonicalComplete` の統合で使われ、残余 `CanonicalLevelTwoForcedResidual` は `CanonicalForcedGrowth` の統一チェンバーへ変換される。`growth_negative` は、`CanonicalForcedGrowth` の一般定理 `nextState`(即時ランク下降の不可能性)の水準 2 版の予告に当たり、なぜ二段先読み(`CanonicalGrowthRecovery`)が必要かを実軌道の言葉で説明する。
