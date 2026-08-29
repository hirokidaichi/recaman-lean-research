# CanonicalForcedGrowth

**役割:** 水準 1・2 の商 1 強制加算残余を統一チェンバーにまとめ、直後の状態では位相探索ランクが下がり得ないことを厳密に証明した上で、二段先読みにより必ず被覆へ回収できることを示す。

## このモジュールの役割

`CanonicalLevelOne`・`CanonicalLevelTwo` が残した二つの商 1 残余は同じ力学を持つ: 阻止された減算が加算を強制し、値は商 2・負ポテンシャルの状態へ成長する。成長した子は意味的不変量(proof-carrying な探索 domain の成員資格)を満たすにもかかわらず、履歴予算も旧 anchor も下がらないため、現在の 4 成分位相探索ランクの子にはなれない。本モジュールはこの「ランク閉包の反例」を一般形と具体例(目標 5)の両方で確定し、同時に、もう一段先の実遷移を見れば減算候補 `n + level` が目標以上かつ旧値未満の `CoverageStep`(被覆の一段証明)を必ず与えることを証明する。したがって新しい位相もランク成分も追加せず、二段先読みだけで残余は閉じる。

## 主要な定義

### `CanonicalForcedGrowthChamber` (L16)

二つの商 1 強制成長残余を水準 `level` で径数付けした統一の証明つき状態である。構成子 `forced` は `level = 1 ∨ level = 2`、canonical 証明書、現在値の初出、`target < a(orbitTime)`、値の等式 `a(orbitTime) = orbitTime + 1 + level`、`level < orbitTime + 1`、減算不可能性を保持する。水準 1 では `a(n) = n + 2`、水準 2 では `a(n) = n + 3` に対応する。

## 定理と証明

### `CanonicalLevelOneForcedQOneResidual.toForcedGrowthChamber` (L32)

**主張:** 水準 1 の残余は `level = 1` の統一チェンバーに変換できる。

**証明:** 残余の証拠(`a(n) = n + 2` など)を読み替えて `forced` に渡すだけである。

### `CanonicalLevelTwoForcedResidual.toForcedGrowthChamber` (L42)

**主張:** 水準 2 の残余は `level = 2` の統一チェンバーに変換できる。

**証明:** 同様の読み替えである。`level < orbitTime + 1` は near-target 条件と `2 < target` から従う。

### 補助補題 (L54, L62)

`forcedGrowth_natTripleLex_fst_le` (L54) は三成分辞書式下降の第一成分が非増加であること、`forcedGrowth_natQuadLex_tail_of_budgetEq` (L62) は四成分辞書式下降で第一成分が等しいとき残り三成分が下降することを言う private 補題である。

### `normal_anchorGrowth_budgetEq_no_phaseProgress` (L77)

**主張:** normal 同士のノードで、履歴予算(ランク第一成分)が等しく anchor(第二成分)が厳密に増えるとき、子から親への `PhaseSearchProgress` は成立しない。

**証明:** ランク下降があったと仮定する。第一成分が等しいので下降は残り三成分の辞書式下降に落ちる(L62 の補題)。その第一成分は anchor であり、辞書式下降からは `childAnchor ≤ parentAnchor` が従う(L54 の補題)。これは仮定 `parentAnchor < childAnchor` と矛盾する。

### `CanonicalForcedGrowthChamber.nextState` (L107)

**主張:** チェンバーの次の実状態は完全に決まっており、次をすべて満たす子 `child = ⟨n+1, a(n+1), normal, a(n+1)⟩` が存在する:

```text
a(n+1) = 2n + 2 + level,  CoordinatesAt (n+1) 2 level,  potential 2 level < 0,
a(n) < a(n+1),  missingBelowCount target (n+1) = missingBelowCount target n,
PhaseSemanticInvariant target child,  NormalPhaseInvariantAt target child (n+1) 2 level,
¬ PhaseSearchProgress target child parentNode
```

**証明:** 強制加算により `a(n+1) = a(n) + (n+1) = (n+1+level) + (n+1) = 2n + 2 + level = (n+1)·2 + level` であり、`level < n+1` から座標は正規の `(2, level)` になる。`potential 2 level = level − upperTri(2) = level − 3` は `level ∈ {1,2}` で負である。値は増加し、新値は `time_ready` から目標以上なので目標未満の新出値はなく、履歴予算は不変である。子は履歴からの初出証明で通常の意味的 normal ノードになるだけでなく、自分自身を anchor とすれば強い負normal不変量 `NormalPhaseInvariantAt` すら満たす。それでも `normal_anchorGrowth_budgetEq_no_phaseProgress`(予算不変・anchor 厳密増加)により、旧 canonical 親のランク子にはなれない。すなわち意味的には健全だがランク的には進捗にならない、という正確な障害の形が確定する。

### `CanonicalForcedGrowthChamber.twoStep_phaseSemantic` (L170)

**主張:** 即時のランク下降は不可能だが、もう一段先の実遷移まで見れば、目標の出現、または旧 canonical 親に対してランクを厳密に下げる意味的子ノードが必ず得られる。

**証明:** これが残余解消の核心である。強制状態 `a(n+1) = 2n + 2 + level` での次の減算候補は

```text
candidate = a(n+1) − (n+2) = n + level
```

である。canonical の near-target 条件(`n = target−1` または `n = target`)と `level ≥ 1` から `target ≤ candidate` が従い、他方 `candidate = n + level < n + 1 + level = a(n)` なので候補は旧 canonical 値よりちょうど 1 小さい。ここで時刻 `n+2` の遷移で場合分けする。

  - 減算が合法なら `a(n+2) = candidate` であり、合法減算の結果は fresh なので初出時刻 `n+2` を持つ。
  - 減算が阻止されるなら、候補は正(`target > 0` 以上)なので阻止の理由は既出しかなく、`candidate` は履歴の中に初出時刻を持つ。

どちらの場合も「`target ≤ candidate < a(n)` を満たす値とその初出」が得られ、これは旧 canonical 値 `a(n)` に対する `CoverageStep` である。よって `canonicalCoverage_phaseSemantic`(`CanonicalOracle`)により、目標の出現、またはランクを下げる意味的子ノードが従う。新しい位相もランク成分も不要で、必要なのはこの二段の先読みだけである。

### `canonicalForcedGrowth_five_realized` (L222)

**主張:** 水準 1 のチェンバーはインターフェース上の仮構ではない。実際の目標 5 の canonical 状態(時刻 5、`a(5) = 7`)がこれを実現する。

**証明:** `CanonicalLevelOne` の具体例 `canonicalLevelOne_forcedQOne_five` を変換するだけである。

### `canonicalForcedGrowth_five_immediate_not_progress` (L229)

**主張:** 目標 5 の実チェンバーにおいて、意味的不変量を満たすのに旧 canonical ノードのランク子にはならない子ノードが具体的に存在する。すなわちランク閉包への具体的反例である。

**証明:** `nextState` を目標 5 の実現に適用し、意味的健全性と進捗不成立の二成分を取り出す。

## 全体の中での位置づけ

証明地図の「canonical開始 — 強制成長も二段先の CoverageStep へ回収」に対応する。`CanonicalComplete` が残した `CanonicalForcedResidual` の二つの枝は本モジュールの統一チェンバーに合流し、`twoStep_phaseSemantic` が閉包を与える。この結果を公開 API に包み直すのが `CanonicalGrowthRecovery` である。また `nextState` と目標 5 の反例は、PROOF_MAP の「level 1/2 の強制加算直後は即時の PhaseSearchProgress にならない」という記述の形式的裏付けであり、ランク設計の限界を正直に記録する役割も持つ。
