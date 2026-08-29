# CanonicalLevelOne

**役割:** canonical開始点のポテンシャル水準 1 の残余を一段の実遷移で解析し、閉じ残る状態を「商 1・`a(n) = n + 2`・減算候補 1 が既出」という強制加算チェンバーただ一つに固定する。

## このモジュールの役割

`CanonicalOracle` が切り出した低水準残余のうち、ポテンシャル水準 1(`potential q r = 1`)を扱う。次の一歩が合法減算なら直ちに閉じ、強制加算でも商が 2 以上なら二段先の履歴フロンティアで閉じることを示す。唯一閉じないのは商 1 の場合であり、そのとき算術は完全に固定される: `r = 2`、`a(n) = n + 2`、減算候補は `1` で、`1 = a(1)` はすでに履歴にあるため加算が強制される。この正確な残余状態 `CanonicalLevelOneForcedQOneResidual` は後段の `CanonicalForcedGrowth` が引き受ける。また目標 5 で実際にこの残余が実現されることも検証する。

## 主要な定義

### `CanonicalLevelOneForcedQOneResidual` (L8)

水準 1 でランクに直接見える分岐をすべて除去した後に残る正確な状態である。構成子 `forced` は、canonical 証明書、現在値の初出時刻、`target < a(orbitTime)`、`2 < orbitTime`、値の等式 `a(orbitTime) = orbitTime + 2`、near-target 条件(`orbitTime = target − 1` または `target`)、減算候補の等式 `a(orbitTime) − (orbitTime + 1) = 1`、`1 ∈ valuesThrough orbitTime`、そして減算不可能性 `¬CanSubtract` を保持する。

## 定理と証明

### `canonical_legalSubtraction_phaseSemantic` (L29)

**主張:** `target < a(n)` の canonical 状態で次の減算が合法なら、目標の出現、または位相探索ランクを厳密に下げる意味的 normal 子ノードが得られる。

**証明:** 合法減算により `a(n+1) = a(n) − (n+1) < a(n)` である。三つの場合に分ける。

  - `a(n+1) = target` ならば目標が出現する。
  - `target ≤ a(n+1)` ならば、合法減算の結果は fresh(その値の初出が時刻 `n+1`)である。子 `⟨n+1, a(n+1), normal, a(n+1)⟩` は normal 証明書を満たし、horizon 前進と anchor の厳密下降によりランクが下がる。
  - `a(n+1) < target` ならば軌道は目標水準を下方横断した。下方横断定理 `orbit_downcrossing_occurs_or_budgetDrop` により、目標が実際に出現するか、履歴予算 `missingBelowCount`(目標未満の未出値数)が厳密に減る。後者では旧値 `a(n)` を新 horizon `n+1` で再利用した子を作り、ランクは第一成分で下がる。

### `canonical_forcedAddition_twoQuotient_phaseSemantic` (L67)

**主張:** canonical な above-target 状態(`target ≤ n+1`、`target < a(n)`)で減算が阻止され、かつ商が `q ≥ 2` ならば、目標の出現またはランクを下げる意味的子ノードが得られる。

**証明:** 商 2 以上の強制加算に対する二段履歴フロンティア定理 `coordinates_forcedAddition_twoQuotient_historySearchProgress` を適用する。二つの結果がある。

*blocker 枝。* `target ≤ y < a(n)` を満たす値 `y` と初出時刻 `fy` が得られる(blocker とは、減算先が既出のため下降を止める値のこと)。子 `⟨max(n+2, fy), y, normal, y⟩` を作れば、horizon は前進し anchor は厳密に下がるのでランクが低下する。horizon に `max` を使うのは初出時刻を確実に含めるためである。

*生の前進枝。* 二歩先の状態 `⟨n+2, a(n), normal, a(n+2)⟩` へのランク下降(anchor は旧値のまま)が得られる。ここで `a(n+2)` の位置で場合分けする。

  - `target ≤ a(n+2)` のとき、`NonnegativeSemantic` の再anchor定理 `normalProgress_reanchorAtValue` により、anchor を子自身の値 `a(n+2)` に付け替えてもランク下降が保たれる。履歴から初出を取れば normal 証明書も立つ。
  - `a(n+2) < target` のとき下方横断であり、目標の出現、または履歴予算の厳密下降が従う。後者では旧値 `a(n)` を horizon `n+2` で再利用する。

### `canonicalLowLevel_levelOne_phaseSemantic_or_forcedQOne` (L119)

**主張:** 水準 1 の canonical 残余(`potential q r = 1`、`q > 0`、`target < a(n)`)は、(1) 目標の出現、(2) ランクを下げる意味的子ノード、(3) `CanonicalLevelOneForcedQOneResidual` のいずれかに帰着する。

**証明:** 次の一歩で場合分けする。減算が合法なら `canonical_legalSubtraction_phaseSemantic` で (1) または (2)。減算が阻止され `q ≥ 2` なら `canonical_forcedAddition_twoQuotient_phaseSemantic` で (1) または (2)。

残るのは減算阻止かつ `q = 1` の場合である。このとき算術がすべて固定される: `potential 1 r = r − upperTri(1) = r − 1 = 1` から `r = 2`。剰余条件 `r < n` から `2 < n`。座標方程式から `a(n) = n + 2`。したがって減算候補は `a(n) − (n+1) = 1` であり、`1 = a(1)` は `n ≥ 1` の履歴に必ず含まれる。これらの証拠一式を `forced` に詰めて (3) とする。

### `canonicalLevelOne_forcedQOne_five` (L168)

**主張:** この残余状態は現実に到達される。目標 5 の canonical 開始は時刻 5 で `a(5) = 7`、商 1・剰余 2(水準 1)であり、減算候補 1 は既出なので時刻 6 の遷移は強制加算になる。

**証明:** `a(5) = 7` の初出が時刻 5 であることを含め、必要な有限事実をすべて `decide`(Leanカーネルの計算検証)で確認し、`forced` を具体的に構成する。

## 全体の中での位置づけ

証明地図の「canonical開始 — 局所閉包」の水準 1 担当である。本モジュールの主定理は `CanonicalComplete` の統合分類で使われ、残余 `CanonicalLevelOneForcedQOneResidual` は `CanonicalForcedGrowth` の統一チェンバー(`toForcedGrowthChamber`)へ変換されて、二段先読みによる被覆(`CanonicalGrowthRecovery`)で最終的に閉じられる。また本モジュールは `NonnegativeSemantic` の再anchor定理を輸入しており、非負意味論との接続点でもある。
