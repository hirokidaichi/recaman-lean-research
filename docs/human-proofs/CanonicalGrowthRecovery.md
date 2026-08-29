# CanonicalGrowthRecovery

**役割:** 強制成長チェンバーの二段先読み閉包を公開 API に包み直し、canonical開始点に対する完全な局所オラクル定理 `targetStartInvariant_phaseSemanticStep` を完成させる。

## このモジュールの役割

`CanonicalComplete` は canonical開始点の未解決部分を水準 1・2 の強制加算残余 `CanonicalForcedResidual` に絞り、`CanonicalForcedGrowth` はその統一チェンバーが二段先読みで必ず `CoverageStep` に到達することを示した。本モジュールはこの二つを接続する薄い層である。各残余を個別に閉じる定理を用意し、直和を場合分けで束ね、最終的に「すべての canonical開始点は、目標の出現、または位相探索ランクを厳密に下げる意味的子ノードを持つ」という無条件の局所オラクル定理を与える。これが証明地図の「canonical局所オラクル」段の完成形である。

## 定理と証明

### `canonicalLevelOneForcedQOne_phaseSemanticStep` (L16)

**主張:** 水準 1 の商 1 強制残余 `CanonicalLevelOneForcedQOneResidual` は、目標の出現、またはランクを厳密に下げる意味的子ノードを与える。

**証明:** 残余を統一チェンバーへ変換し(`toForcedGrowthChamber`)、`CanonicalForcedGrowthChamber.twoStep_phaseSemantic` の二段先読みを適用する。強制加算の一段先で現れる減算候補 `n + level` が目標以上かつ旧 canonical 値未満の被覆候補になる、という機構である。

### `canonicalLevelTwoForced_phaseSemanticStep` (L26)

**主張:** 水準 2 の強制残余 `CanonicalLevelTwoForcedResidual` も同じ結論を満たす。

**証明:** 同じ二段機構である。変換して `twoStep_phaseSemantic` を適用する。

### `canonicalForcedResidual_phaseSemanticStep` (L37)

**主張:** 統合残余 `CanonicalForcedResidual` は既存の意味的 domain の中で完全に解消される。新しい探索位相もランク成分も必要ない。

**証明:** 直和の場合分けであり、`level_one` 枝は L16 の定理、`level_two` 枝は L26 の定理に委ねる。

### `targetStartInvariant_phaseSemanticStep` (L53)

**主張:** 正の目標 `target` に対し、canonical開始不変量 `TargetStartInvariant target parent` を満たす任意のノード `parent` は、

```text
(∃ witness, a(witness) = target)  ∨
(∃ child, PhaseSemanticInvariant target child ∧ PhaseSearchProgress target child parent)
```

を満たす。すなわち canonical開始点に対する局所オラクル(「目標到達または真に小さい次ノードの構成」という証明義務)は、すべての符号領域・すべてのポテンシャル水準で無条件に成立する。

**証明:** `CanonicalComplete` の分類定理 `targetStartInvariant_phaseSemanticStep_or_forced` を適用する。第一枝(目標出現)と第二枝(意味的ランク子)はそのまま結論である。第三枝の強制残余は `canonicalForcedResidual_phaseSemanticStep` により第一・第二枝のいずれかへ解消される。

まとめると、canonical開始点の解析は次の一枚の場合分けに集約される: 負ポテンシャルは負normal オラクル、目標以上のポテンシャルは即時被覆、水準 3 以上のアンダーシュートは非負エポックの履歴フロンティア、水準 0 は後継境界を経て二歩で目標出現、水準 1・2 の合法減算・商 2 以上の強制加算は一段で閉じ、最後に残る商 1 の強制成長も二段先読みの被覆で閉じる。

## 全体の中での位置づけ

証明地図の「canonical開始 — 局所閉包済み」を宣言するモジュールである。`CanonicalOracle` から始まる canonical 系列(`CanonicalLevelZero`・`CanonicalLevelOne`・`CanonicalLevelTwo`・`CanonicalComplete`・`CanonicalForcedGrowth`)の最終出力であり、`Recaman.lean` 経由でプロジェクト全体に公開される。位相探索(`PhaseSearch`)の整礎停止証明と組み合わせると、「canonical開始点から探索を始める限り、最初の一歩は常に供給できる」ことになる。残る未証明部分は、canonical開始点以外の一般の到達可能ノード(provenance 付き normal domain、crossing など)に対する同種の局所 step であり、それは `NormalProvenance` 以降のモジュール群が扱う。
