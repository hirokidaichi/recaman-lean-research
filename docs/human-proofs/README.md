# 人間向け証明の欠落状況 — 洗い出しレポート

**調査基準日時:** 2026-08-29 08:50 JST
**対象:** `Recaman/` 配下の全 Lean モジュール(基準時点で 92 ファイル、19,981 行、定理・補題 704 件、定義 178 件)

> **注意:** 本リポジトリは自律研究ループにより現在も活発に更新されている
> (基準日時直前にも新規コミットと新規モジュール `PermanentAboveCycleExit` の追加を確認)。
> 本レポートの行数・件数は基準時点のスナップショットである。
> ビューワーの表示と `viewer/manifest.json` は `python3 viewer/gen_manifest.py` の再実行で最新化できる。

## 1. 調査の目的と方法

このプロジェクトの証明はすべて Lean 4 で機械検証されているが、
**Lean を読めない人間がその証明の数学的内容を理解できるドキュメント**
(いわゆる「人間向け証明」= 論文スタイルの自然言語による証明)が
どの程度整備されているかを調査した。判定基準は次の3段階。

1. **日本語の人間向け証明ドキュメント** — モジュール単位で、各定理の主張と
   証明の筋道を自然言語で説明したもの(`docs/human-proofs/<Module>.md`)
2. **英語のモジュール docstring** — Lean ファイル冒頭の `/-! ... -/`。
   数段落の要約であり、個々の定理の証明は説明しない
3. **なし** — ファイル内はコードと定理単位の短い英語コメントのみ

## 2. 調査結果(基準時点)

| 項目 | 件数 |
|---|---:|
| Lean モジュール総数 | 92 |
| 日本語の人間向け証明があるモジュール | **0(全滅)** |
| 英語の短いモジュール docstring があるモジュール | 41 |
| モジュール説明が一切ないモジュール | 51 |
| Lean ソース中の日本語コメント行 | 0 行 |

つまり、**92 モジュールすべてが「人間向けの証明」を欠いていた。**

`docs/` 配下には日本語の全体文書(`RESEARCH_REPORT.md`、`PROOF_MAP.md`、
`GLOSSARY.md` など)が存在するが、これらはプロジェクト全体の戦略・状況を
俯瞰するものであり、**個々のモジュール・定理レベルの証明の説明は含まれない**。
英語 docstring がある 41 モジュールも、記述は「何を示すか」の要約にとどまり、
「なぜ成り立つか」(証明の議論)は Lean のタクティク列を読み解くしかない状態だった。

## 3. 対応

上記の欠落を埋めるため、**全モジュールについて日本語の人間向け証明レポート**
`docs/human-proofs/<ModuleName>.md` を整備する(書式は [STYLE.md](#/) 参照、
`docs/human-proofs/STYLE.md`)。各レポートは以下を含む。

- モジュールの役割と、全射性予想攻略の全体戦略における位置づけ
- 主要な定義の日本語での説明
- 各定理の主張(日本語の数学文)と、人間向けの証明
  (タクティクの逐語訳ではなく、場合分け・帰納法・鍵となる不等式を明示した数学的議論)
- 見出しには Lean ソースの行番号 `(L42)` を付し、ビューワーの右ペインの該当行へジャンプできる

> **追記(2026-08-29 09:20 JST):** 上記対応は完了した。自律ループの追加分
> (`PermanentAboveCorridor*` ファミリー36件、`PermanentAboveCycleExit`、
> `PermanentAboveCycleRebase`、`PermanentAboveCorridorSuccessorRank`)を含め、
> この時点の全 **129 モジュールすべて**に日本語の人間向け証明レポートを生成済み。
> 以後に追加されたモジュールは `python3 viewer/gen_manifest.py` 実行後、
> ビューワーのサイドバーに赤バッジで表示される。

## 4. モジュール別一覧(基準時点)

「日本語証明」列は本対応**着手前**の状態(すべて「なし」だった)。
現在の生成状況はビューワーのサイドバー(緑=生成済み / 赤=未生成)で確認できる。

| モジュール | 行数 | 定理数 | 定義数 | 英語docstring | 日本語証明(着手前) |
|---|---:|---:|---:|:-:|:-:|
| [`ActualDescent`](#/module/ActualDescent) | 239 | 15 | 3 | **なし** | なし |
| [`AnchorBoundary`](#/module/AnchorBoundary) | 209 | 6 | 0 | **なし** | なし |
| [`Audit`](#/module/Audit) | 349 | 0 | 0 | **なし** | なし |
| [`Basic`](#/module/Basic) | 109 | 7 | 8 | **なし** | なし |
| [`Blocker`](#/module/Blocker) | 92 | 5 | 5 | **なし** | なし |
| [`BoundaryAudit`](#/module/BoundaryAudit) | 235 | 6 | 0 | あり | なし |
| [`CanonicalComplete`](#/module/CanonicalComplete) | 135 | 2 | 3 | あり | なし |
| [`CanonicalForcedGrowth`](#/module/CanonicalForcedGrowth) | 237 | 7 | 1 | あり | なし |
| [`CanonicalGrowthRecovery`](#/module/CanonicalGrowthRecovery) | 66 | 4 | 0 | あり | なし |
| [`CanonicalLevelOne`](#/module/CanonicalLevelOne) | 187 | 4 | 1 | **なし** | なし |
| [`CanonicalLevelTwo`](#/module/CanonicalLevelTwo) | 181 | 2 | 1 | **なし** | なし |
| [`CanonicalLevelZero`](#/module/CanonicalLevelZero) | 223 | 3 | 2 | あり | なし |
| [`CanonicalOracle`](#/module/CanonicalOracle) | 238 | 7 | 1 | あり | なし |
| [`CoordinateDynamics`](#/module/CoordinateDynamics) | 231 | 19 | 1 | **なし** | なし |
| [`Coordinates`](#/module/Coordinates) | 114 | 8 | 4 | **なし** | なし |
| [`Coverage`](#/module/Coverage) | 154 | 10 | 3 | **なし** | なし |
| [`CoverageDebtBridge`](#/module/CoverageDebtBridge) | 252 | 7 | 5 | あり | なし |
| [`CrossingBelowRefined`](#/module/CrossingBelowRefined) | 188 | 2 | 1 | あり | なし |
| [`CrossingDowncrossRefined`](#/module/CrossingDowncrossRefined) | 112 | 3 | 2 | あり | なし |
| [`CrossingFrontier`](#/module/CrossingFrontier) | 249 | 8 | 1 | あり | なし |
| [`CrossingFrontierRefined`](#/module/CrossingFrontierRefined) | 96 | 2 | 0 | あり | なし |
| [`CrossingGap`](#/module/CrossingGap) | 228 | 5 | 1 | **なし** | なし |
| [`CrossingGrowth`](#/module/CrossingGrowth) | 159 | 5 | 2 | **なし** | なし |
| [`CrossingHorizon`](#/module/CrossingHorizon) | 164 | 7 | 0 | あり | なし |
| [`CrossingIteration`](#/module/CrossingIteration) | 115 | 5 | 1 | **なし** | なし |
| [`CrossingRecovery`](#/module/CrossingRecovery) | 164 | 7 | 1 | **なし** | なし |
| [`CrossingRefinedBoundary`](#/module/CrossingRefinedBoundary) | 169 | 7 | 1 | あり | なし |
| [`CrossingTailRefined`](#/module/CrossingTailRefined) | 306 | 11 | 3 | あり | なし |
| [`DebtAddition`](#/module/DebtAddition) | 146 | 7 | 0 | **なし** | なし |
| [`DebtBackward`](#/module/DebtBackward) | 230 | 5 | 0 | **なし** | なし |
| [`DebtCrossing`](#/module/DebtCrossing) | 176 | 10 | 1 | **なし** | なし |
| [`DebtInvariant`](#/module/DebtInvariant) | 251 | 12 | 1 | **なし** | なし |
| [`DebtStep`](#/module/DebtStep) | 160 | 4 | 2 | **なし** | なし |
| [`DebtSubtraction`](#/module/DebtSubtraction) | 81 | 3 | 0 | **なし** | なし |
| [`Diagonal`](#/module/Diagonal) | 236 | 8 | 1 | **なし** | なし |
| [`DowncrossBudgetGap`](#/module/DowncrossBudgetGap) | 274 | 6 | 1 | あり | なし |
| [`EarlyForcedCandidateClosure`](#/module/EarlyForcedCandidateClosure) | 234 | 6 | 1 | あり | なし |
| [`EarlyRepresentative`](#/module/EarlyRepresentative) | 336 | 4 | 5 | あり | なし |
| [`EarlyRepresentativeClosure`](#/module/EarlyRepresentativeClosure) | 201 | 3 | 2 | あり | なし |
| [`EarlyRepresentativeComplete`](#/module/EarlyRepresentativeComplete) | 121 | 4 | 1 | あり | なし |
| [`Examples`](#/module/Examples) | 162 | 11 | 0 | **なし** | なし |
| [`ExtendedHistoryBudgetClosure`](#/module/ExtendedHistoryBudgetClosure) | 199 | 5 | 1 | あり | なし |
| [`ExtendedHistoryComplete`](#/module/ExtendedHistoryComplete) | 100 | 6 | 0 | あり | なし |
| [`ExtendedHistoryDirectRefined`](#/module/ExtendedHistoryDirectRefined) | 233 | 7 | 0 | あり | なし |
| [`ExtendedHistoryNormal`](#/module/ExtendedHistoryNormal) | 297 | 10 | 4 | あり | なし |
| [`Gate`](#/module/Gate) | 42 | 1 | 1 | **なし** | なし |
| [`HistoricalDebtBridge`](#/module/HistoricalDebtBridge) | 519 | 10 | 8 | あり | なし |
| [`History`](#/module/History) | 99 | 5 | 0 | **なし** | なし |
| [`HistoryBudget`](#/module/HistoryBudget) | 411 | 23 | 7 | **なし** | なし |
| [`HistoryFrontier`](#/module/HistoryFrontier) | 641 | 14 | 1 | **なし** | なし |
| [`InitialRegion`](#/module/InitialRegion) | 71 | 2 | 0 | **なし** | なし |
| [`LandingSurfaces`](#/module/LandingSurfaces) | 216 | 19 | 1 | **なし** | なし |
| [`Mechanisms`](#/module/Mechanisms) | 196 | 14 | 0 | **なし** | なし |
| [`MultiBorrow`](#/module/MultiBorrow) | 386 | 22 | 1 | **なし** | なし |
| [`NegativeEpoch`](#/module/NegativeEpoch) | 271 | 5 | 0 | **なし** | なし |
| [`NegativeRegion`](#/module/NegativeRegion) | 163 | 10 | 0 | **なし** | なし |
| [`NonnegativeSemantic`](#/module/NonnegativeSemantic) | 242 | 3 | 1 | **なし** | なし |
| [`NormalClosure`](#/module/NormalClosure) | 387 | 8 | 2 | **なし** | なし |
| [`NormalComplete`](#/module/NormalComplete) | 65 | 1 | 0 | **なし** | なし |
| [`NormalPhase`](#/module/NormalPhase) | 225 | 2 | 8 | **なし** | なし |
| [`NormalProvenance`](#/module/NormalProvenance) | 242 | 13 | 3 | あり | なし |
| [`NormalSemanticBoundary`](#/module/NormalSemanticBoundary) | 210 | 9 | 2 | あり | なし |
| [`OneBorrowFrontier`](#/module/OneBorrowFrontier) | 61 | 2 | 0 | **なし** | なし |
| [`Oracle`](#/module/Oracle) | 143 | 3 | 5 | **なし** | なし |
| [`OrbitBounds`](#/module/OrbitBounds) | 81 | 7 | 0 | **なし** | なし |
| [`OrbitReadyAdapters`](#/module/OrbitReadyAdapters) | 281 | 12 | 1 | あり | なし |
| [`OrbitReadyComplete`](#/module/OrbitReadyComplete) | 252 | 7 | 1 | あり | なし |
| [`OrbitReadyDirectRefined`](#/module/OrbitReadyDirectRefined) | 519 | 10 | 0 | あり | なし |
| [`OrbitReadyRefinedStep`](#/module/OrbitReadyRefinedStep) | 154 | 4 | 2 | あり | なし |
| [`PermanentAboveCanonical`](#/module/PermanentAboveCanonical) | 303 | 17 | 7 | あり | なし |
| [`PermanentAboveCycleExit`](#/module/PermanentAboveCycleExit) | 430 | 16 | 9 | あり | なし(基準直前に追加) |
| [`PermanentAboveCycleRank`](#/module/PermanentAboveCycleRank) | 208 | 10 | 5 | あり | なし |
| [`PermanentAboveHistory`](#/module/PermanentAboveHistory) | 446 | 9 | 4 | あり | なし |
| [`PermanentAbovePotential`](#/module/PermanentAbovePotential) | 68 | 4 | 1 | あり | なし |
| [`PermanentAboveTail`](#/module/PermanentAboveTail) | 488 | 16 | 5 | あり | なし |
| [`PhaseEpoch`](#/module/PhaseEpoch) | 117 | 4 | 0 | **なし** | なし |
| [`PhaseProgress`](#/module/PhaseProgress) | 39 | 2 | 0 | **なし** | なし |
| [`PhaseSearch`](#/module/PhaseSearch) | 141 | 8 | 6 | **なし** | なし |
| [`PhaseSearchStart`](#/module/PhaseSearchStart) | 103 | 5 | 4 | **なし** | なし |
| [`PhaseSemantic`](#/module/PhaseSemantic) | 230 | 8 | 6 | **なし** | なし |
| [`PrestateCoverage`](#/module/PrestateCoverage) | 315 | 12 | 0 | **なし** | なし |
| [`ReadyCurrentDebt`](#/module/ReadyCurrentDebt) | 136 | 8 | 1 | あり | なし |
| [`ReadyDebtInvariant`](#/module/ReadyDebtInvariant) | 173 | 8 | 2 | あり | なし |
| [`ReadyDebtRefined`](#/module/ReadyDebtRefined) | 116 | 3 | 0 | あり | なし |
| [`Recovery`](#/module/Recovery) | 236 | 14 | 0 | **なし** | なし |
| [`RecoveryBudget`](#/module/RecoveryBudget) | 255 | 18 | 3 | **なし** | なし |
| [`RecoveryFrontier`](#/module/RecoveryFrontier) | 228 | 8 | 0 | **なし** | なし |
| [`RecoveryWindows`](#/module/RecoveryWindows) | 62 | 4 | 0 | **なし** | なし |
| [`RefinedOracleBoundary`](#/module/RefinedOracleBoundary) | 75 | 4 | 1 | あり | なし |
| [`TargetDescent`](#/module/TargetDescent) | 156 | 5 | 2 | **なし** | なし |
| [`TypedNormalProvenance`](#/module/TypedNormalProvenance) | 673 | 17 | 7 | あり | なし |
| [`Undershoot`](#/module/Undershoot) | 468 | 13 | 0 | **なし** | なし |

## 5. 閲覧方法

リポジトリルートでサーバーを起動し、`/viewer/` を開く。

```
bun run viewer/server.ts
# → http://localhost:8642/viewer/
```

左サイドバーでモジュールを選ぶと、**左ペインに日本語の人間向け証明、
右ペインに Lean ソース**が並んで表示される。レポート見出しの `L42` チップを
クリックすると、右ペインの該当行へジャンプしてハイライトされる。
