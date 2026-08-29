# CanonicalComplete

**役割:** 低水準残余を水準 0・1・2 に証明相当に分割し、水準 0 を後継定理で消去して、canonical開始点の未解決部分を二つの強制加算チェンバーだけに統合する。

## このモジュールの役割

`CanonicalOracle` の分類定理は「ポテンシャル水準 ≤ 2」という数値上界付きの残余 `CanonicalLowLevelResidual` を返すが、水準そのものは存在量化の中に隠れている。本モジュールはまずこの隠れた水準を 0・1・2 の三つに証明相当(proof-relevant)に分割する。その上で、水準 0 は `CanonicalLevelZero` の後継定理により目標出現へ吸収され、水準 1・2 はそれぞれの一段解析(`CanonicalLevelOne`・`CanonicalLevelTwo`)を適用して、閉じ残りを二つの剛的な強制加算チェンバーの直和 `CanonicalForcedResidual` にまとめる。これが現在の局所 API で得られる最強の canonical開始定理である。

## 主要な定義

### `CanonicalLowLevelResidual.IsOne` (L15)

低水準残余の隠れた水準が 1 である場合の精密化である。残余は `Prop` 値で証人を射影できないため、構成子は時刻・座標・証明書・初出・`potential q r = 1`・`1 < target` などの証拠を再掲し、`source_eq` で元の残余がこの証拠から作られた `low` と一致することを記録する。

### `CanonicalLowLevelResidual.IsTwo` (L36)

同様の水準 2 版であり、`potential q r = 2` と `2 < target` を保持する。

### `CanonicalForcedResidual` (L83)

符号と低水準の完全解析の後に残る唯一の未解決チェンバーの直和である。構成子は二つ: `level_one`(`CanonicalLevelOneForcedQOneResidual` を包む)と `level_two`(`CanonicalLevelTwoForcedResidual` を包む)。

## 定理と証明

### `CanonicalLowLevelResidual.level_cases` (L59)

**主張:** 低水準残余の隠れた水準は正確に 0・1・2 のいずれかであり、それぞれ `IsZero`・`IsOne`・`IsTwo` が成り立つ。

**証明:** 残余を分解すると `level ≤ 2` から `level ∈ {0, 1, 2}` である。各場合で保持していた証拠をそのまま対応する精密化の構成子に渡す。`source_eq` の等式は、`Prop` の証明が一意であること(証明無関係性、Lean では `Subsingleton.elim`)から直ちに従う。

### `targetStartInvariant_phaseSemanticStep_or_forced` (L98)

**主張:** 正の目標 `target` の canonical開始ノードは、(1) 目標が出現する、(2) 位相探索ランクを厳密に下げる意味的子ノードが存在する、(3) `CanonicalForcedResidual`(水準 1 または 2 の強制加算チェンバー)に入る、のいずれかである。

**証明:** 各モジュールの結果を順に接続する。まず `CanonicalOracle` の `targetStartInvariant_phaseSemanticStep_or_lowLevel` を適用する。負領域・目標以上・水準 3 以上はそこで (1) または (2) に閉じており、残るのは低水準残余だけである。残余に `level_cases` を適用して水準で分岐する。

*水準 0。* `canonicalLowLevel_zero_phaseSemanticStep_or_successor` により (1)・(2)・または後継境界 `CanonicalSuccessorResidual` に落ちる。後継境界の場合はさらに `CanonicalSuccessorResidual.target_occurs` により二歩以内に目標が出現するので、この枝全体が (1) に吸収される。つまり水準 0 は残余として消滅する。

*水準 1。* `IsOne` の証拠を展開し、`canonicalLowLevel_levelOne_phaseSemantic_or_forcedQOne` を適用する。閉じない場合は `CanonicalForcedResidual.level_one` として (3) へ。

*水準 2。* 同様に `canonicalLevelTwo_phaseSemanticStep_or_forcedQOne` を適用し、閉じない場合は `level_two` として (3) へ。

## 全体の中での位置づけ

証明地図の「canonical開始」段の統合点である。`CanonicalOracle`・`CanonicalLevelZero`・`CanonicalLevelOne`・`CanonicalLevelTwo` の成果をひとつの定理に束ね、残余を `CanonicalForcedResidual` に限定する。この残余は `CanonicalForcedGrowth` の統一チェンバーに変換され、`CanonicalGrowthRecovery` の二段先読みで解消される。最終形 `targetStartInvariant_phaseSemanticStep`(`CanonicalGrowthRecovery`)は本定理を直接の入力とする。
