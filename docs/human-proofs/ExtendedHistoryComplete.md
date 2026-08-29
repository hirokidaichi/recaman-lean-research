# ExtendedHistoryComplete

**役割:** early-representative閉包とbudget-gap閉包を合流させ、extended-history normal nodeの残余なしの完全なsemantic stepを与え、typed historical provenanceへ配線する。

## このモジュールの役割

extended-history nodeの最小分類(`ExtendedHistoryNormal`)には2つの残余があった。代表時刻でのtarget readinessの失敗は `EarlyRepresentativeComplete` が、履歴予算(`missingBelowCount`)の真のgapは `ExtendedHistoryBudgetClosure` が、それぞれ将来のcrossing recoveryを経由して閉じている。本モジュールは両者を組み合わせ、**すべての**extended-history証明書について、既存の四成分phase-search rankのままの全域的なsemantic stepを確立する。さらにその完全定理を、5種類の生成機構(provenance)付きhistorical normal node(`TypedHistoricalNormalProvenance`)へ適用する接続部を提供する。

## 定理と証明

### `ExtendedHistoryNormalCertificate.phaseSemanticStep` (L17)

**主張:** 任意のextended-history normal証明書は、目標の出現証人を与えるか、semantic不変量 `PhaseSemanticInvariant` を持つchildへの既存rankでの真の下降を与える。残余はない。

**証明:** `ExtendedHistoryBudgetClosure` の強化分類 `phaseSemanticStep_or_readiness` を実行する。出現と下降はそのまま返る。唯一残り得る `representative_not_ready` 残余は、その構成データ(証明書、時計失敗 `代表時刻 + 1 < target`、値の真の超過)がちょうどearly-representative証明書を成すので、`EarlyRepresentativeComplete` のアダプタ `representativeNotReady_phaseSemanticStep` で閉じる。三択の分類が二択に落ち、extended-history nodeの局所全域性(local totality)が完成する。

### `ExtendedHistoryNormalInvariant.phaseSemanticStep` (L38)

**主張:** 存在量化版。選ばれた代表座標を外に見せずに全域性を保つ。

**証明:** 存在量化を開いて前定理を適用するだけである。

### `TypedHistoricalNormalCertificate.phaseSemanticStep_of_horizonReady` (L50)

**主張:** typed historical証明書(生成機構の監査のためにextended-historyのデータを直接携帯する証明書)は、horizon readiness `target ≤ historyHorizon + 1` を追加するだけで完全なsemantic stepを持つ。

**証明:** `TypedNormalProvenance` の変換 `toExtendedHistory` でextended-history証明書に落とし、完全定理を適用する。horizon readinessが変換に必要な唯一の追加前提であり、それ以外の残余はすべて消えている。

### `TypedHistoricalNormalProvenance.phaseSemanticStep_of_horizonReady` (L63)

**主張:** 5種類の機構別historical provenance constructor(parent-drop、coverage anchor、downcross restart、debt exit、crossing frontier)すべてに対する統一の包み。生成されたchildは、historical node自身の真のsuccessorを持つ。

**証明:** どのconstructorもhistorical証明書を携帯しているので、前定理をその証明書へ適用する。得られる下降はhistorical node `child` からのものであり、生成親 `parent` からの下降は次の2定理で合成する。

### `TypedHistoricalNormalProvenance.sourceProgress` (L74)

**主張:** 機構別constructorはいずれも、生成元の辺、すなわち `PhaseSearchProgress target child parent`(historical nodeがそれを生成した親より真にrankが低いこと)を保持している。

**証明:** 5つのconstructorそれぞれについて格納された `rank_edge` フィールドを取り出すだけの場合分けである。

### `TypedHistoricalNormalProvenance.phaseSemanticStep_from_source_of_horizonReady` (L87)

**主張:** 完全なhistorical stepを生成元の辺と合成する: horizon-readyなprovenance付きhistorical nodeは、目標の出現、または生成親 `parent` から見ても真にrankが下がるsemantic childを与える。

**証明:** `phaseSemanticStep_of_horizonReady` で `next < child`(rankの意味で)を得て、`sourceProgress` の `child < parent` と辞書式順序の推移律で `next < parent` を得る。

## 全体の中での位置づけ

証明地図の「意味的探索domain: extended-history局所閉包済み」の到達点である。`ExtendedHistoryNormal`(分類)、`EarlyRepresentative`〜`EarlyRepresentativeComplete`(early時計残余の閉包)、`ExtendedHistoryBudgetClosure`(budget残余の閉包)の成果がここで1本の定理に合流する。また `TypedNormalProvenance` の5機構constructorに完全stepを配線することで、historical normal nodeを生成するどの機構からでも探索を安全に継続できることを示す。refined domain上の対応物は `ExtendedHistoryDirectRefined` の `ExtendedHistoryNormalCertificate.refinedStep` であり、そちらはchildの時計情報を `PhaseSemanticInvariant` に忘れさせずに保持する。
