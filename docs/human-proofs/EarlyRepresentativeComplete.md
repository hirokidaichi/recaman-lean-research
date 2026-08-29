# EarlyRepresentativeComplete

**役割:** early-representative chamberの2残余の閉包を合流させて残余なしの完全なsemantic stepとし、generic extended-history残余をbudget輸送constructorひとつに縮約する。

## このモジュールの役割

`EarlyRepresentative.classify` の分類は、2つの成功child形(forward child、debt child)と2つの残余遷移を持っていた。合法減算のdowncrossは `EarlyRepresentativeClosure` が将来のcrossing recoveryで、blockされたtarget未満候補は `EarlyForcedCandidateClosure` が候補の過去の出現点から代表時刻までの区間に必ず存在する弱上方crossingで、それぞれ閉じている。本モジュールは両閉包を合流させ、early-time chamber(代表時刻の時計がまだtarget-readyでない領域)から残余を完全に除去する。さらにこの完全stepを、genericなextended-history残余(`ExtendedHistoryNormalResidual`)の `representative_not_ready` constructorへのアダプタとして配線し、残る残余が独立な `budget_transport` だけであることを示す。

## 定理と証明

### `EarlyRepresentativeCertificate.phaseSemanticStep` (L20)

**主張:** 代表時刻の時計がtarget-readyでない任意の証明書について、目標の実際の出現、または既存の統合semantic不変量 `PhaseSemanticInvariant` を持つchildへの既存phase-search rankでの真の下降、のいずれかが成り立つ。

**証明:** `classify` を実行し4分岐を処理する。

- 出現はそのまま返す。
- forward child、debt childは、分類自身が保持するsemantic証明書とprogressを取り出す。
- `legal_downcross` 残余は `EarlyRepresentativeClosure` の `legalDowncross_phaseSemanticStep` で閉じる(将来の弱上方crossingをcrossing recovery childに格納し、pre-crossing値による真のanchor下降を得る)。
- `forced_below_candidate` 残余は `EarlyForcedCandidateClosure` の `forcedBelowCandidate_phaseSemanticStep` で閉じる。blockされた候補はtarget未満の値として代表時刻**以前**にすでに出現している。その出現点では値がtarget未満、代表時刻では `target ≤ a(代表時刻)` なので、この有限区間のどこかに強制加算による弱上方crossingが存在し、legal downcrossの場合と同じcrossing recovery構成が適用できる。

いずれの分岐でも、新しい位相もrankも導入せず、既存の四成分rank(履歴予算・anchor・位相・局所値の辞書式順序)の真の下降で閉じている。

### `EarlyRepresentativeCertificate.completeSemanticStep` (L52)

**主張:** 前定理の別名(存在量化パッケージ)。呼び出し側の名前の便宜のためのものである。

### `ExtendedHistoryNormalResidual.representativeNotReady_phaseSemanticStep` (L66)

**主張:** genericなextended-history残余の `representative_not_ready` constructorへの直接アダプタ: その構成データ(extended-history証明書と時計失敗 `代表時刻 + 1 < target`)から完全なsemantic stepが従う。

**証明:** 証明書と時計失敗はちょうど `EarlyRepresentativeCertificate` の2フィールドである。residualが余分に保持する「値の真の超過」フィールドは、完全なearly分類器と整合するが、必要ではない(分類器は内部で `a(代表時刻) = target` の場合も出現として扱えるため)。組んだ証明書に `phaseSemanticStep` を適用する。

### `RemainingExtendedHistoryBudgetTransport` (L84)

**主張(定義):** not-ready constructorを除去した後の、任意のextended-history残余のproof-relevantな残り。constructorは `budget_transport` のみで、元の残余と同一のデータ(証明書、代表時刻のreadiness、semantic child、代表nodeからの局所下降、履歴予算のgap `missingBelowCount target node.horizon < missingBelowCount target 代表時刻`)を保持する。

### `ExtendedHistoryNormalResidual.phaseSemanticStep_or_budgetTransport` (L102)

**主張:** 旧extended-history残余の網羅的アダプタ: 任意の残余は、完全なsemantic step(出現または真の下降)を与えるか、独立な `budget_transport` constructorに落ちる。early-clockの場合は完全に閉じている。

**証明:** 残余の2 constructorで場合分けする。`representative_not_ready` は前アダプタで閉じ、`budget_transport` はデータを新しい残余型へそのまま写す。この時点で残るbudget輸送は、本モジュールとは独立の機構(`ExtendedHistoryBudgetClosure` の新below-target出現からのcrossing recovery)で閉じられる。

## 全体の中での位置づけ

証明地図の「意味的探索domain: early representativeもcrossing recoveryへ接続」の完了点である。`EarlyRepresentative`(分類)→`EarlyRepresentativeClosure`(legal downcross閉包)→`EarlyForcedCandidateClosure`(forced候補閉包)の系列がここで合流し、`ExtendedHistoryNormal` の2残余のうち片方が完全に消える。もう片方のbudget輸送は `ExtendedHistoryBudgetClosure` が閉じ、最終合流点の `ExtendedHistoryComplete` が本モジュールの `representativeNotReady_phaseSemanticStep` を直接呼んで、extended-history normal nodeの残余なしの完全stepを完成させる。
