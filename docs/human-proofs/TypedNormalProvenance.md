# TypedNormalProvenance

**役割:** historical normal ノードに「代表時刻・履歴 horizon・初出時刻」を分離して保持する typed 証明書を定義し、parent-drop / coverage anchor / downcross restart / debt exit / crossing frontier の五つの生成機構別 provenance を実装する。

## このモジュールの役割

弱い `NormalSearchInvariant` は「horizon 内のどこかで anchor 値が初出した」ことしか覚えていない。将来の total oracle に必要な局所軌道解析は、そのノードが**どの実軌道状態**を表しているかを知る必要があり、しかもその状態の時刻(representative time: anchor 値と座標を実際に取る軌道時刻)とランクを測る履歴時刻(history horizon)は一致するとは限らない。たとえば downcross restart は旧軌道状態を代表に保ったまま横断の先まで履歴を延長する。本モジュールは三つの時刻を分離した `TypedHistoricalNormalCertificate` を核に、historical 子を生む五つの機構それぞれについて生成証拠を保持する構造体と構成関数を与え、統一 domain `TypedHistoricalNormalProvenance` にまとめる。いずれも `ProvenancedNormalInvariant` への加入を与えるが、局所後続定理そのものは意図的に主張しない(それは extended-history 側の課題として `phaseSemanticStep_or_residual` に正直な残余付きで委ねる)。

## 主要な定義

### `TypedHistoricalNormalCertificate` (L32)

生の historical 証明書に隠れていた完全な軌道データ。フィールドは

- `historyHorizon`: `phaseSearchRank` の第一成分(履歴予算)を測る時刻
- `representativeTime`: 実際に解析される軌道状態の時刻、`value = a representativeTime`
- `firstTime`: `value` の初出時刻(`FirstAt a value firstTime`)
- `quotient`, `remainder`: 代表時刻での座標 `CoordinatesAt representativeTime q r`
- ノード形 `node = ⟨historyHorizon, value, normal, value⟩`、`0 < target ≤ value`、`firstTime ≤ historyHorizon`、`representativeTime ≤ historyHorizon`

である。証明書は `Prop` ではなく `Type` として定義され、データとして持ち回れる。

### `ParentDropNormalProvenance` (L189)

親 anchor 下降分岐で生成された historical 子。provenance 付き親 `source`、typed 証明書、生の horizon、`NormalParentDropEvidence`、およびランク edge を保持する。

### `CoverageAnchorNormalProvenance` (L263)

`CoverageStep`(親の値から見て、目標出現か、より小さい値とその初出を返す一段の証明)の非 target 分岐から選ばれた historical 子。中間の被覆値 `coveredValue` を、より小さい historical anchor(`certificate.value < coveredValue ≤ parent.anchorParent`)と区別して保持する。

### `DowncrossRestartNormalProvenance` (L349)

target 以上の代表状態から target 未満の端点へ下方横断した前進区間。子は旧代表値を保ったまま、後の端点を history horizon に採用し、履歴予算の厳密下降 `budget_drop` をランク edge とする。`endpoint_below_target : a historyHorizon < target` を明示的に持つ。

### `DebtExitNormalProvenance` (L419)

強い debt ノードが保持する初出値で退出する遷移。debt 親のノード形、`DebtInvariant`、子のノード形 `⟨historyHorizon, value, normal, value⟩`、非 normal ルート、ランク edge を持つ。

### `CrossingFrontierNormalProvenance` (L497)

処理済み crossing frontier(フロンティア: 解析領域の境界で成立する定理群)が旧 debt anchor 未満の初出値 `frontierValue` を供給した場合。frontier の初出は debt horizon より後かもしれないため、子の horizon は両者の最大値 `max historyHorizon frontierFirstTime` である。

### `TypedHistoricalNormalProvenance` (L602)

五機構の proof-relevant な直和。生の `NormalSearchInvariant` からの構成子は意図的に存在せず、すべての要素が代表状態データと具体的な生成機構の両方を露出する。

## 定理と証明

### `TypedHistoricalNormalCertificate.node_eq_representative` (L52)

**主張:** ノードの数値形は `⟨historyHorizon, a representativeTime, normal, a representativeTime⟩` である。

**証明:** `value = a representativeTime` をノード形の等式に代入するだけである。

### `TypedHistoricalNormalCertificate.firstTime_positive` (L66)

**主張:** 表される値は target 以上なので、その初出時刻は正である。

**証明:** 初出時刻が 0 なら初出値は `a 0 = 0` だが、`0 < target ≤ value` に矛盾する。

### `TypedHistoricalNormalCertificate.toNormalSearchInvariant` (L82)

**主張:** 代表状態データを忘れると旧来の通常 normal 証明書が回収される。

**証明:** 初出時刻は正なのでそこに座標表示が存在する(代表時刻に保持している座標とは独立に取る)。ノード形・目標下界・初出・`firstTime ≤ historyHorizon` はフィールドそのものである。

### `TypedHistoricalNormalCertificate.toPhaseSemanticInvariant` (L103)

**主張:** typed 証明書は旧意味的 domain に保守的に埋め込まれる。

**証明:** 前定理の証明書を normal 構成子へ入れる。

### `TypedHistoricalNormalCertificate.toExtendedHistory` (L113)

**主張:** horizon の時計条件 `target ≤ historyHorizon + 1` を外から与えれば、typed 証明書は extended-history 証明書 `ExtendedHistoryNormalCertificate`(代表時刻・horizon・目標下界・代表座標を持つ最小の historical 証明書)の全フィールドを供給する。

**証明:** ノード形は `node_eq_representative` から、`representativeTime ≤ node.horizon` と時計条件は horizon の等式で書き換えて得る。時計条件を仮定に残すのは、strong debt や crossing をルートとする provenance が現状この条件を含意しないためである。

### `TypedHistoricalNormalCertificate.phaseSemanticStep_or_residual` (L143)

**主張:** 時計条件のもとで、目標出現・意味的な子とランク進捗・`ExtendedHistoryNormalResidual`(代表時刻が早すぎる residual または予算輸送 residual)のいずれかが成り立つ。

**証明:** 前定理で extended-history 証明書へ変換し、その監査定理 `phaseSemanticStep_or_residual` を呼ぶ。無条件の後続は主張しない、extended-history 監査をそのまま継承した正直な分類である。

### `TypedHistoricalNormalCertificate.toHistoricalNormalStep` (L154)

**主張:** typed 証明書と親から子への実ランク edge の組は `HistoricalNormalStep` をなす。

**証明:** 証明書部分は `toNormalSearchInvariant`、進捗部分は仮定である。

### `TypedHistoricalNormalCertificate.toOrbitReady_of_current` (L165)

**主張:** 代表時刻と履歴 horizon が一致し(current な代表)、時刻準備 `target ≤ representativeTime + 1` が与えられれば、ノードは orbit-ready である。

**証明:** 二つの時刻を同一視すると、ノード形・目標下界・座標はそのまま orbit-ready 証明書のフィールドになる。時刻準備だけは typed 証明書から従わないため明示的な仮定である。

### `parentDropNormalProvenance_of_evidence` (L202)

**主張:** provenance 付き normal 親と `NormalParentDropEvidence` から、子 `⟨max rawHorizon firstTime, value, normal, value⟩` の parent-drop provenance を構成できる。

**証明:** 初出時刻は正(初出値が target 以上のため)なので、そこに座標を選ぶ。代表時刻には初出時刻そのものを採用し(`value = a firstTime` は初出の定義から)、ランク horizon は独立に `max rawHorizon firstTime` へ拡大する。ランク edge は閉包定理 `normalParentDrop_phaseSemantic`(`NormalClosure`)の進捗部分である。

### `ParentDropNormalProvenance.toProvenancedNormalInvariant` (L252)

**主張:** parent-drop provenance の子は精密化 domain に属する。

**証明:** `historical_from_normal` に、source と `toHistoricalNormalStep` で包んだ step を渡す。

### `coverageAnchorNormalProvenance_of_blocker` (L278)

**主張:** `CoverageStep` の blocker 分岐(`target ≤ value < coveredValue ≤ parentAnchor`、`value` は初出値)から、拡大 horizon `max parentHorizon firstTime` における coverage provenance を構成できる。

**証明:** parent-drop と同様に初出時刻を代表時刻に採用して座標を選ぶ。anchor の厳密下降は `value < coveredValue ≤ parentAnchor` の合成で得られ、ランク edge は `phaseSearchProgress_of_horizonAndAnchor`(horizon 広義増加・anchor 厳密下降)である。

### `CoverageAnchorNormalProvenance.toProvenancedNormalInvariant` (L336)

**主張・証明:** parent-drop の場合と同一の構成で精密化 domain へ入る。

### `downcrossRestartNormalProvenance_of_budgetDrop` (L365)

**主張:** 代表状態(`target ≤ a representativeTime`、初出、現在座標)と、後の時刻 `historyHorizon` での下方横断端点 `a historyHorizon < target`、および履歴予算の厳密下降から、子 `⟨historyHorizon, a representativeTime, normal, a representativeTime⟩` の downcross-restart provenance を構成できる。

**証明:** coverage provenance と異なり、代表座標は初出時刻ではなく旧軌道状態そのものの座標を保持する。ランク edge は予算の厳密下降による辞書式第一成分の下降であり、`Prod.Lex.left` そのものである。これは `orbit_downcrossing_occurs_or_budgetDrop` の予算下降分岐の包装である。

### `DowncrossRestartNormalProvenance.toProvenancedNormalInvariant` (L409)

**主張・証明:** 同様に `historical_from_normal` で精密化 domain へ入る。

### `DebtExitNormalProvenance.certificate` (L435)

**主張:** debt-exit provenance から typed 証明書を再構成できる。

**証明:** debt の初出時刻は正(`debt_firstTime_pos`)なのでそこに座標を選ぶ。代表時刻は初出時刻、履歴 horizon は debt horizon で、`firstTime < horizon` から両時刻の順序条件が従う。値・初出・目標下界は `DebtInvariant` のフィールドである。

### `debtExitNormalProvenance_of_invariant` (L464)

**主張:** すべての既存 strong debt 証明書は debt-exit provenance を生む(アダプタ)。

**証明:** ルートは `NormalProvenanceRoot.debt`、ランク edge は anchor 下降による debt 退出定理 `phaseSearch_exitDebt_of_anchorDrop`(`value < anchorParent` を使う)である。

### `DebtExitNormalProvenance.toProvenancedNormalInvariant` (L484)

**主張・証明:** 非 normal ルートを持つので `historical_from_root` で精密化 domain へ入る。

### `CrossingFrontierNormalProvenance.certificate` (L519)

**主張:** crossing-frontier provenance から typed 証明書を再構成できる。

**証明:** frontier 値は target 以上なので初出時刻は正であり、そこに座標を選ぶ。履歴 horizon は `max historyHorizon frontierFirstTime`、代表時刻は frontier の初出時刻で、どちらの順序条件も max の性質から従う。

### `crossingFrontierNormalProvenance_of_firstAt` (L556)

**主張:** debt 証明書と、旧 debt anchor 未満の初出 frontier 値(`target ≤ frontierValue < debtAnchor`)から crossing-frontier provenance を構成できる(アダプタ)。

**証明:** ルートは debt、ランク edge は「horizon を広義に延長しつつ anchor を厳密に下げる debt 退出」`phaseSearch_exitDebt_of_extendedHorizonAndAnchor` である。

### `CrossingFrontierNormalProvenance.toProvenancedNormalInvariant` (L587)

**主張・証明:** debt ルートからの `historical_from_root` で精密化 domain へ入る。

### `TypedHistoricalNormalProvenance.historicalCertificate` (L621)

**主張:** 五機構のいずれからも共通の typed 証明書を取り出せる。

**証明:** 機構ごとの場合分けで、それぞれが保持(または構成)する証明書を返す。

### `TypedHistoricalNormalProvenance.toNormalSearchInvariant` (L632) / `.toPhaseSemanticInvariant` (L638) / `.toProvenancedNormalInvariant` (L644)

**主張:** 統一 domain の要素は、通常証明書・旧意味的 domain・精密化 domain のそれぞれへ埋め込まれる。

**証明:** 前二者は共通証明書の対応する変換の合成。最後は機構ごとに、各構造体の `toProvenancedNormalInvariant` を呼ぶ場合分けである。

### `TypedHistoricalNormalProvenance.phaseSemanticStep_or_residual` (L660)

**主張:** 時計条件 `target ≤ historyHorizon + 1` のもとで、統一 domain の任意の要素は「目標出現・意味的な子とランク進捗・extended-history residual」に分類される。

**証明:** 共通証明書の同名定理へ委譲する。horizon readiness は呼び出し側の明示的義務のままであり、二種類の正直な残余(early representative と budget transport)は残りうる。

## 全体の中での位置づけ

証明地図の「historical回避」段階の中核で、「意味的探索domain」の行に挙がる provenance 実装の本体である。`NormalProvenance` の抽象 API(current/historical 分離)に対し、本モジュールは PROOF_MAP が挙げる五つの生成機構(parent-drop、coverage anchor、downcross restart、debt exit、crossing frontier)を具体的に実装した。ここで残された二つの残余、すなわち early representative(`representativeTime + 1 < target`)と budget gap(horizon までの予算下降の輸送)は、それぞれ `EarlyRepresentative`/`EarlyForcedCandidateClosure`/`EarlyRepresentativeComplete` と `ExtendedHistoryBudgetClosure`/`DowncrossBudgetGap` が crossing recovery への接続によって閉じる。本モジュールは `DowncrossBudgetGap` と `HistoricalDebtBridge` から import される。
