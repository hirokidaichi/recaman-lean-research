# CoverageDebtBridge

**役割:** 現在状態の親から得た `CoverageStep` のblockerを、未来の初出なら orbit-ready な現在normal子、過去の初出なら強いdebt子へ振り分け、汎用のhistorical normal nodeを完全に回避する橋渡し。

## このモジュールの役割

大域探索の基本部品である `CoverageStep`(目標 `m` の出現、または `m ≤ y < v` を満たすより小さい初出値 `y` の提示)は、一般には「履歴のどこかで初出した値」しか返さない。これを素朴に探索nodeへ変換すると、現在の軌道状態と対応しないhistorical normal node(座標もepoch定理も適用できない弱い証明書)が生まれてしまう。本モジュールは、親が実際の軌道の現在状態(canonical start または orbit-ready normal)である場合に限れば、blockerの初出時刻と親時刻の大小で完全に二分できることを示す。初出が親より未来なら、その初出時刻自体が新しい現在状態であり orbit-ready 証明書が作れる。初出が親より過去なら、親のhorizonとanchorを保ったままdebt位相(過去の初出値を処理する探索モード)へ入り、強い `DebtInvariant` が成立する。いずれの枝でも四成分ランクは厳密に下がるため、historical normal構成子を一切使わずに探索を継続できる。

## 主要な定義

### `CurrentCoverageParentCertificate` (L22)

現在親に要求する最小限の仮定を束ねた構造体。目標の正値性 `0 < target`、時刻準備 `target ≤ n + 1`(目標がその時刻の探索で扱える段階に達していること)、値の下界 `target ≤ a n` の三つからなる。canonical start証明書とorbit-ready証明書のどちらからも取り出せる共通インターフェースである。

### `CoverageCurrentChildCertificate` (L31)

未来blocker枝の正確なデータ。`target < value`、初出 `FirstAt a value firstTime`、親時刻より真に未来 `n < firstTime`、値の厳密減少 `value < a n` に加え、初出時刻を現在状態とする `OrbitReadyNormalInvariant` と、親からのランク下降 `PhaseSearchProgress` を保持する。

### `CoverageDebtChildCertificate` (L45)

過去blocker枝の正確なデータ。`target < value`、初出、`firstTime < n`、`value < a n` に加え、node `⟨n, a n, .debt, firstTime⟩`(horizon・anchorは親のまま、位相はdebt、局所量は初出時刻)についての強い `DebtInvariant`、broad semantic所属、ランク下降を保持する。

### `CoverageCurrentDebtOutcome` (L62)

現在親からの `CoverageStep` の証明保持型分類。`target_occurs`(目標出現)、`current_child`(未来枝の証明書)、`debt_child`(過去枝の証明書)の三構成子を持つ。目標との等号は子を作る前に処理されるため、どちらの子証明書も `target < value` の厳密不等式を保つ。

### `CurrentOrDebtInvariant` (L210)

`OrbitReadyNormalInvariant target node ∨ ∃ value firstTime, DebtInvariant target node value firstTime` として定義される精密化domain。historical normal nodeを意図的に含まない。

## 定理と証明

### `TargetStartCertificate.toCurrentCoverageParentCertificate` (L75)

**主張:** canonical start証明書(`InitialRegion` が供給する、目標近傍の開始時刻の証明書)は `0 < target` の下で現在親証明書を与える。

**証明:** 証明書のフィールド `time_ready` と `value_ready` をそのまま移すだけである。

### `OrbitReadyNormalInvariant.toCurrentCoverageParentCertificate` (L86)

**主張:** canonical node `targetStartNode n = ⟨n, a n, .normal, a n⟩` におけるorbit-ready不変量も同じ現在親証明書を与える。

**証明:** orbit-ready証明書は存在量化された時刻 `time` を持つが、node等式 `node = ⟨time, a time, .normal, a time⟩` のhorizon成分を比較すると `time = n` が従う。あとは証明書の `time_ready`、`target_le_value` を読み替える。どの座標が readiness を証言していても結論は変わらない。

### `coverageStep_currentOrDebt` (L110)

**主張:** 現在親証明書と `CoverageStep target (a n) n` から、`CoverageCurrentDebtOutcome target n` が得られる。すなわち目標出現・未来current子・過去debt子のいずれかに必ず分類できる。

**証明:** 本モジュールの中核である。`CoverageStep` の第一枝(目標出現)はそのまま `target_occurs` になる。第二枝はblocker `(value, firstTime)` を与え、`target ≤ value`、`FirstAt a value firstTime`、`value < a n` が成り立つ。

まず `value = target` の場合、初出の定義から `a firstTime = value = target` なので目標出現である。以下 `target < value` とする。

初出時刻と親時刻を比較する。`n ≤ firstTime` の場合、実は等号は起こらない: `firstTime = n` なら初出の定義から `a n = value` となり `value < a n` と矛盾する。よって `n < firstTime` である。この初出時刻は正なので座標 `CoordinatesAt firstTime q r` が存在し、`a firstTime = value` から `target ≤ a firstTime` と `a firstTime < a n` を得る。時刻準備は親の `target ≤ n + 1` と `n < firstTime` から `target ≤ firstTime + 1` として従う。これで `targetStartNode firstTime` のorbit-ready証明書がそろう。ランク下降は「horizonが伸び(履歴予算 `missingBelowCount` は非増加)、anchorが `a firstTime < a n` と厳密に下がる」ことから辞書式に成立する(`phaseSearchProgress_of_horizonAndAnchor`)。

`firstTime < n` の場合、子node を `⟨n, a n, .debt, firstTime⟩` とする。`DebtInvariant` の全フィールド — 位相がdebt、局所量が初出時刻、`target ≤ value`、初出、`firstTime < n`(horizon内)、`value < a n`(anchor未満)— はblockerのデータそのものである。ランク下降は、horizon・anchor不変のままdebt位相へ入ることで位相成分が厳密に下がること(`phaseSearch_enterDebt`)から従う。

### `coverageStep_targetStart_currentOrDebt` (L191)

**主張:** canonical start証明書を親とするwrapper。

**証明:** L75の変換を挟んで主橋渡しを適用する。

### `coverageStep_orbitReady_currentOrDebt` (L200)

**主張:** orbit-ready親を持つ場合のwrapper。

**証明:** L86の変換を挟んで主橋渡しを適用する。

### `CoverageCurrentDebtOutcome.toCurrentOrDebtStep` (L217)

**主張:** 証明保持型分類を忘却すると、「目標出現、または `CurrentOrDebtInvariant` を満たす子とランク下降の対」という制限step形式になる。

**証明:** 三構成子をそれぞれの選言枝へ写すだけである。current子はdomainの左枝、debt子は右枝に入る。

### `CoverageCurrentDebtOutcome.toPhaseSemanticStep` (L236)

**主張:** 同じ分類はbroad semantic domain(`PhaseSemanticInvariant`)のstepとしても読める。しかもその際、historical normal構成子は一度も使われない。

**証明:** current子はorbit-ready不変量を経由してsemantic domainへ埋め込み、debt子は証明書が保持する `semantic` フィールドをそのまま使う。

## 全体の中での位置づけ

証明地図の「Coverage blocker」段に対応する。`ReadyDebtInvariant.lean` はここで作られるdebt子証明書に親のclock条件を付加してhorizon-ready化し(`CoverageDebtChildCertificate.toReadyDebtInvariant`)、`ReadyCurrentDebt.lean` は本モジュールの分類を親のclockが生きているうちに `ReadyCurrentOrDebtInvariant` へ変換する。さらに `OrbitReadyDirectRefined.lean` の各refined step定理は、被覆を生成するすべての分岐でこの橋渡しを通すことで、refined child domainからhistorical normal nodeを排除している。
