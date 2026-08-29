# ReadyCurrentDebt

**役割:** orbit-readyな現在normal状態とhorizon-readyな強debt状態からなる精密化domain `ReadyCurrentOrDebtInvariant` を定義し、被覆の橋渡しとready debt継続がこのdomainで閉じることを示す。

## このモジュールの役割

`CoverageDebtBridge` は現在親からの `CoverageStep` を「未来current子/過去debt子」へ分けるが、debt子の証明書は親のclock条件を保持していない(`ReadyDebtInvariant.lean` の反例)。本モジュールは、親の `CurrentCoverageParentCertificate` がまだスコープにあるうちに被覆の分類結果を変換することで、debt子にhorizon readinessを渡し損ねないようにする統合点である。得られるdomainは「現在の実軌道状態(orbit-ready normal)」と「時刻準備済みのdebt状態(ready debt)」だけからなり、以後の再帰探索でepoch定理群を常に適用できる。さらに、ready debtの一歩がこのdomain内に留まること(唯一の残余は既存のcrossing障害)も示す。

## 主要な定義

### `ReadyCurrentOrDebtInvariant` (L18)

`OrbitReadyNormalInvariant target node ∨ ∃ value firstTime, ReadyDebtInvariant target node value firstTime`。すなわち、実際に時刻 `time` の軌道状態であり `target ≤ time + 1` と座標を持つ現在normal node、または固定horizonが目標時刻に達している強debt node、のいずれかである。

## 定理と証明

### `ReadyCurrentOrDebtInvariant.toCurrentOrDebtInvariant` (L25)

**主張:** debt側のreadinessを忘却すると、以前の(readyでない)current/debt domainに埋め込まれる。

**証明:** current枝は恒等、debt枝は `ReadyDebtInvariant` の `debt` フィールドを射影する。

### `ReadyCurrentOrDebtInvariant.toPhaseSemanticInvariant` (L34)

**主張:** 精密化domainの各nodeは既存のbroad semantic domainにも属する。

**証明:** current枝はorbit-ready不変量のsemantic埋め込み、debt枝はready debtのsemantic埋め込み(いずれも既証明の変換)をそのまま使う。

### `CoverageCurrentDebtOutcome.toReadyCurrentOrDebtStep` (L45)

**主張:** 現在親証明書がスコープにある状態で、被覆の分類 `CoverageCurrentDebtOutcome target n` を「目標出現、または `ReadyCurrentOrDebtInvariant` を満たす子とランク下降の対」へ変換できる。

**証明:** 目標出現枝はそのまま。current子枝は、証明書が保持する `OrbitReadyNormalInvariant`(node `targetStartNode firstTime`)と `PhaseSearchProgress` をdomainの左枝として返す。debt子枝が本定理の存在理由である: debt子のhorizonは親時刻 `n` なので、親証明書の `time_ready : target ≤ n + 1` を `CoverageDebtChildCertificate.toReadyDebtInvariant` に渡してhorizon-ready化し、右枝として返す。被覆の出力が親証明書を忘れた後ではこの変換は不可能であり、ここが「debt子がreadinessを失わないための統合点」である。

### `coverageStep_readyCurrentOrDebt` (L67)

**主張:** 現在親証明書と `CoverageStep target (a n) n` から直接、目標出現または精密化ready domainの厳密なstepが得られる。

**証明:** `coverageStep_currentOrDebt`(CoverageDebtBridge)で分類し、L45で変換する合成である。

### `coverageStep_targetStart_readyCurrentOrDebt` (L78)

**主張:** canonical start証明書を親とするwrapper。

**証明:** 証明書から現在親データを取り出してL67を適用する。

### `coverageStep_orbitReady_readyCurrentOrDebt` (L90)

**主張:** orbit-readyな現在親を持つ場合のwrapper。親nodeの実際の形(`targetStartNode n`)が、同じhorizon上界をdebt子まで届けることを保証する。

**証明:** orbit-ready不変量から現在親データを取り出してL67を適用する。

### `ReadyDebtClosedOutcome.toReadyCurrentOrDebtStep_or_obstruction` (L102)

**主張:** ready debtの一歩の分類(`ReadyDebtClosedOutcome`)を、精密化domainのstepまたは既存のcrossing障害 `DebtStepObstruction` へ、障害を一切変形せずに忘却できる。

**証明:** 目標出現はそのまま。`continue_debt` 枝は、子node `⟨horizon, anchor, .debt, childTime⟩` がready debtなのでdomainの右枝に入り、付随するランク下降(局所の初出時刻の厳密下降)と組にする。`crossing` 枝は障害をそのまま返す。

### `ReadyDebtInvariant.readyCurrentOrDebtStep_or_obstruction` (L123)

**主張:** ready debtの局所step。`0 < target` の下で、目標出現、精密化ready domain内の厳密step、または三種の既存crossing障害のいずれかになる。通常継続はdomainを保存し、残余は既存障害のみである。

**証明:** `readyDebtStep_classify_without_normalExit`(ReadyDebtInvariant)による分類にL102の忘却を合成する。

## 全体の中での位置づけ

証明地図の「Coverage blocker: ready current/debt閉包済み」段の仕上げにあたる。本モジュールのdomainは、`OrbitReadyRefinedStep.lean` が定義するrefined child domain `OrbitReadyRefinedInvariant`(= `ReadyCurrentOrDebtInvariant ∨ ExtendedHistoryNormalInvariant ∨ CrossingSearchInvariant`)の第一成分であり、`OrbitReadyDirectRefined.lean` の各生成分岐は被覆を経る場合すべてL67の橋渡しを通る。残余として残るcrossing障害は `ReadyDebtRefined.lean` がcrossing recovery子とextended-history脱出へ解消する。
