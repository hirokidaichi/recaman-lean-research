# ReadyDebtInvariant

**役割:** 強いdebt不変量に「固定horizonでの時刻準備 `target ≤ horizon + 1`」を付加したhorizon-ready debt状態を定義し、通常のdebt継続がこの条件を自動的に保存することを示す。

## このモジュールの役割

debt位相(過去に初出した妨害値を処理する探索モード)の強い証明書 `DebtInvariant` は、固定されたhistory horizonの下で初出時刻が下降していくことを保証するが、そのhorizonが目標のclock条件 `target ≤ horizon + 1` に達していることまでは述べない。ところがdebtから脱出して局所epoch定理を適用するには、この絶対時刻条件が不可欠である。本モジュールはこの一条件を対で持つ `ReadyDebtInvariant` を定義し、(1) 被覆由来のdebt子は親のclockから ready 化できること、(2) 証明書単独では ready 性が従わないことを具体的反例で示すこと、(3) 通常のdebt継続はhorizonを変えないので readiness が定義から保存されること、の三点を確立する。用語集の「horizon-ready debt / 時刻準備済み負債」がこの概念である。

## 主要な定義

### `ReadyDebtInvariant` (L18)

強いdebt証明書 `DebtInvariant target node value firstTime`(位相がdebt、局所量が初出時刻、`target ≤ value`、初出 `FirstAt a value firstTime`、`firstTime < horizon`、`value < anchor`)と、時刻準備 `target ≤ node.horizon + 1` の組。

### `ReadyDebtClosedOutcome` (L98)

readiness を保持した証明関連(proof-relevant)なdebt一歩の分類。`target_occurs`(目標出現)、`continue_debt`(同じhorizon・anchorでより早い初出時刻へ移る、readyなdebt子とランク下降の対)、`crossing`(既存の `DebtStepObstruction` そのまま)の三構成子を持つ。readiness を加えても新しい障害は一切増えない。

## 定理と証明

### `ReadyDebtInvariant.toDebtInvariant` (L25)

**主張:** readiness を忘却すると既存のdebt domainへ戻る。

**証明:** フィールド `debt` の射影である。

### `ReadyDebtInvariant.toPhaseSemanticInvariant` (L33)

**主張:** ready debtはhistorical normalへの変換なしにbroad semantic domainへ埋め込める。

**証明:** semantic domainのdebt構成子に `debt` フィールドを渡すだけである。

### `ReadyDebtInvariant.toCurrentOrDebtInvariant` (L40)

**主張:** ready debtは精密化current/debt domain(`CurrentOrDebtInvariant`)にも属する。

**証明:** 右枝(debt側)に `debt` フィールドを入れる。

### `CoverageDebtChildCertificate.toReadyDebtInvariant` (L50)

**主張:** 被覆が生んだdebt子証明書に、現在親のclock条件 `target ≤ n + 1` を外から与えれば、node `⟨n, a n, .debt, firstTime⟩` のready debtになる。

**証明:** debt子のhorizonは親時刻 `n` そのものなので、親のclock条件がそのままhorizon readinessになる。clock条件を明示的な仮定とするのは、`CoverageDebtChildCertificate` が構成時に使った親証明書を保持していないためである。

### `coverageDebtChildCertificate_does_not_imply_ready` (L64)

**主張:** 上の明示的なclock仮定は現行の証明書APIにとって本当に必要である。具体的に、`CoverageDebtChildCertificate 19 9 20 7` は成立するが `19 ≤ 9 + 1` は成立しない。

**証明:** レカマン数列の実値で構成する。値 `20` は時刻 `7` で初出し(`a 7 = 20`、それ以前に `20` は現れないことを時刻 `0` から `6` の場合分けとカーネル計算 `decide` で確認)、`a 9 = 21` である。したがって目標 `19` に対して `19 ≤ 20 < 21`、初出時刻 `7 < 9` がすべて成り立ち、node `⟨9, a 9, .debt, 7⟩` の強いdebt不変量と被覆debt子証明書が組み立てられる。一方 `19 ≤ 10` は偽である。つまりこの証明書はhorizon `9` のclockが目標に達していないまま成立し得るので、証明書単独からreadinessは導けない。

### `readyDebtStep_classify_without_normalExit` (L115)

**主張:** ready debtの一歩は必ず `ReadyDebtClosedOutcome` に分類される。特にすべての `continue_debt` 枝はreadinessを保存する。

**証明:** 既存の分類定理 `debtStep_classify_without_normalExit` を `debt` フィールドへ適用し、三枝を写す。鍵は継続枝である: 継続はhorizonを固定したまま局所の初出時刻だけを下げるので、子nodeのhorizonは親と同一であり、親の `horizon_ready` がそのまま子のreadinessになる。目標出現と障害はそのまま通す。

### `ReadyDebtClosedOutcome.toReadyDebtStep_or_obstruction` (L135)

**主張:** 分類を「目標出現/減少するready debt子/既存障害」という、refined restricted oracleが要求する正確な三択形式へ忘却できる。

**証明:** 構成子ごとの単純な振り分けである。

### `ReadyDebtInvariant.step_or_obstruction` (L157)

**主張:** ready debtの直接的な局所step。`0 < target` の下で、目標出現、readinessを保った厳密下降するdebt子、または `DebtStepObstruction` のいずれかが得られる。

**証明:** L115の分類とL135の忘却を合成するだけである。

## 全体の中での位置づけ

証明地図の「Coverage blocker」段(`CoverageDebtBridge`, `ReadyDebtInvariant`, `ReadyCurrentDebt`)の中心概念を提供する。`ReadyCurrentDebt.lean` は本モジュールの分類を `ReadyCurrentOrDebtInvariant` domainのstepへ持ち上げ、`ReadyDebtRefined.lean` は残る三つの `DebtStepObstruction` をextended-history脱出とcrossing recovery子へ精密化して、ready debtの残余なしrefined stepを完成させる。また `OrbitReadyRefinedStep.lean` では、broad semantic childのdebt構成子にhorizon clockが欠けていることが正確な残余として現れるが、それを埋める型が本モジュールの `ReadyDebtInvariant` である。
