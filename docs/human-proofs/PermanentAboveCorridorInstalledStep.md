# PermanentAboveCorridorInstalledStep

**役割:** terminal residual treeの全分岐をblocker-predecessorのsemantic/master-rank pipelineへ接続し、一回のdischarge解析を「strict history progress・finite return候補・immediate insufficient・typed historical step」の四形total outcomeへ統合する。

## このモジュールの役割

恒久上方tail(仮想的な最小未出`target`が強制する、以後ずっと`target`より大きい軌道区間)のdischarge/return証明書(`PermanentTailDischargeReturnCertificate`、historical downcrossからcanonical return upcrossingまでの全provenance)に対して、先行モジュール群は残余をimmediate二形・finite clock band・finite outer blockerの四outer residualまで縮約し(`PermanentAboveCorridorResidual.lean`、`PermanentAboveCorridorCandidates.lean`)、blockerのpredecessorをnormal-ready/above残余/below-target master stepへ分類していた(`PermanentAboveCorridorPredecessorAdapter.lean`、`PermanentAboveCorridorMasterRank.lean`)。本モジュールはこれらを合成して、discharge一回が必ず返す四つのtop-level結果 — strict missing-history進捗、有限return-clock候補への所属、immediate insufficient算術残余、eligible historical predecessor step — を一つの定理にまとめる。historical枝ではchronology的にineligibleな旧crossing自体がstrict history progressになること、below-target master結果が次のsemantic installed parentを再構成できるだけのcrossingデータを保持することも同時に示す。

## 主要な定義

### `TerminalOuterHistoricalInstalledStepOutcome` (L26)

eligibleなterminal outer blocker(final forced additionを妨げた既出値`candidate`とその初出`firstTime`の証明書)一つに対するsemantic/master結果。三つのconstructorを持つ:

- `normal_ready`: predecessor(初出直前の実軌道値`a(firstTime − 1)`)が既存のnormal位相invariant `NormalPhaseInvariantAt`に入る。
- `above_residual`: predecessorがtarget以上だがclock未準備または非負potentialである明示的残余(`AboveTargetPredecessorResidual`)。
- `below_master`: predecessorがtarget未満で、`TerminalBelowPredecessorMasterRankOutcome`(global phase exitまたは七成分master rankのstrict辺)を持つ。

いずれの枝も、blocker初出直前へのdual budget下降を与える`TerminalHistoricalBacktrackCertificate`を併せて保持する。

### `TerminalOuterHistoricalEligibleInstalledStep` (L107)

chronology eligibility証明`source.downTime + 1 ≤ source.oldCrossingTime`と上記outcomeの組。後段の精密化がeligibility証明を再構成せずに済むよう、両者を一つの構造体に束ねる。

### `TerminalFiniteReturnWindowCertificate` (L118)

finite枝のfull provenance。従来はreturn clockのband所属だけが残されていたが、本構造体は(1) `origin_le`: terminal endpointがdowncross endpoint以後にあること、(2) `window`: all-forced crossing窓の算術証明書(`TerminalAllForcedCrossingWindow`)、(3) `insufficient`: 最終減算失敗の数値証明書、(4) `clock_band`: `return < target < 2(return+1)`のband証明書、(5) `candidate_membership`: `source.returnTime ∈ terminalReturnCandidates target`、をすべて保持する。この完全保持が後の選択rank化(`PermanentAboveCorridorWindowSelection.lean`以降)と最終的な算術的排除(`PermanentAboveCorridorFiniteClosure.lean`)を可能にする。

### `PermanentTailTerminalInstalledStepOutcome` (L132)

discharge levelでのconstructor-complete outcome。`history_progress`(`missingBelowCount`のstrict下降`TerminalChronologyHistoryProgress`)、`finite_return_candidate`、`immediate_insufficient`(即時谷+insufficient証明書)、`historical_step`(blocker証明書とeligible installed step)の四形。

## 定理と証明

### `TerminalOuterHistoricalBlockerCertificate.installedStepOutcome` (L60)

**主張:** chronology eligibility(`source.downTime + 1 ≤ source.oldCrossingTime`)の下で、すべてのeligible outer blockerはfull semantic/master pipelineに入る。

**証明:** `PermanentAboveCorridorPredecessorAdapter.lean`の完全分類`predecessorSemanticOutcome`を場合分けする。`normal_ready`と`above_residual`はそのまま対応するconstructorへ写し、`below_historical`枝ではbelow証明書に`PermanentAboveCorridorMasterRank.lean`の`masterRankOutcome`(eligibility仮定を使用)を適用して`below_master`を得る。backtrack証明書は各枝でblockerの`backtrackCertificate`から供給する。

### `TerminalBelowPredecessorMasterRankOutcome.exists_install` (L83)

**主張:** すべてのbelow-target master結果は、選択crossingとそのinstalled permanent-tail親を露出する: ある`crossingTime`と座標に対する`TerminalBelowPredecessorCrossingCertificate`と、その上の`TerminalSelectedCrossingInstallCertificate`が存在する。

**証明:** master outcomeの二つのconstructor(global phase exitである`phase_exit`と、master rank辺である`master_progress`)は、どちらも選択crossing証明書をデータとして保持している。その証明書に`PermanentAboveCorridorSelectedInstall.lean`の`install`を適用するだけでよい。すなわちmaster pipelineを通過したbelow枝は、進捗の種類によらずsemantic反復用の親を失わない。

### `PermanentTailDischargeReturnCertificate.terminalInstalledStepOutcome` (L162)

**主張:** すべてのterminal dischargeは、証明済みのstrict history辺、有限候補、immediate数値残余、typed installed historical stepのいずれかへ到達する(total)。

**証明:** 二段構成である。

*第一段(非clock残余の処理)。* 補助関数として、`PermanentTailTerminalNonClockResidual`(immediate二形+finite outer blockerの三形、`PermanentAboveCorridorCandidates.lean`)から結論を導く変換を作る。`PermanentAboveCorridorOuterHistory.lean`の`rankOutcome`で三分類し、

- `immediate_insufficient`はそのまま第三constructorへ。
- `forward_budget_progress`(blocker初出がfresh endpointより後の場合)は、`missingBelowCount`のstrict下降そのものなので`history_progress`へ。
- `original_history_blocker`(blocker初出がfresh endpoint以前)はchronology eligibilityで場合分けする。eligible(`downTime + 1 ≤ oldCrossingTime`)ならL60を適用してeligible installed stepを束ね`historical_step`へ。ineligible(`oldCrossingTime < downTime + 1`)なら、downcross endpoint `a(downTime + 1)`はbelow-targetの値の初出であり、その時刻は`oldCrossingTime`より真に後なので、`missingBelowCount_strict_of_firstAt`により`missingBelowCount target (downTime+1) < missingBelowCount target oldCrossingTime`。すなわちchronology mismatchは処理すべき残余ではなく、それ自体がstrict history progressである。

*第二段(master residualの振り分け)。* `PermanentAboveCorridorResidual.lean`の`terminalBudgetProgress_or_outerResidual`を適用する。左枝(fresh endpointより後のblocker初出によるstrict budget progress)は直ちに`history_progress`。右枝の四outer residualのうち、`finite_insufficient`はwindow・insufficient・bandを束ねて`TerminalFiniteReturnWindowCertificate`を組み(候補list所属はbandの`mem_terminalReturnCandidates`)、`finite_return_candidate`へ。残る三形は第一段の変換に渡す。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「terminal installed step」(discharge全枝を統合済み)に対応する。上流は`PermanentAboveCorridorResidual.lean`/`Candidates.lean`(outer residualの分類)、`PermanentAboveCorridorOuterHistory.lean`(backtrackとrank分類)、`PermanentAboveCorridorPredecessorAdapter.lean`(semantic分類)、`PermanentAboveCorridorMasterRank.lean`(七成分rank)、`PermanentAboveCorridorSelectedInstall.lean`(install)である。下流では`PermanentAboveCorridorAboveClosure.lean`が本モジュールの`historical_step`枝から`above_residual`を除去してcomplete化し、`TerminalFiniteReturnWindowCertificate`は`PermanentAboveCorridorWindowSelection.lean`以降の有限選択と`PermanentAboveCorridorFiniteClosure.lean`での矛盾導出の入力になる。
