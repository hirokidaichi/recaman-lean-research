# PermanentAboveCorridorResidual

**役割:** terminal shape(immediate valley / finite crossing window)、strict crossing balance、forced reason(insufficient value / historical blocker)、blocker positionの全case splitを一つのmaster定理へ集約し、strictな履歴予算progressの枝を分離して、真のouter residualを四constructorに確定する。

## このモジュールの役割

corridor解析の先行モジュール群は、discharge(historical downcrossの処理)の終端を段階的に分類してきた: `PermanentAboveCorridorTerminal.lean`は全dischargeを「immediate historical valley」か「terminal all-forced crossing window」の二形へ正規化し、`PermanentAboveCorridorBlocker.lean`は最終減算の失敗理由を「値の不足(insufficient value)」か「正のhistorical blocker(既出の減算候補)」に二分し、`PermanentAboveCorridorBlockerPosition.lean`はblockerの初出時刻をfresh endpointと比較した。本モジュールはこれらの直積をひとつの網羅的なinductive分類`PermanentTailTerminalResidual`にまとめる。五つのconstructorのうち一つ(blocker初出がfresh endpointより後の場合)はstrictな履歴予算下降そのものなので、進捗として分離できる。それを取り除いた残りが、本当に外側で処理すべき四つのouter residualである。

## 主要な定義

### `TerminalFiniteClockBandCertificate` (L15)

all-forced insufficient-value枝に現れる有限なreturn-clock帯: `returnTime < target`(窓の性質)かつ`target < 2·(returnTime + 1)`(insufficient valueの帰結)。すなわち`return`は`target/2 − 1 < returnTime < target`程度の有限帯に閉じ込められ、target固定の下で候補は有限個しかない。

### `PermanentTailTerminalResidual` (L21)

typed discharge証明書`PermanentTailDischargeReturnCertificate`(historical downcrossから最初のreturn upcrossingまでの全provenance)に対する網羅的terminal分類。五つのconstructorを持つ。

- `immediate_insufficient`: immediate valley(downcross直後が即return predecessorとなる正確な谷、`a(downTime+2) = a(downTime) + 1`)+ insufficient value証明書(`a(returnTime) ≤ returnTime + 1`から従う数値上界群)。
- `immediate_historical`: immediate valley + historical blocker証明書(正の減算候補`candidate = a(returnTime) − (returnTime+1)`が既出で、初出`firstTime < returnTime`、かつ`candidate`はpredecessorとtargetの両方より小さい)。このときblockerの初出は必ずfresh endpoint `downTime + 1`より前にある(`firstTime < downTime + 1`)。
- `finite_insufficient`: terminal all-forced crossing窓(`PermanentAboveCorridorWindow.lean`)+ insufficient value + 上記clock band。
- `finite_outer_blocker`: 窓 + historical blockerで、blocker初出がterminal endpoint以前(`firstTime ≤ terminalEndpoint`)。blockerは既存の外側履歴に属する。
- `finite_budget_progress`: 窓 + historical blockerで、blocker初出がterminal endpointより後(`terminalEndpoint < firstTime`)。このとき`missingBelowCount target firstTime < missingBelowCount target terminalEndpoint`という履歴予算の厳密下降が付随する。

### `PermanentTailTerminalOuterResidual` (L105)

上記から`finite_budget_progress`を除いた四constructor(immediate_insufficient、immediate_historical、finite_insufficient、finite_outer_blocker)。strict予算progressを進捗側へ分離した後に残る、真のouter residualの型である。

## 定理と証明

### `PermanentTailDischargeReturnCertificate.terminalResidual` (L72)

**主張:** すべてのtyped dischargeは`PermanentTailTerminalResidual`のいずれかのconstructorに正確に分類される。

**証明:** まず`terminalShape`(`PermanentAboveCorridorTerminal.lean`のsuffix cursor強帰納の結果)でimmediate valleyかfinite crossing windowかに分ける。次に`strictTerminalCrossingBalance.forcedReason`(`PermanentAboveCorridorBalance.lean` / `PermanentAboveCorridorBlocker.lean`)で最終減算の失敗理由をinsufficient valueかhistorical blockerかに分ける。

- immediate × insufficient: そのまま第一constructor。
- immediate × blocker: immediate valleyではfresh endpointがreturnそのものなので、blockerの`firstTime < returnTime = downTime + 1`(`firstTime_lt_immediateEndpoint`)が自動的に付く。第二constructor。
- finite × insufficient: 窓の`return_before_target`とinsufficientの`target_lt_twice_clock`を束ねてclock band証明書を作り、第三constructor。
- finite × blocker: `firstTime ≤ terminalEndpoint`かどうかで分岐する。以前なら第四constructor(outer blocker)。より後なら、blocker候補はtarget未満の値でその初出が`terminalEndpoint`より後にあるので、`missingBelowCount_strict_of_firstAt`が履歴予算の厳密下降を与え、第五constructor(budget progress)になる。

### `PermanentTailDischargeReturnCertificate.terminalBudgetProgress_or_outerResidual` (L145)

**主張:** master terminal解析は二者択一である: `terminalEndpoint < firstTime`かつ`missingBelowCount target firstTime < missingBelowCount target terminalEndpoint`を満たす時刻対が存在する(strictなbelow-history予算step)か、さもなくば四つの真のouter residualのいずれかが成り立つ。

**証明:** L72の五分類を並べ替えるだけである。`finite_budget_progress`枝は存在文の左側へ、他の四枝はそのまま`PermanentTailTerminalOuterResidual`の対応constructorへ写す。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「master terminal residual」(四outer residualへ縮約済み)に対応する。上流は`PermanentAboveCorridorTerminal.lean`(terminal二形)、`PermanentAboveCorridorBalance.lean`(strict balanceとforced reasonの取り出し)、`PermanentAboveCorridorBlocker.lean`(insufficient / blockerの二分)、`PermanentAboveCorridorBlockerPosition.lean`(初出位置の比較と予算下降)である。下流では、`PermanentAboveCorridorCandidates.lean`が`TerminalFiniteClockBandCertificate`を`List.range target`のfilterによる明示的有限列挙`terminalReturnCandidates`へ変換し、`PermanentAboveCorridorOuterHistory.lean`がouter blockerの数値rank辺を、`PermanentAboveCorridorInstalledStep.lean`が四residual全体をinstalled master rank pipelineへ接続する。dischargeの終端に何が残り得るかを一枚の型で確定させた集約点であり、以降のモジュールはこの四residualの各個撃破として読める。
