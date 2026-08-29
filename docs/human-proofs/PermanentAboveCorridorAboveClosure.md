# PermanentAboveCorridorAboveClosure

**役割:** terminal blockerのpredecessorがtarget以上である場合のclock/sign残余を、orbit-ready normalとcomplete early representativeの二つの既存total APIで完全に閉じ、historical blockerのcomplete outcomeを「target出現・early/ready semantic step・below installed master step」に限定する。

## このモジュールの役割

`PermanentAboveCorridorInstalledStep.lean`のtotal outcomeには、historical blockerのpredecessor(初出直前の実軌道値`a(firstTime − 1)`)がtarget以上だがclock未準備または非負potentialである`above_residual`枝が残っていた。本モジュールはこの残余を除去する。鍵は、predecessorのclockに正確に二つの場合しかないことである: `target ≤ firstTime`なら時刻`firstTime − 1`の実状態はorbit-ready normal node(値・座標・clock条件を同時に持つcurrent状態)であり、そうでなければ同じ実状態を旧ready history horizon上のcomplete early representative(代表時刻がhorizonより早いhistorical normal状態)として格納できる。どちらの既存APIも局所的にtotalで、target出現またはsemantic phase-rank childを返す。これをbelow-target master枝と組み合わせると、旧来のabove clock/sign残余はdischarge-level terminal outcomeから消える。

## 主要な定義

### `terminalCurrentPredecessorNode` (L25)

時刻`time`の実軌道状態をそのまま表すcurrent探索node `⟨time, a(time), normal, a(time)⟩`。horizonと値の時刻が一致するorbit-ready用のnodeである。

### `terminalHistoricalPredecessorNode` (L28)

同じ実軌道値を旧親のhorizonに載せたhistorical探索node `⟨parent.horizon, a(time), normal, a(time)⟩`。代表時刻`time`とhistory horizonが分離したextended-history用のnodeである。

### `TerminalOuterHistoricalCompleteStepOutcome` (L34)

above両clock caseを閉じた後のcomplete結果。四つのconstructorを持つ:

- `target_occurs`: `a(witness) = target`となる時刻の存在。
- `early_step`: historical predecessor node上の`EarlyRepresentativeCertificate`と、semantic invariant付きchildおよびそのnodeに対する`PhaseSearchProgress`(四成分位相ランクの厳密下降)。
- `ready_step`: current predecessor node上の`OrbitReadyNormalCertificate`と、同様のsemantic child・progress。
- `below_master`: predecessorがtarget未満の場合の`TerminalBelowPredecessorMasterRankOutcome`(`PermanentAboveCorridorMasterRank.lean`)。

`early_step`と`ready_step`はいずれもpredecessor証明書とbacktrack証明書(blocker初出直前でのdual budget下降)を併せて保持する。

### `PermanentTailTerminalCompleteInstalledOutcome` (L157)

discharge levelのterminal total outcomeからabove clock/sign残余を除去した形。`history_progress`(`missingBelowCount`のstrict下降)、`finite_return_candidate`(full finite window証明書)、`immediate_insufficient`(即時谷+insufficient証明書)、`historical_complete`(blocker証明書と上記complete outcome)の四constructor。

## 定理と証明

### `TerminalOuterHistoricalBlockerCertificate.completeStepOutcome` (L81)

**主張:** chronology eligibility(`source.downTime + 1 ≤ source.oldCrossingTime`)の下で、すべてのeligible outer blockerは`TerminalOuterHistoricalCompleteStepOutcome`を持つ。above predecessorはearlyまたはorbit-readyのtotal局所定理で閉じ、below predecessorはinstalled master結果を保つ。

**証明:** まず`exists_predecessorCertificate`(`PermanentAboveCorridorPredecessorAdapter.lean`)でpredecessor値とその初出時刻を取り、target位置で場合分けする。

*below枝。* below証明書へ変換し、eligibilityを渡して`masterRankOutcome`を適用、`below_master`を得る。

*above枝。* まず時刻`firstTime − 1`が正であることを確かめる。もし`firstTime − 1 = 0`なら`predecessor = a(0) = 0`だが、above仮定`target ≤ predecessor`と`0 < target`が矛盾する。正の時刻なので商剰余座標`CoordinatesAt (firstTime − 1) q r`が存在する。また`target ≤ a(firstTime − 1)`はabove仮定の書き換えで得る。次にclock readiness `target ≤ firstTime`で場合分けする。

- **ready(`target ≤ firstTime`)の場合。** current node上に`OrbitReadyNormalCertificate`を直接構成する。必要なfieldは、targetの正値性、node定義(`rfl`)、clock条件`target ≤ (firstTime − 1) + 1`(readiness仮定から)、値下界`target ≤ a(firstTime − 1)`、座標である。`OrbitReadyComplete.lean`の局所total定理`phaseSemanticStep`を適用すると、target出現(`target_occurs`へ)またはsemantic child + progress(`ready_step`へ)が返る。
- **not ready(`firstTime < target`)の場合。** 代表時刻がhorizon以内であること`firstTime − 1 ≤ parent.horizon`を、blockerの`firstTime < returnTime`とdischargeの`returnTime < parent.horizon`から得る。旧horizon上のhistorical nodeに`ExtendedHistoryNormalCertificate`を構成する。horizonのclock条件`target ≤ parent.horizon + 1`は親のready crossingの`horizon_ready`から移送する。not-ready条件`firstTime − 1 + 1 < target`と合わせて`EarlyRepresentativeCertificate`になり、`EarlyRepresentativeComplete.lean`のtotal定理`phaseSemanticStep`が同様にtarget出現(`target_occurs`)またはsemantic child + progress(`early_step`)を返す。

いずれの枝でもbacktrack証明書はblockerから取って結論に添える。

### `PermanentTailDischargeReturnCertificate.terminalCompleteInstalledOutcome` (L185)

**主張:** すべてのdischarge/return証明書は`PermanentTailTerminalCompleteInstalledOutcome`を持つ。

**証明:** `PermanentAboveCorridorInstalledStep.lean`の`terminalInstalledStepOutcome`を場合分けする。最初の三枝はそのまま対応するconstructorへ写す。`historical_step`枝では、束ねられたeligibility証明`installed.eligible`を渡してL81の`completeStepOutcome`を適用し、`historical_complete`を得る。installed step outcomeに残っていた`above_residual`は、L81がpredecessor証明書から直接再分類することで現れなくなる。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「above predecessor closure」(clock/sign残余を除去済み)に対応する。上流は`PermanentAboveCorridorInstalledStep.lean`(total installed step)、`PermanentAboveCorridorPredecessorAdapter.lean`(predecessor証明書)、および位相統合層の二つのtotal API — `OrbitReadyComplete.lean`(current normalの局所totality)と`EarlyRepresentativeComplete.lean`(early representativeの完全閉包)である。下流では`PermanentAboveCorridorImmediateClosure.lean`が本モジュールのoutcomeを引き継いでimmediate insufficient枝をsemantic閉包し、以降のreturn/window選択モジュール群と`PermanentAboveCorridorTerminalProgress.lean`の四progress形統合もこの`historical_complete`構造の上に築かれる。
