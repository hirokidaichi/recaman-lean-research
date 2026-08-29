# PermanentAboveCorridorLandingInstall

**役割:** combined permanent-tail証明書がhorizonにしか依存しないことを使って、搭載済みlanding crossing node上へ証明書全体を移送し、閉じたterminal解析をそのnodeから再入可能にする。あわせて、mounted nodeと旧parentのrank関係を「anchorの厳密下降ならglobal位相退出、さもなくばanchor非減少」の既知二分へ載せる。

## このモジュールの役割

`PermanentAboveCorridorLandingMount.lean`でhistory枝はready crossing nodeという semantic domainの実objectを手にしたが、そのnodeが「解析の終端の葉」なのか「同じ解析を続けられる新しいparent」なのかは未確定だった。本モジュールは後者であることを示す。鍵となる観察は、combined証明書(`PermanentTailCombinedCertificate` = tail + zero-budget crossing + minimum blocker)のうちready crossing以外の全フィールド — horizonがtail内にあること、履歴予算0、horizon値のstrict上方性、future downcross不在、およびtail・minimum証明書 — がnodeのhorizon成分にしか依存しないことである。mounted node `⟨parent.horizon, a(c), normal, a(c)⟩`はparentとhorizonを共有するので、証明書全体が定義的にそのまま移送でき、mounted nodeを新しいparentとするcombined証明書が得られる。従ってterminal解析(`terminalMountedOutcome`)はmounted nodeから再入でき、landing枝は反復の一段になる。旧parentとのrank比較は、installed successor反復を統べるのと同じ二分 — crossing直前値がparent anchorより厳密に小さければ即時のglobal `PhaseSearchProgress`、さもなくばanchor非減少 — に従う。

## 主要な定義

### `MountedLandingRankOutcome` (L62)

mounted crossing nodeの旧parentに対するrank位置の二分。

- `phase_exit`: mounted nodeから旧parentへの`PhaseSearchProgress`(四成分global位相rankの厳密下降)が成り立つ。
- `anchor_nondecreasing`: `parent.anchorParent ≤ a(crossingTime)`、すなわち新crossingの直前値が旧anchorを下回らない。

## 定理と証明

### `PermanentTailCombinedCertificate.installReadyCrossing` (L24)

**主張:** combined証明書は、同じhorizonを持つ任意のmounted ready crossing nodeへ移送できる: parentについての`PermanentTailCombinedCertificate`と、node `terminalPredecessorCrossingNode parent crossingTime`上の`ReadyCrossingSearchInvariant`から、そのnodeをparentとする同じ`minimumTime`・`predecessorFirstTime`のcombined証明書が得られる。

**証明:** まず`PermanentTailCrossingCertificate`をnode上で再構成する。`ready_crossing`は仮定そのもの。残る五条件 — `horizon_in_tail`(`start ≤ horizon`)、`tail_strictly_before_horizon`(`start < horizon`)、`budget_zero`(`missingBelowCount target horizon = 0`)、`horizon_strictly_above`(`target < a(horizon)`)、`no_future_downcross` — はいずれもnodeのhorizon成分だけの述語であり、mounted nodeのhorizonは定義上`parent.horizon`なので、parentの対応フィールドが定義展開(`simpa`)だけで移る。最後に、nodeに依存しない`tail`と`minimum`をそのまま添えれば、mounted nodeをparentとするcombined証明書が完成する。上流の定理には一切触れない、純粋な移送である。

### `PermanentTailCombinedCertificate.mountedLandingRankOutcome` (L74)

**主張:** すべてのmounted crossing nodeは旧parentに対して`MountedLandingRankOutcome`の二分に入る。

**証明:** `a(crossingTime) < parent.anchorParent`かどうかで場合分けする。

*厳密下降の場合。* parentのready crossing不変量を展開すると、その`node_eq`によりparent自身が`⟨parent.horizon, a(oldTime), normal, a(oldTime)⟩`という形であり、とくに`parent.anchorParent = a(oldTime)`(旧crossingの搭載値)である。従って仮定は`a(crossingTime) < a(oldTime)`となり、mounted nodeとparentはhorizonが等しくanchorが厳密に下がるので、既存補題`phaseSearchProgress_of_horizonAndAnchor`(`NormalClosure.lean`: horizon非減少+anchor厳密下降は位相progress)がそのまま`PhaseSearchProgress`を与える。これは反復の内部ではなく、global位相rankへの即時exitである。

*そうでない場合。* 否定から`parent.anchorParent ≤ a(crossingTime)`をliteralに返す。

この二分は`PermanentAboveCorridorSelectedInstall.lean`以来のinstalled successor反復を統べるanchor境界と同じ形であり、mounted landing crossingも同じrank体制の下に入ることを意味する。

### `PermanentTailCombinedCertificate.terminalMountedOutcome_of_landing` (L98)

**主張:** 閉じたterminal解析はmounted landing crossingから再入する: parentのcombined証明書とmounted nodeのready crossing不変量から、mounted nodeをparentとする`PermanentTailTerminalMountedOutcome`が得られる。landing枝は終端の葉ではなく、同じ解析の新しいparentである。

**証明:** L24でcombined証明書をmounted nodeへ移送し、その上で`terminalMountedOutcome`(`PermanentAboveCorridorLandingMount.lean`)を適用するだけである。一行の合成だが、これによりlanding → mount → install → 再びterminal解析、という反復の輪が型レベルで閉じる。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「landing crossing mount」の直後に位置し、mount段階で得たsemantic nodeを反復の新parentへ昇格させる。上流は`PermanentAboveCorridorLandingMount.lean`(搭載nodeと`terminalMountedOutcome`)、`PermanentAboveTail.lean`(crossing証明書のhorizon依存性)、`NormalClosure.lean`(位相progress補題)である。これでhistory枝の再帰構造は、installed successor反復(`PermanentAboveCorridorSuccessorRank.lean`〜`PermanentAboveCorridorIterationClosure.lean`)と同じ「anchor厳密下降ならglobal exit、さもなくばanchor非減少のまま次のparentへ」という統一境界に従う。残る反復残余は、semantic枝の位相rank、replay固定点(`PermanentAboveCorridorReplayPinning.md`以降の数値挟撃が進行中)、およびanchor非減少のまま続くlanding反復に対する新しいwell-founded量の三点であり、landing枝自体はもはやinterfaceの盲点ではない。
