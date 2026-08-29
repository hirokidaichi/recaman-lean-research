# RefinedOracleBoundary

**役割:** refined child domainのconstructor監査を完了し、全射性への未証明残余を`CrossingRefinedStepHypothesis`ただ一つの局所命題に縮約する。

## このモジュールの役割

大域探索は、proof-carryingなノードだけを対象とするrefined domain

```text
OrbitReadyRefinedInvariant =
  ReadyCurrentOrDebtInvariant ∨ ExtendedHistoryNormalInvariant ∨ CrossingSearchInvariant
```

の上で行われる。orbit-ready currentノード、ready debtノード(debtは「通常探索へ戻る前に解消すべき局所的証明義務」の比喩)、extended-history normalノードの三者には、それぞれ先行モジュールで残余なしの直接refined step定理が用意されている。唯一、crossing recoveryノード(target未満からtarget以上への強制加算横断を記録し、pre-crossing値をanchorに採るノード)だけがまだ局所stepを持たない。本モジュールはその残る義務を、任意の数値ノードへ広げ戻すことなく、型付きの仮説`CrossingRefinedStepHypothesis`として一箇所に梱包し、この仮説だけからtargetの出現(occurrence)が従うことを証明する。

## 主要な定義

### `CrossingRefinedStepHypothesis` (L16)

restricted phase-search oracle(オラクル: 各探索ノードで「目標到達または真に小さい次ノード」を構成できるという証明義務)をrefined domain上で完成させるために残る、ただ一つの局所命題である。すなわち「`CrossingSearchInvariant`を満たす任意のノードについて、targetが軌道に出現するか、またはrefined domainに属しランクが真に下がる子ノードが存在する」という主張を、target `m`ごとの命題として定義する。

## 定理と証明

### `OrbitReadyRefinedInvariant.refinedStep_or_crossing` (L25)

**主張:** `0 < target`のとき、refined domainの任意のノードは、(i) targetの出現、(ii) refined domain内でランク進捗する子、のいずれかを与えるか、さもなくば (iii) 自身の`CrossingSearchInvariant`証明書をそのまま返す。すなわちconstructorごとの完全監査である。

**証明:** refined domainの三つの選言肢で場合分けする。

- orbit-ready currentノードは`OrbitReadyDirectRefined`の直接step定理で (i) または (ii) を返す。
- ready debtノードでは、まずdebt証明書からノードの位相成分が`debt`、局所成分が初出時刻であることを取り出してノードの形を正規化し、`ReadyDebtRefined`の直接step定理を適用する。
- extended-history normalノードは`ExtendedHistoryDirectRefined`の直接step定理で閉じる。
- crossingノードは証明書を変形せずそのまま (iii) として返す。ここが唯一、局所stepが未証明の分岐である。

### `refinedPhaseSearchOracle_of_crossing` (L46)

**主張:** `CrossingRefinedStepHypothesis target`を仮定すれば、`OrbitReadyRefinedInvariant target`を有効領域とするrestricted phase-search oracleが得られる。

**証明:** 任意の有効ノードに前定理を適用する。(i)(ii)の場合はそのままoracleの結論である。(iii)の場合は仮定した仮説をそのcrossing証明書に適用すればよい。仮説は結論の子ノードもrefined domainに返すので、領域は保存される。

### `targetStartInvariant_orbitReadyRefined` (L57)

**主張:** 正のtargetに対する正準開始ノード(`TargetStartInvariant`)は、refined domainのcurrent成分に属する。

**証明:** 正準開始証明書はorbit-ready normal証明書へ直接変換でき(値が実際に`a(time)`であり、時計・座標条件を持つ)、これはrefined domainの第一選言肢である。1〜2行の埋め込み補題である。

### `crossingRefinedStepHypothesis_implies_occurs` (L65)

**主張:** `0 < target`かつ`CrossingRefinedStepHypothesis target`ならば、`∃ witness, a(witness) = target`。すなわち大域出現定理は、この型付きcrossing局所仮説ひとつに帰着した。

**証明:** `PhaseSearchStart`の整礎探索定理`targetStart_reaches_of_restrictedOracle`を、有効領域`OrbitReadyRefinedInvariant target`で起動する。開始ノードが領域に入ることは前定理、各ステップの供給は`refinedPhaseSearchOracle_of_crossing`が与える。四成分辞書式ランク(履歴予算、anchor、位相、局所量)は整礎なので、oracleの反復は有限回でtargetの出現枝に到達する。

## 全体の中での位置づけ

証明地図の「refined oracle境界」の行そのものであり、状態は「crossingだけ未証明」である。上流では`OrbitReadyDirectRefined`、`ReadyDebtRefined`、`ExtendedHistoryDirectRefined`が非crossing三成分の直接stepを供給し、本モジュールがそれらを束ねて残余を一点に絞る。下流では`CrossingRefinedBoundary`がこの残る一点のランク上の形(strict budget dropかcrossing内下降しかない)を確定し、`CrossingDowncrossRefined`・`CrossingBelowRefined`・`CrossingTailRefined`が`CrossingRefinedStepHypothesis`の充足を`TargetTailReturnHypothesis`という長期軌道命題まで縮約していく。
