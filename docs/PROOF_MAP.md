# 証明地図

本書で使う`potential`、`borrow`、`blocker`、`epoch`、`oracle`、`debt`などの意味と、
標準用語／研究固有用語の区別は[用語集](GLOSSARY.md)を参照。
ordinary normal constructorの生成箇所と精密化方針は
[normal provenance監査](NORMAL_PROVENANCE_AUDIT.md)にまとめる。

## 全体依存関係

```mermaid
flowchart TD
    A["数列・履歴定義"] --> B["商剰余・ポテンシャル"]
    B --> C["借用遷移の全域式"]
    C --> D["実多段借り排除"]
    D --> E["負エポック有限化"]
    E --> F["非負帯有限化"]
    F --> G["三成分履歴ランク"]
    G --> H["対角負債分岐"]
    H --> I["極大後方鎖・早期blocker"]
    I --> J["四成分位相ランク"]
    J --> K["負債・crossing閉包"]
    K --> L["canonical局所オラクル"]
    L --> M["refined非crossing domain"]
    M --> N["ready crossing: tail returnまで縮約"]
    N --> O["tail return／refined restricted oracle"]
    O --> P["全射性"]
```

上図の`数列・履歴定義`から`refined非crossing domain`までは証明済みである。
ready crossingの局所stepは`TargetTailReturnHypothesis`まで縮約済みである。
この長期再帰命題とrefined oracleへのclocked domain統合以降が未証明である。

## 状況一覧

| 領域 | 状態 | 内容 | 主モジュール |
|---|---|---|---|
| 数列定義 | 証明済み | 再帰、履歴、減算可能性 | `Basic`, `History` |
| 座標力学 | 証明済み | 通常・借用・全域遷移 | `Coordinates`, `CoordinateDynamics`, `MultiBorrow` |
| 実軌道上界 | 証明済み | `aₙ≤U(n)`、`2q≤n+1` | `OrbitBounds` |
| 多段借り | 解消済み | 実軌道では`b=0,1`のみ | `OrbitBounds` |
| 目標面 | 証明済み | `G=m`と目標方程式の接続 | `LandingSurfaces`, `PrestateCoverage` |
| 負領域 | 証明済み | 有限時間で一段借り | `Recovery`, `RecoveryBudget` |
| 高商障壁 | 証明済み | 高商失敗をblockerへ変換 | `RecoveryFrontier`, `OneBorrowFrontier` |
| 非負帯 | 証明済み | 負領域復帰・Coverage・レベル下降 | `Undershoot` |
| 大域値帰納 | 証明済み | `CoverageOracle`から全射性 | `Coverage` |
| 履歴探索帰納 | 証明済み | 三成分ランクと抽象オラクル | `HistoryBudget`, `HistoryFrontier` |
| 対角後方履歴 | 証明済み | 極大減算鎖と早期blocker | `Diagonal` |
| 位相探索 | 骨格証明済み | 四成分ランクと抽象オラクル | `PhaseSearch` |
| 負債局所解析 | semantic閉包済み | 同時成長は実在するが、frontier下降またはstrong debt self-exitで閉包 | `DebtInvariant`, `DebtSubtraction`, `DebtAddition`, `DebtStep`, `DebtBackward`, `DebtCrossing`, `AnchorBoundary`, `CrossingRecovery`, `CrossingGap`, `CrossingGrowth`, `CrossingHorizon`, `CrossingIteration`, `CrossingFrontier` |
| 負エポック位相接続 | ランク証明済み | 対角仮定なしで目標出現またはPhaseSearchProgress | `PhaseEpoch` |
| canonical開始 | 局所閉包済み | 全符号とlevel 0/1/2を分類し、強制成長も二段先のCoverageStepへ回収 | `CanonicalOracle`, `CanonicalLevelZero`, `CanonicalLevelOne`, `CanonicalLevelTwo`, `CanonicalComplete`, `CanonicalForcedGrowth`, `CanonicalGrowthRecovery` |
| 意味的探索domain | extended-history局所閉包済み | current normalとhorizon-ready historical normalは全分岐閉包。generic budget gapとearly representativeもcrossing recoveryへ接続 | `NormalProvenance`, `ExtendedHistoryNormal`, `ExtendedHistoryBudgetClosure`, `ExtendedHistoryComplete`, `EarlyRepresentativeComplete`, `DowncrossBudgetGap` |
| Coverage blocker | ready current/debt閉包済み | current親からのCoverageStepは未来初出ならorbit-ready、過去初出ならhorizon-ready strong debtへ送る | `CoverageDebtBridge`, `ReadyDebtInvariant`, `ReadyCurrentDebt` |
| historical回避 | refined閉包済み | parent-dropはfuture current／earlier ready debtへ分解。通常debtはtyped extended-history境界だけを使い、crossing frontierの二時計区間もhorizon-ready extended-historyへ収容 | `HistoricalDebtBridge`, `ReadyDebtRefined`, `CrossingFrontierRefined` |
| refined child | 非crossing閉包済み | orbit-ready normal、ready debt、extended-historyは生成分岐から直接refined stepを返す | `OrbitReadyDirectRefined`, `ReadyDebtRefined`, `ExtendedHistoryDirectRefined` |
| refined oracle境界 | crossingだけ未証明 | constructor監査とcanonical接続を完了し、残余を`CrossingRefinedStepHypothesis`ひとつへ縮約 | `RefinedOracleBoundary` |
| crossing rank境界 | 証明済み | 非crossing successorはstrict budget dropが必須。同一horizonのrefined successorはcrossingに限る | `CrossingRefinedBoundary` |
| crossing future downcross | 条件付き閉包済み | 保存horizon以後のdowncross endpointはfresh below-targetであり、budget下降からextended-historyへ退出 | `CrossingDowncrossRefined` |
| crossing horizon-below | 完全分類済み | 次のupcrossingが進捗するかstable-budget/anchor-growth残余。target 19に残余の実例 | `CrossingBelowRefined` |
| crossing above tail | 長期仮説まで縮約 | no future downcrossはpermanent above tailと同値。tail returnでready crossing局所totality | `CrossingTailRefined` |
| tail returnの強さ | 同値性証明済み | 最小未出目標はeventually strictly above。全targetのtail returnは全射性と同値 | `CrossingTailRefined` |
| permanent tail局所構造 | 証明済み | 高々二遷移のCoverage、zero-budget ready crossing、tail最小値直下のhistorical blockerを抽出 | `PermanentAboveTail` |
| zero-budget crossing境界 | 証明済み | refined子はcrossingに留まり、budget 0を保ってanchorを厳密下降 | `PermanentAboveTail` |
| tail potential監査 | 局所候補棄却 | 二連続forced additionだけではpotentialは増減両方向。実軌道例をkernel検証 | `PermanentAbovePotential` |
| historical tail反復 | 有限化済み | downcrossならbudget下降、なければtail minimum下降。強帰納で必ずfresh historical downcrossへ到達 | `PermanentAboveHistory` |
| historical cycle接続 | 残余まで分類 | anchor dropならrefined crossing子。任意crossing選択ではchild=parentのstationary residualが必ず構成可能 | `PermanentAboveHistory` |
| canonical upcrossing | 存在・一意性証明済み | 最初のfuture weak upcrossingを強帰納で構成。再選択は同時刻なのでearliest規則単独では停留 | `PermanentAboveCanonical` |
| dual history budget | 証明済み | `seenBelowCount = target - missingBelowCount`。過去のpositive-missing点へ戻るとstrict下降 | `PermanentAboveCanonical` |
| permanent-tail cycle rank | 骨格証明済み | anchor／one-way phase／seen budget／minimumの四成分rank。全historical内部stepを閉包 | `PermanentAboveCycleRank` |
| cycle discharge exit | 必要十分条件まで縮約 | dischargeからcrossingへ戻るrank edgeはstrict anchor dropと同値。growth residualは退出不能 | `PermanentAboveCycleRank` |
| typed discharge return | 証明済み | combined obstructionからhistorical downcross、最初のreturn upcrossing、旧crossing provenanceを一証明書へ統合 | `PermanentAboveCycleExit` |
| crossing-time cursor | 骨格証明済み | `(anchor, crossingTime, phase, seen, minimum)`の五成分well-founded rank。同anchorの早いreturnもstrict exit | `PermanentAboveCycleExit` |
| discharge kernel | 三残余まで分類 | 非進捗はstrict anchor growth、旧crossingのendpoint以前、同anchor・同時刻stationaryのみ | `PermanentAboveCycleExit` |
| canonical return rebase | no-goまで証明済み | return crossingを同horizonの親へ型付き再構成可能。tail/minimumを保存するが再生は必ずliteral stationary | `PermanentAboveCycleRebase` |
| canonical below corridor | 局所完全分類済み | fresh endpointからfirst return predecessorまで全値below。内部stepはbudget dropまたはtarget-bounded clock | `PermanentAboveCorridor` |
| 非負normal | 通常域閉包済み | `3≤potential<target`をsemantic rankへ接続し、残余をlevel 0/1/2に限定 | `NonnegativeSemantic` |
| 全域局所被覆 | 未証明 | provenance付きreachable normal domain上の機構適用 | 将来エポック |
| 全射性 | 未証明 | `∀m, ∃t, a t=m` | 最終目標 |

## 証明済みの縮約

```mermaid
flowchart TD
    A["任意の負状態"] --> B["高々 floor(r/2) 歩"]
    B --> C{"一段借り着地"}
    C -->|"G≥m"| D["CoverageStep"]
    C -->|"0≤G<m"| E["非負アンダーシュート"]
    E --> F{"有限降下"}
    F --> D
    F --> A
    F --> G["対角 q=1 debt"]
    G --> H{"後方極大鎖"}
    H --> I["目標出現"]
    H --> J["早期 blocker"]
    J --> K["位相負債へ厳密下降"]
```

## 現在の一点

canonical開始点からの最初の局所stepは全分岐で閉じた。level 1/2の強制加算直後は
値とanchorが増え、履歴予算も不変なので即時の`PhaseSearchProgress`にはならない。
しかし、もう一段先の候補が元のcanonical値より厳密に小さいため、合法減算ならfresh、
blockなら既出値として、どちらも`CoverageStep`へ変換できる。

残る境界はordinary normal constructorの強さである。現行`NormalSearchInvariant`は概念的に
次だけを保持する。

```text
history horizon
FirstAt a value firstTime
firstTime ≤ horizon
target ≤ value ≤ anchor
```

この証明書では`value = a horizon`も`target ≤ horizon+1`も従わない。実際、過去の初出値と
後のhorizonを組み合わせた反例を`NormalSemanticBoundary`で証明した。したがって、任意の
weak normal nodeに座標を選んで局所epoch定理を適用することはできない。

次のdomainには少なくとも以下をproof-carrying dataとして保持させる必要がある。

```text
node = ⟨time, anchor, normal, a time⟩
target ≤ time+1
target ≤ a time ≤ anchor
CoordinatesAt time q r
または、parent-drop／coverageから生成されたことを示すprovenance
```

`OrbitReadyNormalCertificate`は前者を実装し、負potentialの場合のsemantic stepまで接続済みである。
さらに`OrbitReadyNormalInvariant.phaseSemanticStep`は、負、高potential、非負undershoot、
level 0/1/2をすべて閉じ、current-state normalの局所totalityを与える。

`ProvenancedNormalInvariant`はcurrent nodeとrank edge付きhistorical nodeを分離する基礎APIを
与える。`TypedHistoricalNormalProvenance`はparent-drop、coverage anchor、downcross restart、
debt exit、crossing frontierの5種類を実装した。またcurrent親のCoverageStepは、candidateの
初出時刻で分けるとfuture currentまたはstrong debtへ送れるため、generic historical normalを
回避できる。

extended-history stepの当初の残余は次の二つであり、それぞれ独立な実例がある。

```text
representativeTime + 1 < target
missingBelowCount target historyHorizon
  < missingBelowCount target representativeTime
```

両方とも既存rankのまま閉じた。early representativeでは次遷移または既出の減算候補から
below-target実出現を得る。budget gapでは、countのstrict dropそのものから代表時刻では未出で
後のhorizonまでに出現したbelow-target値を抽出する。いずれもそこからfuture upcrossingを取り、
history horizonを拡張した`crossing_recovery` childへ移る。pre-crossing値はtarget未満なので、
旧representative anchorより厳密に小さく、四成分rankのanchorが下降する。

refined child domainは次を保持する。

```text
OrbitReady current
ReadyDebtInvariant
ExtendedHistoryNormalInvariant
CrossingSearchInvariant
```

orbit-ready normal、ready debt、extended-history normalについては、broad
`PhaseSemanticInvariant`を経由せず生成分岐から直接refined resultを構成した。crossing frontierの
二時計middle区間もready debt sourceのhorizon readinessを継承するextended-history childへ入る。
したがってconstructor監査で残るのは`CrossingSearchInvariant`自身だけである。

このcrossing証明書はpredecessor、forced addition、strict crossing、post-state coordinatesを持つが、
元のstrong debtにあったpost値の`FirstAt`、post値が旧anchor未満であること、target-ready horizonを
保持しない。既存debt-crossing closureを再利用する前に、このprovenance消失を修復する必要がある。

さらに`CrossingRefinedBoundary`は、crossing nodeのanchorがtarget未満、非crossing refined nodeの
anchorがtarget以上であることから、両者のrank edgeが必ずstrict history-budget dropを伴うと証明する。
同じhorizonのrefined successorはcrossingに留まる。このためsource provenanceの追加だけでは足りず、
新しいbelow-target履歴またはcrossing-to-crossingの下降を実際に構成する必要がある。

`ReadyCrossingSearchInvariant.refinedStep_of_futureDowncross`は、このうち保存horizon以後にdowncrossが
存在する枝を閉じる。downcross endpointはlegal subtractionによりfreshで、元crossingのpost-stateを
representativeとするextended-history childへstrict budget edgeで移れる。

horizonがbelow-targetである場合、次のweak upcrossingは必ず存在する。
`refinedStep_or_continuationGrowth_of_horizonBelow`は、それがbudgetまたはanchorを下げる枝と、
どちらも下げない`CrossingContinuationGrowthResidual`を完全に分ける。後者は
target 19、horizon 31、anchor 13→14の実軌道で実在する。ただしそのchild horizonは必ず
at-or-above targetで、その後のdowncrossは元の親に対するstrict budget edgeを作る。

`no_futureDowncross_iff_tail_atOrAbove`により、最後に残る枝は「以後ずっとtarget以上」
という真の長期軌道命題である。`refinedStep_of_tailDowncross`は、このtail returnを仮定すれば
ready crossingの両枝が共に閉じることを証明する。
ただしこの長期命題は局所的な残余ではない。最小未出目標を仮定すると、それ未満の値はすべて
ある有限history horizonで既出になるためfuture downcrossが不可能となり、軌道はeventually strictly above
targetになる。`all_targetTailReturn_iff_surjective`は、全targetのtail returnが元の全射性と同値であることを証明する。

`PermanentAboveTail`は、この同値性を仮定として使わず、仮想的な最小未出targetが強制する
tail内部をさらに解析する。tailの任意の状態は、合法減算なら直ちに、強制加算なら次の候補
`a n - 1`のfresh／既出分岐により、高々二遷移で`CoverageStep`を与える。tail最小値では
両遷移が強制加算となり、`a n - 1`はtail開始前に初出したhistorical blockerである。

同時に、below-target値はすべて既出なので`missingBelowCount=0`である。仮想反例からは実際に
tail内部のready crossingを構成でき、その将来downcrossは存在しない。zero-budget crossingから
非crossing refined子へは進めず、refined子があればbudget 0のcrossingに留まってpre-crossing
anchorを厳密に下げる。したがって次の未証明接続は、tail最小値が返すhistorical blockerを
このcrossing anchor下降へ変換する一歩である。

`PermanentAbovePotential`は、最小値で現れる二連続forced additionの座標候補を監査する。
実軌道の`2→7→13`ではpotentialが`2→-2`へ下がり、重なる`7→13→20`では`1→3`へ上がる。
よって二連続forced additionだけを根拠とするpotential単独ランクは使えず、履歴証明書との結合が必要である。

`PermanentAboveHistory`は、この履歴証明書を反復可能にした。直下値の初出時刻以後にdowncrossが
あれば、そのendpointはfreshで`missingBelowCount`を厳密に下げる。downcrossがなければ初出時刻から
新しいstrict-above tailを作れ、その最小値は旧最小値より厳密に小さい。自然数最小値に対する
強帰納により、後者だけを無限反復することはできず、必ず有限回でhistorical downcrossへ到達する。

そのdowncross後のupcrossingをcombined zero-budget crossingと同じhorizonへ置くと、anchor dropなら
正当なrefined crossing子になる。しかし親crossingをそのupcrossing自身として選べばchild=parentとなり、
同budget・同anchorで進捗しない`HistoricalCycleGrowthResidual`を必ず構成できる。
したがって任意のcrossing証明書を許す現行domainではhistorical cycle一回の再生はrankにならない。
次の未証明点は、earliest/latest/minimum-anchorなどのcanonical crossing provenance、または複数cycleを
同時に測る新しいwell-founded量でこの停留選択を排除することである。

`PermanentAboveCanonical`は最初のfuture weak upcrossingを、既知witness時刻を上界とする強帰納で
canonicalに構成し一意性を示す。しかし同じdowncross endpointから再選択すれば一意性により同時刻へ
戻るため、earliest規則だけではstationary residualを解消しない。同モジュールは
`seenBelowCount = target - missingBelowCount`を導入し、zero-budget tail horizonからpositive-missingな
historical first occurrenceへ戻る向きで厳密下降するdual budgetを証明する。

`PermanentAboveCycleRank`はこのdual budgetを統合する。rankは
`(anchor, phase, seenBelowCount, tailMinimum)`の辞書式順序で、phaseは
`crossing > backtrack > discharge`の一方向である。combined obstructionは同anchorのbacktrackへ入り、
renewed tailはseen/minimumを下げ、historical downcrossはdischargeへ入る。すべてstrict stepであり、
rankはwell-foundedである。dischargeからcrossingへ戻るstepはstrict anchor dropと同値なので、
stationary cycleは進捗として排除される。ただしanchor非減少のgrowth residualはexit obstructionとして残る。

`PermanentAboveCycleExit`はhistorical downcrossから最初のreturn upcrossingまでの全時刻・値provenanceを
`PermanentTailDischargeReturnCertificate`へまとめる。外側cursorを`(anchor, crossingTime)`へ精密化した
五成分cycle rankもwell-foundedである。これにより同anchorでもreturn時刻が早ければcycleを退出できる。
完全分類`cycleExit_or_kernelResidual`の非進捗側は、strict anchor growth、旧crossingがdowncross endpointより
前にあるchronology mismatch、anchorと時刻がともに同一のliteral stationaryの三constructorだけである。
同じendpointですでにcanonicalな旧crossingを再選択すると、最後のconstructorが実際に生じる。

`PermanentAboveCycleRebase`は、return crossing自体を次のzero-budget parentにする自然な修正を監査する。
旧horizon上でready crossingを再構成でき、同じpermanent tailとminimum certificateを持つcombined obstructionに
戻せる。しかし同じhistorical downcrossを再生したdischarge certificateでは、returnが旧crossingそのものであり、
anchor・時刻とも等しい`stationary` kernelになる。従ってcanonical rebaseは三残余を一つのstationary coreへ
正規化するが、progressを作らない。次のrankにはendpoint再訪の禁止または別のhistorical choiceが必要である。

`PermanentAboveCorridor`はstationary core内部の有限区間を抽出する。first weak upcrossingの最小性から、
fresh downcross endpointとreturn predecessorの間にある全状態がtarget未満である。returnが即時なら、downcrossの
合法減算と次のforced additionは`a (d+2) = a d + 1`という谷形を作る。遅延returnでは任意の内部transitionを
分類でき、legal subtractionはfirst occurrenceを作ってhistory budgetを厳密下降させる。forced additionは
次状態もbelowなので`time+1 < target`を強制する。従ってbudgetを下げない内部区間は有限なtarget-bounded clockに限られる。

## モジュール層

| 層 | モジュール |
|---|---|
| 基礎 | `Basic`, `History`, `Coordinates` |
| 局所遷移 | `CoordinateDynamics`, `MultiBorrow`, `OrbitBounds` |
| 下降・blocker | `ActualDescent`, `Blocker`, `TargetDescent` |
| 目標面 | `Gate`, `Mechanisms`, `LandingSurfaces`, `PrestateCoverage` |
| 回復 | `NegativeRegion`, `Recovery`, `RecoveryBudget`, `RecoveryFrontier`, `RecoveryWindows` |
| エポック | `OneBorrowFrontier`, `NegativeEpoch`, `Undershoot` |
| 大域探索 | `Coverage`, `HistoryBudget`, `HistoryFrontier`, `Diagonal`, `PhaseSearch` |
| 負債局所解析 | `DebtInvariant`, `DebtSubtraction`, `DebtAddition`, `DebtStep`, `DebtBackward`, `DebtCrossing`, `AnchorBoundary`, `CrossingRecovery`, `CrossingGap`, `CrossingGrowth`, `CrossingHorizon`, `CrossingIteration`, `CrossingFrontier` |
| 位相統合 | `PhaseProgress`, `PhaseEpoch`, `PhaseSearchStart`, `NormalPhase`, `PhaseSemantic`, `NormalClosure`, `BoundaryAudit`, `NormalComplete`, `NormalSemanticBoundary`, `NormalProvenance`, `ExtendedHistoryNormal`, `TypedNormalProvenance`, `NonnegativeSemantic`, `OrbitReadyComplete`, `OrbitReadyAdapters`, `CoverageDebtBridge`, `DowncrossBudgetGap`, `EarlyRepresentative`, `EarlyRepresentativeClosure`, `EarlyForcedCandidateClosure`, `EarlyRepresentativeComplete`, `ExtendedHistoryBudgetClosure`, `ExtendedHistoryComplete`, `HistoricalDebtBridge`, `ReadyDebtInvariant`, `ReadyCurrentDebt`, `OrbitReadyRefinedStep`, `OrbitReadyDirectRefined`, `ReadyDebtRefined`, `CrossingFrontierRefined`, `ExtendedHistoryDirectRefined`, `RefinedOracleBoundary`, `CrossingRefinedBoundary`, `CrossingDowncrossRefined`, `CrossingBelowRefined`, `CrossingTailRefined`, `PermanentAboveTail`, `PermanentAbovePotential`, `PermanentAboveHistory`, `PermanentAboveCanonical`, `PermanentAboveCycleRank`, `PermanentAboveCycleExit`, `PermanentAboveCycleRebase`, `PermanentAboveCorridor` |
| 初期領域・canonical閉包 | `InitialRegion`, `CanonicalOracle`, `CanonicalLevelZero`, `CanonicalLevelOne`, `CanonicalLevelTwo`, `CanonicalComplete`, `CanonicalForcedGrowth`, `CanonicalGrowthRecovery` |
| 検証 | `Examples`, `Audit` |

## 証明と計算実験の境界

- `Recaman/`以下のみがLean証明本体である。
- `experiments/`のC++結果は仮説選択にのみ使用する。
- 計算実験の結果を証明の仮定として利用していない。
- 具体例の小規模計算はLeanカーネルの`decide`で検証する。
