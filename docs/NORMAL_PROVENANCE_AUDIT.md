# ordinary normal provenance監査

## 目的

`PhaseSemanticInvariant.normal`を生成する既存箇所を、現在horizonの実軌道を表す
current-state nodeと、過去の初出値を後の履歴horizonで再利用するhistorical nodeに分ける。
後者を誤って`OrbitReadyNormalInvariant`として扱わず、total semantic oracleに必要な
proof-carrying constructorを特定する。

## 結論

直接のnormal semantic生成24箇所のうち、8箇所はその場でorbit-readyな証明を構成できる。
残りはhistorical nodeであり、少なくとも次の生成元を区別する必要がある。

| constructor候補 | 生成機構 | 必要な主要データ |
|---|---|---|
| `current` | 現在の実軌道状態 | node shape、time readiness、target下界、現在座標 |
| `parent_drop` | smaller anchorへの下降 | 元normal証明、`NormalParentDropEvidence`、rank edge |
| `coverage_anchor` | Coverage／既出candidate | candidateの`FirstAt`、target下界、元anchorからの値下降 |
| `downcross_restart` | 目標未満への横断と履歴予算下降 | representative time、拡張horizon、downcrossing、budget drop |
| `debt_exit` | strong debtからnormalへ退出 | 元`DebtInvariant`、初出値、debt-to-normal rank edge |
| `crossing_frontier` | crossing frontierからの下降 | crossing/debt source、frontier初出値、anchorまたはbudget下降 |

`ProvenancedNormalInvariant`はcurrentとrank edge付きhistorical chainを分ける基礎APIである。
ただしgenericなprovenanceだけではhistorical childの次stepを構成できないため、上表のtyped dataと
extended-history theoremが別途必要である。

その後、5種類すべてを`TypedHistoricalNormalProvenance`として実装した。current生成8系統にも
`OrbitReadyAdapters`でadapterを用意した。既存公開定理は互換性のため旧semantic resultを返すが、
refined APIへの移行に必要なproof dataは揃っている。

## 生成箇所

| モジュール／定理 | 分類 | orbit-ready化 | 次の対応 |
|---|---|---|---|
| `PhaseSemantic.targetStartInvariant_normal` | canonical current | 可 | current constructor |
| `PhaseSemantic.debtInvariant_selfExit_phaseSemantic` | debt historical | 不可 | `debt_exit` |
| `PhaseSemantic.anchorBoundary_phaseSemantic_closure` | debt historical | 不可 | `debt_exit` |
| `NormalClosure.firstAt_normalSearchInvariant` | 汎用historical helper | 一般には不可 | typed constructor内部だけで使う |
| `NormalClosure.normalParentDrop_phaseSemantic` | parent-drop historical | 不可 | `parent_drop` |
| `NormalClosure.normalEpochExit_phaseSemantic_or_sharp`のabove-target枝 | forward current | 可 | current constructor |
| 同定理のanchor-drop枝 | downcross historical | 不可 | `downcross_restart` |
| 同定理のbudget-drop枝 | downcross historical | 不可 | `downcross_restart` |
| `NormalClosure.normalPhaseInvariant_phaseSemantic_progress` | negative current | 可 | current constructor |
| `CrossingFrontier.frontierFirstAt_phaseSemantic` | crossing historical | 一般には不可 | `crossing_frontier` |
| `NonnegativeSemantic.nonnegative_epoch_phaseSemanticOutcome`のparent枝 | parent-drop historical | 不可 | `parent_drop` |
| 同定理のforward above-target枝 | forward current | 可 | current constructor |
| 同定理のforward downcross枝 | downcross historical | 不可 | `downcross_restart` |
| `CanonicalOracle.canonicalCoverage_phaseSemantic` | coverage historical | 一般には不可 | `coverage_anchor` |
| `CanonicalOracle.canonicalHistoryFrontier_phaseSemantic`のabove-target枝 | forward current | 条件付き | time readinessをAPIへ通す |
| 同定理のbelow-target枝 | downcross historical | 不可 | `downcross_restart` |
| `CanonicalLevelZero.canonicalLowLevel_zero_phaseSemanticStep_or_successor` | future current | 可 | current constructor |
| `CanonicalLevelOne.canonical_legalSubtraction_phaseSemantic`のabove-target枝 | future current | 条件付き | time readinessをAPIへ通す |
| 同定理のdowncross枝 | downcross historical | 不可 | `downcross_restart` |
| `canonical_forcedAddition_twoQuotient_phaseSemantic`のcandidate枝 | coverage historical | 不可 | `coverage_anchor` |
| 同定理のforward above-target枝 | future current | 可 | current constructor |
| 同定理のforward below-target枝 | downcross historical | 不可 | `downcross_restart` |
| `CanonicalLevelTwo.canonicalLevelTwo_phaseSemanticStep_or_forcedQOne`のbelow-target枝 | downcross historical | 不可 | `downcross_restart` |
| `CanonicalForcedGrowthChamber.nextState` | intermediate current | 可 | current constructor。ただし即時rank childではない |

`CanonicalLevelTwo`のlegal-above枝と`CanonicalForcedGrowthChamber.twoStep_phaseSemantic`は
`canonicalCoverage_phaseSemantic`を経由する。fresh candidateならcurrent化できるが、blocked
candidateは履歴由来なので、呼出し側で分岐を保持するか`coverage_anchor`へ送る必要がある。

## current-state側の完了

`OrbitReadyNormalInvariant.phaseSemanticStep`は次をすべて処理する。

- 負potential
- target以上のpotential（商0を含む）
- `0 ≤ potential < target`の通常非負域
- level 0/1/2
- quotient-one forced additionの二段lookahead

したがって、current constructorそのものに局所残余はない。

さらにcurrent親から得た`CoverageStep`は、candidateの初出時刻を親時刻と比較することで
historical normalを使わずに処理できる。

- 親より後の初出: 実際のfuture current nodeとしてorbit-ready
- 親より前の初出: 親horizonとanchorを保ったstrong debt node
- candidateがtargetそのもの: 初出時刻を直接witnessにする

この分類は`coverageStep_currentOrDebt`で証明済みである。

## historical側の中心命題

historical nodeでは二つの時刻を分離する必要がある。

```text
historyHorizon
representativeTime
representativeTime ≤ historyHorizon
node = ⟨historyHorizon, a representativeTime, normal, a representativeTime⟩
CoordinatesAt representativeTime q r
target ≤ a representativeTime
typed provenance
```

`representativeTime < historyHorizon`では、representative stateの局所軌道を解析しつつ、
rank第一成分には拡張済みhistory budgetを使わなければならない。特にdowncross restartは
`a historyHorizon < target`を持つため、nodeをcurrent-stateへ変換することは原理的にできない。

`ExtendedHistoryNormalCertificate.phaseSemanticStep_or_residual`により、直接輸送の条件は正確に
次の二つと判明した。

1. `target ≤ representativeTime+1`
2. representative timeとhistory horizonで`missingBelowCount`が等しい

両方を満たせばorbit-ready total stepをhistorical nodeへ輸送できる。第一条件が失敗する実例と、
第一条件を満たしながら第二条件が失敗する実例をLean化した。budget gapがある場合、historical
nodeはrepresentative nodeより既にrank下位なので、既存local edgeの単純輸送は不可能である。

debt exitでは現行`DebtInvariant`単独から`target ≤ historyHorizon+1`が従わない。debt domainを
強めるか、debt生成元provenanceからtime readinessを復元する必要がある。

## 実装順序

1. ~~typed provenance constructorの共通時刻・座標データを確定する。~~
2. ~~extended-historyの直接輸送条件と残余を証明する。~~
3. ~~current生成8系統のorbit-ready adapterを用意する。~~
4. budget-gapとrepresentative-not-readyを生成機構固有のstepで処理する。
5. refined semantic domain上のrestricted oracleへ統合する。

計算実験はこの設計判断の仮定には使用しない。
