# OrbitReadyDirectRefined

**役割:** broad semantic stepがclock証拠を消す前に生成分岐そのものを辿り直し、orbit-ready normal nodeに対して残余のないrefined step(`OrbitReadyRefinedInvariant` の子への厳密下降)を直接構成する。

## このモジュールの役割

`OrbitReadyComplete` の黒箱stepは局所完全だが子のhistory-clock証拠を消し、`OrbitReadyRefinedStep` の構成子検査ではhorizon clockの欠けたnormal/debt子が残余として残った。本モジュールはその残余を根本から消す。すなわち、閉包を生成する各分岐(負エポック、非負帯、商0・商1・商2以上の強制加算、低レベル帯)を忘却前の形で再構成し、(1) parent-dropは未来current子または(親clockを写した)earlier ready debt子へ分解し、(2) above-targetの実状態はorbit-readyのまま保持し、(3) below-targetへのdowncross再出発は旧representative状態をextended-history証明書として保持する。結果として `OrbitReadyNormalInvariant.refinedStep` は「目標出現、またはrefined domainの子への厳密下降」を残余なしで与える。

## 定理と証明

### `ParentDropCurrentDebtOutcome.toReadyRefinedStep` (L16)

**主張:** parent-drop(anchorとなる値の厳密減少)の分類結果は、sourceのclock条件 `target ≤ parentTime + 1` を添えれば、refined domainのstepになる。

**証明:** 三構成子の振り分けである。目標出現はそのまま。current子は `targetStartNode firstTime` のorbit-ready不変量を保持しているので、refined domainのcurrent枝に入る。debt子はnode `⟨parentTime, activeParent, .debt, firstTime⟩` の強debt不変量を持つが、そのhorizonは親時刻そのものなので、仮定のclock条件がhorizon readinessになり `ReadyDebtInvariant` が組める。これが「sourceの時計をdebt子へ写してから証明書を忘れる」という本モジュールの基本手筋である。

### 補助補題 `coverageReady_to_refined` (L42)

ready current/debt domainのstepをより大きいrefined domainのstepへ包含写像で持ち上げる1行の補助補題(private)。

### `negativeNormal_refinedStep` (L57)

**主張:** 負ポテンシャルの現在normal不変量 `NormalPhaseInvariantAt` からは、目標出現またはrefined子への厳密下降が得られる。

**証明:** 負エポックの完全分類 `negative_epoch_historySearchOutcome_or_qOneDebt` は四枝を返す。

1. 目標出現: そのまま。
2. parent-drop: 返された初出値・anchor下降・ランク下降を `NormalParentDropEvidence` に束ね、`normalParentDrop_currentOrDebt` で現在/過去に分類してからL16で refined stepへ変換する。sourceのclockは不変量の `time_ready` である。
3. forward exit(未来時刻 `time` への軌道前進): 証拠 `NormalEpochExitEvidence` を組み、`target ≤ a time` かどうかで分ける。above なら `normalEpochExit_above_orbitReadyAdapter` がorbit-readyな現在子と下降を与える。below なら、軌道は `target ≤ a n` から `a time < target` へ下向き横断しているので、`orbit_downcrossing_occurs_or_budgetDrop` により目標が出現するか、履歴予算 `missingBelowCount` が厳密に減る。後者では子 `⟨time, a n, .normal, a n⟩` を取る。これは旧時刻 `n` をrepresentative、`time` をhorizonとするextended-history nodeであり(horizon readinessはexit証拠の `time_ready`)、ランク下降は予算の厳密減少(辞書式第一成分)による。
4. 商1のdebt分岐: この場合は既存定理 `normalPhase_qOneDebt_already_occurs` により目標が既に出現している。

### `nonnegative_epoch_refinedStep` (L129)

**主張:** 正則レベル `3 ≤ g < target` の非負帯状態も、結果をbroad domainへ変換する前に refined step を返す。

**証明:** 非負エポックの分類 `nonnegative_epoch_historySearchOutcome` の四枝を処理する。目標出現はそのまま。parent-dropは負の場合と同じくL16経由。商0枝は矛盾で消える: 商0なら `a n = r` かつ `r = g < target` となり、目標下界 `target ≤ a n` に反する。forward枝は負の場合と同一の above/below 分割で、aboveは `nonnegativeForwardAbove_orbitReadyAdapter`、belowはdowncrossの予算下降からextended-history子 `⟨time, a n, .normal, a n⟩` を作る(representativeは `n`、その座標は仮定の `hcoord` をそのまま使う)。

### `zeroQuotient_potential_aboveTarget_refinedStep` (L201)

**主張:** 商0で `target ≤ potential 0 r` の状態は、sourceのclockが生きているうちに被覆を生成するので、earlier blockerはbroadなhistorical normalではなくready debtになる。

**証明:** 数学的内容は `OrbitReadyComplete` の同名semantic版と同じである: `a n = r`、目標との等号なら出現、さもなくば強制加算後の座標 `(1, r)` の次の減算候補 `r − 1` が時刻 `n + 2` までに必ず履歴へ現れ、`target ≤ r − 1 < a n` のblockerとして `CoverageStep` を与える。違いは変換先である。ここでは `CurrentCoverageParentCertificate`(目標正値・`target ≤ n + 1`・値下界)を組み、`coverageStep_readyCurrentOrDebt` に渡す。これにより未来blockerはorbit-ready current子、過去blockerはhorizon-ready debt子になり、L42でrefined domainへ持ち上げる。

### `quotientOne_forcedAddition_refinedStep` (L243)

**主張:** 商1の強制成長も、二歩先の被覆候補を分類し終えるまでready current親を保持する。

**証明:** semantic版(`OrbitReadyComplete` L79)と同じ算術である。`a n = n + 1 + level`、強制加算後 `a (n+1) = 2n + 2 + level`、次の候補 `candidate = n + level` は `target ≤ candidate < a n` を満たす。二歩目が合法ならfreshな着地、塞がれるなら既出、いずれもblockerで `CoverageStep` を得る。あとは現在親証明書と `coverageStep_readyCurrentOrDebt` で ready current/debt へ振り分け、refined domainへ持ち上げる。

### `forcedAddition_twoQuotient_refinedStep` (L303)

**主張:** 商2以上の強制加算frontierを、被覆・current前進・downcrossの各生成分岐で精密化する。

**証明:** frontier定理 `coordinates_forcedAddition_twoQuotient_historySearchProgress` は、blockerデータか、二歩先 `n + 2` へのraw履歴エッジを返す。前者は `CoverageStep` として現在親証明書と共にready橋渡しへ送る。後者は `target ≤ a (n+2)` で分け、aboveなら `forcedAdditionForwardAbove_orbitReadyAdapter` でorbit-ready子、belowならdowncrossにより目標出現または予算の厳密下降を得て、extended-history子 `⟨n+2, a n, .normal, a n⟩`(representative `n`、horizon `n+2`)を返す。

### `OrbitReadyLowLevelResidual.refinedStep` (L356)

**主張:** 正確な低レベル残余(レベル `0, 1, 2`)もrefined child domainで完全である。

**証明:** 残余の時刻 `n` で `a n = target` なら出現。以下 `target < a n` とし、次の減算の可否で分ける。

減算が合法な場合、semantic版と違い着地値の位置でさらに分ける。`target ≤ a (n+1)` なら `canonicalLegalSubtraction_above_orbitReadyAdapter` がorbit-readyな現在子を与える。`a (n+1) < target` なら下向き横断なので、目標出現または予算下降が得られ、後者ではextended-history子 `⟨n+1, a n, .normal, a n⟩`(representative `n`)へ移る。

減算が塞がれている場合、商1ならL243、商2以上ならL303(残余の `quotient_positive` により商0はない)。

### `OrbitReadyNormalCertificate.refinedStep_or_lowLevel` (L414)

**主張:** refined子を保持したままの完全な符号分類。目標出現、refined子への下降、または低レベル残余の三択。

**証明:** `OrbitReadyComplete` の分類と同じ骨格で、各枝をrefined版に置き換える。負ポテンシャルはL57(証明書から `NormalPhaseInvariantAt` を組んで適用)。目標面以上では、商0はL201、商1以上は `positiveQuotient_potential_aboveTarget_gives_coverageStep` の被覆を現在親証明書と共にready橋渡しへ送る(`time = 0` は `a 0 = 0` と目標正値の矛盾で排除)。非負アンダーシュートでは、まず商が正であることを確かめる(商0なら `a time = r` かつ `r < target` が目標下界と矛盾)。レベル `level = r − upperTri q` が3以上ならL129、さもなくば `NonnegativeLowLevelResidualAt` の全フィールドを埋めて残余を返す。

### `OrbitReadyNormalCertificate.refinedStep` (L498)

**主張:** 証明書レベルのrefined局所totality。目標出現またはrefined子への厳密下降の二択。

**証明:** L414の三択のうち低レベル残余をL356で解消する。

### `OrbitReadyNormalInvariant.refinedStep` (L510)

**主張:** orbit-readyな現在normal nodeは残余のないrefined stepを持つ。

**証明:** 存在量化を開いてL498を適用する。

## 全体の中での位置づけ

証明地図の「refined child: 非crossing閉包済み」段のnormal側を完成させる主モジュールである。`ReadyDebtRefined.lean` はここで定義された結論の型(refined stepの形)を使ってready debt側の残余なしstepを与え、`ExtendedHistoryDirectRefined` がextended-history側を担う。これによりconstructor監査で未処理として残るのは `CrossingSearchInvariant` 自身だけとなり(`RefinedOracleBoundary`)、以後のcrossing解析(`CrossingRefinedBoundary` 以降)へ問題が一点化される。
