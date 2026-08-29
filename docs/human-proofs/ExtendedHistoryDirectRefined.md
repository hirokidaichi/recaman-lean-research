# ExtendedHistoryDirectRefined

**役割:** extended-history normal nodeの完全閉包を、childの時計情報を忘れないrefined domain上で直接構成し直し、3つの履歴予算機構を単一の将来upcrossingアダプタで処理する。

## このモジュールの役割

広いextended-history完全定理(`ExtendedHistoryComplete`)は、proof-carryingなchildを構成した直後にその時計データを `PhaseSemanticInvariant` へ忘れさせてしまう。refined oracle(orbit-ready current、ready debt、extended-history、crossingの4種だけを許すchild domain)を構成するには、生成分岐ごとにこのデータを保持したまま返す必要がある。本モジュールは、実際のbelow-target値から出発する3つの履歴予算機構 — genericなbudget gap、early representativeの合法downcross、blockされたbelow-target候補 — を、共通の将来upcrossingアダプタ1本で処理し、extended-history nodeのrefined domain上での局所全域性(local totality)を確立する。

ここで `OrbitReadyRefinedInvariant target node` は

`ReadyCurrentOrDebtInvariant ∨ ExtendedHistoryNormalInvariant ∨ CrossingSearchInvariant`

であり、refined stepとは「目標の出現、またはこのdomainに属するchildへの既存rankでの真の下降」を指す。

## 定理と証明

### `extendedNormal_crossingRecovery_refinedStep_from_below` (L19)

**主張(共通アダプタ):** node形状 `⟨horizon, a(代表時刻), normal, a(代表時刻)⟩` と `target ≤ a(代表時刻)` を持つnodeに対し、**任意の**below-target実軌道点 `a(startTime) < target` から、目標の出現、または `OrbitReadyRefinedInvariant` を持つchildへの真のrank下降が得られる。

**証明:** below-target点から `exists_weakUpcrossingStep_from_below` で弱上方crossing(target未満の値から強制加算でtarget以上へ跳ぶ遷移)の時刻 `crossingTime` を取る。目標が `crossingTime` までに既出、または `a(crossingTime + 1) = target` なら出現証人を返す。残る真の横断の場合、`DebtCrossing` とpost-state座標を組み、child

`⟨max(node.horizon, crossingTime + 2), a(crossingTime), normal, a(crossingTime)⟩`

を `CrossingRecoveryInvariant` で証明する(crossingは新horizonより前、目標はcrossing前に未出、pre-crossing値 `a(crossingTime) < target ≤ a(代表時刻)` は旧anchor未満)。childは `CrossingSearchInvariant` を持ち、refined domainの第三選言肢に入る。rank下降は、horizon拡大による履歴予算の非増加とanchorの真の下降から従う。budget gapを越えて局所stepを輸送するのではなく、below-target点そのものを下降辺に変えるのが要点である。

### `ExtendedHistoryNormalCertificate.refinedStep_of_budgetGap` (L81)

**主張:** 履歴予算の真のgap `missingBelowCount target node.horizon < missingBelowCount target 代表時刻` を持つextended-history証明書は、refined crossing childを直接与える。

**証明:** `ExtendedHistoryBudgetClosure` の `exists_newBelow_occurrence_of_missingBelowCount_strict` により、gapの原因である「代表時刻には未出でhorizonまでに出現したtarget未満の値」の出現時刻を取り、その点をbelow-target開始点として共通アダプタに渡す。

### `EarlyRepresentativeResidual.legalDowncross_refinedStep` (L101)

**主張:** early representativeの合法downcross残余では、着地 `a(代表時刻 + 1) < target` 自身がbelow-target開始点を直接与え、refined stepが従う。

**証明:** 共通アダプタに `startTime = 代表時刻 + 1` を渡すだけである。残余に格納された2つの予算不等式は使わない。

### `EarlyRepresentativeResidual.forcedBelowCandidate_refinedStep` (L124)

**主張:** blockされたbelow-target候補の残余では、候補が代表時刻以前にすでに出現しているから、その早い出現点が同じ将来upcrossing構成の開始点になる。

**証明:** `candidate ∈ valuesThrough 代表時刻` から出現時刻 `startTime` と `a(startTime) = candidate < target` を取り、共通アダプタに渡す。

### `EarlyRepresentativeCertificate.refinedStep` (L153)

**主張:** early representative(`代表時刻 + 1 < target`)の完全なrefined step。forward childはextended-historyのまま、debt childは親のready horizonを継承したready debtとして、両残余機構はcrossing recoveryとして、いずれもrefined domain内に返る。

**証明:** `classify` の4分岐を処理する。出現はそのまま。forward childはそのextended-history証明書を存在量化して第二選言肢へ。debt childは、childのhorizonが親のhorizonに等しいことから親のhorizon readiness `target ≤ horizon + 1` を継承し、`ReadyDebtInvariant`(strong debt + horizon readiness)として第一選言肢へ入る。ここが広いsemantic版との差であり、debt childの時計情報が保持される。2つの残余はそれぞれ上の2定理で閉じる。

### `ExtendedHistoryNormalCertificate.refinedStep` (L195)

**主張:** extended-history normal nodeはrefined domainで局所全域である: 任意の証明書について、目標の出現、または `OrbitReadyRefinedInvariant` を持つchildへの真のrank下降が成り立つ。

**証明:** 代表時刻のreadinessと履歴予算の安定性で三分する。

1. ready かつ 予算安定: 代表時刻の現在nodeをorbit-ready証明書に変換し、その直接refined定理(`OrbitReadyDirectRefined`)を呼ぶ。得られた下降は、予算が等しいので `transportProgress_of_budgetStable` でhistorical nodeへそのまま輸送できる。
2. ready かつ 予算gap: 予算の単調性から真のgapが従い、`refinedStep_of_budgetGap` で閉じる。
3. not ready: early証明書を組み、`EarlyRepresentativeCertificate.refinedStep` で閉じる。

### `ExtendedHistoryNormalInvariant.refinedStep` (L224)

**主張:** 存在量化版の包み。代表時刻・座標を開いて前定理を適用する。

## 全体の中での位置づけ

証明地図の「refined child: 非crossing閉包済み」段階の一角である。`OrbitReadyDirectRefined`(orbit-ready current)、`ReadyDebtRefined`(ready debt)と並び、本モジュールがextended-history normalを担当することで、broad `PhaseSemanticInvariant` を経由しない直接のrefined step構成が3機構すべてで完成する。この結果、refined oracleのconstructor監査で未閉包に残るのは `CrossingSearchInvariant` 自身だけとなり(`RefinedOracleBoundary`)、以降の解析は `CrossingRefinedBoundary`・`CrossingDowncrossRefined`・`CrossingBelowRefined`・`CrossingTailRefined` のcrossing境界問題へ縮約される。
