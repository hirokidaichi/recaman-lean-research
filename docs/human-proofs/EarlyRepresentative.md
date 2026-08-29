# EarlyRepresentative

**役割:** 代表時刻が目標のtime-readinessに達していないextended-history nodeについて、次の1遷移を解析し、成功分岐と2つの正確な残余に分類する。

## このモジュールの役割

extended-history node(過去の代表時刻の軌道値を、後の履歴horizonで再利用するnormal node)は、`代表時刻 + 1 < target` のとき、horizon側がreadyでもepoch API(orbit-ready理論)へ渡せない。本モジュールはこの**early representative**の局所構造を、実軌道の次の1遷移を直接調べることで解析する。合法減算がtarget以上に留まればより小さいextended-history child、blockされた候補がtarget以上ならstrong debtへの進入、目標に一致すれば即座に出現、が得られる。閉じない場合は正確に2つ: target未満へ横断する合法減算(履歴予算がすでに消費されている)と、既出のtarget未満候補によるblockからの強制加算である。両残余は後続モジュールで閉じられる。

## 主要な定義

### `EarlyRepresentativeCertificate` (L25)

extended-history証明書に、時計失敗 `not_ready : 代表時刻 + 1 < target` を追加した構造。「epoch APIには早すぎる代表時刻」を持つnodeの証明書である。

### `EarlyRepresentativeForwardChild` (L82)

同じ履歴horizonにおける、target以上の合法減算child。新しい代表時刻(`代表時刻 + 1`)でのextended-history証明書、値の真の超過 `target < a(新代表時刻)`、readinessの二値分岐(1歩進んだ結果、通常のepoch境界に達したか、まだearly domainに留まるか)、semantic不変量、親からの真のrank下降を保持する。

### `EarlyRepresentativeResidual` (L97)

次遷移の検査後に残る正確な残余。2つのconstructorを持つ。

- `legal_downcross`: 合法減算の着地 `a(代表時刻 + 1)` がtarget未満に横断した場合。代表時刻から次時刻への履歴予算(`missingBelowCount`)の真の下降と、horizonでの予算gapの両方を記録する。
- `forced_below_candidate`: 減算がblockされ、候補 `candidate = a(代表時刻) − (代表時刻 + 1)` が正・target未満・既出である場合。強制加算の値の式も記録する。

### `EarlyRepresentativeOutcome` (L131)

強いproof-relevantな分類。目標の出現、forward child、debt child(nodeの形・`DebtInvariant`・semantic・progressを保持)、残余、の4分岐である。成功分岐は必ずextended-history childまたはstrong debt childを保持し、裸のhistorical `NormalSearchInvariant` を導入しない。

### `EarlyRefinedInvariant` (L292)

成功分岐が保存するrefined domain: `ExtendedHistoryNormalInvariant ∨ CurrentOrDebtInvariant`(proof-carryingなextended-history nodeと、`CoverageDebtBridge` のcurrent/debt domain)。

## 定理と証明

### `EarlyRepresentativeCertificate.coordinate_constraints` (L37)

**主張:** early above-target representativeが強制する初等算術: `0 < 代表時刻`、`0 < 商`、減算候補が正(`代表時刻 + 1 < a(代表時刻)`)、さらに商が1なら `剰余 ≥ 2` かつ `potential(1, r) ≥ 1`。

**証明:** `代表時刻 + 1 < target ≤ a(代表時刻)` から候補の正値性が出る。代表時刻が0なら `a(0) = 0 ≥ target > 0` で矛盾。商が0なら座標方程式から `a(代表時刻) = 剰余 < 代表時刻` となり候補の正値性に矛盾する。商が1のとき `a(代表時刻) = 代表時刻 + 剰余` なので `剰余 ≥ 2`、また `potential(1, r) = r − upperTri(1) = r − 1 ≥ 1`。商が2以上では一様なpotential下界は主張しない(target 5の実例は負のpotentialを持つ)。

### `EarlyRepresentativeCertificate.classify` (L159)

**主張:** early representativeの1歩解析。任意のearly証明書は `EarlyRepresentativeOutcome` のいずれかの分岐に入る。

**証明:** `a(代表時刻) = target` なら出現。以下 `target < a(代表時刻)` とする。時計失敗 `代表時刻 + 1 < target` とhorizon readiness `target ≤ horizon + 1` から `代表時刻 < horizon`、したがって `代表時刻 + 1 ≤ horizon` が従う。次遷移で場合分けする。

**(1) 合法減算の場合。** 着地値は `a(代表時刻 + 1) = a(代表時刻) − (代表時刻 + 1)` で、現在値より真に小さい。着地値がtargetなら出現。target以上なら、新代表時刻 `代表時刻 + 1` の座標を取り、同じhorizonのchild `⟨horizon, a(代表時刻+1), normal, a(代表時刻+1)⟩` に対するextended-history証明書を組む(horizon readinessは親から継承)。rank下降は、horizonが同一なので履歴予算成分が等しく、anchor成分が `a(代表時刻+1) < a(代表時刻)` で真に下がることから従う。これがforward childである。着地値がtarget未満なら、区間 `[代表時刻, 代表時刻+1]` に標準のdowncrossing定理 `orbit_downcrossing_occurs_or_budgetDrop` を適用する: 途中で目標に一致する時刻があるか、さもなければ履歴予算が代表時刻から次時刻へ真に下がる。後者の場合、予算の単調性でhorizonでのgapも従い、両不等式を `legal_downcross` 残余に記録する。

**(2) 減算がblockされた場合。** 候補 `candidate = a(代表時刻) − (代表時刻 + 1)` は正である(座標制約)から、blockの理由は「候補が既出」しかない(`not_canSubtract_cases` の非正枝は矛盾)。候補がtargetに等しければ、既出性から出現証人が取れる。候補がtarget以上なら、候補の初出時刻 `firstTime` を取る。`firstTime = 代表時刻` は `a(代表時刻) = candidate = a(代表時刻) − (代表時刻+1)` を意味し不可能なので `firstTime < 代表時刻 < horizon`。child `⟨horizon, anchor, debt, firstTime⟩` は `DebtInvariant`(目標下界、初出、horizon内、`candidate < anchor = a(代表時刻)`)を満たし、位相rankの下降 `phaseSearch_enterDebt` により親から真に下がる。これがdebt childである。候補がtarget未満なら、強制加算の値の式とともに `forced_below_candidate` 残余を返す。

### `EarlyRepresentativeOutcome.toRefinedStep_or_residual` (L299)

**主張:** 最強の分類を忘却してrestricted-step形にする: 目標の出現、`EarlyRefinedInvariant` を持つchildへの真の下降、または2つの正直な残余、の三択。

**証明:** 各分岐の写し替えである。forward childはextended-history側、debt childはcurrent/debt側の選言肢に入る。

### `earlyRepresentative_five_three_legalDowncross` (L322)

**主張:** target 5の実在するearly representative `⟨4, a(3), normal, a(3)⟩`(`a(3) = 6`、代表時刻3、座標 `(q,r) = (2,0)`)は `legal_downcross` 残余を取る。合法減算は `a(4) = 2 < 5` に着地し、target 5の履歴予算はhistorical horizon 4ですでに下がっている。

**証明:** 各条件をLeanカーネルの `decide` で数値検証する。この実例が、legal downcross残余が空虚な分岐ではないことを保証する。

## 全体の中での位置づけ

証明地図の「意味的探索domain: early representative」の入口である。`ExtendedHistoryNormal` の `representative_not_ready` 残余をここで1遷移分だけ展開し、閉じる分岐と閉じない分岐を正確に切り分ける。残った `legal_downcross` は `EarlyRepresentativeClosure` が、`forced_below_candidate` は `EarlyForcedCandidateClosure` が、いずれも将来(または過去区間)の弱上方crossingからのcrossing recoveryで閉じ、`EarlyRepresentativeComplete` で残余なしの完全stepに統合される。refined domain版の閉包は `ExtendedHistoryDirectRefined` にある。
