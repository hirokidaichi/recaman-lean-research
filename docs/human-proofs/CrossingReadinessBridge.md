# CrossingReadinessBridge

**役割:** 「crossing子がhorizon clockを失う」漏れは実軌道の具体例で満たされるため非存在証明では閉じられないことを確定させ、代わりに生成箇所を全数調査してreadiness保持版へ再証明し、残余を`TargetTailReturnHypothesis`一本へ橋渡しする。

## このモジュールの役割

`SemanticOracleRecursion.lean`の`ReadyRefinedInvariant.step_or_readyCrossing`は、readiness（節点の履歴horizonがtarget時計を満たすこと、すなわち`target ≤ node.horizon + 1`）を持つ親からの局所stepを与えるが、返される子は素の`OrbitReadyRefinedInvariant`である。従って再帰は、子がcrossing構成子でありかつその格納horizonがtarget時計より後退したときに漏れる。この「unready crossing漏れ」が大域残余の第三項だった。

本モジュールはその漏れを三方向から解析する。第一に、漏れの**literalな形は証明不能**である（実軌道に反例が存在する）。第二に、漏れが起こりうる辺の形状を完全に特定する（budget不変・horizon下降・anchor非増加のcrossing辺に限る）。第三に、crossing子を実際に生成する箇所を全数調査し、そのすべてで子は最初からreadyであり型がそれを記録していなかっただけであることを示して、readiness保持版を再証明する。結果として残余は`ReadyCrossingReadyStepHypothesis`一本になり、さらにそれは`TargetTailReturnHypothesis`から従う。

## 主要な定義

### `OrbitReadyNormalNonCrossingStep` (L463)

「orbit-ready normal親の子は決してcrossing構成子に落ちない」という監査述語。`OrbitReadyDirectRefined.lean`の`OrbitReadyNormalInvariant.refinedStep`は目視監査では全分岐がready current/debtまたはextended-historyへ落ちるが、statementが結論をrefined unionで述べているためその事実を記録していない。この述語は**その欠けているstatementちょうど**を名指すものであり、それ以上の主張ではない。本モジュール内では仮定として扱われ、`CrossingReadinessClosure.lean`で定理になる。

### `ReadyCrossingReadyStepHypothesis` (L539)

ready crossing節点からの局所stepで、**子側のclockも保つ**もの。すなわち「任意のready crossing節点は、targetを出現させるか、`ReadyRefinedInvariant`（refined domain所属 ∧ readiness）を満たす子へrank下降する」。既存の`ReadyCrossingRefinedStepHypothesis`は子のreadinessを忘れた弱い形であり、本仮説はその強化版である。

## 定理と証明

### `crossingSearchInvariant_twelve_unready` (L39)

**主張:** target 12・節点`⟨7, 7, .normal, 7⟩`は`CrossingSearchInvariant 12`を満たし、かつ`node.horizon + 1 = 8 < 12`、すなわちunreadyである。

**証明:** 実軌道の値を並べるだけである。`a 5 = 7 < 12 < 13 = a 6`なので時刻5→6はtargetを跨ぐ上昇で、しかも`6`は減算不能なので強制加算である。さらに`12 ∉ valuesThrough 5 = {0,1,3,6,2,7}`だから`target_missing`も成立する。`crossing_before_horizon`は`crossingTime + 1 < horizon`すなわち`6 < horizon`を要求するので合法な最小のhorizonは`7`であり、節点のanchorとlocal measureはどちらも`a 5 = 7`となる。この最小horizonでは`horizon + 1 = 8`がtarget 12にはるかに届かない。すべて有限計算で決まる。

### `exists_unreadyCrossing_twelve` (L59) / `not_forall_crossing_horizonReady` (L67)

**主張:** unready crossing残余は充足可能であり、「すべてのcrossing節点はready」は**偽**である。

**証明:** 上の節点をそのまま存在証拠にする。全称版に適用すれば`12 ≤ 8`が出る。

この三つが本モジュールの最初の成果であり、その内容は否定的である。crossing構成子は自分自身のhorizon時計を含意しない。よって**この残余は「そのような節点は存在しない」という形では絶対に閉じられず、「再帰がそこへ到達しない」という到達不能性でしか閉じられない**。以降の全設計はこの制約から出ている。

### `horizon_lt_of_budgetDrop` (L80)

**主張:** 履歴budget（`missingBelowCount target h` = 時刻`h`までの履歴にまだ現れていないtarget未満の値の個数）が厳密に減るなら、horizonは厳密に増えている。

**証明:** budgetは時刻について単調非増加なので対偶を取る。

### `readyRefinedInvariant_iff` (L102)

**主張:** `ReadyRefinedInvariant target node ↔ RefinedNonCrossingInvariant target node ∨ ReadyCrossingSearchInvariant target node`。

**証明:** refined domainの三構成子で場合分けする。非crossingの二つでは`horizon_ready`フィールドが最初から備わっている（`RefinedNonCrossingInvariant.horizon_ready` (L91)）ので、readiness条件は情報を足さない。crossing構成子でだけreadinessが独立した内容を持ち、それはちょうど`ReadyCrossingSearchInvariant`が加えるフィールドである。この同値式が本モジュールの設計図で、「readinessはcrossing構成子の内部だけの問題である」ことを型のレベルで述べている。

### `readyRefined_of_horizon_le` (L137) / `readyRefined_of_budgetDrop` (L146)

**主張:** 親がreadyで子のhorizonが親を下回らないなら子もready。特にbudgetを落とすrank辺は常にreadinessを保存する。

**証明:** 前者は`target ≤ parent.horizon + 1 ≤ child.horizon + 1`。後者は`horizon_lt_of_budgetDrop`を前者に接続する。

### `unreadyRefinedChild_shape` (L161)

**主張:** readyな親から出てreadinessを失うrefined子は、必ず(1) crossing節点であり、(2) `child.horizon < parent.horizon`、(3) 履歴budgetは不変、(4) anchorは増えていない。

**証明:** refined domainのreadiness-or-crossing分解から、unreadyな子はcrossing構成子でしかありえない。horizonの下降は`child.horizon + 1 < target ≤ parent.horizon + 1`から直ちに出る。rank辺は四成分lex順なので第一成分は落ちるか等しいかだが、horizonが下がっている以上budgetは落ちえない（単調性）。よって第一成分は等しく、残る成分を見て(4)を得る。

**この補題が効いているところ:** 履歴horizonを前進させる機構（downcross exit、budget gap exit）は原理的に漏れを起こせないことがこれで確定する。漏れの候補は「同じbudgetのままhorizonを巻き戻すcrossing辺」だけに絞られる。

### `ReadyDebtInvariant.readyExtendedHistoryExit` (L201)

**主張:** readyなdebt節点は、`ExtendedHistoryNormalInvariant`を満たす子へrank下降できる（子構成子をrefined unionへ広げずに保つ）。

**証明:** debtの初出時刻から`⟨horizon, a firstTime, .normal, a firstTime⟩`を組む。horizonは親のものをそのまま再利用するので親のreadinessが逐語的に移る。rank下降はdebt不変量の`value_lt_anchor`によるanchor下降で出る。

### `ReadyDebtInvariant.obstruction_readyRefinedStep` (L234)

**主張:** ready debt節点の強制加算障害は、targetの出現か、`ReadyRefinedInvariant`を満たす子を与える。

**証明:** 障害の三形で場合分けする。`legal_reaches_anchor`は前定理のextended-history出口へ流す。残る二つ（`addition_nonpositive`と`addition_seen_below_target`）は`debtCrossing_enters_recovery`でcrossing recovery証明書を得るが、**構成される子のhorizonは親のhorizonそのもの**なので、親の`horizon_ready`がそのまま子の`horizon_ready`になる。ここが「子は元からready、型が記録していなかっただけ」の第一例である。

### `ReadyDebtInvariant.readyRefinedStep` (L292)

**主張:** ready debt節点はready refined domain内で残余なしにstepできる。

**証明:** 既存の分類（ready current/debt step か障害か）に前定理を接続する。

### `extendedNormal_readyCrossingRecovery_refinedStep_from_below` (L315)

**主張:** extended-history normal節点から、target未満の値を持つ時刻が一つあれば、targetの出現かready refined子が得られる。

**証明:** target未満の地点から`exists_weakUpcrossingStep_from_below`で次の強制加算による上昇（weak upcrossing）を取る。端点がtargetに一致すれば出現、しなければ厳密crossingになりcrossing recovery証明書が組める。要点は子のhorizonを`max node.horizon (crossingTime + 2)`に取ることで、この値は定義上親のhorizon以上だから親のreadinessが単調性だけで移る。rank下降は`a crossingTime < target ≤ a representativeTime`によるanchor下降。**crossing子を新規生成しながら漏れない**のは、horizonをmaxで取っているからである。

### `ExtendedHistoryNormalCertificate.readyRefinedStep_of_budgetGap` (L382)

**主張:** 代表時刻とhorizonの間にbudget gapがあるextended-history節点も、ready refined子を持つ。

**証明:** budget gapは「代表時刻以降にtarget未満の新しい値が初出する」ことを意味するので、その時刻を前定理に渡す。

### `EarlyRepresentativeCertificate.readyRefinedStep` (L405)

**主張:** early representative（target時計を満たさない代表時刻を持つextended-history節点）は決して漏れない。

**証明:** 既存の四分類に沿う。target出現枝はそのまま、forward child枝はextended-history構成子で親horizonを再利用、blocked候補枝はready debtへ入る（readinessは親の`horizon_time_ready`から移送）。二つの残余機構（`legal_downcross`と`forced_below_candidate`）はいずれも「target未満の地点」を供給するのでL315のready版upcrossing出口へ流せる。

### `ExtendedHistoryNormalCertificate.readyRefinedStep` (L472) / `ExtendedHistoryNormalInvariant.readyRefinedStep` (L504)

**主張:** 監査述語`OrbitReadyNormalNonCrossingStep`のもとで、extended-history normal節点はready refined domain内で局所全域である。

**証明:** 代表時刻がtarget時計を満たすかで分ける。満たさなければearly representative（L405）。満たす場合、budgetが代表時刻とhorizonで一致するなら唯一ここでorbit-ready生成器を呼び、結果を`transportProgress_of_budgetStable`で親のrankへ移送する。一致しないならbudget gap枝（L382）。**orbit-ready生成器を参照する分岐はこの一箇所だけ**であり、監査述語が要るのもここだけである。

### `ReadyCurrentOrDebtInvariant.readyRefinedStep` (L516)

**主張:** ready current / ready debt節点も同様に局所全域である。

**証明:** current枝は監査述語を直接使い、debt枝は相とlocal measureを`DebtInvariant`のフィールドで正規化してからL292を適用する。

### `ReadyCrossingReadyStepHypothesis.toReadyCrossingRefinedStep` (L546)

**主張:** 子のclockを忘れると既存の弱い仮説に戻る。新仮説が旧仮説の真の強化であることの確認である。

### `ReadyRefinedInvariant.readyStep` (L557) / `readyRefinedPhaseSearchOracle` (L572)

**主張:** 監査述語とclock保存crossing stepの二つを認めれば、ready refined domainは制限付きphase-searchオラクル（rank下降を保証する局所全域な子供供給器）になる。

**証明:** L102の同値式で三構成子に分解し、非crossing側はL472/L516、crossing側は仮説そのもの。

### `occurs_of_readyCrossingReadyStep` (L584)

**主張:** `0 < target`と上記二仮定から、`∃ t, a t = target`。

**証明:** canonical startがready refined節点であること（`targetStartInvariant_readyRefined`）と、オラクルの整礎下降を組み合わせる。**unready crossing残余は消えている**：以前の`occurs_or_unreadyCrossing_of_readyCrossingStep`が明示的に返していた残余項が、子のclockを保つよう仮説を強めたことで発生しなくなったためである。

### `phaseSemanticChild_occurs_of_readyCrossingReadyStep` (L595)

**主張:** readyなsemantic子から始めた下降でも同じ結論が出る。

**証明:** semantic不変量とreadinessからready refined節点を作り、同じオラクルで下降する。

### `ReadyCrossingSearchInvariant.readyRefinedStep_of_futureDowncross` (L614)

**主張:** future downcross（格納horizon以降にtarget以上からtarget未満へ落ちる遷移）を持つready crossingは、ready refined子を持つ。

**証明:** downcross端点は新鮮なので履歴budgetを厳密に落とす。`readyRefined_of_budgetDrop`でreadinessが自動的に付く。

### `ReadyCrossingSearchInvariant.readyRefinedStep_or_continuationGrowth_of_horizonBelow` (L630)

**主張:** 格納horizonの値がtarget未満のready crossingは、targetの出現か、ready refined子か、joint-growth残余（`CrossingContinuationGrowthResidual`：budget不変かつanchor非減少でrank下降が取れないliteralな障害）のいずれかである。

**証明:** 次のweak upcrossingを取り、その厳密crossingから子`⟨time + 2, a time, .normal, a time⟩`を組む。子のreadinessは無料で出る：親のreadinessとupcrossing開始時刻の下界`node.horizon ≤ time`から`target ≤ node.horizon + 1 ≤ time + 1 ≤ time + 3`。あとはbudgetが落ちるかで分ける。落ちれば第一成分でrank下降。落ちない場合はanchorを見て、下降していれば`phaseSearchProgress_of_horizonAndAnchor`、していなければ**rank下降が存在しないことを証明した上で**残余として記録する。既存版との差はready子を返す点だけで、証明の実質は変わらない。ここも「子は最初からready、statementが忘れていただけ」の例である。

### `ReadyCrossingSearchInvariant.readyRefinedStep_of_tailDowncross` (L732)

**主張:** `ReadyCrossingTailDowncrossHypothesis`（target以上の格納horizonを持つready crossingからは出現かfuture downcrossが取れる）のもとで、ready crossingは常にready refined子を持つ。

**証明:** 格納horizonの値がtarget以上ならtail仮説→L614。target未満ならL630で三分岐する。残余枝が出た場合が要点である。中間子のhorizonは`time + 2`で、budget不変性から`a (time + 2)`はtarget以上でなければならない（target未満ならそこにdowncrossができてbudgetが厳密に落ち、不変性に反する）。従って中間子にもう一度tail仮説を適用でき、そこから得たdowncrossがbudgetを落とす。budget不変性により、その下降は元の親から見ても第一成分の下降になる。孫のreadinessは`horizon_lt_of_budgetDrop`で`time + 2 < next.horizon`を得てから移送する。

### `ReadyCrossingSearchInvariant.readyRefinedStep_of_targetTailReturn` (L789) / `readyCrossingReadyStepHypothesis_of_targetTailReturn` (L800)

**主張:** `TargetTailReturnHypothesis target`（target以上の値を取った任意の時刻以降に、targetが出現するかtarget未満へ戻る時刻がある）から、clock保存crossing stepが従う。

**証明:** tail returnからtail downcross形を作る既存補題（`readyCrossingTailDowncross_of_targetTailReturn`）にL732を接続する。

### `occurs_of_targetTailReturn` (L809)

**主張:** `0 < target`・監査述語・`TargetTailReturnHypothesis target`から、`∃ t, a t = target`。

**証明:** L800とL584の合成。**従来、tail return仮説は「認めても主残余が閉じない」と評価されていた**ので、単一targetで出現を生むようになったこと自体は位置づけの変化である。

### `OrbitReadyNormalNonCrossingStep.toRefinedStep` (L822)

**主張:** 監査述語から既存の`OrbitReadyNormalInvariant.refinedStep`が逐語的に復元される。

**証明:** 子の非crossing性を忘れてrefined unionへ埋めるだけ。監査述語が独立した新仮定ではなく既存定理の**真の強化**であることの確認である。

### `LeastMissingTarget.not_readyStep_pair` (L839)

**主張:** 最小未出target（全軌道で出現せず、それ未満の値はすべて出現する値）は、監査述語とclock保存crossing stepの連言を反証する。

**証明:** 二つを認めればL584でtargetの出現が出るが、最小未出targetは出現しない。

### `readyCrossingReadyStep_iff_occurs` (L852)

**主張:** 監査述語だけを認めると、`ReadyCrossingReadyStepHypothesis target ↔ ∃ t, a t = target`。

**証明:** 順方向はL584。逆方向はtargetが出現するなら任意の節点で第一枝を返せばよい。

**この二定理の役割:** これらは前進の記録ではなく、**難所を隠していないことを明示する装置**である。L839とL852は「残ったcrossing仮説は結論と同値であり、証明の困難はそこへ移動しただけで消えていない」と述べている。縮んだのは仮説の適用範囲（全crossing節点上の`CrossingRefinedStepHypothesis` → *ready* crossing節点上で*ready*な子を返すstep）であって、証明の難しさではない。

## 補助補題

`RefinedNonCrossingInvariant.horizon_ready` (L91) は非crossing構成子が`horizon_ready`フィールドを最初から持つことの確認である。`RefinedNonCrossingInvariant.toReadyRefinedInvariant` (L122) と `ReadyCrossingSearchInvariant.toReadyRefinedInvariant` (L129) は`readyRefinedInvariant_iff`の両向き埋め込みで、以降のほぼ全定理で機械的に使われる。

## 全体の中での位置づけ

証明地図（docs/PROOF_MAP.md）では「unready crossingの実在性」「readiness橋」「tail return仮説の効力」の三行に対応する。上流は`SemanticOracleRecursion.lean`（ready refined domainとその局所step、および残余の三分解）と`CrossingTailRefined.lean`（`TargetTailReturnHypothesis`とtail downcross形）である。下流は`CrossingReadinessClosure.lean`で、そこで監査述語`OrbitReadyNormalNonCrossingStep`が仮定から定理へ格上げされ、本モジュールの全結論が無仮定形になる。

成果を正確に述べると次のようになる。**否定的結果**として、unready crossing漏れのliteralな形は証明不能であることが確定した（`not_forall_crossing_horizonReady`）。**構造的結果**として、漏れうる辺の形状が完全に特定され（`unreadyRefinedChild_shape`）、crossing子の生成箇所すべてで子は元からreadyであることが確認された。**縮約**として、残余は監査述語一本＋`TargetTailReturnHypothesis`になった。ただし最後の点については`readyCrossingReadyStep_iff_occurs`が同時に示すとおり、残った仮説はtargetの出現と同値であり、証明の難しさは移動しただけで減っていない。
