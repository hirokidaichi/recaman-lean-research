# レカマン数列の全射性に向けたLean 4形式化 — 研究結果レポート

**基準日:** 2026-08-28  
**形式化環境:** Lean 4.33.1  
**研究状態:** 局所力学とwell-founded探索骨格は大幅に形式化済み。全射性は未証明。

## 1. 要旨

レカマン数列を

\[
a_0=0,
\qquad
a_n=
\begin{cases}
a_{n-1}-n & (a_{n-1}>n\text{ かつ候補が未出現})\\
a_{n-1}+n & (\text{それ以外})
\end{cases}
\]

で定義する。未解決問題は、任意の \(m\in\mathbb N\) に対して
\(a_t=m\) となる時刻 \(t\) が存在するか、すなわち数列が
\(\mathbb N\) 上で全射かどうかである。

本研究では、全射性を直接仮定することなく、実軌道、履歴、商・剰余座標、
符号付きポテンシャル、借用遷移、blocker、CoverageStepをLean 4で形式化した。
その結果、軌道の大部分を有限降下またはwell-foundedな探索進捗へ変換できた。

最新の到達点では、対角負債とcrossingを意味的domain内で閉じ、任意の正目標に対する
canonical開始点の全符号・低level分岐を、目標出現または既存ランクの下降へ接続した。
level 1/2の強制成長は即時にはrankを下げないが、二段先のcandidateが元値より小さくなる
ためCoverageStepへ回収できる。さらにcurrent normal、ready debt、horizon-ready extended-history
normalをclock provenanceを保ったrefined stepへ閉包し、crossing frontierの二時計middle区間も
typed extended-historyへ収容した。残る中心課題は`CrossingSearchInvariant`自身の局所stepである。

## 2. 形式化方針

### 2.1 実軌道と保存履歴

数列値だけでなく、それまでに出現した値の履歴を明示的に扱う。
減算候補が既出かどうかというレカマン数列固有の非局所条件を、
`valuesThrough`、`FirstAt`、`CanSubtract`として形式化した。

### 2.2 三角座標

時刻 \(n>0\) で

\[
a_n=nq+r,\qquad 0\le r<n,
\]

とし、三角数 \(U(q)=q(q+1)/2\) を用いて

\[
G(q,r)=r-U(q)
\]

を定義した。`G=m` は、商に対応する連続減算が目標値 \(m\) を狙う
「目標面」と一致する。

### 2.3 CoverageStep

固定目標 \(m\) と親値 \(v\) に対して、局所探索の成功を

1. \(m\) の実出現、または
2. \(m\le y<v\) を満たす別の初出値 \(y\)

として統一した。これにより、直接着地、blocker、exact gate、局所脱出、
合法減算を同じ大域帰納インターフェースへ接続できる。

## 3. 証明済みの主要結果

### 3.1 座標遷移の全域化

借用証明書

\[
b(n+1)+r=q+s,\qquad 0\le s<n+1
\]

を導入し、加算・減算双方について任意借用回数の商、剰余、ポテンシャル変化を
証明した。借用回数の存在と一意性、通常領域・一段借り・多段借りの分類も
機械検証済みである。

### 3.2 実軌道上の多段借り排除

全時刻で

\[
a_n\le U(n),\qquad 2q\le n+1
\]

を証明した。これと借用証明書から、実軌道では常に \(b=0\) または
\(b=1\) であり、真正な多段借り \(b\ge2\) は発生しない。

### 3.3 負領域から一段借りへの有限到達

\(G(q,r)<0\) でゼロ借用が続く間、剰余は各遷移で少なくとも2減る。
したがって任意の負状態から高々 \(\lfloor r/2\rfloor\) 歩で一段借りが
発生することを証明した。

一段借りの欠損を \(\delta=q-r\) とすると、

\[
0<\delta\le q,
\qquad
G(q,r)=-(U(q)+\delta)
\]

であり、ポテンシャル増加は

\[
\Delta G_{+}=n+1-q,
\qquad
\Delta G_{-}=n+q
\]

となる。

### 3.4 低商回復と高商blocker

一段借り後の着地商が3以下なら、着地ポテンシャルは必ず非負になる。
回復に失敗する場合は着地商4以上である。高商加算では、既出の減算候補が
目標以上かつ現在値未満のblockerとなり、CoverageStepを与える。
合法減算側は着地点そのものが小さい新値となる。

### 3.5 非負アンダーシュート帯の有限化

\(0\le G<m\) では状態は通常領域にあり、合法減算は \(G\) を保存して商を下げる。
強制加算はblockerを生成する。低商 \(q\le1\) まで到達した後は、
高々2歩でポテンシャルが厳密に下がる。

これを統合し、有限時間内に次のいずれかが起こることを証明した。

- CoverageStep
- 負領域への復帰
- 非負ポテンシャルの厳密下降

### 3.6 履歴予算と三成分探索ランク

時刻 \(n\) までに未出現の \(0,\ldots,m-1\) の個数を
`missingBelowCount m n` と定義した。新しい目標未満値が初出するとこの個数が下がる。

探索状態

\[
(\text{horizon},\text{activeParent},\text{orbitValue})
\]

に対して

\[
(\text{missingBelowCount},\text{activeParent},\text{orbitValue})
\]

という辞書式ランクを構成し、well-founded性を証明した。
全ノードをこのランクで進める`HistorySearchOracle`があれば目標出現が従う。

### 3.7 対角状態の極大後方解析

正の対角状態 \(a_t=t\) は加算では到達できず、直前は合法減算である。
末尾の連続減算を後方へ極大延長し、その開始時刻を \(s\)、長さを
\(L\ge2\) とすると、開始直前では加算が強制されている。

その既出減算候補を \(y\)、初出時刻を \(f_y\) とすると、

\[
t+1\le y<a_s,
\qquad
f_y<s<t,
\qquad
y+2s=a_s
\]

が成立する。したがって任意の対角状態から、

- \(t+1\) の実出現、または
- 目標以上で、初出時刻が対角時刻より早い具体的blocker

を無条件に得られる。

### 3.8 位相付き四成分ランク

値の上昇と時刻の下降を単純に「どちらかが下がる」とすると循環し得る。
そこで通常探索と対角負債探索を区別し、

\[
(\text{missingBelowCount},\text{anchorParent},\text{phase},\text{localMeasure})
\]

を導入した。

- 通常から負債へ入ると `phase` が下がる
- 負債中は `localMeasure` として初出時刻を下げる
- 通常へ戻るには `anchorParent` の厳密下降を要求する

この順序のwell-founded性、入口・内部下降・出口の各進捗補題、
および`PhaseSearchOracle`から目標出現が従うことを証明した。

### 3.9 canonical開始点の局所閉包

任意の正目標について構成できるcanonical開始点を、potentialの負、目標以上、
通常の非負undershoot、level 0/1/2へ分類した。負領域と通常の非負域は既存epoch定理へ、
level 0は二段以内の目標出現へ接続した。level 1/2のquotient-one強制加算だけは直後に
値とanchorが増え、履歴予算も不変なので即時rank下降にならない。しかし次の候補は
元値より1小さく、legalならfresh、blockedなら既出であるため、両方をCoverageStepへ変換した。
これにより`targetStartInvariant_phaseSemanticStep`を追加仮定なしで証明した。

同時にordinary `NormalSearchInvariant`を監査し、過去の初出値を後のhorizonへ載せられるため、
現在値との一致とepochの時刻条件が従わないことを具体反例で証明した。現在軌道に整合する
`OrbitReadyNormalCertificate`については、負、高potential、非負undershoot、level 0/1/2の
全分岐を残余なしのsemantic stepへ接続した。

### 3.10 extended-historyの完全局所閉包

historical normalではanchor値を取るrepresentative timeと、履歴予算を測るhistory horizonを
分離した。単純なcurrent-step輸送にはrepresentative readinessとbudget stabilityが必要だが、
失敗する二分岐も既存四成分rankのまま閉じる。

- early representative: 次の合法減算でtarget未満へ落ちるか、強制加算の原因となる既出の
  target未満candidateを持つ。
- budget gap: `missingBelowCount`のstrict dropから、representative historyでは未出で後の
  horizonまでに出現したtarget未満値を抽出できる。

いずれも実際のbelow-target occurrenceから将来のforced upcrossingを取り、pre-crossing値を
新anchorとする`crossing_recovery` childへ進む。新horizonを元horizon以上に取るので履歴予算は
増えず、新anchorは`below target ≤ old anchor`により厳密に下がる。

またparent-dropはfuture current／earlier debtへ分解し、通常debt evolutionはhistorical normal
self-exitを使わずearlier debtを保てることを証明した。debtにはhorizon readinessを追加した
`ReadyDebtInvariant`を導入し、current Coverageからこの条件を伝搬する。

### 3.11 refined clock閉包とoracle境界

orbit-ready normalの負・高potential・undershoot・level 0/1/2を生成分岐から直接たどり、broad
`PhaseSemanticInvariant`を経由しない`OrbitReadyNormalInvariant.refinedStep`を証明した。これにより
normal/debt childのhorizon readinessがinterfaceで消える問題はreachable theoremから除かれた。

ready debtのforced-addition obstructionはcrossing recoveryへ直接入り、合法減算が固定anchorへ達する
二時計境界だけはhorizon-ready extended-historyへ退出する。crossing frontierのmiddle residualも同じ
typed childへ入る。extended-history側ではbelow-target occurrenceからfuture upcrossingを作る共通adapterを
導入し、early／budget-gapの全分岐をrefined domain内で閉じた。

constructor完全監査の結果、refined restricted oracleに残る証明義務は
`CrossingRefinedStepHypothesis`ひとつになった。現行`CrossingSearchInvariant`は入口crossingを保持するが、
元のstrong debtのpost-state first occurrence、post値と旧anchorの比較、horizon readinessを保持しない。
これが次の型設計上の境界である。さらにcrossing nodeのanchorはtarget未満、非crossing refined
nodeのanchorはtarget以上なので、両者のrank edgeはstrict history-budget dropを必ず伴う。
同じhorizonのsuccessorはcrossingに限られることも形式化した。
ただし保存horizon以後にactual downcrossが起きる場合、そのendpointはfreshなlegal-subtraction値なので、
strict budget dropを使ってextended-historyへ退出できる。この条件付き枝もrefined stepとして閉じた。

## 4. 大域証明骨格

既に証明済みの大域結論は次の形である。

\[
(\forall m>0,\ \mathrm{CoverageOracle}(m))
\Longrightarrow
\forall m,\exists t,\ a_t=m.
\]

また、`HistorySearchOracle`および`PhaseSearchOracle`についても、
totalな局所進捗オラクルから目標出現を導くwell-founded inductionを証明している。

したがって未解決部分は、全射性を直接Leanで証明することではなく、
各探索ノードに対する局所オラクルを埋めることへ明示的に圧縮されている。

## 5. 現在の未証明部分

historical normalのbudget gapとearly representativeは解消済みであり、horizon-readyな
`ExtendedHistoryNormalInvariant`はrefined domain内で残余なしの局所stepを持つ。current nodeの全局所
分岐、current生成8系統のadapter、5種類のtyped provenance、ready debt obstruction、crossing frontier
middle区間もrefined stepへ統合済みである。

現在の未証明部分は、crossing recovery node自身の局所stepである。
refined child domainは次を含む。

- orbit-ready current normal
- horizon-ready strong debt
- extended-history normal
- crossing recovery

最初の三constructorは具体的なtotal refined stepを持つ。`RefinedOracleBoundary`はcanonical startの
domain所属とconstructor監査を統合し、`CrossingSearchInvariant`の局所stepだけを仮定すれば目標出現が
従うことを証明する。次に必要なのは、crossing生成時に消えているstrong debt provenanceとready
horizonを保持するconstructorを導入し、その局所stepを既存crossing frontier解析へ接続することである。
ただしprovenance追加だけでは不十分であり、新しいbelow-target履歴によるbudget下降、または
crossing-to-crossingの追加下降を構成する必要がある。

horizon-below枝は次のweak upcrossingまで完全分類した。
`crossingNumeric_progress_iff_budgetDrop_or_anchorDrop`により、新crossingが現行rankを下げるのは
history budgetまたはpre-crossing anchorが下がる場合に限る。どちらも下がらない枝を
`CrossingContinuationGrowthResidual`として固定し、target 19、horizon 31、anchor 13→14の
実軌道で実在することをLeanで検証した。したがってcrossing-to-crossingの現行rank下降は
無条件には成り立たない。

ただしこのgrowth残余のchild horizonは必ずat-or-above targetであり、その後のdowncrossは
中間のanchor growthを迂回して元の親へ直接strict budget edgeを作る。
`no_futureDowncross_iff_tail_atOrAbove`は、future downcrossが一つもないことがpermanent
above-target tailと同値だと示す。`TargetTailReturnHypothesis`はこのpermanent tailの排除を厳密に表し、
`refinedStep_of_targetTailReturn`はそれがready crossingの全局所分岐を閉じることを証明する。
よって残る数学的核心は、局所crossing構成ではなくabove-target tailの長期再帰である。

この長期命題の強さも形式化した。仮想的な最小未出目標では、それ未満の値は個々に出現し、
有限個しかないので一つのhistory horizonまでにすべて既出となる。その後のdowncross endpointは
legal subtractionによりfreshでなければならず、既出性と矛盾する。
`LeastMissingTarget.eventually_strictlyAbove`はこれを用いて、最小未出目標があれば軌道がある時刻以降
常にその目標より大きいことを証明する。`all_targetTailReturn_iff_surjective`により、全targetに対する
tail returnは元のRecamán全射性予想と同値である。したがってこの境界を無条件に証明すること自体が本問題である。

この境界の内側も追加解析した。`MissingPermanentAboveTail`は、正の未出target、target未満の
履歴被覆、以後のstrictly-above tailを一つの証明書にする。tail内の任意の状態は高々二遷移で
`CoverageStep`を持つ。tail最小値では直後の減算と、その次の候補`a n - 1`への減算がともに
blockされるため二連続forced additionとなり、`a n - 1`の最初の出現はtail開始前にある。

一方、履歴被覆により四成分rankの外側予算はすでに0である。仮想反例からは、tail内horizon、
budget 0、future downcross不在を同時に持つ`PermanentTailCrossingCertificate`を構成できる。
このcrossingからnoncrossing refined子へ出るには負の履歴予算が必要になるため不可能である。
refined子が存在するなら、それはbudget 0のcrossingで、pre-crossing anchorを厳密に下げる。
したがって現在の核心は、tail最小値のhistorical blockerと、このstrict anchor childを接続することである。

座標potential単独はこの接続を与えない。二連続forced additionの実軌道例として、時刻4の
`2→7→13`はpotentialを`2→-2`へ下げるが、時刻5の`7→13→20`は`1→3`へ上げる。
両方をLeanカーネルで証明したため、二連続forced additionだけに基づくpotential単調性は棄却された。

historical blockerの反復は有限化できた。直下値の初出時刻から将来downcrossがあれば、endpointは
合法減算による初出のbelow-target値で、履歴予算が厳密に下がる。downcrossがなければ、その初出時刻を
新しいstrictly-above tailの開始点にでき、新tail最小値は旧最小値より厳密に小さい。
`MissingStrictAboveTail.exists_historicalDowncrossCertificate`はminimum valueへの強帰納により、
必ず有限回で前者へ到達することを証明する。

ただしこのbudget下降はzero-budget crossing親の未来ではなく、tail以前の履歴区間にある。
downcross後のupcrossingを親と同じzero-budget horizonへ載せ、anchorが小さければrefined childになる。
非下降の場合は`HistoricalCycleGrowthResidual`を返す。さらに親crossingをその再構成upcrossing自身に
選ぶとchild=parentとなる停留residualを、任意の仮想permanent tailから構成できることも証明した。
これは任意crossing選択を許したままでは、一回のhistorical cycleが新rankにならないというno-go結果である。

canonical selectionも監査した。最初のfuture weak upcrossingは自然数強帰納で存在・一意に選べる。
historical downcross endpointからこの規則を適用すると旧tail開始前にendpointがある。しかし同じendpointから
再選択すれば一意性により同じcrossing時刻へ戻るため、earliest規則はwitness ambiguityだけを除き、
stationary cycle自体は除かない。

そこで`seenBelowCount = target - missingBelowCount`をdual-history量として導入した。実時間の増加に対して
単調増加し、missing budgetのstrict dropとちょうど逆向きのstrict gainを持つ。zero-budget tail horizonから
positive-missingなhistorical first occurrenceへ戻るとseen countは厳密に下がる。

`PermanentAboveCycleRank`は`(anchor, phase, seenBelowCount, tailMinimum)`の四成分lex rankを定義する。
phaseはcrossing、backtrack、dischargeの順に一方向下降する。combined obstructionからbacktrackへ入り、
no-downcross renewed tailではseen/minimumが下降し、downcrossではdischargeへ入る。rankはwell-foundedで、
すべてのhistorical内部stepを受け入れる。dischargeからcrossingへのexitはstrict anchor dropと必要十分であり、
stationary同anchor exitは拒否される。従来の`HistoricalCycleGrowthResidual`はこのrankでも正確にexit obstructionとなる。

`PermanentAboveCycleExit`はこのexitを時刻provenanceまで精密化した。
`PermanentTailDischargeReturnCertificate`はcombined obstruction、有限historical downcross、そのendpointからの
最初のreturn upcrossing、親crossingの実時刻を同時に保持する。`(anchor, crossingTime, phase,
seenBelowCount, tailMinimum)`の五成分rankはwell-foundedで、同anchorでもreturn crossingが旧crossingより
早ければ厳密に退出できる。chronologicalに旧crossingがendpoint以後ならcanonicalityによりreturn時刻は
旧時刻以下である。従って最終的な非進捗kernelは、strict anchor growth、旧crossingがendpointより前、
anchor・時刻とも同一のliteral stationaryの三ケースに限られる。同じendpointですでにcanonicalな旧crossingは
実際にstationary constructorを生むため、time cursorだけで全cycleを閉じることもできない。

さらに`PermanentAboveCycleRebase`で、canonical returnを同じzero-budget horizonの新しい親にする操作を
完全に型付けした。returnのforced addition、目標未出、座標、horizon以前性からready crossingを再構成し、
旧permanent tailとtail minimumをそのまま持つcombined certificateを得る。ところが同じdowncross provenanceを
新しい親から再生すると、canonical returnは親crossingそのものである。従ってanchorと時刻が一致した
literal stationary kernelとcycle exit不成立が、任意の元discharge certificateから無条件に得られる。
これはgrowth／chronology残余をcanonical rebaseで処理する案が、stationary coreへ正規化するだけというno-goである。

よって、全射性を証明済みとは主張しない。

## 6. 計算実験の位置づけ

標準軌道を10億項まで調べた実験では、一段借りイベント35回、真正な多段借り0回、
全イベントが最初の一段借りで非負へ回復するという結果を得た。
ただしこの結果は仮説選択の材料であり、Lean証明には一切取り込んでいない。

再現コードは`experiments/`にあり、Lean本体から依存しない。

## 7. 主要定理と所在

| 内容 | 代表的なLean定理 | モジュール |
|---|---|---|
| 実軌道上界 | `a_le_upperTri` | `OrbitBounds.lean` |
| 多段借り排除 | `BorrowData.eq_zero_or_one_of_coordinatesAt` | `OrbitBounds.lean` |
| 負領域から一段借り | `eventually_oneBorrow_of_negative_halfRemainder` | `Recovery.lean` |
| 負エポック主二分法 | `negative_epoch_undershoot_or_coverage` | `NegativeEpoch.lean` |
| 非負帯有限降下 | `undershoot_eventually_negative_or_localCoverage` | `Undershoot.lean` |
| 三成分ランク | `historySearchProgress_wellFounded` | `HistoryBudget.lean` |
| 対角極大後方鎖 | `diagonal_longDescent_has_maximalTail` | `Diagonal.lean` |
| 早期blocker抽出 | `diagonal_successor_occurs_or_earlierBlocker` | `Diagonal.lean` |
| 四成分位相ランク | `phaseSearchProgress_wellFounded` | `PhaseSearch.lean` |
| 対角負債への入口 | `diagonal_successor_or_entersPhaseDebt` | `PhaseSearch.lean` |
| 位相オラクル帰納 | `phaseSearchOracle_implies_occurs` | `PhaseSearch.lean` |
| canonical局所step | `targetStartInvariant_phaseSemanticStep` | `CanonicalGrowthRecovery.lean` |
| forced growth二段回収 | `CanonicalForcedGrowthChamber.twoStep_phaseSemantic` | `CanonicalForcedGrowth.lean` |
| ordinary normal境界 | `normalSearchInvariant_not_orbitReady` | `NormalSemanticBoundary.lean` |
| current normal局所totality | `OrbitReadyNormalInvariant.phaseSemanticStep` | `OrbitReadyComplete.lean` |
| provenance-aware normal domain | `ProvenancedNormalInvariant` | `NormalProvenance.lean` |
| extended-history境界 | `ExtendedHistoryNormalCertificate.phaseSemanticStep_or_residual` | `ExtendedHistoryNormal.lean` |
| typed historical生成元 | `TypedHistoricalNormalProvenance` | `TypedNormalProvenance.lean` |
| Coverage current/debt分解 | `coverageStep_currentOrDebt` | `CoverageDebtBridge.lean` |
| downcross budget-gap閉包 | `DowncrossRestartNormalProvenance.phaseSemanticStep` | `DowncrossBudgetGap.lean` |
| early representative totality | `EarlyRepresentativeCertificate.phaseSemanticStep` | `EarlyRepresentativeComplete.lean` |
| generic historical totality | `ExtendedHistoryNormalCertificate.phaseSemanticStep` | `ExtendedHistoryComplete.lean` |
| historical current/debt分解 | `normalParentDrop_currentOrDebt` | `HistoricalDebtBridge.lean` |
| ready debt局所step | `ReadyDebtInvariant.step_or_obstruction` | `ReadyDebtInvariant.lean` |
| refined child境界 | `OrbitReadyNormalInvariant.refinedStep_or_horizonResidual` | `OrbitReadyRefinedStep.lean` |
| current direct refined totality | `OrbitReadyNormalInvariant.refinedStep` | `OrbitReadyDirectRefined.lean` |
| ready debt refined totality | `ReadyDebtInvariant.refinedStep` | `ReadyDebtRefined.lean` |
| crossing frontier middle閉包 | `ReadyDebtInvariant.crossingFrontierFirstAt_refinedStep` | `CrossingFrontierRefined.lean` |
| historical direct refined totality | `ExtendedHistoryNormalInvariant.refinedStep` | `ExtendedHistoryDirectRefined.lean` |
| refined oracle境界 | `crossingRefinedStepHypothesis_implies_occurs` | `RefinedOracleBoundary.lean` |
| crossing rank境界 | `crossing_refinedChild_budgetDrop_or_crossing` | `CrossingRefinedBoundary.lean` |
| future downcross閉包 | `ReadyCrossingSearchInvariant.refinedStep_of_futureDowncross` | `CrossingDowncrossRefined.lean` |
| horizon-below完全分類 | `ReadyCrossingSearchInvariant.refinedStep_or_continuationGrowth_of_horizonBelow` | `CrossingBelowRefined.lean` |
| crossing growth実例 | `crossingContinuationGrowth_actual_example` | `CrossingBelowRefined.lean` |
| no-downcross/above-tail同値 | `no_futureDowncross_iff_tail_atOrAbove` | `CrossingTailRefined.lean` |
| tail-return仮説下のready totality | `ReadyCrossingSearchInvariant.refinedStep_of_tailDowncross` | `CrossingTailRefined.lean` |
| tail return/全射性同値 | `all_targetTailReturn_iff_surjective` | `CrossingTailRefined.lean` |
| permanent tail二段Coverage | `strictAboveTail_coverageStep` | `PermanentAboveTail.lean` |
| zero-budget crossing抽出 | `MissingPermanentAboveTail.exists_crossingCertificate` | `PermanentAboveTail.lean` |
| tail最小値historical blocker | `MissingPermanentAboveTail.exists_minimumCertificate` | `PermanentAboveTail.lean` |
| zero-budget crossing anchor境界 | `MissingPermanentAboveTail.crossing_refinedChild_shape` | `PermanentAboveTail.lean` |
| potential非単調の実例 | `doubleForced_potential_has_both_directions` | `PermanentAbovePotential.lean` |
| historical predecessor二分法 | `PermanentTailMinimumCertificate.historicalPredecessorOutcome` | `PermanentAboveHistory.lean` |
| finite historical downcross | `MissingStrictAboveTail.exists_historicalDowncrossCertificate` | `PermanentAboveHistory.lean` |
| historical cycle residual分類 | `PermanentTailCombinedCertificate.refinedStep_or_historicalCycleGrowth` | `PermanentAboveHistory.lean` |
| stationary cycle no-go | `MissingPermanentAboveTail.exists_stationaryHistoricalCycleResidual` | `PermanentAboveHistory.lean` |
| canonical first upcrossing | `exists_firstWeakUpcrossingStep_from_below` | `PermanentAboveCanonical.lean` |
| dual history strict量 | `seenBelowCount_strict_of_missingBelowCount_strict` | `PermanentAboveCanonical.lean` |
| historical rank strict entry | `PermanentTailCombinedCertificate.entersTailHistory` | `PermanentAboveCanonical.lean` |
| permanent-tail cycle rank | `tailCycleProgress_wellFounded` | `PermanentAboveCycleRank.lean` |
| cycle exit/anchor同値 | `tailCycle_exitCrossing_iff_anchorDrop` | `PermanentAboveCycleRank.lean` |
| growth residual exit obstruction | `HistoricalCycleGrowthResidual.tailCycleExitObstruction` | `PermanentAboveCycleRank.lean` |
| typed canonical discharge return | `PermanentTailCombinedCertificate.exists_dischargeReturnCertificate` | `PermanentAboveCycleExit.lean` |
| cursor-refined cycle rank | `tailCursorCycleProgress_wellFounded` | `PermanentAboveCycleExit.lean` |
| cursor cycle exit同値 | `tailCursorCycle_exit_iff_cursorProgress` | `PermanentAboveCycleExit.lean` |
| 三kernel residual分類 | `PermanentTailDischargeReturnCertificate.cycleExit_or_kernelResidual` | `PermanentAboveCycleExit.lean` |
| canonical return rebase | `PermanentTailDischargeReturnCertificate.exists_canonicalReturnRebase` | `PermanentAboveCycleRebase.lean` |
| rebased stationary no-go | `PermanentTailDischargeReturnCertificate.exists_rebase_with_noCycleExit` | `PermanentAboveCycleRebase.lean` |

## 8. 結論

本形式化により、座標上の未定義領域、多段借り、負領域の無限滞留、
非負アンダーシュートの無限滞留、対角状態の後方履歴、crossing、canonical開始点の
全局所分岐は既存の意味的ランクへ接続され、current normal、ready debt、horizon-ready historical
normalはrefined局所totalityまで完成した。研究上の残余はcrossing recovery constructor自身に集中し、
その入口で失われたpost-state debt provenanceとhorizon readiness、およびstrict budget下降か
crossing内部下降を構成することへ限定された。
保存horizon以後のdowncross枝は解消済みであり、残るのはhorizon時点ですでにbelow-targetである場合と、
将来downcrossが得られない場合のcrossing内部解析である。
その後のhorizon-below分類により、前者は次のcrossingと実在するgrowth残余へ縮約され、
残余は必ずabove-sideへ戻ることが分かった。よってready crossingで未解決な数学的核心は、
permanent above-target tailを排除する長期再帰命題である。
permanent tailの追加解析により、仮想反例はzero-budget ready crossingと、tail最小値直下の
historical blockerを同時に持つことまで分かった。前者の任意のrefined stepはcrossing anchorを
厳密に下げなければならない。後者からそのstepを構成する接続は未証明であり、potential単独では
二連続forced addition上でも単調にならないことを反例で確認した。
historical blocker反復自体はminimum値下降により有限化され、必ずtail以前のfresh downcrossとbudget下降へ
到達する。しかしその後のupcrossingを同じcrossing親として再選択できるため、現行rankには停留residualが
残る。次に必要なのはcrossing選択のcanonical provenanceまたは複数cycleを測る新rankである。
earliest provenance単独では同時刻再選択を避けられないが、one-way cycle phaseとdual history budgetを持つ
well-founded rankにより、historical内部の無限loopは排除された。crossing time cursorを追加すると
equal-anchorかつearlier-timeのreturnもstrict exitへ変わる。残る義務は、完全分類された三kernel residual、
すなわちanchor growth、chronology mismatch、literal stationaryの排除またはさらなる縮約である。
canonical rebaseは前二者をliteral stationaryへ正規化できるが、その再生edgeはcycle rank上進捗しない。
従って次の本質は、同じendpoint／crossing対を再利用しない履歴選択またはvisited量の構成である。

これは全射性の証明ではないが、未解決部分を明示的かつ機械検証可能な境界へ
押し込めた研究基盤である。
