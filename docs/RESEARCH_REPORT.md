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
ためCoverageStepへ回収できる。さらにcurrent normalとhorizon-ready extended-history normalの
局所totalityを証明し、early／budget-gap残余もcrossing recoveryで解消した。残る中心課題は、
各局所分岐が持つclock provenanceをrefined domainへ直接伝搬し、全域オラクルへ接続することである。

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
`ExtendedHistoryNormalInvariant`は残余なしの局所stepを持つ。current nodeの全局所分岐、current生成
8系統のadapter、5種類のtyped provenance、ready debtの通常継続も構成済みである。

現在の未証明部分は、これらを精密domain上のtotal oracleへ統合する際のproof data伝搬である。
refined child domainは次を含む。

- orbit-ready current normal
- horizon-ready strong debt
- extended-history normal
- crossing recovery

既存のblack-box `OrbitReadyNormalInvariant.phaseSemanticStep`はchildをbroad
`PhaseSemanticInvariant`として返す。この結果を事後にconstructor検査すると、normal/debt childの
`target≤horizon+1`だけが復元できない。broad normalにはこのclock条件がない実例があるが、それが
orbit-ready stepから到達する反例ではない。したがって次に必要なのは、局所定理の各生成分岐から
clock provenanceを消さずrefined resultを直接構成し、ready debt obstruction／crossing frontierと
合わせてrestricted oracleへ接続することである。

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

## 8. 結論

本形式化により、座標上の未定義領域、多段借り、負領域の無限滞留、
非負アンダーシュートの無限滞留、対角状態の後方履歴、crossing、canonical開始点の
全局所分岐は既存の意味的ランクへ接続され、current normalとhorizon-ready historical normalは
局所totalityまで完成した。研究上の残余は、局所分岐が既に持つchild horizonのclock条件を
broad semantic interfaceで失わず、refined domain上のtotal局所オラクルへ統合することに集中している。

これは全射性の証明ではないが、未解決部分を明示的かつ機械検証可能な境界へ
押し込めた研究基盤である。
