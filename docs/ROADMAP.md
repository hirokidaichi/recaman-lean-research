# 証明ロードマップ

## 目標

最終目標は次をLeanで証明することである。

```lean
∀ m : Nat, ∃ t : Nat, a t = m
```

現時点では、大域帰納の器は完成している。残作業は局所探索のtotalityを示すことである。

## Milestone 1 — 対角負債の局所二分法

### 証明したいこと

`FirstAt a y fy`、`m≤y`、`fy<debtTime`を持つ負債ノードから、次のどれかを得る。

1. `m`の実出現
2. より早い初出時刻を持つ次の負債ノード
3. `anchorParent`未満の値を持つ通常ノード

### 調査順序

1. ~~初出時刻`fy`における最終遷移を加算／減算で完全分類する。~~
2. ~~合法減算なら直前値とその初出時刻を抽出する。~~
3. ~~強制加算なら、その減算候補の初出時刻を抽出する。~~
4. blocker値がanchor未満の場合を即時出口へ接続する。
5. blocker値がanchor以上の場合に初出時刻が厳密下降する条件を証明する。

最初の三項は`DebtInvariant`、`DebtSubtraction`、`DebtAddition`で形式化した。
合法減算では直前値の初出時刻が必ず下がる。強制加算では正の既出候補と
そのより早い初出時刻を抽出できる。一方、候補が目標以上またはanchor未満で
あることは強制加算だけからは従わず、追加のdebt不変条件または別の履歴予算
分岐が必要である。

後方極大延長を加えると、合法減算分岐は次まで縮約できる。減算尾が2段以上なら
目標以上のblockerと時刻下降を得る。1段だけなら`value+1<anchor`でnormalへ戻り、
残るのは`anchor=value+1`という鋭い等号境界だけである。

強制加算が目標を厳密にまたぐ場合、ランク上のanchor下降は得られるが、移動先の値が
目標未満なのでnormal探索の意味的不変条件を保存しない。またこの分岐は、目標方程式、
目標面、exact gate、履歴予算下降のいずれにも自動では接続しないことを証明した。
`debtStep_classify`は現時点の全分岐を、成功、normal退出、debt継続、明示的obstructionへ
完全分類する。

`anchor=value+1`境界は、landing値`value`自身を新しいnormal anchorにすることで
厳密下降へ接続できることが判明した。さらに強い`DebtInvariant`を満たす任意のnodeは、
その値自身へnormal退出できる。したがって局所debtの停止性ではなく、直前のglobal
normal nodeからrankを下げながらこの意味的不変条件を構成することが本質である。

strict crossing後のポテンシャルは常に目標未満であり、負領域またはundershootに入る。
crossing直後は対角由来の`target≤time+1`が偽になるが、時刻`target-1`または`target`まで
有限前進すればこの絶対時刻条件を必ず回復できる。相対gapだけでは絶対時刻条件を
導けない反例も形式化した。混合ケースはCoverageStepまたはanchor下降へ接続でき、
残る局所形はcatch-up値が元のdebt値とanchorの両方以上になる同時成長である。
このobstructionはtarget 5の実軌道で反復して実在し、catch-up時点のhorizon更新だけでは
自然なnormal childへ戻れない。ただしfrontierからanchor下降またはbudget下降を得る枝は
semantic childへ接続でき、残余でも元のstrong `DebtInvariant`が保持する値自身へのself-exitを
使える。したがって`crossingGrowthObstruction_phaseSemanticStep`でこの分岐は閉包済みである。

### 完了条件

- 負債ノードの全分岐が`PhaseSearchProgress`または目標出現になる。
- 新しい未証明仮説を定理の前提へ紛れ込ませない。
- 公理監査と禁止語走査に合格する。

## Milestone 2 — 負エポックから位相探索への統合

現在の`negative_epoch_historySearchOutcome`は`DiagonalSuccessorProperty`を仮定する。
これを位相負債への遷移で置き換える。

`negative_epoch_phaseSearchOutcome`により、`DiagonalSuccessorProperty`なしで負エポックの
全分岐が目標出現または`PhaseSearchProgress`を返すことを証明した。ただしdebt childの
意味的不変条件保存は別問題として残るため、これはrankレベルの統合完了である。

`NormalPhase`ではこの意味的不変条件を明示し、各rank childを分類した。その後、parent-dropは
初出anchorを弱いsemantic normal childとして採用することで閉じた。forward-exitの見かけ上の
rank同値枝も、目標以上から目標未満への横断が目標出現または履歴予算下降を必ず生むため
不可能である。q=1 debt例外も元normal値の目標下界と矛盾する。したがって
`negativeNormal_phaseSemanticStep`は負normal全分岐を追加仮定なしで閉じる。

### 完了条件

- `DiagonalSuccessorProperty`なしで負エポック全体が目標出現または
  `PhaseSearchProgress`を返す。
- 既存の三成分探索定理を壊さず、互換補題を保持する。

## Milestone 3 — 全域PhaseSearchOracle

canonical開始点については全符号と低levelを分類し、次のいずれかへの局所接続を完了した。

- 目標面
- 負エポック
- 非負アンダーシュート
- blocker parent下降
- 対角負債

特にlevel 1/2のquotient-one強制加算は、直後の値とanchorが増えるため即時rank下降ではない。
ただし二段目の減算候補が元のcanonical値より小さく、合法／blockedの両方でCoverageStepに
なるため、新しいphaseやrank成分を追加せず閉じた。公開結果は
`targetStartInvariant_phaseSemanticStep`である。

一方、現行のordinary `NormalSearchInvariant`は、証明書中の初出値が現在horizonの実値である
ことも、epoch適用に必要な`target≤horizon+1`も保証しない。この弱さは具体反例で証明済みで、
全constructorをそのままtotal oracleのdomainにすることはできない。current-state側は
`OrbitReadyNormalInvariant.phaseSemanticStep`により全符号・低levelを残余なしで閉じ、
さらに生成分岐を直接たどるrefined stepまで構成した。historical normal、ready debt、
crossing frontierもclock provenanceを保ったrefined resultへ接続済みである。

### 次の調査順序

1. ~~`OrbitReadyNormalCertificate`をcurrent-state normal constructorとして採用し、全符号stepを閉じる。~~
2. ~~parent-drop、coverage、frontierから生成されるhistorical normal childをprovenance別に監査する。~~
3. ~~parent-drop／coverage anchor／downcross restart／debt exit／crossing frontierのtyped constructorを実装する。~~
4. ~~history horizonとrepresentative orbit timeを分離し、直接輸送可能な条件と正確な残余を証明する。~~
5. ~~current親のCoverageStepをfuture current／earlier debtへ分解し、historical normalを回避する。~~
6. ~~budget-gap residualをdowncross／debt／crossing固有の次stepへ変換する。~~
7. ~~representative-time readinessを生成元から復元するか、early representative専用機構で閉じる。~~
8. ~~horizon-ready extended-history constructorのtotal semantic stepを証明する。~~
9. ~~orbit-ready局所定理の各生成分岐から、clock情報を失わないrefined childを直接返す。~~
10. ~~ready debt obstructionとcrossing frontierをrefined domain保存stepへ統合する。~~
11. crossing recoveryにhorizon readinessと元debtのpost-state provenanceを保持させる。
12. crossingから新しいbelow-target値を抽出してhistory budget下降へ接続する。
13. ~~budget不変ならcrossing-to-crossingの追加下降量があるか、現行rankで不可能かを監査する。~~
14. `CrossingSearchInvariant`自身のrefined局所stepを証明する。
15. 精密domain上のrestricted oracleを無条件に構成する。

step 6では、strict budget dropが新しいbelow-target実出現を与えることを逆向きに証明し、
そこからfuture upcrossingとcrossing recoveryを構成した。step 7のlegal downcrossと
forced below-candidateも同じ回復機構で閉じた。新しいphaseやrank成分は不要だった。

現在のrefined child domainはorbit-ready current、horizon-ready debt、extended-history normal、
crossing recoveryからなる。最初の三constructorは残余なしのrefined stepを持ち、canonical startから
restricted oracleを得るための残余は`CrossingSearchInvariant`自身だけになった。
現行crossing証明書は入口のstrict crossingを保持する一方、元のstrong debtが持っていた
post-addition値のfirst occurrence、post値と旧anchorの比較、horizon readinessを保持しない。
またcrossing nodeのanchorはtarget未満で、非crossing refined nodeのanchorはtarget以上なので、
非crossing successorへの進捗はhistory budgetの厳密下降を必ず伴う。同じhorizonならsuccessorは
crossingに留まるしかない。次は生成時provenanceの保持に加え、このbudget／crossing下降を構成する。

step 12のうち、保存crossing horizon以後にactual downcrossが存在する枝は閉じた。downcrossは
forced additionではあり得ず、legal subtractionの着地点は直前履歴にfreshなので、親horizonから
`missingBelowCount`が厳密に下がる。残るのは保存horizonですでにbelow-targetである枝と、以後の
軌道がdowncrossしない枝である。

horizon-below枝は次のweak upcrossingまで完全分類した。新しいcrossingは、
budget下降またはpre-crossing anchor下降があれば進捗する。どちらもない枝は
`CrossingContinuationGrowthResidual`で厳密に記録し、target 19、horizon 31、anchor
13→14で実在することをLeanで検証した。これによりstep 13の結論は「現行rankでは
一般に不可能」である。ただし残余のchild horizonは必ずat-or-above targetであり、
その後のdowncrossは中間crossingを迂回して元の親へ直接budget下降を与える。

したがってready crossing局所totalityの残りは`TargetTailReturnHypothesis`、すなわち
「目標が未出なら、任意のat-or-above開始点から将来below-targetへ戻る」へ縮約した。
`no_futureDowncross_iff_tail_atOrAbove`はその否定がpermanent above-target tailと同値であること、
`ReadyCrossingSearchInvariant.refinedStep_of_targetTailReturn`はこの長期仮説が局所stepに十分であることを示す。
仮想的な最小未出目標では、それ未満の値が有限horizonまでにすべて既出になるため、
fresh below endpointを要求するdowncrossは不可能である。`LeastMissingTarget.eventually_strictlyAbove`は
この場合に軌道が最終的に常にtargetより大きくなることを示す。
`all_targetTailReturn_iff_surjective`により、全targetのtail returnを証明することは全射性予想そのもと同値である。
したがってこれを「局所補題が残っただけ」と扱ってはならない。

permanent tailの内部解析は一段進んだ。`PermanentAboveTail`で次を証明済みである。

1. tailの各状態は高々二遷移で、元値より小さくtarget以上の`CoverageStep`を返す。
2. tail最小値では二遷移ともforced additionで、候補`a n - 1`の初出時刻はtail開始前にある。
3. below-target履歴予算は0で、仮想反例は将来downcrossを持たないready crossingを実際に生成する。
4. そのcrossingのrefined子は、存在するならbudget 0のcrossingに留まりanchorを厳密に下げる。

これによりstep 14は、任意のtail状態から一般的な局所解析を再実行する問題ではなく、
`PermanentTailMinimumCertificate`のhistorical predecessorを、zero-budget crossingのstrict anchor childへ
変換する問題へ縮まった。`PermanentAbovePotential`の実軌道二例により、二連続forced additionの
potentialは増減両方向なので、potential単独を第五rank成分にする案は棄却済みである。

この調査順序は`PermanentAboveHistory`で次まで完了した。

1. ~~final upcrossingとtail minimumの間にあるabove-target first-occurrence鎖を型付きで構成する。~~
2. ~~`a n - 1`の初出から次のdowncross／upcrossingを復元し、crossing predecessor anchorとの大小を比較する。~~
3. ~~anchor下降が得られない場合を`HistoricalCycleGrowthResidual`として固定する。~~
4. ~~no-downcross分岐のminimum value下降を強帰納で反復し、有限historical downcrossへ到達する。~~

得られたdowncross endpointはfreshでbudgetを厳密に下げる。続くupcrossingのanchorがcombined parentより
小さければrefined crossing子を構成できる。しかし親をそのupcrossing自身に選ぶとchild=parentとなる
stationary residualを仮想反例から常に構成できる。この後、canonical選択とcycle rankを次まで形式化した。

1. ~~earliest future weak upcrossingをcanonicalに選び、存在と一意性を証明する。~~
2. ~~earliest再選択が同時刻に戻るstationary条件を証明する。~~
3. ~~`seenBelowCount`をdual-history measureとして導入し、monotonicityとstrict dropを証明する。~~
4. ~~anchor／one-way phase／seen budget／minimumの四成分cycle rankとwell-foundednessを証明する。~~
5. ~~combined obstruction、renewed tail、historical downcrossをcycle rankのstrict stepへ接続する。~~
6. ~~dischargeからcrossingへのexitがstrict anchor dropと同値であることを証明する。~~

earliest規則はwitness ambiguityを除くがstationaryを除かない。新cycle rankはstationaryを不正なexitとして
正しく拒否し、historical内部をwell-foundedに閉じる。しかしanchor非減少residualからはcrossingへ戻れない。
このexitを`PermanentAboveCycleExit`で次まで精密化した。

1. ~~fresh downcross endpoint、canonical return、旧crossing時刻をtyped discharge証明書へ統合する。~~
2. ~~`(anchor, crossingTime)` cursorを外側に持つ五成分cycle rankとwell-foundednessを証明する。~~
3. ~~同anchorでもより早いreturn crossingならstrict cycle exitになることを証明する。~~
4. ~~非進捗をanchor growth／chronology mismatch／literal stationaryの三kernel residualへ分類する。~~
5. ~~旧crossingがendpoint以後なら、同anchor非進捗はliteral same timeに限ることを証明する。~~
6. ~~canonical returnを同じzero-budget horizonの親へrebaseし、tail/minimumを保存する。~~
7. ~~任意のrebaseがliteral stationary kernelを生み、cycle exit不能であるno-goを証明する。~~
8. ~~stationary endpointからfirst return predecessorまで全状態がbelow-targetであることを証明する。~~
9. ~~即時returnをexact valley equation、遅延returnをbudget drop／clock boundへ分類する。~~
10. ~~任意のcorridor内部stepに同じbudget drop／target-bounded clock分類を証明する。~~
11. ~~delayed corridorをinternal legal subtractionまたはall-forced runへ完全分類する。~~
12. ~~all-forced runで`returnTime < target`、gap上界、加算trace、値の厳密増加を証明する。~~
13. ~~`target - time`のwell-founded corridor cursorとstrict forward stepを証明する。~~
14. ~~later below suffixでも同じfirst returnがcanonicalであることを証明する。~~
15. ~~legal subtraction endpointへの移動をbudget下降とsuffix-distance下降へ接続する。~~
16. ~~suffixをreturn到達／later legal endpoint／all-forced suffixへ完全分類する。~~
17. ~~legal subtraction直後のforced upcrossがexact targetを打つ境界定理を証明する。~~
18. ~~target-missing下でlegal endpointがreturnへ着地できないことを証明する。~~
19. ~~post-legal terminal suffixをall-forced枝へ縮約する。~~
20. ~~terminal all-forced suffixのtraceをfinal forced upcrossまで延長する。~~
21. ~~strict crossing windowとtarget gap／overshootのreturn-clock上界を証明する。~~
22. ~~post-legal terminalを`TerminalAllForcedCrossingWindow`へtypedに縮約する。~~
23. ~~suffix cursorの強帰納で任意個のlegal endpoint後にall-forced terminalを抽出する。~~
24. ~~全dischargeをimmediate historical valley／finite crossing windowの二形へ型付き正規化する。~~
25. ~~terminal二形に共通するstrict crossing balanceとgap partitionを証明する。~~
26. ~~最終fresh endpointとcanonical returnを共通terminal interfaceに保持する。~~
27. ~~final forced additionを数値不足／historical blockerへ型付き分類する。~~
28. ~~数値枝でtarget<2(return+1)、履歴枝でfirstTime<returnを証明する。~~
29. ~~historical blockerをfinal fresh endpointの前後で完全分類する。~~
30. ~~freshより後のblockerからstrict missing-budget dropを証明する。~~
31. ~~terminal shape／forced reason／blocker positionをmaster residualへ統合する。~~
32. ~~strict budget progressを分離し、真のouter residualを四constructorへ限定する。~~
33. ~~finite clock bandをtarget-indexedな明示候補listへ変換する。~~
34. ~~候補数≤targetとlater-return well-founded rankを証明する。~~
35. ~~finite candidate枝を分離し、non-clock residualを三形へ限定する。~~

次の調査順序は次である。

1. immediate historical／finite outer blockerをouter cycleのseen/minimum rankへ接続する。
2. finite candidate再訪でlater returnを強制するselection provenanceを設計する。
3. terminal shapeから別のhistorical minimum／downcrossをcanonicalに選ぶ。
4. 使用済みreturn crossingを除外する有限visited setまたは最小未使用cursorを設計する。
5. terminal normalizationをcursor-refined outer cycleとrefined oracleへ統合する。

### 完了条件

```lean
∀ m, 0 < m → PhaseSearchOracle m
```

に相当する定理が、追加仮定なしで得られる。

## Milestone 4 — 有限初期領域

エポック定理の一部は`m≤n+1`を要求する。この条件に入るまでの初期領域を、
固定個数の具体例列挙ではなく、任意の可変目標について一様に処理する。

任意の正の`m`について、時刻`m-1`または`m`に`m≤a n`かつ`m≤n+1`を満たす
実状態が存在することを`exists_targetReady_state_of_pos`で証明した。この定理は
座標と現在値の初出証明も返す。このcanonical entryの全符号・低level分岐は、
目標出現またはsemantic rank下降へ接続済みである。残る作業は、返されたnormal childを
Milestone 3の精密domainで再帰的に扱うことである。

`PhaseSearchStart`ではcanonical normal node、その証明書、意味的domain上だけに量化する
`RestrictedPhaseSearchOracle`、およびdomainを保存する整礎帰納を構成した。これにより、
到達不能な数値tupleを含む全node oracleを要求せず、認証済み開始点から探索できる。

`PhaseSemantic`ではcanonical start、通常normal、強いdebt、crossing recoveryの四種を
一つのproof-carrying domainへ統合した。開始点のdomain所属、debtの自己normal退出、
anchor等号境界、strict crossingのdomain保存を証明し、このdomain上のoracleだけで
目標出現が従うことを示した。ただしordinary normal constructorは現在horizonとの整合性が
不足しているため、整礎帰納のdomainとしては精密化が必要である。

### 完了条件

- 任意の初期探索ノードからMilestone 3の適用領域へ進む。
- 有限計算に依存する場合も、Leanカーネルで検証可能な有限証明に限定する。

## Milestone 5 — 全射性定理

`PhaseSearchOracle`から既存のwell-founded inductionを適用し、全正整数の出現を得る。
`a_0=0`と合わせて最終定理を構成する。

## 並行して行う保守

- 一つの数学概念を一つの下位モジュールへ置く。
- 長い存在命題は、安定した段階で結果構造体へ整理する。
- 実験結果とLean定理を文書上でも分離する。
- 各エポックで`Audit.lean`を更新する。
- 大きなAPI変更は定理探索エポックと分離する。

## 主なリスク

| リスク | 意味 | 対応 |
|---|---|---|
| 時刻下降と値下降の循環 | 一方を下げる間に他方が無制限に増える | 位相とanchorを固定した辞書式ランクを使う |
| 局所CoverageStepの輸送不能 | 後続値が元の親値を超える | 履歴予算またはanchor下降へ変換する |
| 経験則への過適合 | 10億項で未観測でも一般には起こり得る | 実験は仮説選択に限定する |
| 定理型の肥大化 | 座標・履歴・初出証明が同時に必要 | 安定後に結果構造体へリファクタリングする |
