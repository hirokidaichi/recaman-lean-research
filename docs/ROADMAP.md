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
36. ~~positive historical blockerから初出直前のstrict missing/seen budget edgeを抽出する。~~
37. ~~blocker predecessor選択を既存tail-cycle rank下降へ接続する。~~
38. ~~blocker時刻をoriginal endpoint前後で分類し、後枝のforward budget下降を証明する。~~
39. ~~blocker first occurrenceのinitial枝を排除し、legal／forced生成遷移を完全分類する。~~
40. ~~legal生成のlarger predecessorとforced生成のtarget-bounded predecessor/clockを抽出する。~~
41. ~~below-target landingがordinary normal/debt invariantへ直結不能であることを証明する。~~

上記の旧調査順序はすべて完了した。predecessor adapter、crossing install、有限selection、canonical minimum、
exact replay解析を経て、finite terminal branch自体が算術的に不可能であることまで証明した。terminal outcomeは
target occurrence、strict history progress、semantic phase progress、installed master progressの四形に閉じ、
installed枝は次のdischargeも保持する。

現在の調査順序（Issue #60）は次である。

1. history cursor、`PhaseSearchNode`、`TailInstalledCycleSearchNode`を跨ぐglobal recursion predicateを定義する。
2. ~~installed successorとnext dischargeをmaster well-founded inductionの帰納仮定へ接続する。~~
3. history progress枝をhistory relation、semantic progress枝をlocal parent付きphase relationの帰納仮定へ接続する。
4. 三relation間の遷移に外側priorityを与えるか、proof-carrying sum state上の単一well-founded relationを構成する。
5. permanent-above tailの矛盾を導き、`CrossingRefinedStepHypothesis`の無条件化へ接続する。

項目2は七成分master rankの帰納仮定を経由せずに解決した。連続する二解析のmaster node
は内側cursor（blocker first time）が比較不能だが、installationが正確に輸送するのは
共有horizon budget・installed anchor gap・old crossing cursorの三成分だけである。
この三成分lexをdischarge-levelのiteration rankとすると、installed successorは
strictに下降するか、anchorとcursorがともに一致するexact replayになる。rankの整礎性で
反復constructorは消去され、terminal解析はmissing-target下でhistory edge・semantic
child・exact replay固定点の三形interfaceへ無条件に閉じた。

replay固定点自体も固定した。return crossingはold crossingと一致する閉cycleで、
installed nodeはparentそのもの、successorは同parent同cursorへのself-mapである。
全cursorはtarget未満のbelow corridor帯に収まり、kernel計算でcrossing clockは6以上・
targetは8以上、上側は`target ≤ upperTri (clock+1)`で挟まれる。従って項目5の矛盾は、
この有限帯self-recurrent cycleを破る新しい大域情報（tail内部の無限構造からの新event列、
または歴史の別canonical選択）の構成に縮約された。項目3の残余はhistory/semantic枝の
continuationのみである。

数値側では`ReplayPrefixSuccessorCoverage`を追加し、larger-prefix値のsuccessor既出性と
later low witnessを一つのinterval floor条件へまとめた。clock 112はminimum=371、
predecessor初出108、downcross 109、`152 < target ≤ 261`へpin済みである。次の優先課題は、
深い実軌道等式を追加公理なしで圧縮検証するtrace certificate、またはこの完全pin cycleから
record excursion／blocker loadの矛盾を抽出することである。

項目3のhistory枝continuationはその後完了した。missing-count dropの不等式単独から
window内のbelow-target fresh landingを逆算でき、反例のbelow coverageと初出最小性が
これをparent history内へ束縛する。landingはready crossing nodeとしてsemantic domainへ
搭載され、combined certificateごとmounted nodeへtransportして解析を再入できる。
この再入反復もanchor gapの強帰納で整礎に閉じ、permanent-tail解析全体の終端は
semantic phase child・exact discharge replay・node不動landing固定点の三形になった。
二固定点は共通核`TailFixedPointCore`（anchor同値・target跨ぎforced addition・
parent node再生産）を持ち、最終統合定理はsemanticまたはprovenance付き固定点の二形である。

固定点のkernel floorはclock 17まで拡張された。唯一の例外は初出が時刻99734と深い値19で、
`18 ≤ clock ∨ target = 19`かつ無条件に`19 ≤ target`が成立する。次の壁は61
（初出t=181653）である。数値走査実験によれば、軌道10¹⁰項でも5,640個の候補対が生存し、
自帯域を時刻200以内に被覆できるclockは17ただ一つなので、kernel decideによる全域的な
floor引き上げは戦略として成立しない。従って残る調査順序は次に更新される。

1. 固定点core（parent node再生産のcanonical crossing）を破る非計算的な大域論法を
   構成する。候補は、tail内部（tailStart以後）の無限構造から取り出す新event列、
   遅い初出値（19、61、…）の遅延性を特徴付ける数論的構造、または歴史の別canonical
   minimum／downcross選択である。**この方向は部分的に実現した**：既出値の遅い再訪
   不可能性（`a_succ_ne_of_seen`）とtail最小値の強制再訪の矛盾により、target 19の
   replayは深い初出の検証なしに完全排除された。次はこの排除機構の一般化である。
   minimum predecessor `f`の直後が「減算→加算」なら`a (f+2) = a f + 1`がtail最小値
   `v`の早期出現になり、同じ矛盾が出る。残る形は`f`直後の遷移が異なるケースの分類
   である。**61も同機構で排除済み**であり、床は無条件に`32 ≤ clock`・`34 ≤ target`と
   なった。clockごとの床引き上げは次の三種の機械的道具で進められる：
   (i) record排除 — replay crossingは軌道running maximumを更新できない
   （`crossingTime_not_record`）ため、櫛の上歯型clockは帯検証なしで消える；
   (ii) downcross候補の有限化 — `target ≤ a downTime`かつ`downTime < clock`なので
   prefix最大値がtarget未満のclockは消え、残るclockでもdownTime候補は少数；
   (iii) 再訪不可能性 — minimum predecessor候補の後続値`a f + 1`が検証済みprefixで
   既出なら排除（`a_succ_ne_of_seen`）。これらの反復適用はサブエージェント向きの
   機械的作業である。
2. semantic progress枝のchildを外側restricted oracle再帰のdomainへ接続し、
   ready crossing局所stepの残余を`TargetTailReturnHypothesis`の証明義務として
   単一定理へ統合する（Issue #60 項目1・4）。

その後、history枝のcontinuationは完了し、解析は頂点定理まで合成された。
`LeastMissingTarget.semantic_or_flooredCore`により、最小未出目標はsemantic phase
childを渡すか、床付き固定点core（`18 ≤ clock ∨ target = 19`かつ`19 ≤ target`）で
終端する。19未満の全値の出現はkernel検証済みなので`LeastMissingTarget 19`は
「19が未出」と同値であり、床を守る最初の未検証instanceは`a 99734 = 19`という
一つの軌道値に確定した（次は`a 181653 = 61`）。

この二値はkernel `decide`の射程（時刻数百）を大きく超える。有望な次の手法は
**軌道区間の閉形式による圧縮検証**である。Recamánの軌道は櫛状区間で
`a (s+2k) = a s - k`、`a (s+2k+1) = a s + s + 1 + k`型の交互パターンに従う。
加算stepの正当性（減算候補の既出性）は直前2 stepの値でwitnessできるが、
減算stepのfreshnessは大域条件であり、区間`[0, t]`の値集合の表現定理
（低レール・高レールの区間和としての特徴付け）が必要になる。この表現定理を
帰納で与えられれば、`a 99734 = 19`は数百区間の合成でkernel検証可能になり、
固定点の床は20以上（次いで61の処理で62以上）へ進む。これは全射性の一般解決では
ないが、床の引き上げと反例構造のさらなる狭窄に直結する。

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

## 予想の真偽二仮説と投資方針

本プログラムの位置づけは、予想の真偽どちらの仮説の下でも変わらないが、期待すべき結末は変わる。

- **予想が真の場合**：仮想反例の構造を締め上げて矛盾へ至る現在の方法は正攻法である。
  ただし固定点の排除だけでは`TargetTailReturnHypothesis`は無条件化しない。統合outcomeの
  semantic枝は`stepParent`が自由変数のため無条件に居住可能であり（`semantic_or_flooredCore_of_pos`）、
  固定点枝を潰しても矛盾は生じないからである。全射性へ到達するには、(i) semantic枝の`stepParent`を
  外側再帰の現parentへ束縛する主張型の再設計、(ii) `CrossingRefinedStepHypothesis`の素の
  `CrossingSearchInvariant`をready化する橋、の二つが追加で必要である。
- **予想が偽の場合**：矛盾は永遠に導けず、固定点として記述している構造は実在する反例の
  忠実な記述である。この場合、証明済みの床（`112 ≤ clock`・`114 ≤ target`）や構造定理は
  「実際の最小未出値が満たす検証済み性質」という真の定理群として残る。

外部報告によれば852655が10²³⁰項を超えても未出とされる（本リポジトリでの独立検算は3×10⁶項までで、
それ以上の規模は検証していない）。偽仮説は真剣に考慮すべきである。従って
「いつかFalseが出る」ことだけを目標に床上げへ投資し続けることは避ける。床上げは1ラウンド
ごとに成功するが、深部残留値は後退しても消えないため、漸近的には定理へ近づかない。
今後の床上げは「一般排除機構のストレステスト」と位置づけ、エージェント作業として
上限付きで行う。主資源は次の優先順位に投じる。

1. **semantic枝のpayloadを捏造不能な形へ強化する（最優先）。** 頂点定理のsemantic disjunctは
   現在`0 < target`だけから導出でき、情報を持たない（`semantic_or_flooredCore_of_pos`）。
   `stepParent`の存在量化とlex順だけのprogressが原因である。加法的な精密outcome型を新設し、
   生成元が既に持っているrefined情報（`PermanentAboveCorridorTerminalSuccessor`の`below_master`・
   `phase_exit`枝など）を拾い直す。固定点を全て排除してもこれ無しには大域組み立ては閉じない。
2. landing固定点へ再訪排除を移植する。dischargeの`downTime ≤ clock - 1`に相当する
   predecessor初出の上界をlanding側で見つけるか、存在しないことを確定する。
   「二連減算」枝がfresh landingを生成する事実は、二つの固定点の接続を示唆する。
3. `CrossingRecoveryInvariant`に`target ≤ horizon + 1`を持たせ、unready crossing漏れを閉じる
   （Milestone 3 step 11の未完部分）。これが閉じれば大域残余は`ReadyCrossingRefinedStepHypothesis`
   一本になる。
4. witnessed dichotomyの「二連減算」枝を調べる。「即時加算」枝の下降連鎖は一段で停止するno-goが
   確定済みであり（`ReplayWitnessDescent`）、clock非依存な一般排除の望みはもう一方の枝にしかない。
   clock 112ではこの二分法を具体化し、109・110の二連合法減算へ固定した。さらにtail minimum clock
   `m`を`FirstAt a 371 m`、`371 < m`、`a (m-1) = m + 371`を満たす一意な初出clockへ縮約した
   （`PermanentAboveClock112Obstruction`）。局所構造だけでは矛盾せず、残る自由度は371の大域初出である。
5. comb圧縮検証でkernel射程をt≈5000へ延長し、深部値371の壁を試す（**縮小方針**。下記の天井の
   測定により、この路線への追加投資は正当化されない。既着手分の整理までに留める）。
   `ChunkedTraceCertificate`で認証bitmap、branch理由、checkpoint合成、既存`State`へのsoundnessを
   kernel内に実装した。15-step例は通常`decide`で通るが、step単位certificateの1024-step入力は
   130秒超で、深部検証には不十分だった。次はcomb区間を一理由で検証するsublinear certificateが必要である。

## 床上げ機構の構造的天井（2026-08-29 測定）

床上げが「漸近的に定理へ近づかない」ことは以前から記録していたが、数値実験
（`experiments/coverage-limit-2026-08-29/`）により、**それ以前に有限の天井がある**ことが判明した。

`ReplayPrefixSuccessorCoverage`のcutoffは時刻と値の両方の上界なので最小witnessは初出時刻であり、
`Need(clock) = max { max(v+1, first[v+1]) : v = a t, t < clock, v > a clock }`とおけば
`coverage(clock, cutoff) ⟺ Need(clock) ≤ cutoff`となる。`Need`はcutoff非依存なので全cutoffの答えが
一度に出る。この再定式化で得た換算は次の通りである。

| kernel射程 | clock床 | 次の障害clock | 障害successor |
|---:|---:|---:|---:|
| 4,825 | 192 | 193 | 834 |
| 56,515 | 776 | 777 | 879 |
| 328,002 | 4,581 | 4,582 | 14,491 |
| 18,394,609 | 24,260 | 24,261 | 82,547 |
| 2,789,105,306 | 53,905 | 53,906 | 167,477 |
| > 5×10¹⁰ | 53,905（未解決） | 53,906 | 167,477は5×10¹⁰まで未出 |

平均的には`射程 ≈ 0.049 · 床^2.01`だが、フロンティア付近の局所指数は6.29まで悪化し、最後は射程を18倍に
しても1 clockも進まない。**clock ≈ 5.4×10⁴が機構の天井である。** 理由は構造的で、初出深度比の裾が
極端に重い（値の約0.6%が実用地平線の外に初出を持つ）一方、anchorより上のprefix値の個数が`k ≈ 0.17·C`と
clockに比例して増えるため、clockが大きいほど「深すぎる後続」を掴む確率が1に近づく。射程無限大でも
clock 10⁶までの65%はcoverageでは消せない。

投資判断としては次を確定とする。

- **深部軌道値のkernel検証（射程延長・圧縮証明書）への追加投資は行わない。** clock 112の障害
  `a 4825 = 371`を検証しても床は192までしか上がらず、その先の階段は急速に不可能になる。
  その後`BalancedTraceCertificate`により`a 4825 = 371`自体は追加公理なしで検証済みとなった。
  ただし既存のformal floor theoremが必要とする後続low witnessはまだkernel検証されておらず、証明済みの
  replay floorは112のままである。4824-prefixの未出bitから`FirstAt a 371 4825`、clock 112 replayから
  `target = 223`とhistorical minimum clock 4825までは無条件に固定済みであり、残余は4825以後のlow witness
  一件に縮約された。圧縮checkerの成立とfloor引き上げを混同しない。
- **床上げは「一般排除機構のストレステスト」としての価値のみ**に限定する。これは以前からの方針だが、
  今回その上限が定量化された。
- 主資源は上記優先順位1〜4、すなわち**大域組み立ての構造的欠陥の修復**と**clock非依存の一般排除**へ
  投じる。特に「pre-tail領域に下界を持つ証明書フィールドの新設」（`ReplayDoubleSubtractDescent`が
  同定した構造的欠落）は、coverageに依存しない唯一の排除路線である。

これらの数値結果は仮説選択と投資判断のためのものであり、Lean証明には一切使用していない。

## 三度確認された壁：`tailStart`の上界が存在しない

pre-tail領域の計数路線（`coveredBelowCount`）は三ラウンド連続で同じ壁に当たった。計数が与えるのは常に
「`tailStart`は十分大きい」方向の**下界**である。無条件の`target < tailStart`はその成果だが、矛盾を出すには
`tailStart`の**上界**が要る。ところが証明書側の上界は`tailStart ≤ start < parent.horizon`だけで、
`parent.horizon`は無制限である。

同じ壁は三つの異なる文脈で現れた。

1. 二連減算枝の排除（`ReplayDoubleSubtractDescent`）：証明書が軌道に下界を課すのはtail開始以降だけ。
2. pre-tail budget（`PreTailBudgetSeparation`）：fresh初出3連発が食うのは3レベルだけで`target + 1`の桁に対し無視できる。
3. 無条件`FirstAt a (a m) m`の残余枝（`PinnedForwardOrbit`）：残余枝は強制加算により`a m ≥ m`を要求し、
   これは遅延再出現による消去が必要とする`a m < m`のちょうど逆である。残余枝は消去の道具が働く条件を
   構造的に打ち消している。

したがって**次エポックの最優先候補の一つは`tailStart`（または`parent.horizon`）の上界機構の新設**である。
`old_crossing_before_horizon`と`tail_strictly_before_horizon`を経由して`parent.horizon`をcrossing側の量で
挟み込めるかが、計数路線を生かす唯一の道である。これが立たない限り、pre-tail領域の計数は下界を出す道具に
とどまる。

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
| 床上げの無限反復 | 1ラウンドごとに成功するが漸近的に定理へ近づかない | 一般機構の検証と割り切り上限を設ける |
| 予想が偽である可能性 | 矛盾導出は原理的に不可能になる | 構造定理・床として残る形で定理を設計する |
| 定理型の肥大化 | 座標・履歴・初出証明が同時に必要 | 安定後に結果構造体へリファクタリングする |
