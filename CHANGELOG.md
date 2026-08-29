# Changelog

## Landing recursion and fixed point floors — 2026-08-29

- history edgeのfresh landingにhorizon境界（landing<start、crossing+1≤start<horizon）を事後導出
- 境界付きlandingをready crossing nodeとしてsemantic domainへ搭載
- combined certificateをmounted nodeへtransportし、terminal解析をlanding枝から再入可能化
- landing再入反復をanchor gap強帰納で整礎閉包し、残余をnode不動landing固定点へ縮約
- 二固定点の共通核`TailFixedPointCore`と最終統合定理`unifiedOutcome`を構成
- 統合coreにblocker不要のkernel floor（clock≥6・target≤upperTri包絡）を証明
- replay floorをclock 17まで拡張：例外は深い遅延値19のみ、`18≤clock∨target=19`と無条件`target≥19`
- replay固定点候補の数値走査実験を追加：10¹⁰項でも5,640対が生存、decide全域排除戦略の不成立を定量確認
- 固定点coreの形状API（parent一意決定・同値crossing・異clock同値再帰）を追加
- first upcrossing一般all-below補題で両固定点のbelow corridorを統一
- 統合coreの床もclock 18・target 19へ拡張し、両固定点の床を完全一致
- 最小未出目標からの頂点定理：semantic childまたは床付き固定点core
- `LeastMissingTarget 19 ↔ 19未出`を形式化し、最初の未検証instanceを一値へ確定
- replay床をclock 32へ拡張し、targetを`19∨61∨34以上`へ三分（例外リスト{19,61}、次の壁76）
- comb run閉形式・witness構成・値集合表現・freshness輸送を証明し、圧縮軌道検証の機構を整備
- target 19のreplayをclock 8の唯一cycle（downcross 7→即時return 8・anchor 12・blocker 3初出2）へ完全特定
- 19-反例のtail最小値を21へ固定し、tailStart>131・horizon>132で固定歴史と未知tailへ二分
- 19未出⟹21の遅い再訪、という将来イベント強制を証明
- 既出値の遅い再訪不可能性（一般力学補題`a_succ_ne_of_seen`）でtarget 19のreplayを完全排除
- 無条件`18 ≤ clock`・`32 ≤ clock ∨ target = 61`・`20 ≤ target`へ床を更新
- 同機構でtarget 61のreplayも完全排除（59分岐の全消去）、無条件`32 ≤ clock`・`34 ≤ target`へ確定
- 排除機構を一般テンプレート化し、生存replayのpredecessor直後を即add／二連subへ制限
- replay crossingのrecord性排除を証明し、三種道具の反復で床を無条件`112 ≤ clock`・`114 ≤ target`へ拡張
- `PermanentAboveCorridorLandingHorizon`、`PermanentAboveCorridorLandingMount`、`PermanentAboveCorridorLandingInstall`、`PermanentAboveCorridorMountedIteration`、`PermanentAboveCorridorFixedPointCore`、`PermanentAboveCorridorFixedPointFloor`、`PermanentAboveCorridorReplayFloorTwo`、`PermanentAboveCorridorFixedPointShape`、`PermanentAboveCorridorFixedPointCorridor`、`PermanentAboveCorridorFixedPointFloorTwo`、`PermanentAboveCorridorLeastMissingSummit`、`PermanentAboveCorridorNineteenBoundary`、`PermanentAboveCorridorReplayFloorThree`、`OrbitComb`、`OrbitCombWitness`、`OrbitCombValues`、`PermanentAboveCorridorNineteenReplay`、`PermanentAboveCorridorNineteenUnique`、`PermanentAboveCorridorNineteenMinimum`、`PermanentAboveCorridorNineteenTail`、`PermanentAboveCorridorNineteenRevisit`、`PermanentAboveCorridorNineteenElimination`、`PermanentAboveCorridorSixtyoneElimination`、`PermanentAboveCorridorMinimumShape`、`PermanentAboveCorridorMinimumFollowUp`、`PermanentAboveCorridorCrossingRecord`、`PermanentAboveCorridorReplayFloorFour`と公理監査を追加

## Successor iteration and replay fixed point — 2026-08-29

- installationが輸送する三成分（horizon budget・anchor gap・old crossing cursor）をdischarge-level iteration rankとして定義
- installed successorをrankのstrict下降またはexact replay固定点へ完全分類
- 三成分lexの整礎性でiteration constructorを再帰消去し、terminal解析を四形へ無条件閉包
- replayで`returnTime = oldCrossingTime = crossingTime`の閉cycleを証明
- ready crossing nodeの形状一意性からinstalled node=parentのnode-level固定点を証明
- successor dischargeを同parent・同cursorへtransportするself-map化を証明
- 固定点の全cursorをtarget未満のbelow corridor帯へ有限化
- 実軌道step検証でclock 3/4/5を排除し、clock≥6・target≥8・target≤upperTri(clock+1)の挟撃を証明
- missing-target下のterminal interfaceをhistory edge／semantic child／replay固定点の三形へ確定
- replay cycleのdischargeごとの一意性を証明
- `PermanentAboveCorridorSuccessorRank`、`PermanentAboveCorridorIterationClosure`、`PermanentAboveCorridorReplayPinning`、`PermanentAboveCorridorReplayCorridor`、`PermanentAboveCorridorReplayFloor`、`PermanentAboveCorridorReplayInterface`と公理監査を追加

## Permanent-tail analysis — 2026-08-29

- strictly-above tailの各状態から高々二遷移で`CoverageStep`を抽出
- below-target履歴被覆から`missingBelowCount = 0`を証明
- 仮想反例からzero-budget・no-future-downcrossのready crossingを構成
- zero-budget crossingのrefined子がcrossingに留まりanchorを厳密下降するrank境界を証明
- 自然数値tailの最小値存在と、直下値のtail以前historical blockerを証明
- tail最小値で二連続forced additionが起きることを証明
- 二連続forced addition上でpotentialが増減両方向に動く実軌道例をkernel検証
- historical predecessorのdowncross／renewed-tail二分法を証明
- renewed-tail minimum下降の強帰納でfinite historical downcrossとstrict budget dropを抽出
- historical downcross後のupcrossingをanchor-drop childまたはgrowth residualへ分類
- 任意crossing選択ではchild=parentのstationary residualが必ず構成可能というno-goを証明
- first future weak upcrossingの存在・一意性を強帰納で証明
- dual-history量`seenBelowCount`とphase／seen／minimum rankを構成
- anchor／one-way cycle phase／seen／minimumの四成分well-founded rankを構成
- dischargeからcrossingへのrank exitがstrict anchor dropと同値であることを証明
- growth residualを新cycle rankのtyped exit obstructionへ接続
- historical downcross／canonical return／旧crossingをtyped discharge証明書へ統合
- `(anchor, crossingTime)` cursorと五成分well-founded cycle rankを構成
- 非進捗をanchor growth／chronology mismatch／literal stationaryの三kernel residualへ完全分類
- canonical return rebaseがtail／horizon／minimumを保存することを証明
- 任意のrebaseがliteral stationary coreとcycle exit不能を生むno-goを証明
- canonical downcross endpointからfirst returnまでのbelow corridorを証明
- 即時corridorのexact valley equationと、全内部stepのbudget drop／target-bounded clock分類を証明
- delayed corridorをinternal subtractionまたはall-forced有限runへ完全分類
- all-forced runのreturn/gap上界、加算trace、strict growth、remaining-clock rankを証明
- first returnのlater below suffix安定性を証明
- legal endpoint移動をhistory-budgetとreturn-distanceの同時下降へ接続し、suffixを完全分類
- legal subtraction直後のforced upcrossがexact targetを打つことを証明
- target-missing下でlegal endpointのreturn着地を排除し、post-legal terminalをall-forcedへ縮約
- all-forced suffixのtraceをfinal return upcrossまで延長
- terminal residualをstrict crossing、target gap／overshoot上界付き有限windowへ縮約
- suffix cursorの強帰納で任意個のlegal endpoint後のall-forced terminal存在を証明
- 全dischargeをimmediate historical valleyまたはfinite crossing windowの二形へ型付き正規化
- terminal二形に共通するgap＋overshoot＝final clockと両差のclock上界を証明
- final fresh endpoint／canonical return／strict balanceの共通interfaceを構成
- final forced additionをdouble-clock数値境界またはstrictly earlier historical blockerへ分類
- historical blockerがfreshより後ならstrict history-budget drop、以前ならouter historyとなる位置分類を証明
- immediate valleyではblockerが必ずfresh endpointより前になることを証明
- terminal解析をmaster residualへ統合し、strict budget progressを除くouter residualを四形へ限定
- finite insufficient枝を`return < target < 2*(return+1)`のclock bandへ縮約
- finite clock bandを長さtarget以下の明示return候補listへ変換
- later candidateで`target-return`が厳密下降するwell-founded rankを構成
- finite candidate枝を除くnon-clock outer residualを三形へ限定
- positive historical blockerの初出直前でstrict missing-drop／seen-gainを証明
- blocker predecessor選択を既存tail-cycle backtrack rank下降へ接続
- blockerをoriginal endpoint以前またはforward budget progressへ分類
- blocker first occurrenceのinitial枝を排除しlegal／forced生成遷移を完全分類
- legal枝のlarger predecessor provenanceとforced枝のtarget-bounded predecessor/clockを抽出
- below-target blocker landingがordinary normal/debt invariantへ直結不能であるno-goを証明
- `PermanentAboveTail`、`PermanentAbovePotential`、`PermanentAboveHistory`、`PermanentAboveCanonical`、`PermanentAboveCycleRank`、`PermanentAboveCycleExit`、`PermanentAboveCycleRebase`、`PermanentAboveCorridor`、`PermanentAboveCorridorRank`、`PermanentAboveCorridorSuffix`、`PermanentAboveCorridorBoundary`、`PermanentAboveCorridorWindow`、`PermanentAboveCorridorTerminal`、`PermanentAboveCorridorBalance`、`PermanentAboveCorridorBlocker`、`PermanentAboveCorridorBlockerPosition`、`PermanentAboveCorridorResidual`、`PermanentAboveCorridorCandidates`、`PermanentAboveCorridorOuterHistory`、`PermanentAboveCorridorBlockerGeneration`と公理監査を追加

## Research baseline — 2026-08-28

- Lean 4.33.1で再現可能な研究リポジトリとして整理
- 座標力学、借用遷移、実軌道上界を形式化
- 実軌道上の多段借りを排除
- 負領域と非負アンダーシュートの有限化
- CoverageStepと履歴探索ランクを構成
- 対角状態の極大後方減算鎖と早期blockerを抽出
- 通常／対角負債の四成分well-foundedランクを構成
- debt crossingと負normal分岐を意味的探索domain内で閉包
- canonical開始点の全符号・低level分岐をsemantic rankへ接続
- quotient-one forced growthを二段先のCoverageStepで回収
- ordinary normal証明書のhorizon不整合境界とorbit-ready代替を形式化
- orbit-ready current normalの全符号・低level局所totalityを証明
- current／historicalを分離するnormal provenance APIと生成箇所監査を追加
- extended-history normalの直接輸送条件と二つの独立残余を形式化
- historical normalの5種類のtyped provenanceとcurrent生成adapterを追加
- current親のCoverage blockerをfuture current／earlier debtへ完全分解
- generic extended-history normalのearly／budget-gap残余をcrossing recoveryで完全閉包
- downcross restartのmechanism-specific total semantic stepを証明
- parent-dropをfuture current／earlier debtへ分解し、debt self-exitを局所戦略から除去
- horizon-ready debtとready current/debt refined domainを追加
- orbit-ready semantic childのrefinement境界をnormal/debt horizon readinessへ限定
- orbit-ready normalの全生成分岐をdirect refined stepへ閉包
- ready debt obstructionとcrossing frontier middle residualをrefined domainへ閉包
- extended-history normalのdirect refined totalityを証明
- refined restricted oracleの残余をcrossing-local stepひとつへ縮約
- crossingから非crossing refined childへの進捗がstrict budget dropを要求するrank境界を証明
- ready crossingの保存horizon以後のfuture downcrossをbudget下降でrefined childへ閉包
- horizon-below ready crossingを次のcrossing進捗またはstable-budget/anchor-growth残余へ完全分類
- target 19の実軌道上にcrossing continuation growth残余が実在することをLeanで検証
- no-future-downcrossをpermanent above-target tailと同値化し、tail-return仮説からready crossing局所totalityを証明
- 研究レポート、証明地図、ロードマップ、再現手順を追加

全射性そのものは未証明である。
