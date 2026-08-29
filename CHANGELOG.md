# Changelog

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
- `PermanentAboveTail`、`PermanentAbovePotential`、`PermanentAboveHistory`、`PermanentAboveCanonical`、`PermanentAboveCycleRank`、`PermanentAboveCycleExit`、`PermanentAboveCycleRebase`、`PermanentAboveCorridor`、`PermanentAboveCorridorRank`、`PermanentAboveCorridorSuffix`と公理監査を追加

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
