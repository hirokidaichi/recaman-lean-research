# CrossingFrontier

**役割:** catch-up 点の符号情報と後のエポック frontier を分離し、frontier で得た初出値を horizon 拡張つきの意味的 normal 子へ変換、残余の場合も strong debt 証明書の self-exit で crossing-growth 分岐の意味的一段を無条件に完成する。

## このモジュールの役割

`CrossingIteration` までで、joint-growth crossing(値と anchor が同時に成長する残余)の frontier には旧 anchor を下回らない residual が残ることが分かった。本モジュールはこの分岐を現行の意味的探索 domain(`PhaseSemanticInvariant`)の中で完全に閉じる。鍵は二つある。第一に、frontier で学んだ初出は拡大した子 horizon(`max horizon firstTime`)に保存し、決して旧 horizon 越しに読まないこと。第二に、frontier 由来の子が取れない正確な residual の場合でも、元の strong debt 証明書(`DebtInvariant`)自身が horizon-safe な self-exit(自分の値を anchor とする normal 子)を常に供給すること。この二つを組み合わせ、「目標出現または意味的ランク子」という無条件の結論に到達する。

## 主要な定義

### `CrossingFrontierResidual` (L114)

frontier の初出が旧 debt anchor を下げられないときに残る状況の帰納命題。

- `negative`: catch-up 以後の負ポテンシャル点で、その normal 化が失敗する理由の二択(`a u < target` で値が normal 探索の資格を欠くか、`anchor ≤ a u` で anchor が下がらないか)を明示的に記録する。
- `coverage`: frontier の `CoverageStep` blocker 値で、`target ≤ value`・初出・frontier 値未満まで揃っているのに `anchor ≤ value` である場合。blocker を `CoverageStep` の中に隠さず露出させる。

## 定理と証明

### `crossingCatchup_quotient_pos` (L14)

**主張:** target-ready な catch-up 点の商は正である。

**証明:** `q = 0` なら座標式から `a t = r < t` だが、catch-up の時刻条件では `t ≤ target ≤ a t` なので矛盾する(`t = target − 1`、`t = target` のどちらの場合も同じ計算)。

### `crossingCatchup_potential_trichotomy` (L38)

**主張:** catch-up 点における正確な局所符号分割: `potential q r < 0`、または `0 ≤ potential q r < target`(undershoot 帯)、または `CoverageStep target (a t) t` が成り立つ。

**証明:** `target = 0` なら `a 0 = 0` が即座に出現証人になる。`target > 0` とし、ポテンシャルの符号で分ける。負なら第一分岐。非負で `target ≤ potential` の above-target 半空間にある場合、`t > 0`(さもなくば `a 0 = 0 ≥ target` に矛盾)と正の商(前定理)と時刻条件から、`CrossingGap` の定理 `positiveQuotient_potential_aboveTarget_gives_coverageStep` により被覆が定理として従う。残るは undershoot 帯である。すなわち被覆にならない符号領域は負領域と非負 undershoot 帯にちょうど限られる。

### `CrossingGrowthObstructionAt.frontier_cases` (L70)

**主張:** joint-growth 障害が保持するエポック frontier の連言標準形: 即時 `CoverageStep`、後の負ポテンシャル点、または後の局所 `CoverageStep` の三択である。

**証明:** frontier の入れ子になった選言を並べ替えるだけの整理補題である。三分律の undershoot 分岐は、有限 undershoot 定理がこの結果を生む前に処理する当のケースに対応する。

### `phaseSearch_exitDebt_of_extendedHorizonAndAnchor` (L90)

**主張:** 履歴 horizon を拡張しつつ(`parentHorizon ≤ childHorizon`)anchor を厳密に下げる(`childAnchor < parentAnchor`)ことは、debt からの正当な脱出であり `PhaseSearchProgress` を与える。

**証明:** 履歴予算 `missingBelowCount` は horizon について単調非増加なので、子の予算は親と等しいか真に小さい。真に小さければ辞書式順序の第一成分で進捗する。等しければ第二成分の anchor 降下で進捗する。これは固定 horizon の脱出定理 `phaseSearch_exitDebt_of_anchorDrop` の horizon-safe 版である。

### `frontierFirstAt_phaseSemantic` (L136)

**主張:** frontier で得た初出値 `value`(`0 < target ≤ value`、`FirstAt a value firstTime`、`value < anchor`)は、節点 `⟨max horizon firstTime, value, normal, value⟩` を子として、`PhaseSemanticInvariant` と旧 debt 節点への `PhaseSearchProgress` を同時に満たす。

**証明:** 意味的資格は normal 構成子と `firstAt_normalSearchInvariant` による: 初出時刻は `max horizon firstTime` 以下なので、この子の horizon で初出を正当に読める。進捗は前定理を `max` の両不等式(`horizon ≤ max`、anchor 降下)に適用する。子 horizon を `max horizon firstTime` に取ることが本質的で、証明書は horizon より後の出現を旧 horizon で読むことが決してない — これは `CrossingHorizon` で監査した「horizon の前進は実履歴経由でのみ正当」という規律の実装である。

### `crossingGrowthObstructionAt_frontier_phaseOutcome` (L159)

**主張:** 旧 debt 親に対する強い frontier 分類: `0 < target` のとき、joint-growth 障害から (i) 目標の出現証人、(ii) `PhaseSemanticInvariant` と `PhaseSearchProgress` を併せ持つ子、(iii) `CrossingFrontierResidual` のいずれかが得られる。

**証明:** `frontier_cases` の三分岐を順に処理する。被覆分岐(即時・後のいずれも)では、blocker 値 `y` について `y = target` なら初出時刻が出現証人 (i)。さもなくば `y < anchor` かどうかで分け、成り立てば `frontierFirstAt_phaseSemantic` の子で (ii)、さもなくば `coverage` residual (iii)。負点分岐では、その軌道値 `a u` の初出を履歴から取り(`history_member_has_firstAt`)、`a u = target` なら (i)、`target ≤ a u` かつ `a u < anchor` なら同じく (ii)、それ以外は `negative` residual に失敗理由(値が target 未満か、anchor 以上か)を添えて (iii) とする。residual は「frontier が子を作れない正確な理由」をそのまま保持する。

### `crossingGrowthObstructionAt_phaseSemanticStep` (L214)

**主張:** 現行意味的 domain における crossing-growth 分岐の最強無条件結果: `0 < target` と strong debt 証明書 `DebtInvariant` のもとで、joint-growth 障害から必ず「目標出現、または `PhaseSemanticInvariant` 付きのランク子」が得られる。

**証明:** 前定理の三択のうち (i)(ii) はそのまま結論になる。residual (iii) の場合が要点で、frontier からは子が取れなくても、元の strong debt 証明書が `debtInvariant_selfExit_phaseSemantic` により自分自身の値を anchor とする normal 子 `⟨horizon, value, normal, value⟩` を供給する。debt 不変量の `value < anchor` からこの self-exit は anchor 降下であり、horizon は変わらないので horizon-safe である。すなわち residual は「危険な行き止まり」ではなく、strong debt 証明書が保険として常に脱出路を持つ形で閉じている。

### `crossingGrowthObstruction_phaseSemanticStep` (L236)

**主張:** 前定理の存在量化版: `CrossingGrowthObstruction`(catch-up 時刻等を存在量化したパッケージ)からも同じ結論が従う。

**証明:** 存在量化を開いて前定理を適用するだけである。frontier 由来の子は anchor を下げるときに使われ、正確な residual の両ケースは self-exit で安全に処理される、という分業の完成形である。

## 全体の中での位置づけ

証明地図の「負債局所解析」層の終端で、`CrossingGrowth` の障害と `NormalClosure` の意味的機構を接続し、crossing-growth 分岐の semantic 閉包(PROOF_MAP の「負債局所解析: semantic 閉包済み」)を完成させる。`frontierFirstAt_phaseSemantic` の `max horizon firstTime` 規律は、後の `TypedNormalProvenance` における crossing frontier 型の historical provenance の原型であり、その二時計 middle 区間の精密化が `CrossingFrontierRefined` で行われる。
