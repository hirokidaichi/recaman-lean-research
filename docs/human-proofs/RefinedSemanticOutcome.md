# RefinedSemanticOutcome

**役割:** 捏造可能だった広義semantic枝を、親を存在量化しない「refined domain内の名前付き辺」四本へ置き換え、その非捏造性を三本の障害定理で裏づける。ただし四枝を忘却した形は依然として空虚である。

## このモジュールの役割

第七十一ラウンドの診断で、大域組み立ての頂点定理が持つsemantic枝(位相探索の進行辺)は
**情報量ゼロ**であることが確定した。`PermanentTailTerminalSuccessorOutcome.semantic_progress`は
広義の`PhaseSemanticInvariant`に属する子と、**存在量化されただけ**のstep parentを積んでいる。
`exists_phaseSearchProgress_parent`は任意のノードの上にanchor成分を1だけ上げた親を作れるし、
`exists_phaseSemantic_start`は正のtargetごとにsemanticノードを供給する。つまり枝のpayloadは
両半分とも「解析を経ずに手で作れる」ものであり、外側の再帰が消費できる情報を何も運んでいなかった。

本モジュールは既存の型を一切壊さずに、**平行して**精密版のoutcome型を追加する。精密化の核心は二点だけである。

1. 子が広義のsemantic不変量ではなく、整礎再帰の**定義域そのもの**である
   `OrbitReadyRefinedInvariant`(refined domain)に属する。
2. **step parentを存在量化しない。** 四つのsemantic枝はそれぞれ、証明書自身が持つ時計から
   決まる名前付きノード(valley後の代表、blocker前駆、discharge親そのもの)を親に固定する。

同時に本モジュールは、この精密化の**限界も明示**する。四枝を忘却して「refined domainの中に
strict辺が一本ある」だけにした`RefinedDomainEdge`は、`0 < target`だけから構成できてしまう
(第七十八・第八十一ラウンド、`TrivialityProbe.lean`)。したがって非捏造性が保証されるのは
親を固定した各constructorであって、忘却形ではない。

## 主要な定義

### `PermanentTailRefinedSuccessorOutcome` (L251)

discharge証明書`source`から得られるterminal successor情報の精密版。既存の
`PermanentTailTerminalSuccessorOutcome`の広義`semantic_progress`一本を、親を固定した四本へ割った七枝の帰納型である。

- `target_occurs`: targetの出現witness(反例の内部では死ぬ枝)。
- `history_progress`: `TerminalChronologyHistoryProgress`(履歴予算の厳密下降)。既存のまま。
- `immediate_refined`: 親を`terminalHistoricalPredecessorNode parent (source.downTime + 2)`に固定。
  即時valleyの代表がextended-history表現でそこに載る。
- `early_refined`: 親を`terminalHistoricalPredecessorNode parent (firstTime - 1)`に固定。
- `ready_refined`: 親を`terminalCurrentPredecessorNode (firstTime - 1)`に固定。
  こちらはcurrent-state表現(`OrbitReadyNormalInvariant`)。
- `crossing_refined`: 親を`parent`そのもの、子を`terminalPredecessorCrossingNode parent crossingTime`に固定。
- `installed_successor`: installed cycleの辺。既存のまま。

四つのsemantic枝(`immediate_refined`・`early_refined`・`ready_refined`・`crossing_refined`)の
いずれも、子には`OrbitReadyRefinedInvariant target child`が**同梱**される。

### `RefinedDomainEdge` (L385)

四枝の共通形を抽出した忘却形:「両端点がrefined domainに属するstrictな位相探索辺が存在する」。

```text
∃ stepParent child, OrbitReadyRefinedInvariant target stepParent
                  ∧ OrbitReadyRefinedInvariant target child
                  ∧ PhaseSearchProgress target child stepParent
```

見た目は強そうだが、**この命題は`0 < target`だけから証明できる**(後述)。忘却は最後の接続点でだけ使う、
というのがこのモジュール以降の設計方針である。

## 定理と証明

### `OrbitReadyRefinedInvariant.debt_or_anchor_eq_local` (L44)

**主張:** refined nodeは debt相であるか、さもなくば `anchorParent = localMeasure` を満たす。

**証明:** refined domainの四つのconstructorを場合分けする。current-state・extended-history・
crossing-recoveryの三つはいずれも証明書の`node_eq`がノードのタプルを実軌道の値へピン留めしており、
そこでanchorとlocal measureは同じ軌道値として現れる。ready-debtのconstructorだけは相がdebtである。
つまり「anchorとlocal measureが乖離した normal ノード」はrefined domainに存在し得ない。
これが後続の反捏造論法の唯一の梃子である。

### `OrbitReadyRefinedInvariant.crossing_of_anchor_lt_target` (L66)

**主張:** refined nodeのanchorがtarget未満なら、そのノードは crossing recovery である。

**証明:** 同じ四分岐。current-stateとextended-historyのconstructorは`target_le_value`を持ち、
anchorは実軌道値そのものなので`target ≤ anchorParent`となり仮定と矛盾する。debt相は
`target ≤ value`と`value < anchor`から同様に矛盾。残るのはcrossing recoveryだけである。
「refined domainでanchorがtargetを下回れるのはcrossing recoveryのみ」というこの剛性が、
crossing枝の非捏造性(L199)の根拠になる。

### `anchorBump_not_orbitReadyRefined` (L93)

**主張:** normal相かつ`anchorParent = localMeasure`のノードに対し、anchorを1だけ上げたタプル
`⟨horizon, anchorParent + 1, phase, localMeasure⟩`は refined nodeでは**ない**。

**証明:** もしrefinedなら、L44により debt相であるか`anchorParent + 1 = localMeasure`である。
相は元のnormalのままなので前者は不可能、後者は`anchorParent = localMeasure`と矛盾する(omega)。
**捏造がどのフィールドで失敗するかを名指しした定理**であり、第七十一ラウンドの
`exists_phaseSearchProgress_parent`が使う操作をそのまま無効化する。

### `refinedNormal_anchorBump_not_orbitReadyRefined` (L110)

**主張:** refined normal nodeに対しては、anchor bumpは常にrefined domainの外へ出る。

**証明:** L44でnormal相なら`anchorParent = localMeasure`が従うので、L93がそのまま適用できる。

**重要な留保(第八十一ラウンドの訂正):** この定理は仮定 `node.phase = .normal` を**要求している**。
`DebtInvariant.value_lt_anchor` は anchorを上げても保たれるので、**debt相ではanchor bumpが
refined domainの中に留まる**。すなわちこの防御はnormal相限定であり、「anchor bumpは必ず外れる」
という当初の主張は誤りだった。精密版が捏造を防いでいるのは各constructorが親を固定しているからであって、
anchor bump単体が普遍的に禁じられているからではない。

### `not_natQuadLex_allZero` (L124)

**主張:** 四成分辞書式順序において、全零タプル`(0,(0,(0,0)))`より前には何もない。

**証明:** `Prod.Lex`の構造に沿った入れ子の場合分けで、どの成分でも`n < 0`が出て矛盾する。補助補題。

### `no_phaseSearchProgress_into_zeroRank` (L144)

**主張:** target未満の履歴予算が尽きている(`missingBelowCount target horizon = 0`)とき、
debt相でanchorもlocal measureも0のノード`⟨horizon, 0, .debt, 0⟩`へは、どんな子からも
`PhaseSearchProgress`が入らない。

**証明:** 予算が0ならこのノードの`phaseSearchRank`は全零タプルに簡約される。`PhaseSearchProgress`は
定義上ランクの厳密減少なので、子のランクが全零より小さいことになり、L124に矛盾する。

### `not_forall_exists_phaseSearchProgress_child` (L161)

**主張:** 予算が尽きたhorizonが一つでもあれば、「すべての親に子が存在する」は**偽**である。

**証明:** L144のゼロランクノードを反例に取る。捏造への**第二の、独立した障害**である。
L93が「anchorを上げる」という特定の操作を潰すのに対し、こちらは「親を固定した枝を
『どの親にも子がいる』という一般論で閉じる」という戦略そのものを潰す。

### `PermanentTailDischargeReturnCertificate.parent_orbitReadyRefined` (L174)

**主張:** discharge証明書の親ノードは、それ自体がrefined nodeである。

**証明:** combined証明書のcrossing成分`ready_crossing.crossing`がまさにready crossing recoveryであり、
refined domainの第四constructorそのものである。`crossing_refined`枝で親側のrefined性を供給するために要る。

### `PermanentTailDischargeReturnCertificate.parent_anchor_lt_target` (L182)

**主張:** discharge親のanchorはtargetより厳密に小さい。

**証明:** 親はcrossing recovery証明書から作られており、そのanchorはold crossing前駆の軌道値`a oldTime`である。
crossing recoveryの定義がこの値をtarget未満に置いている(`recovery.crossing.1`)。

### `crossingChild_anchorDrop_forces_crossingRecovery` (L199)

**主張:** crossing枝の反捏造性の最も鋭い形。親のanchorが既にtarget未満で、子のanchor候補
`a crossingTime`がさらにそれを下回るとき、子がrefined nodeであれば子は**必ず本物のcrossing recovery**である。

**証明:** 子`terminalPredecessorCrossingNode parent crossingTime`のanchorは`a crossingTime`であり、
仮定の連鎖から`a crossingTime < parent.anchorParent < target`。よってL66が適用でき、
`CrossingSearchInvariant`が出る。

**気持ち:** crossing枝の子は親と horizon を共有するので、strict辺はanchorの下降からしか来ない。
そしてrefined domainでanchorがtarget未満になれる唯一の道はcrossing recoveryである。
したがってこの枝を作るには実軌道の本物のstrict upcrossingが要り、親タプルの構文的調整では届かない。
これが四枝のうち最も強い非捏造性である。

### `PermanentTailDischargeReturnCertificate.immediateValley_extended` (L216)

**主張:** 即時valley枝の代表を、親のzero-budget horizonに載せた
`ExtendedHistoryNormalCertificate target (terminalHistoricalPredecessorNode parent (downTime + 2)) (downTime + 2) …`
として構成できる。

**証明:** valleyはdowncrossの2歩後に`a (downTime + 2) = a downTime + 1`で閉じ、`source_above`より
この値はtargetより上である。`return_eq`と`return_before_parentHorizon`から`downTime + 2`が
親のhorizon以下に収まる。horizon readinessは親のcrossing証明書の`horizon_ready`をそのまま流用する。

**気持ち:** 第七十六ラウンドの記録どおり、immediate枝だけは素直に精密化できなかった。元の
`canonicalCoverage_phaseSemantic`経路は`target ≤ downTime + 3`を要求するが、valley証明書は
その時計を持たない(valley自身の軌道時刻がtargetに達している必要がない)。そこで
「現在状態としてtargetを超えている」ことを要求しない**extended-history表現**へ経路を変え、
同じ値を親のhorizonに格納して代表を得た。表現を替えることで時計の要求を回避した、という一手である。

### `PermanentTailDischargeReturnCertificate.refinedSuccessorOutcome` (L326)

**主張:** すべてのdischarge証明書は精密版outcomeを持つ。生成枝は一つも失われない。

**証明:** `terminalFiniteClosedOutcome`を場合分けする。`history_progress`はそのまま移送。
`immediate_semantic`はL216でextended表現を作り、その`refinedStep`を呼んで
「targetに到達した」か「refined childへstrict辺が出た」かの二択を得る。
`historical_complete`の内側では`early_step`と`ready_step`がそれぞれ既に手元に持っている
refined local step(`early.refinedStep` / `ready.refinedStep`)を呼び直し、
`below_master`の`phase_exit`は`certificate.refined`をそのまま`crossing_refined`へ、
`master_progress`は既存の`installed_successor`へ流す。

**気持ち:** ここが精密化の実質である。三つのhistorical枝では、**広義のstepを呼んだその場所に
refined stepが既に存在していた**——つまり情報は元から手に入っていたのに、outcome型が
それを捨てていた。第七十一ラウンドの診断「消費者が存在しないのではなく、消費すべき情報が
outcome型で捨てられている」が、ここで文字どおり回収されている。

### `RefinedDomainEdge.occurs_or_crossing` (L394)

**主張:** refined辺があれば、そこから降下すると「targetに到達」か「crossingノードで停止」に必ず至る。

**証明:** 辺の子はrefined nodeなので整礎再帰の合法な開始点であり、
`orbitReadyRefined_occurs_or_crossing`をそのまま適用する。

### `RefinedDomainEdge.reaches_of_crossingRefinedStep` (L404)

**主張:** crossing局所stepの仮説`CrossingRefinedStepHypothesis target`があれば、同じ辺からtargetに到達する。

**証明:** 仮説からrefined oracleを組み立て、`restrictedPhaseSearchOracle_reaches_from`を子に適用する。

### `PermanentTailRefinedSuccessorOutcome.toEdge` (L415)

**主張:** 精密版outcomeを潰すと「target出現 ∨ history辺 ∨ `RefinedDomainEdge` ∨ installed cycle辺」の四択になる。

**証明:** 七枝それぞれについて、固定された親のrefined性を供給して`RefinedDomainEdge`の存在量化に
放り込む。`immediate_refined`と`early_refined`はextended-history表現、`ready_refined`は
current-state表現、`crossing_refined`はL174のdischarge親そのものを親側の証人にする。

**注意:** これが**忘却操作**である。四本の固定された親はここで存在量化に飲まれ、
どの枝から来たかの情報は消える。次の定理が示すとおり、その代償は大きい。

### `LeastMissingTarget.exists_refinedSuccessorOutcome` (L454)

**主張:** 最小未出targetは、精密版outcomeを載せたdischarge証明書を必ず生む。

**証明:** 最小未出targetからmissing permanent tail、combined証明書、discharge return証明書を順に取り、
L326を当てる。**これが解析が実際に支えている頂点の主張**であり、mounted-iteration連鎖を
組み直さずに述べられる最良の形である。

### `LeastMissingTarget.historyEdge_or_refinedEdge_or_installedEdge` (L473)

**主張:** 最小未出targetは「history辺 ∨ refined辺 ∨ installed cycle辺」の三択を与える。

**証明:** L454とL415を合成し、target出現枝を`target_missing`で潰す。

**この定理は空文である。** ソース自身のdocstringが明記しているとおり、
`TrivialityProbe.lean`の`probe_refinedDomainEdge_of_pos`が`RefinedDomainEdge target`を
**`0 < target`だけ**から導出する(`exists_targetReady_state_of_pos`を二度適用して
`target ≤ a n < a n2`なる実時刻を取り、共通horizonへ`ExtendedHistoryNormalCertificate`として
載せるだけでよい。捏造タプルは使わず、すべて実軌道の状態である)。したがって第二disjunctが
無条件に真であり、この三択は`LeastMissingTarget`仮説すら使わずに成立する。
第八十一ラウンドの敵対的再検査で判明した事実であり、**訂正として記録されている**。
下流の消費者は本定理ではなく、証明書を保持する`RefinedTerminalSemanticStep` /
`RefinedSemanticEdge`(`RefinedSuccessorRank.lean`以降)を使わなければならない。

### `LeastMissingTarget.stuckCrossing_of_refinedEdge` (L490)

**主張:** 頂点のrefined辺は整礎再帰に直ちに食わせられ、stuck crossingノードを出す。

**証明:** L394の二択でtarget出現枝を`target_missing`で潰すだけである。

**留保:** L473がrefined辺を無条件に供給する以上、**この定理の仮定は死んでいる**。
結論`∃ stuck, CrossingSearchInvariant target stuck`は`0 < target`から出るので、
「頂点がstuck crossingを生む」という言明に固有の内容はない。

## 全体の中での位置づけ

証明地図(docs/PROOF_MAP.md)の「semantic枝の精密化」段の起点である。上流は
`SemanticOracleRecursion.lean`(refined domainからの整礎再帰と、広義semantic枝が空である診断)と
`PermanentAboveCorridorTerminalSuccessor.lean`(生成元の広義outcome)。
下流は精密版を頂点まで運ぶ8段チェーンで、段1が`RefinedSuccessorRank.lean`、段2が
`RefinedIterationClosure.lean`、段3が`RefinedReplayInterface.lean`、段4が
`RefinedHistoryLanding.lean`と続き、段5(`RefinedLandingHorizon.lean`)・
段6(`RefinedLandingMount.lean`)・段7(`RefinedMountedIteration.lean`)・
段8(`RefinedFixedPointCore.lean`)まで到達している(第八十五ラウンド)。
頂点は`LeastMissingTarget.refinedSemanticEdge_or_flooredCore`で、
左枝が`RefinedSemanticEdge`、右枝が`32 ≤ crossingTime ∧ 19 ≤ target`の固定点coreである。

正味の位置づけを正直に述べると、本モジュールが達成したのは「semantic枝が捨てていた情報の回収」であって
「semantic枝を閉じたこと」ではない。回収された情報は各constructorのpayloadの中にあり、
忘却形にした瞬間に消える。忘却形は二度にわたって捏造可能だと判明しており
(第七十八・第八十一ラウンド)、本モジュールの`RefinedDomainEdge`(L385)もその一つである。
伝播先の`RefinedSemanticEdge`は二つのconstructorがどちらもpermanent-tail証明書を保持するため
`¬ ∃ t, a t = target`を単独で含み、`target = 1`で即座に反証される
(`RefinedSemanticEdge.target_missing`)。したがって`0 < target`からの空虚化攻撃は
構造的に閉じた。ただし**排除できたのは「`0 < target`からの導出」だけ**であり、
「`LeastMissingTarget`から無条件に出てしまわないか」は未解決のまま残っている。
それが出れば右枝が到達不能になり、頂点定理はふたたび情報量を失う。
