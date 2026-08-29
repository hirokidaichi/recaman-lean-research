# SemanticOracleRecursion

**役割:** 頂点定理のsemantic枝を正面から監査し、それが`0 < target`だけから導出できる**情報量ゼロ**の枝であることを確定させたうえで、消費者が持つべき正しい形(refined domainからの整礎降下)と、その消費者が原理的に払わねばならない代価を測る。

## このモジュールの役割

大域組み立ての頂点定理`LeastMissingTarget.semantic_or_flooredCore`は、外側の再帰に対して
「semantic位相の子」か「床つき固定点core」かの二択を差し出す。これまで攻撃されてきたのは
固定点側だけで、semantic側には消費者が一つも存在しなかった。従来この状況は「消費者を作るのが難しい」と
診断されていた。本モジュールはその診断を検査し、**誤りであったことを確定させる**。

真因は「消費者が存在しない」ことではなく、**semantic枝が消費すべき情報を何も運んでいない**ことである。
そのうえで本モジュールは三つの前向きな結果を積む。(1) semantic子をrefined domain
(整礎再帰の定義域)へ昇格させる構成をconstructor完全に与え、その仮定(horizon readiness)が
除去不能であることを具体反例で示す。(2) 昇格した子から降下すると無仮定で「target到達」か
「crossingノードで停止」に至る。(3) 残余をready crossing局所stepとunready crossing漏れの二つへ分離する。

最後の節では、どんな消費者でも払わねばならない**正確な代価**を記録する。semantic枝を閉じることは
targetの出現と**論理的に同値**であり、constructor局所の補題では原理的に届かない。

## 主要な定義

### `RefinedSemanticProgress` (L207)

semantic枝が外側の再帰に食わせるために到達すべき形。「**与えられた**親`parent`より厳密に下位で、
かつrefined domainに属する子が存在する」。存在量化された親ではなく、指定された親であることが要点である。

### `ReadyRefinedInvariant` (L231)

refined domainへの所属と、自分自身のhistory horizonでの target 時計(`target ≤ node.horizon + 1`)の連言。
「horizon-ready refined domain」と呼ぶ。crossing constructorだけがhorizon readinessを失いうるので、
この連言は残余をready crossingへ絞り込むために要る。

### `ReadyCrossingRefinedStepHypothesis` (L269)

「ready crossingノードからは target 到達かrefined childへのstrict辺が出る」という局所仮説。
素の`CrossingRefinedStepHypothesis`(crossing全体を要求)より弱い。

### `SemanticBranchClosure` (L341)

「すべてのsemanticノードがtargetの出現witnessを生む」。semantic枝を閉じる、ということの正確な意味である。

## 定理と証明

### `exists_phaseSearchProgress_parent` (L39)

**主張:** どの位相探索ノードにも、それより厳密に大きい親が存在する。

**証明:** anchor成分だけを1上げたタプル`⟨horizon, anchorParent + 1, phase, localMeasure⟩`を取る。
history予算(第一成分)は不変で、他成分も何も下がらないので、四成分辞書式順序で厳密に大きい。

**気持ち:** これが全体の鍵である。semantic枝のpayloadに含まれる`stepParent`は**存在量化されているだけ**なので、
この構成により子に対して何の制約も課していない。「進行辺がある」という情報が、実は空だったのである。

### `exists_semanticPhaseProgress` (L48)

**主張:** `0 < target` ならば、semanticノードとその上の進行辺が常に存在する。

**証明:** `exists_phaseSemantic_start`が正のtargetに対しcanonical semantic startを供給するので、
それを子に取り、L39で親を捏造する。

### `semantic_or_flooredCore_of_pos` (L62)

**主張:** 頂点定理の結論そのもの——「semantic進行辺 ∨ 床つき固定点core」——が、
**`0 < target` だけから**導出できる。

**証明:** 左のdisjunctをL48で直接構成する。それだけである。

**これが本モジュールの中心的な否定的結果である。** `LeastMissingTarget`仮説も、
permanent tailの解析も、corridorの数値も、一切使わずに頂点定理の結論が出る。
これは固定点解析の欠陥ではない——右のdisjunctは本当に情報を持っている。
言えるのは、**左のdisjunctを強化しない限り消費者は存在し得ない**、ということである。
第七十一ラウンドの主結果であり、第八十二ラウンドで床を無条件32へ上げた後も、
「頂点定理の二択そのものは依然`0 < target`から出る」という事実は変わっていない。
床上げの価値は枝の内容にあって、二択の存在にはない。

### `LeastMissingTarget.target_pos` (L73)

**主張:** 最小未出targetは正である。

**証明:** `a 0 = 0`なので0は出現済み。補助補題。

### `ReadyCurrentOrDebtInvariant.horizon_ready` (L84) / `ExtendedHistoryNormalInvariant.horizon_ready` (L95)

**主張:** refined domainのcurrent-state・ready-debt・extended-history constructorはいずれも
`target ≤ node.horizon + 1`を知っている。

**証明:** 前者は証明書の`time_ready`(またはready-debtの`horizon_ready`フィールド)、
後者は`horizon_time_ready`フィールドをそのまま読む。補助補題。

### `OrbitReadyRefinedInvariant.horizonReady_or_crossing` (L104)

**主張:** refined nodeはhorizon-readyであるか、crossingノードである。

**証明:** 四constructorのうち三つはL84/L95でready、残る一つがcrossing recoveryそのもの。
**crossing constructorだけがhorizon readinessを保証しない**——この一点が、後の残余分離の形を決めている。

### `PhaseSemanticInvariant.toOrbitReadyRefinedInvariant` (L116)

**主張:** semanticノードは、horizon readiness `target ≤ node.horizon + 1` を補えば
refined domainへ昇格する。constructor完全。

**証明:** semantic不変量の四constructorを場合分けする。canonical startとcrossing recoveryは
そのままrefined domainのconstructorに落ちる(追加情報を要しない)。ordinary normalは
`first.1`で初出時刻の値へ書き換え、extended-history表現の証明書を組み立てる。ここで
`horizon_time_ready`フィールドにちょうど仮定`hready`を差し込む。debtノードも同様に
`horizon_ready`フィールドへ差し込むだけである。

**気持ち:** 「semantic子が持つべき情報量は何か」への答えがこれである。広義のsemantic不変量と
refined domainの差は、**horizon時計ちょうど一つ**である。第七十一ラウンドで
ROADMAPが名指ししていた「ordinary normal constructorのhorizon整合性」は、
確かに実在する層だが唯一の障害ではなかった(三層のうち最も軽い層)。

### `not_forall_phaseSemantic_horizonReady` (L150)

**主張:** horizon readinessは**除去できない**。広義のsemantic domainはそれを含意しない。

**証明:** target 6 に対する具体反例。実軌道の状態`a 3 = 6`をordinary normalノードとして見たものが
`broadNormalChild_can_lack_horizonReadiness`で与えられており、これがsemanticでありながら
`6 ≤ horizon + 1`を満たさない。捏造ではなく実軌道の状態である点が重要で、
「仮定を工夫すれば外せる」類のものではないことを示している。

### `orbitReadyRefined_occurs_or_crossing` (L162)

**主張:** **無仮定の降下定理。** 任意のrefined nodeから位相探索を降下させると、
targetに到達するか、crossingノードで停止する。oracleもclockもtail仮説も使わない。

**証明:** `phaseSearchProgress_wellFounded`による整礎帰納法。各ノードで
`refinedStep_or_crossing`を呼び、「到達」なら終了、「refined childへのstrict辺」なら
帰納法の仮定を子に適用、「crossing」ならそこが停止点である。整礎性が降下の有限性を保証する。

**気持ち:** これが「消費者」の無条件版である。第七十一ラウンドの前向き成果(2)にあたる。
`0 < target`以外は何も要らない。だからこそ、この降下に食わせられる形の情報を
semantic枝が運んでいないことが致命的なのである。

### `phaseSemanticChild_occurs_or_crossing` (L177)

**主張:** horizon-readyなsemantic子は、上の降下の合法な開始点である。

**証明:** L116で昇格し、L162を当てる。

### `phaseSemanticChild_reaches_of_crossingRefinedStep` (L192)

**主張:** すでに分離済みのcrossing局所step仮説`CrossingRefinedStepHypothesis`を認めれば、
semantic子から出発してtargetに到達する。

**証明:** 昇格したノードに`restrictedPhaseSearchOracle_reaches_from`を当てる。
**これが頂点のsemantic枝に欠けていた接続そのものである**——ただし枝の側がこの形の情報を運んでいない。

### `occurs_of_refinedSemanticProgress` (L215)

**主張:** すべてのrefined親に対し`RefinedSemanticProgress`(またはtarget到達)が言えれば、無条件でtargetは出現する。

**証明:** canonical startがrefined nodeであることと、仮定の局所stepを
`targetStart_reaches_of_restrictedOracle`に渡す。これは「semantic枝が到達すべきゴール形」の宣言である。

### `PhaseSemanticInvariant.toReadyRefinedInvariant` (L235) / `targetStartInvariant_readyRefined` (L243)

**主張:** horizon-readyなsemantic子、およびcanonical startは`ReadyRefinedInvariant`に属する。

**証明:** L116と`horizon_ready`を組にするだけ。補助補題。

### `ReadyRefinedInvariant.step_or_readyCrossing` (L255)

**主張:** ready domainでのconstructor完全な監査。各ノードはrefined domain内へstepするか、
**ready** crossingノードである。

**証明:** `refinedStep_or_crossing`を呼び、crossing枝ではready domainが持つhorizon時計を
`ReadyCrossingSearchInvariant`の`horizon_ready`フィールドへ供給する。
素の`refinedStep_or_crossing`と比べると、残余が要求する時計フィールドが付いた分だけ強い。

### `readyCrossingRefinedStepHypothesis_of_targetTailReturn` (L276)

**主張:** `TargetTailReturnHypothesis`があればready-crossing stepは自動で得られる。

**証明:** `ReadyCrossingSearchInvariant.refinedStep_of_targetTailReturn`をそのまま適用。

### `readyRefined_occurs_or_unreadyChild` (L284)

**主張:** ready-crossing stepだけを使った降下。horizon-ready refined nodeから降ると、
targetに到達するか、**horizon readinessを失った** crossingノード
(`unready.horizon + 1 < target`)が明示的な残余として一つ出てくる。

**証明:** 整礎帰納法。各段でL255を呼び、crossing枝は仮定`hcrossing`が処理する。
得られた子がhorizon-readyなら帰納法を回し、readyでなければL104により
その子はcrossingノードでしかありえないので、それを残余として返す。

**気持ち:** 残余を「見えなくす」のではなく**逐語的に手渡す**設計である。
どこで降下が止まりうるかを型に書いておけば、後続の攻撃が一点に集中できる。

### `occurs_or_unreadyCrossing_of_readyCrossingStep` (L312)

**主張:** 大域組み立て。canonical startから始めて「target出現 ∨ unready crossingが存在」。

**証明:** canonical startがready refinedであること(L243)とL284の合成。

### `phaseSemanticChild_occurs_or_unreadyCrossing` (L324)

**主張:** 同じ主張をsemantic子から始めた頂点向けの形。

**証明:** L235とL284の合成。

### `semanticBranchClosure_iff_occurs` (L348)

**主張:** **消費者の代価。** 正のtargetにおいて`SemanticBranchClosure target`は
「targetが出現する」と**論理的に同値**である。

**証明:** (⇒) canonical semantic startを一つ取り、closureを適用すれば出現witnessが出る。
(⇐) 出現すればすべてのノードに対して同じwitnessを返せばよい。

**この同値がsemantic枝の難易度の下限を確定させる。** semantic枝を閉じる作業は、
どう分解しても全射性予想そのものと同じ強さを持つ。したがって
**constructor局所の補題では原理的に閉じない**——消費者は大域的な矛盾の一部でなければならない。
「あと一歩で閉じそう」に見える形が出てきたら、この定理を思い出すべきである。

### `LeastMissingTarget.not_semanticBranchClosure` (L359)

**主張:** 最小未出targetは自分自身のsemantic closureを反証する。

**証明:** L348と`target_missing`の合成。補助補題だが、上の同値の帰結を反例側から言い直したもの。

### `LeastMissingTarget.not_crossingRefinedStepHypothesis` (L368)

**主張:** 同様に、最小未出targetの下では素のcrossing局所仮説`CrossingRefinedStepHypothesis`も成り立たない。

**証明:** `crossingRefinedStepHypothesis_implies_occurs`と`target_missing`の合成。

**含意:** 固定点解析を「crossing局所仮説を仮定する」ことで置き換えることはできない。
その仮定もまた予想と同値の強さを持つからである。

### `LeastMissingTarget.unreadyCrossing_of_readyCrossingStep` (L378)

**主張:** 最小未出targetの下でready-crossing stepを認めると、
horizon readinessを失ったcrossingノードが必ず存在することになる。

**証明:** L312で二択を取り、target出現枝を潰す。

**これがsemantic側に残っている未解決事項の正確な形である。** なお第八十ラウンドで、
この漏れのliteralな形は**証明不能**であることが確定している(target 12・ノード`⟨7,7,.normal,7⟩`が
具体反例。`a 5 = 7 < 12 < 13 = a 6`で時刻6は強制加算、`12 ∉ valuesThrough 5`)。
したがってこの残余は「非存在」ではなく「到達不能性」でしか閉じられない。

## 全体の中での位置づけ

証明地図(docs/PROOF_MAP.md)における「semantic枝」の診断・監査モジュールである。
上流は`RefinedOracleBoundary.lean`(refined domainと整礎再帰の基礎)と
`PermanentAboveCorridorLeastMissingSummit.lean`(頂点定理)。

下流は二方向に分かれる。第一に`RefinedSemanticOutcome.lean`が、本モジュールが暴いた
「情報量ゼロ」を実際に埋める精密版outcome型を導入する(親を存在量化せず、子をrefined domainへ)。
第二に`CrossingReadinessBridge.lean` / `CrossingReadinessClosure.lean`が、
本モジュールの`ReadyCrossingRefinedStepHypothesis`とunready crossing漏れを引き継いで
readiness橋を組む。

正味の位置づけを正直に述べれば、本モジュールの最大の成果は**否定的**である:
頂点定理のsemantic枝が空であることの確定と、消費者の代価が予想そのものと同値であることの確定。
足場を組み直す前にこの二つを知っておくことに価値がある。前向きの成果(昇格・無条件降下・残余分離)は、
いずれもその制約の中で「どこまでなら無料で進めるか」を測ったものである。
