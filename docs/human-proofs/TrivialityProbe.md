# TrivialityProbe

**役割:** 精密化された成果に対する敵対的検査。忘却形 `RefinedDomainEdge` が `0 < target` だけから作れること、debt 相の anchor bump が防御をすり抜けること、regeneration 仮定が実軌道で偽であることを、いずれも**構成的に**証明する。

## このモジュールの役割

このモジュールは新しい前進を作らない。**既存の定理が実際にはどれだけの情報を運んで
いるかを測る**ためのものである。収録された定理はすべて肯定的な構成であって、証明済みの
定理を反証してはいない。示されるのは「その定理の結論は、周辺の解析を一切使わずに作れる」
「その定理の仮定は実軌道で偽である」という形の事実であり、**この指摘そのものが研究成果**である。
三件が独立に記録されている。(1) 忘却形の refined 辺は target の正値性だけから従うので、
それを結論とする頂点定理は空文である。(2) anchor bump が refined domain を必ず外れるという
防御は normal 相限定であり、debt 相はその外にある。(3) regeneration 仮定は実軌道で偽なので、
それを仮定した三つの定理は空虚に真である。

## 参照される定義(他モジュール)

- `PhaseSearchNode`: 探索木の頂点。四成分 `⟨horizon, anchorParent, phase, localMeasure⟩`
  (履歴の見える範囲、親の値、normal / debt の別、局所量)。
- `PhaseSearchProgress target child parent`: rank
  `(missingBelowCount target horizon, anchorParent, phase.rank, localMeasure)` の**辞書式**厳密下降。
- `OrbitReadyRefinedInvariant target node`: refined domain。「ready normal または ready debt」
  「extended-history normal」「crossing」の三択。
- `RefinedDomainEdge target`: refined domain 内の親子ペアで rank が厳密下降するもの。
  生成過程の証明書を捨てた**忘却形**である。
- `BlockedFirstOccurrence value time`: 初出の直後の減算が「歴史的理由だけで」失敗する配置。
  clock は足りている(`time + 1 < value`)のに減算欠損 `value - (time+1)` が既出で加算が強制される。

## 定理と証明

### `probe_refinedDomainEdge_of_pos` (L47)

**主張:** `0 < target` だけから `RefinedDomainEdge target` が構成できる。permanent tail も
discharge 証明書も refined outcome も使わない。

**証明:** 初期領域の補題 `exists_targetReady_state_of_pos` を二度使う。一度目は `target` に対して
適用し、`target ≤ a n`、`target ≤ n + 1`、座標データ付きの**実時刻** `n` を得る。二度目は
`a n + 1`(正)に対して適用し、`a n + 1 ≤ a n2` なる実時刻 `n2` を得る。すなわち
`target ≤ a n < a n2` である。

共通の horizon を `H = max n n2` として二つの頂点を組む:
親 `⟨H, a n2, .normal, a n2⟩` と子 `⟨H, a n, .normal, a n⟩`。どちらも
`ExtendedHistoryNormalCertificate`(代表時刻の軌道値をそのまま anchor と localMeasure に
載せた normal 頂点)の要件を満たす。代表時刻が horizon 以下であることは `max` の性質、
readiness `target ≤ H + 1` は `target ≤ n + 1 ≤ H + 1`、値条件は `target ≤ a n < a n2`、
座標は二度の適用が返したものをそのまま使う。よって両者とも refined domain の第二枝に属する。

rank の下降は、二頂点が **同じ horizon** を持つので第一成分 `missingBelowCount target H` が
一致し、第二成分 `anchorParent` が `a n < a n2` で真に小さいことから辞書式順で従う。

重要なのは**捏造タプルを一つも使っていない**ことである。両頂点の anchor と localMeasure は
実軌道の値 `a n`、`a n2` であり、代表時刻も実時刻である。したがってこれは第七十八ラウンドの
`occurs_or_refinedDomainEdge_of_pos` より真に強く、`LeastMissingTarget` すら要らない。
忘却形は情報を運ばない、と結論できる。

### `probe_two_le_of_leastMissing` (L90)

**主張:** 最小未出値 `target` は `2 ≤ target` を満たす。

**証明:** `a 0 = 0` と `a 1 = 1` が計算で確認できるので、0 と 1 は出現している。
補助補題(他の probe の下限として使う)。

### `probe_summit_disjunction_of_pos` (L104)

**主張:** 頂点定理 `LeastMissingTarget.historyEdge_or_refinedEdge_or_installedEdge` の
結論——history 辺・refined 辺・installed-cycle 辺の三択——は `0 < target` から従う。

**証明:** 第二 disjunct に `probe_refinedDomainEdge_of_pos` を入れるだけである。

つまりこの頂点定理は**空文**である。`target` が最小未出値であるという仮定も、
その背後の permanent tail 解析も、結論に何も寄与していない。第七十一ラウンドで
`semantic_or_flooredCore` について指摘されたのと同じ欠陥が、それを修復するために
作られた精密版の**忘却形**で再発した形になる。下流の消費者は、生成証明書を保持する
`RefinedSemanticEdge` を使わなければならない。

なお、L79〜L87 のコメントが記録しているように、「history 枝も `(childTime, parentTime) = (1, 0)`
で自由である」という当初の報告は**現在の定義に対しては成立しない**。
`TerminalChronologyHistoryProgress` は budget 下降と
`TerminalHistoryCursor target (parentTime + 1)` の連言へ強化されており、`parentTime = 0` では
候補時刻が 0 しかなく `a 0 = 0` なので cursor が満たせない。history 枝は実質的な内容を持つ。
検査時点では正しかった指摘が、並行して進んだ landing 前置界の作業によって閉じられた、という
経緯であり、該当の probe 定理は取り下げられている。

### `probe_stuckCrossing_without_refinedEdge` (L115)

**主張:** `LeastMissingTarget target` から `∃ stuck, CrossingSearchInvariant target stuck` が
従う。`RefinedDomainEdge target` の仮定は不要である。

**証明:** target の canonical start 頂点を取り(`exists_targetStartNode`)、それが refined domain に
属することを使って(`targetStartInvariant_orbitReadyRefined`)整礎再帰
`orbitReadyRefined_occurs_or_crossing` を回す。target は未出なので出現枝は矛盾し、
crossing 枝が残る。

したがって `stuckCrossing_of_refinedEdge` の refined 辺仮定は**死んでいる**。同じ結論が
仮定なしで出る以上、その定理は refined 辺を「使って」いない。

### `probe_unifiedOutcome_conclusion_of_pos` (L127)

**主張:** landing 輸送版の頂点定理 `PermanentTailUnifiedOutcome.semantic_or_thirtytwo_or_landingGap`
の結論(semantic 枝 ∨ 床32付き固定点枝 ∨ landing gap 枝)も `0 < target` から従う。

**証明:** 第一 disjunct に `exists_semanticPhaseProgress`(第七十一ラウンドで確立された
「semantic 枝は正値性から作れる」)を入れる。

ここは誤解を避けて正確に述べる。これは床 `32 ≤ crossingTime` が無価値だという主張ではない。
床の価値は**枝の内容**にあり、この定理の**二択(三択)そのもの**が情報を持たないという指摘である。
第一 disjunct が空である限り、外側の再帰はこの定理から何も受け取れない。

## debt 相の anchor bump

### `probe_debtAnchorBump_stays_orbitReadyRefined` (L147)

**主張:** `ReadyDebtInvariant target node value firstTime` が成り立つとき、anchor を 1 上げた頂点
`⟨node.horizon, node.anchorParent + 1, node.phase, node.localMeasure⟩` もまた
`OrbitReadyRefinedInvariant target` を満たす。

**証明:** `DebtInvariant` の各フィールドを見る。`phase_eq`、`local_eq`、`target_le`、`first`、
`firstTime_lt_horizon` はいずれも anchor に言及しない。anchor に言及する唯一のフィールドは
`value_lt_anchor : value < node.anchorParent` であり、anchor を増やしても保たれる。
`ReadyDebtInvariant` の `horizon_ready` も horizon にしか触れない。よって証明書が丸ごと
持ち上がる。

### `probe_debtAnchorBump_progress` (L168)

**主張:** anchor を 1 上げた頂点は、元の頂点の厳密な rank 上位(親)である。

**証明:** horizon が同じなので第一成分が一致し、第二成分 `anchorParent` が
`node.anchorParent < node.anchorParent + 1` で真に増える。辞書式順の定義そのものである。

### `probe_concrete_readyDebt` (L176)、`probe_concrete_debtBump` (L190)

**主張:** 具体例。target 2 に対し `⟨3, 4, .debt, 2⟩` は refined debt 頂点である
(値 3 は時刻 2 が初出、horizon 3、anchor 4)。さらに `⟨3, 4, .debt, 2⟩` と
anchor を上げた `⟨3, 5, .debt, 2⟩` はともに refined domain に属し、後者は前者の厳密な親である。

**証明:** 各フィールドが実軌道の小さな計算(`a 2 = 3` とその初出性)で決定でき、`decide` で閉じる。
組み立ては前二定理の適用である。

**この節の帰結:** `refinedNormal_anchorBump_not_orbitReadyRefined`(anchor bump は refined domain を
必ず外れる)は仮定に `node.phase = .normal` を持つ。その証明は「refined 頂点は debt 相であるか
`anchor = localMeasure` を満たす」という二分に依存しており、normal 相を仮定して前者を潰している。
つまり**debt 相はこの防御の外**である。`exists_phaseSearchProgress_parent` の捏造(anchor を
一つ上げた親をでっち上げる操作)は、子が debt 相であれば refined domain の内側で完結してしまう。
非捏造性の主張は normal 相限定と訂正された。

## regeneration 仮定の空虚性

### `probe_blockedFirstOccurrence_thirteen` (L202)

**主張:** 実軌道は blocked first occurrence を含む: `BlockedFirstOccurrence 13 6`。

**証明:** 三つのフィールドを計算で確認する。`a 6 = 13` であり 13 は時刻 6 が初出である
(軌道は 0, 1, 3, 6, 2, 7, 13, … と進む)。clock 条件は `6 + 1 = 7 < 13`。
そして時刻 7 の減算候補は `13 - 7 = 6` だが、これは `a 3 = 6` として既に履歴にあるので
減算は失敗する。すべて `decide` で決定できる有限計算である。

### `probe_not_blockedFirstOccurrence_regeneration` (L214)

**主張:** 一様 regeneration 仮定
「任意の blocked first occurrence `(value, time)` とその減算欠損 `value - (time+1)` の初出時刻
`earlier` に対し、`(value - (time+1), earlier)` もまた blocked first occurrence である」
は**偽**である。

**証明:** この仮定を認めると `blockedFirstOccurrence_impossible_of_regeneration` により
blocked first occurrence は一つも存在しないことになるが、前定理が `(13, 6)` を与える。矛盾。

**帰結:** `blockedFirstOccurrence_impossible_of_regeneration` と、そこから引かれた二つの replay 系
(`minimum_predecessor_canSubtract_of_regeneration`、
`minimum_predecessor_doubleSubtract_of_regeneration`)は、いずれも**仮定が偽なので空虚に真**である。
第七十ラウンドで「witness 下降の残余義務を型で固定した」と位置づけられていたが、その位置づけは
**撤回された**。固定されていたのは実現不可能な条件であり、残余義務は何も減っていない。

## 全体の中での位置づけ

証明地図(`docs/PROOF_MAP.md`)では「忘却形の自明性(強形)」「debt 相の anchor bump」
「`regenerate` 仮定の空虚性」の三行がすべて本モジュールを典拠としている。上流は
`RefinedSemanticOutcome`(忘却形と normal 相 anchor 防御)、`LandingRevisitTransport`
(landing 輸送版の頂点定理)、`ReplayWitnessDescent`(regeneration 仮定)である。
下流に定理を供給するモジュールではない。役割は、頂点定理の disjunction をそのまま
消費してはならないこと、非捏造性の防御が相ごとに限定されること、regeneration 系の
三定理を成果として数えてはならないことを、型で固定して残すことにある。
第八十一ラウンドの敵対的再検査で**偽の定理・`sorry`・禁止機構は一つも見つからなかった**点も
併せて記録しておく。見つかったのはすべて「statement が意図した情報を運んでいない」型の欠陥であり、
それを probe として形式化したのがこのファイルである。
