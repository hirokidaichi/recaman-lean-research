# RefinedSuccessorRank

**役割:** 頂点まで届く8段チェーンの第1段。terminal dischargeの分類結果のうちsemantic枝だけを、親を存在量化しない四つの名前付き枝と、生成した証明書を同梱する`RefinedSemanticEdge`へ置き換える。同時に、四枝を忘却した`RefinedDomainEdge`が`0 < target`だけから作れることを本モジュール自身で証明し、忘却形を伝播ペイロードにしてはならない理由を型の水準で固定する。

## このモジュールの役割

`PermanentAboveCorridorSuccessorRank.lean`の`PermanentTailTerminalIterationOutcome`は、頂点定理へ実際に到達するチェーンの先頭段でありながら、semantic枝として広義の`semantic_progress`を運んでいた。そのペイロードは「存在量化されたstep parentの下にある`PhaseSemanticInvariant`な子」であり、第七十一ラウンドの検査で**両半分とも捏造可能**であることが判明している。任意のnodeのanchor成分を1だけ上げれば厳密に大きい親が作れる(`exists_phaseSearchProgress_parent`)し、正のtargetには常にcanonicalなsemantic nodeがある(`exists_phaseSemantic_start`)。つまりこの枝は頂点まで生き残るが、何も運んでいない。

本モジュールは既存の宣言を一切変更せず、同じ段を**精密版の枝**で並置する。精密化の核心は二点である。(i) 子が広義`PhaseSemanticInvariant`ではなくrefined domain `OrbitReadyRefinedInvariant`(制限付きoracle再帰の正当な出発点になれる領域)に属する。(ii) **親を存在量化しない。** 四つのsemantic枝はそれぞれ、証明書自身のclock(`downTime + 2`、blocker初出`firstTime - 1`、選択crossing時刻)から決まる名前付きノードを親に固定する。anchor bumpによる捏造がここで詰まるのは、これらの名前付きノードがすべて`⟨horizon, a t, .normal, a t⟩`という形、すなわちanchorと局所測度が同じ軌道値である形をしており、anchorだけを1上げるとrefined domainの構造署名`OrbitReadyRefinedInvariant.debt_or_anchor_eq_local`を破るからである。

ただし**限界を隠さない。** 四枝を忘却した`RefinedDomainEdge target`(両端がrefined domainに属する厳密phase辺が存在する、という命題)は捏造可能である。それを本モジュールの冒頭2定理が自ら示す。従って設計方針は「下流は可能な限り精密版のまま扱い、忘却(`toRefinedDomainEdge`)は制限付きoracle再帰への最終接続点でだけ使う」となる。

## 主要な定義

### `RefinedTerminalSemanticStep` (L63)

一つのterminal discharge証明書`source`(親node `parent`上)に紐づく、四つの親固定semantic枝。どの枝も「親ノード名 + そこへ入る子 + 子のrefined domain所属証明 + 厳密な`PhaseSearchProgress`辺」という同じ形をしており、異なるのは親をどのclockから作るかだけである。

- `immediate`: 即時谷(downcrossの2ステップ後に`a(downTime+2) = a(downTime)+1`で閉じる歴史的valley)の枝。親は`terminalHistoricalPredecessorNode parent (source.downTime + 2)`、すなわち親のhorizonの上に値`a(downTime+2)`を載せたノードで、その`ExtendedHistoryNormalInvariant`(歴史的代表値をhorizonに格納した正規ノード)を代表として同梱する。
- `early`: 外側historical blocker証明書付きの枝。親は`terminalHistoricalPredecessorNode parent (firstTime - 1)`、代表は同じくextended-history形。
- `ready`: 同じくblocker付きだが、親は`terminalCurrentPredecessorNode (firstTime - 1) = ⟨firstTime-1, a(firstTime-1), .normal, a(firstTime-1)⟩`という**現在状態**ノードで、代表は自分自身のclockでtarget-readyな`OrbitReadyNormalInvariant`。
- `crossing`: 親はdischarge親`parent`そのもの、子は選択crossingノード`terminalPredecessorCrossingNode parent crossingTime`。

### `RefinedSemanticEdge` (L111)

チェーンを昇っていくペイロード本体。添字は`(target, start)`だけで親nodeを含まないので、下流の各段でarity追随が起きない。二つのconstructorを持つ。

- `discharge_step`: discharge親・discharge証明書・上記`RefinedTerminalSemanticStep`の三つ組。
- `mounted_crossing`: mounted親・combined証明書・`ReadyCrossingSearchInvariant`なcrossing子・anchor下降のprogress辺。これは第1段では生成されない。semantic子を**新規生成**する唯一の箇所が第7段`RefinedMountedIteration.lean`のanchor下降枝なので、その形をここで先行して用意してある(第七十八ラウンド)。

どちらのconstructorもpermanent-tail証明書を保持する。これが「positivityだけからは作れない」ことの根拠になる。

### `RefinedTerminalIterationOutcome` (L167)

`PermanentTailTerminalIterationOutcome`の精密版。五つのconstructorのうち`semantic_progress`だけが`refined_semantic (step : RefinedTerminalSemanticStep source)`へ差し替わり、`target_occurs`・`history_progress`・`iteration_progress`(installed successor dischargeと三成分rankの厳密下降)・`exact_replay`(rankが等式として不動の完全再生証明書)はペイロードを逐語的に保つ。

## 定理と証明

### `occurs_or_refinedDomainEdge_of_pos` (L38)

**主張:** `0 < target`なら、targetが出現するか、`RefinedDomainEdge target`が成り立つ。

**証明:** `exists_targetStartNode`が正のtargetに対しcanonical startノードを与える。それは`TargetStartInvariant`を経て`OrbitReadyNormalInvariant`であり、`OrbitReadyNormalInvariant.refinedStep`(第八十ラウンドで仮定ゼロになった局所全域定理)はそこから「targetの出現、またはrefinedな子への厳密辺」を無条件に出す。前者なら出現、後者ならstart自身を親、その子を子とするrefined辺が完成する。permanent-tail解析は一切使っていない。

### `LeastMissingTarget.refinedDomainEdge` (L50)

**主張:** 最小未出target(全軌道で出現しない最小値)は無条件に`RefinedDomainEdge target`を持つ。

**証明:** L38を`target_pos`に適用し、出現枝を`target_missing`で潰すだけである。**これは前進ではなく否定的結果である。** 忘却形は頂点のdisjunctとして無価値であり、それを含む`historyEdge_or_refinedEdge_or_installedEdge`は空文になる。第八十一ラウンドの敵対的再検査はさらに強い経路(`TrivialityProbe.lean`の`probe_refinedDomainEdge_of_pos`)を与えており、そちらは`exists_targetReady_state_of_pos`を二度使って共通horizon上に二つのextended-history正規ノードを並べるだけで、`LeastMissingTarget`仮説も`refinedStep`も要らない。

### `RefinedTerminalSemanticStep.toRefinedDomainEdge` (L132)

**主張:** 四つの親固定枝はいずれも忘却形の辺を与える。

**証明:** 枝ごとに親のrefined domain所属を指定するだけである。`immediate`と`early`は代表がextended-history成分、`ready`は代表がready-current成分、`crossing`は親がdischarge親自身で、その所属は`parent_orbitReadyRefined`(permanent-tail crossing証明書がそのままready crossing recoveryである)から来る。doc commentが明記するとおり、**この関数は最終接続点でだけ使うべきものである。** チェーンを昇る途中で忘却すれば、L38が示した欠陥がそのまま復活する。

### `RefinedSemanticEdge.toRefinedDomainEdge` (L150)

**主張:** 辺の水準でも同様に忘却できる。

**証明:** `discharge_step`はL132へ委譲する。`mounted_crossing`は両端点をcrossing成分に置く: 親はcombined証明書の`ready_crossing.crossing`、子は同梱された`ReadyCrossingSearchInvariant`の`crossing`成分である。

### `PermanentTailDischargeReturnCertificate.refinedTerminalIterationOutcome` (L198)

**主張:** すべてのterminal dischargeは、target出現・history予算の厳密下降・**親固定のrefined semantic step**・iteration rankを厳密に下げるsuccessor discharge・exact replay固定点、のいずれかである。

**証明:** 非精密版と同じく`terminalFiniteClosedOutcome`(finite数値枝が排除済みのtotal outcome)で場合分けするが、semantic枝は**再包装ではなく独立に再分類する**。すなわち、元の分類がその場で作った広義semantic stepは捨て、同じ地点で既に手に入っていたrefinedな局所stepを取り直す。

*history_progress*はそのまま移送する。

*immediate_semantic*では元の経路が使えない。元の`canonicalCoverage_phaseSemantic`は`target ≤ downTime + 3`を要求するが、valley証明書からその時計は出ない(第七十六ラウンド)。そこで`exists_coordinatesAt`で時刻`downTime + 2`の座標を取り、`immediateValley_extended`で同じ値`a(downTime+2)`を**親のzero-budget horizonへ**格納したextended-history代表を作る。horizon側のtarget readinessはdischarge親のready crossingが持っているので、時計条件が代表のclockから親のhorizonへ移る。あとは`refinedStep`が出現かrefinedな子を返す。

*historical_complete*の`early_step` / `ready_step`では、元の分類が既に`EarlyRepresentativeCertificate` / `OrbitReadyNormalCertificate`を持っている。その`refinedStep`を呼び直せば広義stepではなくrefinedな子が得られる。親は前者がhistorical predecessorノード、後者がcurrent predecessorノードで、いずれも証明書のclock `firstTime - 1`から一意に決まる。

`below_master`枝の議論は非精密版と同じである。旧crossingのeligibility `downTime + 1 ≤ oldCrossingTime`で二分し、非eligibleなら`missingBelowCount_strict_of_firstAt`によるhistory予算の厳密下降、eligibleなら`crossingRankOutcome`で二分する。`refined_progress`は選択crossingのrefined証明書をそのまま`crossing`枝へ渡す(非精密版が`toPhaseSemanticInvariant`で弱めていた一行が消える)。`anchor_growth`ではinstallとsuccessor dischargeを作り、anchorの厳密増加・anchor同値かつcrossingが早い・両方とも親を再現、の三分岐で`iteration_progress`二つと`exact_replay`一つを返す。

この三分岐は非精密版と**逐語的に同一のコピー**である。SuccessorRank段が純粋な再包装ではなく`terminalFiniteClosedOutcome`から独立に再分類しているため、精密化と無関係な部分まで書き写す必要が生じた(第七十八ラウンド)。以降の段は再包装なのでこの重複は起きない。

## 精密化の限界(明示)

- **非捏造性が確実なのは、親を固定した各constructorであって忘却形ではない。** 忘却形が自由であることは本モジュールのL50で、さらに強い形で`TrivialityProbe.lean`で証明済みである。
- anchor bumpに対する防御`refinedNormal_anchorBump_not_orbitReadyRefined`は`node.phase = .normal`を要求する。**debt相はこの防御の外にある。** `DebtInvariant.value_lt_anchor`はanchorを上げても保たれるので、refined debtノードはanchor bumpの後もrefined domainに留まる(第八十一ラウンドの訂正)。本モジュールが固定する四つの親はすべてnormal相なので防御は効くが、「refined domainならanchor bumpが必ず外れる」という一般命題は偽である。
- `RefinedSemanticEdge`が自由でないことは第8段`RefinedFixedPointCore.lean`の`RefinedSemanticEdge.target_missing`で確定するが、その根拠は「同梱されたtail証明書が既に『targetは出現しない』を含意する」ことである。非自明性には(i)親固定とrefined domain所属という構造的内容と、(ii)証明書同梱という書誌的内容の二層があり、probe(`not_forall_pos_exists_refinedSemanticEdge`)が反証しているのは(ii)の水準である。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「精密版semantic枝の伝播」チェーンの第1段である。上流は`RefinedSemanticOutcome.lean`(親固定四枝と非捏造性三定理、`immediateValley_extended`)と`PermanentAboveCorridorSuccessorRank.lean`(discharge-level三成分rank、exact replay証明書)。下流は第2段`RefinedIterationClosure.lean`が本モジュールの`refinedTerminalIterationOutcome`を整礎帰納で反復して`iteration_progress`枝を消去し、以降ReplayInterface・HistoryLanding・LandingHorizon・LandingMount・MountedIteration(`mounted_crossing`の生成点)を経て、第8段`RefinedFixedPointCore.lean`の頂点`LeastMissingTarget.refinedSemanticEdge_or_flooredCore`へ至る。全段を通じて`RefinedSemanticEdge`のまま運ばれ、忘却形へ落とすのは制限付きoracle再帰へ接続する最終地点だけである。
