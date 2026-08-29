# RefinedHistoryLanding

**役割:** 精密版semantic辺を保持したまま、history枝を「target未満の値のfresh landing・その時刻へ輸送されたhistory cursor・そこからのcanonical restart crossing」を同梱したanchored形へ強化する。写経が要ったのはlanding復元の6行だけである。

## このモジュールの役割

本モジュールは`PermanentAboveCorridorHistoryLanding.lean`の精密版であり、段3(`RefinedReplayInterface.lean`)が確定した三形interfaceのうち、history枝を具体的な素材へ開き直す。非精密版で確立済みの観察がそのまま使える: 履歴予算`missingBelowCount`(target未満でまだ出現していない値の個数)の厳密な下降は抽象的な大小関係ではなく、常に明示的なwitnessを伴う。すなわちchild cursorまでには出現しているがparent cursorまでには出現していないtarget未満の値が必ず存在し、その初出時刻は二つのcursorの間の窓に厳密に入る。landingの値はtarget未満なので、canonical upcrossing機構(target未満の点から最初のweak upcrossingを取る存在定理)がそこから再起動でき、外側再帰がhistory辺を越えて継続するのにちょうど必要なデータが揃う。

段4で新たに取り込んだのは、第八十二ラウンドで行われたlanding側の強化である。`TerminalChronologyHistoryProgress target childTime parentTime`の定義自体が、素の予算下降`TerminalHistoryBudgetDrop`と`TerminalHistoryCursor target (parentTime + 1)`の連言へ強められた。cursor成分は「parent cursorの手前にtargetを超える時刻`cursorTime`があり、その値がtail最小値の数値的前任であり(`a cursorTime + 1 = a minimumTime`)、target以下の値はすべてtail開始より前に出現している」という軌道側の内容である。この強化を受けて、anchored outcomeも`landing_cursor`を運ぶ形になった。本モジュールで新しく作るものは何もなく、上流の`progress.exists_freshLandingCursor`が返す5成分目をそのまま受けて詰め直すだけである。**semantic枝とreplay枝は段3と同じく素通しで、精密版ペイロード`RefinedSemanticEdge`は忘却形へ落とさずに保たれる。**

設計上の要点を一つ記録しておく価値がある。第八十二ラウンドの強化は当初「コンストラクタに2フィールド追加」で行われるはずだったが、実際には型`TerminalChronologyHistoryProgress`の定義そのものを連言へ強める形になった。この型は`(target childTime parentTime)`という三つの自然数だけで添字付けされており、辺を生成した証明書に依存しない(source-free)。そのおかげで、生成点で供給された情報が下流へ運ばれる際に追加のNat引数も証明書の添字も現れず、段4から段8までの伝播が**arity追随を一切起こさずに**通った。もし強化が`source`依存の添字を持ち込んでいたら、6段すべてのoutcome型とその場合分けを機械的に書き直す必要があった。型を「どこで作られたか」ではなく「何を主張するか」だけで添字付けしておく設計判断が、そのまま伝播コストの差になっている。

## 主要な定義

### `RefinedTerminalAnchoredOutcome` (L21)

anchored interfaceの精密版。三コンストラクタを持つ。

- `fresh_landing`: 元の`TerminalChronologyHistoryProgress`に加えて、landing値`value`・landing時刻`landingTime`・restart crossing時刻`nextCrossingTime`、`value < target`、窓条件`parentTime < landingTime ≤ childTime`、landingの初出性`FirstAt a value landingTime`、landing時刻からの`FirstWeakUpcrossingStep target landingTime nextCrossingTime`(canonical restart crossing)、そして`TerminalHistoryCursor target landingTime`。最後の`landing_cursor`が段4で追加された成分であり、cursorがparent cursorの直後からlanding時刻まで輸送されたことを表す。
- `refined_semantic`: `RefinedSemanticEdge target start`。証明書を保持した精密semantic辺をそのまま運ぶ。
- `exact_replay`: descendantのparent node、その`PermanentTailDischargeReturnCertificate`、および`TerminalExactDischargeReplayCertificate`(discharge反復ランクが動かない停留、replay固定点)。

非精密版`PermanentTailTerminalAnchoredOutcome`との差は、二番目のコンストラクタが広い`semantic_progress`(存在量化された比較元と`PhaseSemanticInvariant`だけを持つ形)ではなく`refined_semantic`である一点のみである。

## 定理と証明

### `PermanentTailCombinedCertificate.refinedTerminalAnchoredOutcome` (L48)

**主張:** missing-target interfaceはanchorする。すべての枝が、証明書付きの精密semantic辺、replay固定点、または具体的なfresh landing(そのcursorとrestart crossingを伴う)のいずれかを外側再帰へ渡す。

**証明:** 段3の`refinedTerminalMissingOutcome`(三形)を場合分けする。`refined_semantic`枝と`exact_replay`枝はペイロードを一切変えずに移送する。

実質的な作業はhistory枝だけである。まず上流の`TerminalChronologyHistoryProgress.exists_freshLandingCursor`(`PermanentAboveCorridorHistoryLanding.lean`)を適用して、landing値`value`、landing時刻`landingTime`、`value < target`、`parentTime < landingTime`、`landingTime ≤ childTime`、`FirstAt a value landingTime`、および`TerminalHistoryCursor target landingTime`の7成分を得る。この補題の中身は二段構えで、(i) 予算の厳密下降から、childの履歴に属しparentの履歴に属さないtarget未満の値`v`を境界についての帰納法で取り出し、履歴の元は必ず初出時刻を持つという事実からその初出`u`を得て、`u ≤ parentTime`だと非所属に矛盾するので`parentTime < u`を結論する、(ii) cursor成分は`parentTime + 1 ≤ landingTime`なので単調性`TerminalHistoryCursor.mono`で境界を`landingTime`まで押し上げる、というものである。段4で追加になったのは(ii)の1行分の情報を受け取ることだけで、証明の側では第5成分を受けるパターンが一つ増えるにすぎない。

次に、`FirstAt`の値等式から`a landingTime = value < target`、すなわちlanding時刻の軌道値がtargetを下回ることを得る。combined証明書のtail成分が持つtargetの正値性とあわせて`exists_firstWeakUpcrossingStep_from_below`(`PermanentAboveCanonical.lean`)を適用し、landing時刻からの最初のweak upcrossing `nextCrossingTime`を得る。全成分を`fresh_landing`へ詰めて終了する。

landingはtarget未満の実軌道点なので、これはcanonical corridor機構(fresh below点 → 最初のupcrossing → crossing node)の再起動条件そのものであり、history辺の先で解析を継続するための入口が型として確保されたことになる。この議論は非精密版と一字一句同じであり、精密版で増えた負担はlanding復元の6行の写経だけだった、というのが第八十三ラウンドの実測である。

## 全体の中での位置づけ

本モジュールは、semantic枝の精密版outcomeを頂点へ伝播する8段チェーン(`RefinedSuccessorRank` → `RefinedIterationClosure` → `RefinedReplayInterface` → **`RefinedHistoryLanding`** → `RefinedLandingHorizon` → `RefinedLandingMount` → `RefinedMountedIteration` → `RefinedFixedPointCore`)の段4である。上流は段3の`RefinedReplayInterface.lean`、非精密版の`PermanentAboveCorridorHistoryLanding.lean`(landing復元とcursor輸送の本体)、および`PermanentAboveCanonical.lean`(最初のweak upcrossingの存在)。下流の段5`RefinedLandingHorizon.lean`は、missing-target反例ではtarget未満の全値がtail開始までに出現済みであることを使ってlanding時刻をtail開始前へ束縛し、restart crossingが`crossing + 1 ≤ start < parent.horizon`という履歴内境界を満たすことを示す。証明地図(docs/PROOF_MAP.md)では「精密版の伝播」の行に対応する。

伝播そのものは第八十五ラウンドで段8まで到達し、精密版の頂点定理`LeastMissingTarget.refinedSemanticEdge_or_flooredCore`(`RefinedFixedPointCore.lean`)が得られている。左枝がpermanent-tail証明書を保持する`RefinedSemanticEdge`、右枝が`32 ≤ crossingTime ∧ 19 ≤ target`の固定点coreである。写経が必要だったのは段5のhorizon評価(約25行)と段7のanchor gap強帰納(約55行)だけで、本モジュールを含む残り6段は事実上の再包装だった。上に書いた`TerminalChronologyHistoryProgress`のsource-free性が、この安さの直接の理由である。

限界も隠さず記しておく。この伝播チェーンが運んでいるsemantic枝は、非精密版では`0 < target`だけから作れる空の枝だった(第七十一ラウンド)。精密版はその情報量を回復する試みであり、実際に左枝の捏造不能性は`RefinedSemanticEdge.target_missing`によって示された(両コンストラクタが証明書を保持するので単独で`¬ ∃ t, a t = target`を含み、`target = 1`で反証される)。しかし排除されたのは「`0 < target`からの導出」だけであって、「`LeastMissingTarget`から無条件に出てしまわないか」は未解決である。もしそれが出れば右枝が到達不能になり、頂点定理はふたたび情報量を失う。本モジュールの段が保証しているのは、その検証が可能な形でペイロードが頂点まで運ばれる、ということまでである。
