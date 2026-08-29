# RefinedReplayInterface

**役割:** 生成証明書を同梱した精密版semantic辺`RefinedSemanticEdge`を落とさないまま、terminal interfaceからtarget出現枝を除いて三形へ縮約する。実質はtarget出現を`target_missing`で潰す一行であり、残りは精密版ペイロードを頂点まで運ぶための型の付け替えである。

## このモジュールの役割

本モジュールは`PermanentAboveCorridorReplayInterface.lean`の精密版であり、そこで確定した三形interface(history辺・semantic辺・exact replay固定点)のうち**semantic枝のペイロードだけ**を差し替える。差し替え前の形は「どこかに比較元`stepParent`があり、そこから位相ランクの下がる子`child`への厳密な探索辺がある」という広いものだった。この形が情報量ゼロであることは第七十一ラウンドに判明している。頂点定理のsemantic枝は`0 < target`だけから導出でき、`PhaseSearchProgress`は四成分の辞書式順序にすぎず`stepParent`が存在量化されているだけなので、anchorを一つ上げた親をいつでも捏造できるからである。第七十六〜七十八ラウンドで構成された`RefinedSemanticEdge`(`RefinedSuccessorRank.lean`)は、辺を生んだpermanent-tail証明書――軌道が以後ずっとtargetを上回り続ける状況を記述するdischarge証明書またはcombined証明書――を各コンストラクタに同梱することで、この捏造を構造的に封じている。段3である本モジュールの仕事は、その同梱物を落とさないことに尽きる。**ここに新しい数学はない。実質的な内容は`target_occurs`枝を`target_missing`で潰す一行だけで、他はすべて型の付け替えである。**

にもかかわらず段を独立に用意する理由ははっきりしている。`RefinedSemanticEdge`から証明書を忘れて、「両端点がrefined domain(精密化された再帰の定義域、`OrbitReadyRefinedInvariant`を満たすノードの集まり)に属する厳密な探索辺が存在する」という忘却形`RefinedDomainEdge target`へ落とすと、その命題は`0 < target`だけから作れてしまう。canonical start自身がrefined nodeであり、そこでrefined stepが局所全域だからである(`RefinedSuccessorRank.lean`の`occurs_or_refinedDomainEdge_of_pos`)。さらに強い形として`TrivialityProbe.lean`の`probe_refinedDomainEdge_of_pos`は、実軌道の二状態を共通horizonへ載せるだけで同じものを作り、`LeastMissingTarget`(最小未出target)の仮説すら使わない。したがって頂点へ登る途中のどの一段であれ、忘却形へ潰した瞬間に、精密化が取り除こうとしていた欠陥そのものが復活する。段ごとにoutcome型を一つ複製するという見た目の冗長さは、この復活を型のレベルで禁止するための代価である。この意味で本モジュールは「証明」ではなく「配管」であり、そう書くのが正確である。

## 主要な定義

### `RefinedTerminalMissingOutcome` (L23)

missing-target permanent tailから得られるterminal情報の三形。非精密版`PermanentTailTerminalMissingOutcome`と同じく、target出現枝を持たない。

- `history_progress`: 第八十二ラウンドで強化された`TerminalChronologyHistoryProgress target childTime parentTime`を逐語的に運ぶ。これは「履歴予算`missingBelowCount`(target未満でまだ出現していない値の個数)の厳密な下降」と「`TerminalHistoryCursor target (parentTime + 1)`」の連言である。後者のcursor成分は、parent cursorの手前にtargetを超える時刻があり、それがtail最小値の数値的前任であって、target以下の値はすべてtail開始より前に出現している、という軌道側の内容を指す。
- `refined_semantic`: `RefinedSemanticEdge target start`。生成した証明書を保持したままのsemantic辺。
- `exact_replay`: descendantのparent node、その`PermanentTailDischargeReturnCertificate`、および`TerminalExactDischargeReplayCertificate`。これはdischarge反復ランクが動かない停留(replay固定点)であり、return crossingがold crossingと一致する閉cycleになる形である。

非精密版との差は`refined_semantic`コンストラクタ一つだけである。history枝とreplay枝は文字どおり同一の型を持ち、証明でも素通しされる。

## 定理と証明

### `PermanentTailCombinedCertificate.refinedTerminalMissingOutcome` (L43)

**主張:** permanent-tail combined証明書からは、強化されたhistory辺、証明書を保持した精密semantic辺、exact replay固定点のいずれかが得られる。

**証明:** 段2の`PermanentTailCombinedCertificate.refinedTerminalReplayReducedOutcome`(`RefinedIterationClosure.lean`。installed successor反復をdischarge反復ランクの整礎再帰で消費し終えた四形)を場合分けする。四枝のうち本質的に処理されるのは`target_occurs`だけである。この枝が与える出現witness `⟨witness, value_eq⟩`は、combined証明書のtail成分が保持する`target_missing`――この解析全体が「全軌道で出現しない最小の値」という仮想反例の内部で行われているという前提――に直接矛盾するので、`False.elim`で消える。残る`history_progress`・`refined_semantic`・`exact_replay`は、対応するconstructorへそのまま移送する。

証明の内容はこれで尽きている。数学的に確認すべきことは一点しかない: 移送の際に`refined_semantic`のペイロードが`RefinedSemanticEdge target start`のまま保たれ、`RefinedDomainEdge target`へ落ちていないこと。上に述べたとおり忘却形は`0 < target`から無料で作れるので、この一点を守ることだけが段3の主張である。

なお、この段では非精密版で示したreplay剛性の二定理(`crossingTime_unique`と`anchor_value_unique`。同一discharge上の相異なるreplay証明書は、blockerのprovenanceでは異なり得てもcrossing時刻とanchor値では一致する)を再証明していない。本モジュールは`PermanentAboveCorridorReplayInterface.lean`をimportしており、`exact_replay`枝の型も同一なので、剛性はそのまま流用できるからである。

## 全体の中での位置づけ

本モジュールは、semantic枝の精密版outcomeを頂点へ伝播する8段チェーン(`RefinedSuccessorRank` → `RefinedIterationClosure` → **`RefinedReplayInterface`** → `RefinedHistoryLanding` → `RefinedLandingHorizon` → `RefinedLandingMount` → `RefinedMountedIteration` → `RefinedFixedPointCore`)の段3である。上流は段2の`RefinedIterationClosure.lean`と、非精密版の三形interfaceを与える`PermanentAboveCorridorReplayInterface.lean`。下流は段4の`RefinedHistoryLanding.lean`で、そこではhistory枝が具体的なfresh landingとそのcursor・restart crossingへ強化される。証明地図(docs/PROOF_MAP.md)では「精密版の伝播」の行に対応する。

この伝播は第八十五ラウンドで段8まで到達し、精密版の頂点定理`LeastMissingTarget.refinedSemanticEdge_or_flooredCore`(`RefinedFixedPointCore.lean`)として結実した。左枝が`RefinedSemanticEdge`、右枝が`32 ≤ crossingTime ∧ 19 ≤ target`の固定点coreである。左枝が捏造不能であることは`RefinedSemanticEdge.target_missing`で示されている: 二つのコンストラクタがどちらもpermanent-tail証明書を保持しているので、この命題は単独で`¬ ∃ t, a t = target`を含み、`target = 1`で即座に反証される。したがって`probe_refinedDomainEdge_of_pos`と同型の空虚化攻撃は構造的に不可能になった。

ただし留保も明示しておく。排除できたのは「`0 < target`だけからの導出」であって、「`LeastMissingTarget`から無条件に出てしまわないか」は排除していない。手で追う限りそれは`mounted_crossing`枝の`a crossingTime < mountedParent.anchorParent`という実軌道のanchor下降を作ることに帰着し、固定点解析が現に格闘している内容そのものなので無料である見込みは薄いが、証明されてはいない。もし出てしまえば右枝が到達不能になり、頂点定理はふたたび情報量を失う。本モジュールの段は、その検証を可能にする形で証明書を運び切るための一段である、というのが正確な位置づけである。
