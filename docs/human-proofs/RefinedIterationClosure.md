# RefinedIterationClosure

**役割:** 精密版チェーンの第2段。discharge-level三成分rankの整礎性による強帰納法をそのまま反復し、installed successorの反復constructorを消去する。第1段と違うのは、semantic出口で「どのdischargeがその辺を生成したか」を捨てずに`RefinedSemanticEdge`として記録する一点だけである。

## このモジュールの役割

`PermanentAboveCorridorIterationClosure.lean`の`terminalReplayReducedOutcome`は、installed successor(選択crossingを新しい親としてinstallし、その上でhistorical dischargeを再構成した次の解析対象)の反復を整礎帰納で食い尽くし、terminal解析を「target出現・strict history辺・semantic位相辺・あるdescendant discharge上のexact replay固定点」の四形へ縮約した。しかしそのsemantic枝は広義の`(stepParent, child, PhaseSemanticInvariant, PhaseSearchProgress)`であり、**帰納の各ステップで足元にあったdischarge証明書を捨てている**。第七十一ラウンドが示したとおりこの四つ組は`0 < target`だけから捏造できるので、四形のうちsemantic枝は情報量ゼロのまま頂点へ運ばれることになる。

本モジュールは同じ再帰を、第1段`RefinedSuccessorRank.lean`の証明書同梱ペイロードで繰り返す。**再帰そのものは元と同一である。** strict iteration辺は輸送可能な三成分

```text
terminalDischargeIterationRank = (missingBelowCount target parent.horizon,
                                  target − parent.anchorParent,
                                  source.oldCrossingTime)
```

を辞書式に下降し、その順序は自然数のlexとして整礎であり、exact replay固定点は全構成chainを保ったまま出口になる。変わるのはsemantic constructorだけで、記録の追加に新しい数学は要らない。これは「記録を捨てなくても再帰は回る」という主張であり、逆に言えば非精密版が情報を落としていたのは必要に迫られてではなかった、ということでもある。

## 主要な定義

### `RefinedTerminalReplayReducedOutcome` (L26)

反復constructorを持たないterminal outcome。添字は`(target, start)`だけで、親nodeを含まない。四つのconstructorを持つ。

- `target_occurs`: `a(witness) = target`という実出現。
- `history_progress`: `TerminalChronologyHistoryProgress`。第八十二ラウンドの強化により、これは単なる予算下降ではなく`TerminalHistoryBudgetDrop`と`TerminalHistoryCursor target (parentTime + 1)`の連言である。この型が`source`に依存しない`(target, childTime, parentTime)`だけで添字付けられているおかげで、精密版の伝播でarity追随が一切発生していない。
- `refined_semantic`: `RefinedSemanticEdge target start`。すなわちdischarge親・discharge証明書・親固定の四枝(`RefinedTerminalSemanticStep`)の三つ組か、mounted crossing形か。生成元の証明書がここに残る。
- `exact_replay`: 停止したdescendantのparent node、そのdischarge証明書、および`TerminalExactDischargeReplayCertificate`(installed successorが親のanchorを同じcrossing cursorで再生産し、rankが等式として不動であることを、blocker・below predecessor・選択crossing・install・次dischargeの全構成chainとともに保持する構造)。

`exact_replay`と`history_progress`のペイロードは非精密版と逐語的に同一である。

## 定理と証明

### `PermanentTailDischargeReturnCertificate.refinedTerminalReplayReducedOutcome` (L48)

**主張:** 任意のterminal dischargeから出発して、strict iteration辺に沿った再帰はすべてのinstalled successor枝を消費する。生き残るのはtargetの出現、strict history辺、**生成元の証明書を伴うrefined semantic辺**、またはexact replay固定点である。

**証明:** 内部補題「任意のrank値`rank`と、そのrankを持つ任意の親node上の任意のdischarge証明書について結論が成り立つ」を、三成分lex順序の整礎性`natTripleLex_wellFounded`に対するaccessibility帰納法で示す。与えられたdischarge `node`(親`parentNode`上)に第1段の完全分類`refinedTerminalIterationOutcome`を適用し、五枝を処理する。

- `target_occurs`・`history_progress`はそのまま対応するconstructorへ移送する。
- `refined_semantic step`枝が本モジュールの実質である。非精密版はここで`(stepParent, child, semantic, progress)`の四つ組だけを渡し、いま足元にある`parentNode`と`node`を捨てていた。精密版は`.discharge_step parentNode node step`として**その二つを一緒に格納する**。結論の型が`(target, start)`のみに添字付けられており、証明書は構成子の内側で束縛されるので、この記録は再帰の合流を妨げない。
- `iteration_progress`枝では、successor discharge `next`が`TerminalDischargeIterationProgress`、すなわち三成分rankのstrictなlex下降を伴う。rankの等式`hrank`で書き換えれば帰納法の仮定がそのまま適用でき、`next`に対する結論が親に対する結論になる。successorの親nodeは元と異なる(installed node `terminalPredecessorCrossingNode parent crossingTime`)が、outcomeの型が特定の親に依存しないため、異なるnode上の再帰がそのまま合流する。cursor記録`next_old_eq`はここでは使わない。それは第1段でrank下降を作る際に既に消費されている。
- `exact_replay`枝では、現在のdischarge自身が停止点なので、その親・discharge・replay証明書を格納して終了する。

最後に元の`source`のrankで内部補題を起動する。第一・第二成分がtarget以下で有限なので、strict下降は有限回しか続かない。したがって「どのdischargeから始めても、有限回のinstalled successorの後に四形のいずれかへ到達する」が結論である。

### `PermanentTailCombinedCertificate.refinedTerminalReplayReducedOutcome` (L83)

**主張:** 任意のcombined permanent-tail obstruction(tail本体・zero-budget crossing・tail最小値blockerの束)は初期dischargeを持つので、そのsuccessor反復全体が同じ四形へ縮約される。

**証明:** `exists_dischargeReturnCertificate`で初期dischargeを取り、L48を適用するだけである。

## 到達点と限界

得られたのは「仮想反例 → combined証明書 → 有限回のterminal反復 → 四形(semantic枝は証明書付き)」である。第七十一ラウンドで暴かれた欠陥のうち、**この段で塞がったのは「semantic出口で証明書を落とす」という伝播側の穴だけ**であり、精密化そのものの限界は第1段のまま持ち越される。

- 忘却形`RefinedDomainEdge`は`0 < target`だけから作れる(第1段`occurs_or_refinedDomainEdge_of_pos`、およびより強い`TrivialityProbe.lean`の`probe_refinedDomainEdge_of_pos`)。従って本段の`refined_semantic`枝を下流で`toRefinedDomainEdge`に落とせば、その瞬間に情報はゼロに戻る。忘却は最後の接続点でだけ行う。
- anchor bumpに対する防御は`node.phase = .normal`限定であり、**debt相は防御の外にある**(第八十一ラウンドの訂正)。
- `RefinedSemanticEdge`が捏造不能であることは第8段の`RefinedSemanticEdge.target_missing`で確定するが、その直接の根拠は同梱されたtail証明書が既に「targetは出現しない」を含意することである。この段が保証しているのは「記録が生き残る」ことであって、記録の中身が外側の再帰で消費できることではない。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「精密版semantic枝の伝播」チェーンの第2段である。上流は第1段`RefinedSuccessorRank.lean`(親固定四枝・`RefinedSemanticEdge`・精密版iteration outcome)と`PermanentAboveCorridorIterationClosure.lean`(整礎帰納の原型)、および`PermanentAboveCycleExit.lean`(combined証明書からの初期discharge)である。下流は第3段`RefinedReplayInterface.lean`が`target_occurs`枝をtailの`target_missing`で潰して三形interfaceを確定し(第八十三ラウンド、実質は一行)、第4段`RefinedHistoryLanding.lean`がhistory枝にfresh landingとrestart crossingを回収する。以降LandingHorizon・LandingMount・MountedIterationを経て、第8段`RefinedFixedPointCore.lean`の頂点`LeastMissingTarget.refinedSemanticEdge_or_flooredCore`(左枝が証明書付きrefined semantic辺、右枝が`32 ≤ crossingTime`かつ`19 ≤ target`の固定点core)へ至る。
