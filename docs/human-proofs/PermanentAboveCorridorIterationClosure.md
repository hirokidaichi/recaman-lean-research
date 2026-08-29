# PermanentAboveCorridorIterationClosure

**役割:** discharge-levelの三成分反復rankの整礎性に沿った強帰納法でinstalled successorの反復constructorを消去し、任意のterminal解析を「target出現・strict history辺・semantic位相辺・あるdescendant discharge上のexact replay固定点」の四形へ縮約する。

## このモジュールの役割

`PermanentAboveCorridorSuccessorRank.lean`は、installed successor(選択crossingを新parentとしてinstallし、その上でhistorical dischargeを再構成した次の解析対象)の間で実際に輸送される座標だけを取り出したdischarge-level rank

```text
terminalDischargeIterationRank = (missingBelowCount target horizon,
                                  target − anchorの残gap,
                                  oldCrossingTime)
```

を定義し、各dischargeのterminal解析が「確立済みの大域辺を返すか、このrankを厳密に下げるsuccessorを渡すか、rankが文字どおり不動のexact replay(完全再生)証明書を返すか」に分類されることを示した。本モジュールはこの分類を反復する。三成分の辞書式順序は自然数のlexとしてwell-foundedなので、rankに対する強帰納法によりiteration constructorそのものを消去できる: どのdischargeから始めても、有限回のinstalled successorの後に、targetの出現、strict chronology history辺(`missingBelowCount`の厳密下降)、semantic位相辺、またはあるdescendant discharge上のexact replay固定点のいずれかへ必ず到達する。replay枝は停止したdescendant discharge自身とその完全なreplay証明書を保持するため、残る数学は非有界な反復ではなく一つの型付き対象に集中する。

## 主要な定義

### `PermanentTailTerminalReplayReducedOutcome` (L23)

iteration-freeなterminal outcome。四constructorを持つ。

- `target_occurs`: `a(witness) = target`の実出現。
- `history_progress`: `TerminalChronologyHistoryProgress`(履歴予算`missingBelowCount`の厳密下降)。
- `semantic_progress`: 比較元`stepParent`付きのsemantic位相辺(`PhaseSemanticInvariant`なchildと`PhaseSearchProgress`)。
- `exact_replay`: 反復rankが停止したdescendantのparent node `replayParent`、そのdischarge証明書`replaySource`、および`TerminalExactDischargeReplayCertificate`(installed successorがparent anchorを同じcrossing cursorで再生産し、rankが等式として不動であることを、blocker・below predecessor・選択crossing・install・次dischargeの全構成chainとともに保持する構造)。

反復constructorが存在しないことが本質である。なお、この「exact replay」はdischarge反復のrank固定点であり、`PermanentAboveCorridorReplayBoundary.lean`のexact canonical revisit(visited listのkey残余)とは別の概念である点に注意する。

## 定理と証明

### `PermanentTailDischargeReturnCertificate.terminalReplayReducedOutcome` (L48)

**主張:** strict iteration辺に沿った再帰はすべてのinstalled successor枝を消費する。生き残るのはtarget、確立済みのstrict辺、またはexact replay固定点だけである。

**証明:** 内部補題として「任意のrank値と、そのrankを持つ任意のdischargeについて結論が成り立つ」を、三成分lex rankのwell-founded性(`natTripleLex_wellFounded`)に対するaccessibility帰納法で示す。与えられたdischarge `node`に前モジュールの完全分類`terminalIterationOutcome`を適用し、五枝を処理する。

- `target_occurs`・`history_progress`・`semantic_progress`の三枝は、そのまま対応するconstructorへ移送する。
- `iteration_progress`枝では、successor discharge `next`が`TerminalDischargeIterationProgress`、すなわち`terminalDischargeIterationRank`のstrictなlex下降を伴う。rankの等式を書き換えれば帰納法の仮定がちょうど適用でき、`next`に対する結論が親に対する結論になる。ここでsuccessorのparent nodeは元と異なる(`terminalPredecessorCrossingNode`)が、outcomeの型が特定のparentに依存しない`(target, start)`のみのPropであるため、異なるnode上の再帰がそのまま合流する。
- `exact_replay`枝では、現在のdischarge自身が停止点なので、そのparent・discharge・replay証明書を`exact_replay` constructorへ格納して終了する。

最後に元の`source`のrankで内部補題を起動する。

### `PermanentTailCombinedCertificate.terminalReplayReducedOutcome` (L82)

**主張:** 任意のcombined permanent-tail obstruction(tail本体・zero-budget crossing・tail minimum blockerの束)は初期dischargeを持つので、そのsuccessor反復全体が同じ四形へ縮約される。

**証明:** `PermanentAboveCycleExit.lean`の`exists_dischargeReturnCertificate`で初期dischargeを取り、L48を適用するだけである。これにより「仮想反例 → combined証明書 → 有限回のterminal反復 → 四形」の連鎖が、dischargeの明示的な選択なしに成立する。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「successor iteration closure(反復constructorを整礎帰納で消去済み)」に対応する。上流は`PermanentAboveCorridorSuccessorRank.lean`(輸送可能な三成分rankとreplay証明書)と`PermanentAboveCycleExit.lean`(combined証明書からの初期discharge)である。下流では、`PermanentAboveCorridorReplayPinning.lean`が唯一残ったexact replay枝を数値的に固定してnode-levelのself-map固定点へ強め、`PermanentAboveCorridorReplayInterface.lean`がmissing-target仮定でtarget枝を落として最終interfaceを確定する。私が先に書いた`PermanentAboveCorridorTerminalSuccessor.lean`(次discharge存在の同梱)は、まさに本モジュールの再帰の一歩分の素材であり、ここでその反復が実際に整礎的に閉じたことになる。
