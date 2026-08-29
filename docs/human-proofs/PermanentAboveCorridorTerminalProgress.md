# PermanentAboveCorridorTerminalProgress

**役割:** finite数値枝を除去済みのterminal outcomeの内側constructorを全展開し、すべてのterminal dischargeを「target出現・strict history下降・semantic位相下降・installed master下降」の四つのprogress形だけへ平坦化する。terminal residualは残らない。

## このモジュールの役割

`PermanentAboveCorridorFiniteClosure.lean`により、terminal dischargeの分類からfinite数値枝(insufficient clock band)は完全に消え、残る枝はhistory progress、immediate semantic、historical completeの三つになった。しかしこれらの枝は内部にさらに入れ子の場合分け(immediate枝のsemantic outcome、historical枝のearly/ready/below-master分岐、below枝のphase exit/master progress分岐)を抱えている。本モジュールはその内側をすべて展開し、各葉がどの確立済みwell-founded関係の厳密な辺に対応するかを一段の帰納型`PermanentTailTerminalProgressOutcome`として平坦化する。設計上の要点は、semantic辺のconstructorが比較の基準となった実際のlocal parent(`stepParent`)を明示的に保持することである。early・ready・immediate・selected-crossingの各stepはそれぞれ異なるparent node(historical predecessor node、current predecessor node、valley後のstart node、元のdischarge parent)に対して位相ランクを下降させており、これらを元のdischarge parentへの下降と不正に同一視しないため、rank文脈をデータとして持ち運ぶ。

## 主要な定義

### `PermanentTailTerminalProgressOutcome` (L18)

typed historical discharge証明書に対する、progress形のみの完全分類。四constructorを持つ。

- `target_occurs`: `a(witness) = target`の実出現。
- `history_progress`: `TerminalChronologyHistoryProgress`、すなわち`missingBelowCount target childTime < missingBelowCount target parentTime`という履歴予算の厳密下降。
- `semantic_progress`: 実際の比較元`stepParent`、semantic domainに属するchild(`PhaseSemanticInvariant`)、およびそのparentに対する`PhaseSearchProgress`(四成分位相ランクの厳密下降)の三つ組。
- `installed_master_progress`: 七成分installed-cycle master rank(`TailInstalledCycleProgress`)の厳密な辺。

いずれの関係もwell-founded性は先行モジュールで証明済みであり、新しいrankは導入されない。

## 定理と証明

### `PermanentTailDischargeReturnCertificate.terminalProgressOutcome` (L42)

**主張:** すべてのterminal dischargeは、targetを出現させるか、すでに証明済みのwell-founded関係の厳密な辺を返す。数値的residualも型付きresidualも残らない。

**証明:** `terminalFiniteClosedOutcome`(finite枝除去済みの三分類)を場合分けし、各葉を四形へ写す。

*history_progress枝。* そのまま`history_progress`へ移送する。

*immediate_semantic枝。* 即時谷のsemantic outcome(`ImmediateTerminalSemanticOutcome`、`PermanentAboveCorridorImmediateClosure.lean`)を展開する。target出現なら`target_occurs`。semantic stepなら、谷の底から二歩戻った時刻のnode `targetStartNode (downTime + 2)`をstepParentとして`semantic_progress`にする。谷のCoverageStepはこのnodeを親とするcanonical coverage adapterから作られているためである。

*historical_complete枝。* outer historical blockerのcomplete outcome(`TerminalOuterHistoricalCompleteStepOutcome`、`PermanentAboveCorridorAboveClosure.lean`)を展開する。

- `target_occurs`はそのまま。
- `early_step`(predecessorがabove-targetだがclockがtarget-readyでない場合のearly representative経由の閉包)は、historical predecessor node `terminalHistoricalPredecessorNode parent (firstTime − 1)`(旧horizon上にpredecessor値を載せたnode)をstepParentとする`semantic_progress`。
- `ready_step`(clock readyなabove predecessorのorbit-ready経由の閉包)は、current predecessor node `terminalCurrentPredecessorNode (firstTime − 1)`(時刻とhorizonが一致するcurrent node)をstepParentとする`semantic_progress`。
- `below_master`はさらに内側の`TerminalBelowPredecessorMasterRankOutcome`で分かれる。`phase_exit`(選択crossingが位相ランクを直ちに下げる場合)は、元のdischarge parentをstepParentとし、crossing childのrefined invariantを`toPhaseSemanticInvariant`でsemantic invariantへ埋め込んで`semantic_progress`。`master_progress`は、child node `⟨parent.horizon, a(crossingTime), crossingTime, firstTime−1, crossing, firstTime−1, 0⟩`とparent node `⟨parent.horizon, parent.anchorParent, source.oldCrossingTime, firstTime, discharge, firstTime, 0⟩`という明示的な七成分nodeの組の間の`installed_master_progress`になる。

以上で全葉が尽くされ、各枝は生成時のprovenance(どのparentに対する下降か)を保ったまま四形のいずれかに入る。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「terminal progress flattening(四progress形へ完全統合済み)」に対応する。上流は`PermanentAboveCorridorFiniteClosure.lean`(finite枝の無条件排除)、`PermanentAboveCorridorImmediateClosure.lean`(即時谷のsemantic閉包)、`PermanentAboveCorridorAboveClosure.lean`(above predecessorの完全閉包)、`PermanentAboveCorridorMasterRank.lean`(below predecessorのmaster rank)である。直後の`PermanentAboveCorridorTerminalSuccessor.lean`は、このうち`installed_master_progress`枝だけを強化し、次のdischargeを実際に再構成できるsemantic provenanceを同じoutcomeへ同梱する。本モジュールの平坦化により、zero-budget permanent tail上のterminal解析は「一回のdischargeごとに、必ずどれかの証明済みwell-founded量が厳密に下がる(またはtargetが出る)」という形に整理された。残る問題はrank下降そのものではなく、master辺の反復を意味的に継続するためのデータ(次モジュール)である。
