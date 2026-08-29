# PermanentAboveCorridorTerminalSuccessor

**役割:** terminal progress分類のinstalled master枝を強化し、選択されたcrossing、そのsemantic install証明書、および次のdischarge証明書の存在(`Nonempty`)を同じoutcomeへ同梱する。これによりmaster child上で次のterminal解析へproof provenanceを失わず進める。

## このモジュールの役割

`PermanentAboveCorridorTerminalProgress.lean`の`installed_master_progress`は、七成分master rankの厳密な辺として停止性への寄与を証明するが、その辺のchild nodeは数値tupleであり、「次に解析すべき意味的対象」を隠してしまう。historical below-target枝では実際にはもっと多くのことが分かっている: 選択されたpredecessor crossingは`PermanentAboveCorridorSelectedInstall.lean`によりpermanent-tail parentとしてinstallでき(tail本体・zero budget・tail minimumなどの全semanticsが同一horizonのまま移送される)、さらにそのinstalled parentの上でhistorical discharge構成を再実行した次のdischarge証明書が、`oldCrossingTime`を選択crossing時刻に固定した形で存在する。本モジュールはこの連鎖全体をterminal outcomeに保持する`PermanentTailTerminalSuccessorOutcome`を定義し、master反復のsourceを型として接続する。すなわち「rankが下がる」という事実だけでなく、「下がった先で同じterminal解析を適用できる対象が実在する」ことまでが一つの定理にまとまる。

## 主要な定義

### `PermanentTailTerminalSuccessorOutcome` (L16)

terminal progress四形のうち、target出現・history progress・semantic progressの三形はそのまま保持し、第四形を`installed_successor`へ置き換えた帰納型。`installed_successor`は次の全データを同時に保持する。

- outer historical blocker証明書と、そのbelow-target predecessor証明書。
- 選択されたcrossingの`TerminalBelowPredecessorCrossingCertificate`(最初のweak upcrossing、return以下の時刻、旧horizon上のready crossing)。
- `TerminalSelectedCrossingInstallCertificate`: 選択crossing nodeを新しいpermanent-tail crossing親としてinstallしたsemantic証明書(permanent tail・combined証明書・同一horizon・selected anchorの保存)。
- `Nonempty (TerminalSelectedCrossingDischargeCertificate install)`: installされた親の上の次のdischarge証明書の存在。この証明書は`discharge.oldCrossingTime = crossingTime`、すなわち旧crossing witnessが任意の存在量化ではなくまさに選択されたcrossingであることを型で固定している。
- 七成分master rankの厳密な辺`TailInstalledCycleProgress`(childはphase `crossing`、parentはphase `discharge`の明示的node)。

## 定理と証明

### `PermanentTailDischargeReturnCertificate.terminalSuccessorOutcome` (L54)

**主張:** すべてのterminal dischargeについて、installedな反復辺は選択されたsemantic parentと実際の次discharge存在証明を伴って返される。他の枝は`PermanentAboveCorridorTerminalProgress.lean`と同じ四形(のうち三形)に入る。

**証明:** 場合分けの骨格は`terminalProgressOutcome`と同一で、`terminalFiniteClosedOutcome`を展開する。history progress枝、immediate semantic枝(target出現または`targetStartNode (downTime+2)`をstepParentとするsemantic step)、historical complete枝のtarget・early・ready・phase_exitの各葉は、前モジュールと同じ移送を行う。唯一異なるのは`below_master`の`master_progress`葉である。ここでは選択crossing証明書`certificate`から

1. `certificate.install`(`TerminalBelowPredecessorCrossingCertificate.install`、選択nodeが旧parentと同じhorizonを持つことからpermanent tail・zero budget・minimumの全条件をsimpで移送する定理)でinstall証明書を作り、
2. その`exists_nextDischarge`(installed parentの上でhistorical discharge構成を再実行し、`oldCrossingTime`を選択時刻に固定した証明書を返す定理)で次dischargeの`Nonempty`を得て、
3. master rank辺とあわせて`installed_successor`の全フィールドを詰める。

これにより、master辺を取るたびに「その辺のchildを親とする次のdischarge」が構成済みであることが保証される。

### `TerminalSelectedCrossingDischargeCertificate.parent_is_installed` (L99)

**主張:** successor packageが公開するdischargeのparentは、定義的に(definitionally)installされた選択crossing node `terminalPredecessorCrossingNode parent crossingTime`である。

**証明:** 次discharge証明書の`discharge`フィールドの射影であり、その型がすでに`PermanentTailDischargeReturnCertificate target start (terminalPredecessorCrossingNode parent crossingTime)`になっている。すなわち等式の証明を運ぶ必要はなく、型検査だけでparentの同一性が確定する。次のterminal解析(`terminalShape`、`terminalProgressOutcome`など)をこのdischargeへそのまま適用できることを明示する定義である。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「terminal successor provenance(master反復sourceを接続済み)」に対応し、執筆時点のcorridorファミリーの最新端である。上流は`PermanentAboveCorridorTerminalProgress.lean`(四形への平坦化)、`PermanentAboveCorridorSelectedInstall.lean`(install証明書と次discharge構成)、`PermanentAboveCorridorMasterRank.lean`(七成分rank)である。全体構図の中では、仮想的な最小未出targetのpermanent tailに対して「discharge → terminal解析 → (targetか、確立済みrankの下降) → installed successor上の次のdischarge」という反復が、意味的データを一切失わずに型付きで一周つながったことを意味する。masterrelationはwell-foundedなので、この反復の各周回はrank上で厳密に下降する。残る大域的課題は、この反復と他のprogress形(history・semantic)をprovenance付きreachable domain全体の探索(PROOF_MAP「全域局所被覆」)へ統合することである。
