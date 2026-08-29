# PermanentAboveCorridorReplayInterface

**役割:** 仮想反例の内部ではtarget出現枝が矛盾するため、閉じたterminal解析がouter探索へ渡す情報を「strict history辺・semantic位相child・exact replay固定点」の三形interfaceに確定する。さらにreplayのcrossing cursorとanchor値がdischargeだけで一意に決まる剛性を示す。

## このモジュールの役割

`PermanentAboveCorridorIterationClosure.lean`のiteration-free outcomeは、target出現・history辺・semantic辺・exact replayの四形だった。しかしpermanent-tail解析はそもそも仮想的な最小未出target(全軌道で出現しない値)の内部で行われており、combined証明書のtail成分は`target_missing`を保持している。従ってtarget出現枝は反例の内部では起こり得ず、interfaceは三形に縮む。これがmissing-target permanent tailのterminal解析が外側の大域探索へ提供する完全なinterfaceである: 履歴予算の厳密下降か、位相ランクを下げるsemantic childか、あるdescendant discharge上のreplay固定点か。さらに本モジュールは、replay枝の剛性(rigidity)を記録する。replay証明書の二つの等式(`time_eq`、`anchor_eq`)はいずれも「格納されたold crossingデータを読み返す」形をしているため、同じdischargeの上の相異なるreplay証明書は、blockerのprovenance(freshEndpoint、candidate、firstTimeなど)では異なり得ても、閉じるcycle(crossing時刻とanchor値)においては一致する。replay固定点は「dischargeごとに高々一つのcycle」であり、これが後続の数値攻撃(corridor band、kernel floor)を一点に集中させることを正当化する。

## 主要な定義

### `PermanentTailTerminalMissingOutcome` (L24)

missing-target permanent tailから得られるterminal情報の三形。target枝を持たない。

- `history_progress`: `TerminalChronologyHistoryProgress`(`missingBelowCount`の厳密下降)。
- `semantic_progress`: 比較元`stepParent`付きのsemantic位相辺。
- `exact_replay`: descendantのparent node、そのdischarge証明書、および`TerminalExactDischargeReplayCertificate`。

なおこの「exact replay」はdischarge反復のrank固定点であり、`PermanentAboveCorridorReplayBoundary.lean`で扱ったexact canonical revisit(visited list上のkey残余。後に`PermanentAboveCorridorFiniteClosure.lean`で無条件排除済み)とは別の対象である。

## 定理と証明

### `PermanentTailCombinedCertificate.terminalMissingOutcome` (L45)

**主張:** target出現枝はmissing-targetフィールドと矛盾するので、閉じたterminal解析はちょうど三つのinterface形を返す。

**証明:** combined証明書の`terminalReplayReducedOutcome`(反復消去済みの四形)を場合分けする。`target_occurs`枝はwitness `⟨witness, value_eq⟩`がtailの`target_missing`に直接矛盾するので`False.elim`。残る三枝はそのまま対応するconstructorへ移送する。

### `crossingTime_unique` (L67)

**主張:** replayのcrossing cursorはdischargeだけで決まる: 同じdischarge上の任意の二つのreplay証明書`r₁, r₂`について`r₁.crossingTime = r₂.crossingTime`。

**証明:** 両者の`time_eq`はどちらも`crossingTime = source.oldCrossingTime`という同じ格納値への等式なので、推移律(omega)で一致する。

### `anchor_value_unique` (L76)

**主張:** replayのanchor値も同様に一意である: `a(r₁.crossingTime) = a(r₂.crossingTime)`。

**証明:** L67の等式で書き換えるだけである。`anchor_eq`を経由すればどちらも`parent.anchorParent`に等しい、と読むこともできる。

二つの一意性定理を合わせると、同一dischargeの複数のreplay証明書はblocker側のprovenanceでしか異なり得ず、「どのcycleが閉じるか」は一意である。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「missing-target interface(三形interfaceへ確定済み)」に対応する。上流は`PermanentAboveCorridorIterationClosure.lean`(四形への縮約)と、replay剛性の基礎である`PermanentAboveCorridorReplayPinning.lean`の等式群である(importチェーン上は`PermanentAboveCorridorReplayFloor.lean`経由で全結果を継承する)。下流では`PermanentAboveCorridorHistoryLanding.lean`が三形のうちhistory枝を強化し、抽象的なmissing-count下降からfresh landing(parent cursorより後に初出するbelow-target値)とそのrestart crossingを回収して、anchored interfaceへ進む。全体構図では、本モジュールの三形が「仮想反例のpermanent tailに残された全可能性の台帳」であり、replay枝はcorridor band・kernel floorによる数値挟撃、history枝はlanding回収、semantic枝は既存の位相ランクという、それぞれ独立の攻略線に接続されている。
