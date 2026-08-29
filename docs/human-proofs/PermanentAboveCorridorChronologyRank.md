# PermanentAboveCorridorChronologyRank

**役割:** installed next discharge(selected crossingを親としてinstallし直した次のdischarge)のchronology mismatch — 次のdowncross endpointがselected crossing時刻より後にある場合 — が、実はそのendpointのbelow-target初出による`missingBelowCount`の厳密下降であることを証明し、mismatchを独立なwell-foundedのhistory進捗へ変換して、chronology kernelの残余を消す。

## このモジュールの役割

`PermanentAboveCorridorSelectedInstall.lean`は、blocker predecessorから選んだcrossingを次cycleの親としてinstallし、その親の上で再構成した次のdischarge証明書に対し、「次のdowncross endpointがselected crossing時刻以前にある(eligible)」か「後にある(mismatch)」かの正確なchronology二分を与えた。eligibleな側は`PermanentAboveCorridorRestartRank.lean`のrestart/cursor定理がそのまま適用できるが、mismatchの側は一見すると時系列が逆転した扱えない残余に見える。本モジュールは、このmismatchが実は進捗であることを示す。downcross endpointは合法減算による着地なので、その値はtarget未満かつ初出である。selected crossing時刻より後に初出のtarget未満値が現れるのだから、selected時刻からendpointへ進む間にmissing履歴予算が必ず一つ以上減っている。これは`missingBelowCount`を自然数`<`へ引き戻した独立のwell-founded関係の厳密辺であり、従ってinstalled iterationの全体は「eligibleでrestart定理が使える」か「すでにstrictなhistory進捗である」かの二形に完全分類され、chronology由来のkernelは残らない。

## 主要な定義

### `TerminalChronologyHistoryProgress` (L21)

二つのhistory clockの間のmissing予算の厳密下降

```text
missingBelowCount target childTime < missingBelowCount target parentTime
```

を進捗関係とする。時刻そのものの前後ではなく予算だけで比較する点が要点で、時系列上は前へ進むmismatchでも予算では下降になる。

### `TerminalSelectedCrossingChronologyProgressCertificate` (L41)

installed next discharge `next`のchronology mismatchが露出する完全なstrict history辺の証明書。フィールドは: `crossingTime < next.discharge.downTime + 1`(selectedが次endpointより前)、次endpointの値がtarget未満、そこでの初出性`FirstAt`、missing予算の厳密下降(selected時刻からendpointへ)、双対seen予算の厳密増加、および上記progress関係そのもの。

### `TerminalSelectedCrossingIterationProgress` (L104)

installed next dischargeのtotalなchronology結果。constructorは`eligible`(`next.discharge.downTime + 1 ≤ crossingTime`)と`history_progress`(上記証明書)の二つ。

## 定理と証明

### `terminalChronologyHistoryProgress_wellFounded` (L26)

**主張:** `TerminalChronologyHistoryProgress target`は整礎である。

**証明:** 自然数`<`の整礎性のaccessibilityを、rank写像`missingBelowCount target`に沿って時刻へ引き戻す。予算が等しい時刻同士は関係しないので、rank上の帰納法がそのまま時刻上のaccessibilityを与える。

### `TerminalSelectedCrossingDischargeCertificate.chronologyProgress` (L73)

**主張:** literalなmismatch(`crossingTime < next.discharge.downTime + 1`)からは、初出に基づくstrictなhistory辺の証明書が得られる。

**証明:** 次のdischargeのdowncross証明書から、endpoint値がtarget未満であること(`endpoint_below`)と、その時刻での初出性(`endpoint_first`)を読む。target未満の値が時刻`next.discharge.downTime + 1`に初出し、mismatchによりこの時刻はselected時刻`crossingTime`より真に後なので、`missingBelowCount_strict_of_firstAt`(`HistoryBudget.lean`)が

```text
missingBelowCount target (next.discharge.downTime + 1)
  < missingBelowCount target crossingTime
```

を与える。seen予算の厳密増加は分割等式による双対化(`seenBelowCount_strict_of_missingBelowCount_strict`、`PermanentAboveCanonical.lean`)であり、progressフィールドはmissing下降そのものである。

### `TerminalSelectedCrossingDischargeCertificate.iterationProgress` (L129)

**主張:** installed next dischargeのchronologyは、正確にeligibleであるか、それ自体がwell-foundedなstrict history辺であるかのいずれかである。

**証明:** `PermanentAboveCorridorSelectedInstall.lean`のtotalなchronology二分(`chronology`: eligible / mismatch)で場合分けする。eligible枝はそのまま第一形へ。mismatch枝はL73で証明書化して`history_progress`とする。場合分けが排他的かつ全域なので、第三の残余は存在しない。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「installed chronology rank(mismatchをhistory下降化済み)」に対応する。入力は`PermanentAboveCorridorSelectedInstall.lean`のinstall証明書とchronology二分、および`HistoryBudget.lean`・`PermanentAboveCanonical.lean`の予算定理である。直接の下流は`PermanentAboveCorridorMasterRank.lean`で、そこでは本モジュールのmissing下降が七成分master rankの最外成分(chronology cursorでのmissing予算)の下降として取り込まれ(`TerminalSelectedCrossingChronologyProgressCertificate.masterProgress`)、eligible側のrestart/anchor/cursor辺と同じ一つのwell-founded relationに統合される。`PermanentAboveHistory.lean`以来続いた「downcross endpointの時系列がcrossing選択と噛み合わない」という懸念は、本モジュールにより予算の言葉で常に進捗側へ倒れることが確定した。
