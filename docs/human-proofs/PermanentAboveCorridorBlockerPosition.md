# PermanentAboveCorridorBlockerPosition

**役割:** terminal historical blockerの初出時刻を正規化されたfresh endpoint(回廊の最終的な未出below-target着地点)と比較し、初出がfreshより後なら履歴予算`missingBelowCount`の厳密下降を得る位置分類を与える。

## このモジュールの役割

`PermanentAboveCorridorBlocker.lean`は回廊終端の強制加算の理由を「数値帯」または「historical blocker」へ分類した。blocker枝が返す初出時刻`firstTime`は`firstTime < returnTime`(returnより前)としか分かっていない。しかし恒久上方tail解析のrank(整礎な探索順序)にとって重要なのは、この初出が回廊の正規化されたfresh endpoint(`PermanentAboveCorridorBalance.lean`が両terminal形に共通して与える、target未満の値の初出時刻`freshEndpoint`)の前にあるか後にあるかである。初出がfreshより後なら、blockerはfresh時点ではまだ未出だったtarget未満の値がその後に初出したことを意味し、履歴予算(history budget、未出のtarget未満値の個数`missingBelowCount`)がfreshからblocker初出までに厳密に下がる。これは既存の大域rankの第一成分の下降であり、探索の真の進捗になる。初出がfresh以前なら、blockerは回廊の外側の歴史に属し、outer history側の解析(`PermanentAboveCorridorOuterHistory.lean`)へ回される。さらに、immediate valley(historical downcross直後がそのままreturn predecessorになる即時谷)ではfresh endpointがreturn predecessor自身なので、後者の枝しか起こり得ないことも示す。証明地図の「blocker position」段階に対応する。

## 主要な定義

### `NormalizedTerminalBlockerOutcome` (L17)

正規化されたterminal crossingの最終減算失敗を、位置情報込みで三分岐する帰納型。

- `insufficient_value`枝: fresh endpoint証明書と、`PermanentAboveCorridorBlocker.lean`の数値帯証明書。
- `blocker_at_or_before_fresh`枝: fresh endpoint証明書、blocker証明書、および`firstTime ≤ freshEndpoint`。blockerは回廊より前からある外側の歴史である。
- `blocker_after_fresh`枝: fresh endpoint証明書、blocker証明書、`freshEndpoint < firstTime`、および履歴予算の厳密下降

  ```text
  missingBelowCount target firstTime < missingBelowCount target freshEndpoint
  ```

  を保持する。

## 定理と証明

### `NormalizedTerminalCrossingData.blockerOutcome` (L47)

**主張:** 正規化されたterminalデータ(fresh endpointの存在とstrict crossing balance)からは、必ず上の三分岐のいずれかが得られる。特に、fresh endpointより後に初出するblockerは履歴予算を厳密に下げる。

**証明:** まずデータからfresh endpoint `freshEndpoint`とその証明書を取り出す。次にbalanceへ`forcedReason`(`PermanentAboveCorridorBlocker.lean` L52)を適用して二分する。

- insufficient value枝ならそのまま第一構成子。
- historical blocker枝なら`firstTime ≤ freshEndpoint`か否かで場合分けする。前なら第二構成子。後(`freshEndpoint < firstTime`)なら、`missingBelowCount_strict_of_firstAt`(`HistoryBudget.lean`)を適用する。この補題は「target未満の値が時刻`freshEndpoint`より後の`firstTime`に初出する」ことから予算の厳密下降を導く: その値は時刻`freshEndpoint`の時点では未出だったが`firstTime`までに出現したため、未出カウントが少なくとも1減る。blockerの`candidate_below_target`と`candidate_first`がちょうどこの補題の仮定であり、第三構成子の全成分が揃う。

### `TerminalHistoricalBlockerCertificate.firstTime_lt_immediateEndpoint` (L69)

**主張:** immediate historical valley(`returnTime = downTime + 1`、すなわちhistorical downcrossの直後が最初のreturn predecessorでもある即時谷)においては、すべての正のblockerの初出はfresh endpoint `downTime + 1`より厳密に前にある。

**証明:** blocker証明書は`firstTime < returnTime`を保証する。valley証明書の`return_eq`により`returnTime`は`downTime + 1`に等しいので、書き換えるだけで`firstTime < downTime + 1`を得る。immediate valleyではfresh endpointがreturn predecessorそのものなので、`blocker_after_fresh`枝は空である: 予算下降はこの形からは得られず、blockerは常に外側歴史に落ちる。これが`PermanentAboveCorridorResidual.lean`のimmediate historical残余の由来である。

### `PermanentTailDischargeReturnCertificate.terminalBlockerOutcome` (L81)

**主張:** discharge return証明書(historical downcrossとcanonical returnを束ねた証明書、`PermanentAboveCycleExit.lean`)から直接、位置分類つきのblocker outcomeを取り出せる。

**証明:** 証明書の正規化データ`normalizedTerminalCrossingData`(`PermanentAboveCorridorBalance.lean`)にL47を適用する適配定理である。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「blocker position」(budget枝まで分類済み)に対応する。入力は`PermanentAboveCorridorBlocker.lean`のforced reason分類、`PermanentAboveCorridorBalance.lean`のfresh endpoint証明書、`HistoryBudget.lean`の予算下降補題である。出力の三分岐は`PermanentAboveCorridorResidual.lean`のmaster theoremにそのまま吸収される: `blocker_after_fresh`枝はstrict budget progressとして進捗側へ分離され、残るouter residualはimmediate二形・finite clock band・finite outer blockerの四形に縮約される。fresh以前枝のblockerは`PermanentAboveCorridorOuterHistory.lean`でbacktrack rank辺へ、さらに`PermanentAboveCorridorBlockerGeneration.lean`で生成分類へと引き継がれる。
