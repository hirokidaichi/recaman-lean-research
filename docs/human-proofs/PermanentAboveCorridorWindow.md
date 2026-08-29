# PermanentAboveCorridorWindow

**役割:** legal endpointをすべて消費した後に残るall-forced suffixを、telescoping加算trace・両側strictなcrossing・target gapとovershootのclock上界(`≤ returnTime`)を持つ有限算術証明書`TerminalAllForcedCrossingWindow`へ変換する。

## このモジュールの役割

`PermanentAboveCorridorBoundary.lean`までで、missing-target回廊内のlegal endpoint消費は有限で、残余は「endpointからreturnまで全遷移が強制加算」のall-forced suffixに限られることが分かった。本モジュールはこの残余が、構造のない軌道断片ではなく完全に明示的な有限算術オブジェクトであることを示す。全遷移が強制加算なら値のtraceは加算clockの総和`forcedClockSum`でtelescopingに書け、最後のreturn upcrossing(これも強制加算)まで延長できる。targetが未出であることからcrossingは両側でstrict(`a(returnTime) < target < a(returnTime+1)`)になり、crossing直前のtarget gap `target − a(returnTime)`とcrossing直後のovershoot `a(returnTime+1) − target`はともに正で、いずれもreturn clock以下に押さえられる。従ってpost-legalなterminal residualは有限な「crossing窓」に縮約される。

## 主要な定義

### `TerminalAllForcedSuffixCertificate` (L78)

missing targetの下でのterminalなall-forced suffixの証明対象: (1) canonical suffix(fresh endpointとそのfirst return、`PermanentAboveCorridorSuffix.lean`)、(2) targetが全軌道で未出、(3) `endpointTime < returnTime`(非空)、(4) 内部全遷移が強制加算(`AllForcedAdditionSuffix`)。

### `TerminalAllForcedCrossingWindow` (L86)

terminal crossingに残る最小の有限算術窓。上記証明書に加えて、(1) `returnTime < target`、(2) `a(returnTime) < target`(crossing直前はbelow)、(3) `target < a(returnTime+1)`(crossing直後はstrictにabove)、(4) 最終加算式`a(returnTime+1) = a(returnTime) + (returnTime+1)`、(5) endpointからの全trace `a(returnTime+1) = a(endpointTime) + forcedClockSum endpointTime (returnTime − endpointTime + 1)`、(6)(7) target gap `target − a(returnTime)`が正かつ`≤ returnTime`、(8)(9) overshoot `a(returnTime+1) − target`が正かつ`≤ returnTime`、を保持する。

## 定理と証明

### `AllForcedAdditionSuffix.value_eq_add_forcedClockSum` (L20)

**主張:** all-forced suffix上では、return predecessorまでの値がclock総和でtelescopingに書ける: `endpointTime + steps ≤ returnTime`なら

```text
a(endpointTime + steps) = a(endpointTime) + forcedClockSum endpointTime steps
```

ここで`forcedClockSum start steps`は`(start+1) + (start+2) + ⋯ + (start+steps)`に相当する再帰定義(`PermanentAboveCorridorRank.lean`)である。

**証明:** `steps`についての帰納法。0歩なら両辺とも`a(endpointTime)`。`steps + 1`歩目は仮定によりreturnより前の内部遷移なので強制加算であり、`a`は加算clock `endpointTime + steps + 1`だけ増える。帰納法の仮定とあわせて総和の再帰式どおりに積み上がる。

### `AllForcedAdditionSuffix.final_value_eq_add_forcedClockSum` (L48)

**主張:** 同じtraceを最終のreturn upcrossingまで延長できる:

```text
a(returnTime + 1) = a(endpointTime) + forcedClockSum endpointTime (returnTime − endpointTime + 1)
```

**証明:** L20を`steps = returnTime − endpointTime`で適用してreturn predecessorまでのtraceを得る。first return crossingの定義から時刻`returnTime + 1`への一歩も強制加算なので、さらにclock `returnTime + 1`を加えれば総和の再帰式の最後の項と一致する。

### `TerminalAllForcedSuffixCertificate.crossingWindow` (L104)

**主張:** すべてのterminal all-forced suffix証明書は有限crossing窓`TerminalAllForcedCrossingWindow`を与える。

**証明:** 各成分を順に確かめる。

- `returnTime < target`: 非空all-forced suffixのclock上界(`PermanentAboveCorridorSuffix.lean`の`returnTime_lt_target`)。
- `a(returnTime) < target`: crossingの`below`条件そのもの。
- `target < a(returnTime+1)`: crossingの`endpoint_ge`は`target ≤ a(returnTime+1)`しか言わないが、等号ならtargetの出現witnessになりmissing仮定に矛盾するのでstrictになる。
- 最終加算式とfull traceはそれぞれ強制加算の等式とL48。
- target gapが正であることは`a(returnTime) < target`から。gap ≤ clockは、最終加算式より`target < a(returnTime) + (returnTime+1)`なので`target − a(returnTime) ≤ returnTime`。
- overshootが正であることはstrict上側性から。overshoot ≤ clockは、`a(returnTime+1) − target = a(returnTime) + (returnTime+1) − target`で、`a(returnTime) + 1 ≤ target`より`≤ returnTime`。

gapとovershootの各上界は独立に得られるが、後に`PermanentAboveCorridorBalance.lean`が示すとおり両者の和はちょうど`returnTime + 1`である。

### `CanonicalReturnRebaseCertificate.terminalWindow_of_legal` (L139)

**主張:** 仮想permanent tailのdischarge回廊内で、時刻`time`の合法減算の後にもはやlegal endpointが残っていない(`¬∃ later`)なら、endpoint `time + 1`におけるterminal all-forced crossing窓が実際に構成でき、同時に`missingBelowCount target (time+1) < missingBelowCount target time`という履歴予算下降が付いてくる。

**証明:** `PermanentAboveCorridorBoundary.lean`の`legalSuffixChild_missingBoundary`により、子suffix・厳密なendpoint分離・予算下降・残余分類を得る。残余の「後続legal endpointあり」枝は仮定`hterminal`に矛盾するので、all-forced枝しか残らない。子suffix、tail証明書の`target_missing`、分離`time + 1 < returnTime`、all-forced性を束ねて`TerminalAllForcedSuffixCertificate`とし、L104で窓に変換する。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「terminal crossing window」(有限算術へ縮約済み)に対応する。上流は`PermanentAboveCorridorBoundary.lean`のlegal return boundaryと`PermanentAboveCorridorRank.lean`の`forcedClockSum`である。下流では、`PermanentAboveCorridorTerminal.lean`がsuffix cursorの強帰納で全dischargeを「immediate valley」または本モジュールの窓の二形へ正規化し、`PermanentAboveCorridorBalance.lean`がgap + overshoot = returnTime + 1という釣合いを抽出し、`PermanentAboveCorridorBlocker.lean`が窓の最終減算失敗の理由を分類する。また窓はそのまま`TerminalFiniteReturnWindowCertificate`(`PermanentAboveCorridorInstalledStep.lean`)の主成分となり、有限選択rank(`PermanentAboveCorridorWindowSelection.lean`)の対象になる。
