# PermanentAboveCorridorReplayCorridor

**役割:** pinned replay cycleの全cursor(downcross endpoint、return、old crossing、blocker初出、fresh endpoint)がtarget未満の初期帯に収まり、endpointからcrossingまでの区間全体がbelow-target corridorであることを示す。kernel計算によりcrossing clock ≥ 3、従ってtarget ≥ 5を得る。

## このモジュールの役割

`PermanentAboveCorridorReplayPinning.lean`は、exact replay固定点が軌道上の一つの具体的なcycle(fresh downcross endpoint → canonical return = old crossing)を閉じることを示した。本モジュールはこのcycleを軌道の初期部分へ閉じ込める。鍵は二つの不等式の合成である: replayのcrossing clockはその値より小さく(`crossingTime + 1 < a(crossingTime)`)、その値はtargetより小さい(straddleの下側)。従ってcrossing clock自体がtarget未満であり、pinningの等式群によってcycleが保持する他のすべての時刻cursorも連鎖的にtarget未満に落ちる。さらに、endpointからcrossingまでの間にtarget以上の値が一度でも現れると、その手前に中間のweak upcrossingが存在してcanonical returnの最初性に矛盾するため、cycle全体がbelow-target corridor(全値がtarget未満の区間)である。最後に、`a(0) = 0`、`a(1) = 1`、`a(2) = 3`というLeanカーネルの直接計算により小さいclockでは`clock + 1 < a(clock)`が成り立たないことを確認し、replay固定点の存在にはcrossing clock ≥ 3、target ≥ 5が必要という最初の数値的下限を得る。

本モジュールの定理はすべて`TerminalExactDischargeReplayCertificate`のnamespace内にあり、replay証明書`r`のメソッドとして書かれている。

## 定理と証明

### `crossingTime_lt_target` (L28)

**主張:** replayのcrossing clockはtargetより厳密に小さい: `crossingTime + 1 < target`。

**証明:** pinningの`clock_lt_crossingValue`(`crossingTime + 1 < a(crossingTime)`)とstraddleの下側(`a(crossingTime) < target`)を連結するだけである。

### `all_below_up_to_crossing` (L37)

**主張:** cycle区間は全値target未満である: `downTime + 1 ≤ t ≤ crossingTime`なるすべての`t`で`a(t) < target`。

**証明:** 背理法。ある`t`で`target ≤ a(t)`とする。区間の始点`a(downTime + 1)`はdowncross endpointなのでtarget未満であり、below-target点からat-or-above点までの間には必ずweak upcrossingが存在する(`exists_weakUpcrossingStep_between`)。その witness 時刻は`t`より前、従って`t ≤ crossingTime = oldCrossingTime`(pinningの`time_eq`)によりold crossingより厳密に前にある。しかしpinningの`canonicalReturn_is_oldCrossing`は、endpointからの*最初の*weak upcrossingがold crossingであることを主張しており、それより早いwitnessの存在は最初性(`first`フィールド)に矛盾する。

### `cursor_band` (L55)

**主張:** self-recurrentなdischargeが保持する全時刻cursorはtarget未満の帯に入る:

```text
downTime + 1 < target,  returnTime < target,  oldCrossingTime < target,
firstTime < target,  freshEndpoint < target
```

**証明:** L28の`crossingTime + 1 < target`を軸に、pinningの等式・不等式群を代入する。`returnTime = crossingTime`(`return_eq_crossingTime`)、`oldCrossingTime = crossingTime`(`time_eq`)、`downTime + 1 ≤ crossingTime`(`endpoint_le_crossingTime`)、`firstTime < crossingTime`(`firstTime_lt_crossingTime`)、そしてfresh endpoint証明書の`fresh_le_return`。すべて一回のomegaで閉じる。反例のcycleが軌道の先頭`target`歩以内に完全に埋め込まれることを意味する。

### `anchor_mem_candidates` (L70)

**主張:** replayのcrossing anchor(= parent anchor)は有限のstrict-crossing anchor候補リスト`terminalCrossingAnchorCandidates target`(実体は`List.range target`)に属する。

**証明:** membershipの同値`mem_terminalCrossingAnchorCandidates_iff`は「target未満」であり、replayの`anchor_eq`でanchorを`a(crossingTime)`に書き換えればstraddleの下側がそれを与える。`PermanentAboveCorridorAnchorCandidates.lean`の有限列挙とここで接続する。

### `three_le_crossingTime` (L77)

**主張:** kernel計算はclock 3未満を排除する: `3 ≤ crossingTime`。

**証明:** `crossingTime ∈ {0, 1, 2}`と仮定すると、clock境界`crossingTime + 1 < a(crossingTime)`は具体的な数値命題になる。`a(0) = 0`(`1 < 0`)、`a(1) = 1`(`2 < 1`)、`a(2) = 3`(`3 < 3`)はいずれも偽であり、Leanカーネルの`decide`が直接棄却する。

### `five_le_target` (L89)

**主張:** replay固定点はtargetが5以上であることを強制する。

**証明:** L77の`3 ≤ crossingTime`とL28の`crossingTime + 1 < target`から`5 ≤ target`。

## 全体の中での位置づけ

本モジュールは証明地図(docs/PROOF_MAP.md)の「replay corridor band(固定点cursorをtarget未満帯へ有限化済み)」に対応する。上流は`PermanentAboveCorridorReplayPinning.lean`(cycle閉包の等式群)と`PermanentAboveCorridorAnchorCandidates.lean`(anchor候補の有限列挙)である。ここで確立した「cycleは初期帯のbelow corridorに閉じ込められ、パラメータは小さいclockから順にkernel検証で削れる」という攻め方は、直後の`PermanentAboveCorridorReplayFloor.lean`がそのまま引き継ぎ、実軌道stepの検証(clock 3は実際には減算、clock 5がまたぐtargetはすべて実出現)でclock ≥ 6・target ≥ 8まで下限を引き上げる。`PermanentAboveCorridorFiniteClosure.lean`がterminal窓の数値枝を具体的な軌道値で殺したのと同型の戦略が、今度はreplay固定点そのものに適用されている。
