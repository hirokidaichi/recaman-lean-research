# TargetStreamUpwardResets

**役割:** B枝のunbounded right-terminal streamが、任意のcutoffより後に必ずblockerの上向きreset付きの連続same-target macro対を持つことをblocker値の強帰納法で示し、仮想反例の大域kernelを「eventual-high回廊 または 無限個のupward reset」へ精密化する。

## このモジュールの役割

`TargetTailResidualKernel.lean` は、仮想反例(missing permanent tail: 正のtargetが全軌道で未出、target未満の値はある時刻までに全て既出、それ以後の軌道値は常にtarget超)を、A枝「eventual-high candidate corridor」とB枝「固定分離rootの右側を走るunbounded right-terminal stream」に二分した。本モジュールはB枝を精密化する。streamは任意に遅いtarget-lowの完了comb(櫛状区間)を含み、各combから次のconsecutive macro episodeを取り出せるが、隣接episode間のblocker(妨害値)には「厳密に上がる」か「第二entryが第一blockerの下に落ち、そのとき第二blocker自身も厳密に下がる」かの二択しかない。下がる枝は自然数上で無限に続けられないので、streamは任意のcutoff後に必ず上向きreset `blocker₁ < blocker₂` を実行する。最後の定理はこの強制を大域二分法に合流させる。

## 定理と証明

まず、本モジュールが輸入している語彙を確認する。

- **comb / 櫛状区間** `HistoryTerminatedComb s k blocker`: 時刻 `s` に合法減算でfresh値 `a s` に入り、「強制加算とその即時返済減算」を `k` 周期繰り返して時刻 `s + 2k` に着地する区間である。low rail `a (s + 2i) = a s − i` (0 ≤ i ≤ k) はすべて初出であり、最終着地は `a (s + 2k) = blocker + 1`、直後の強制加算の次に試みられる返済候補 `blocker` が既出であるために区間が停止する。entry恒等式 `a s = blocker + k + 1`(`entry_eq_blocker_add_length`)により、combはfresh値区間 `{blocker + 1, …, blocker + k + 1}` をちょうど消費する。
- **減算候補** `nextSubtractionCandidate n = a n − (n + 1)`: 時刻 `n + 1` に試みられる減算先。これが `target` 未満のとき、そのcombを**target-low**と呼ぶ。
- **stream** `UnboundedRightTerminalStream target tailStart root`: (i) tail内(`tailStart ≤ start`)の全完了combのentryが `root ≤ a start` を満たす(no-escape床)、かつ (ii) 任意のcutoffより後に開始するtarget-lowの完了combが存在する、という二成分の命題。
- **macro対** `TargetMacroSuccessor target tailStart s₁ k₁ blocker₁ s₂ k₂ blocker₂`: 二つの完了combで、第一combがtailの真内部(`tailStart < s₁`)にあり、時系列 `s₁ + 2k₁ < s₂` を満たし、両entryの候補がtarget-lowで、間の全時刻の候補がtarget超であるもの。つまり第二combは第一combの後の「最初の」target-low時刻から始まる連続episodeである。

### `UnboundedRightTerminalStream.exists_upwardReset_after` (L29)

**主張:** streamと仮想反例の証明書のもとで、任意の `cutoff` に対し、`cutoff < s₁` かつ `TargetMacroSuccessor target tailStart s₁ k₁ blocker₁ s₂ k₂ blocker₂` かつ `blocker₁ < blocker₂` を満たす連続macro対が存在する。すなわちstreamは任意に遅くまで**upward blocker reset**を行う。

**証明:** 次の補助命題を、第一blockerの値 `blocker₁` に関する強帰納法で示す。

> `cutoff < s₁`、`tailStart < s₁`、候補がtarget-low、`HistoryTerminatedComb s₁ k₁ blocker₁` ならば、cutoff後のupward reset付きmacro対が存在する。

帰納段の議論は次のとおりである。まず `TargetTailResidualKernel.lean` の `exists_targetMacroSuccessor` により、第一combの最終時刻 `s₁ + 2k₁` より後の最小のtarget-low時刻 `s₂` を選び、そこで最大comb抽出をやり直すと、連続macro対 `(s₁, k₁, blocker₁) → (s₂, k₂, blocker₂)` が得られる(最小性が「間はすべてtarget超」の条項をちょうど与える)。

次に区間packingの二分法 `next_entry_below_or_blocker_lt` を適用する: 時系列に並ぶ二つの完了combについて、

`a s₂ < blocker₁`　または　`blocker₁ < blocker₂`

が成り立つ。理由を要約すると、(1) `blocker₁ = blocker₂` は不可能である。最終着地値 `blocker + 1` はその時刻での初出なので、同じblockerを持つ二つのcombは最終時刻が一致してしまい、時系列に矛盾する。(2) `blocker₂ < blocker₁ ≤ a s₂` も不可能である。第二combのlow railは `a s₂` から `blocker₂ + 1` まで1ずつ降りるから、途中で値 `blocker₁` をちょうど踏む。しかしlow railの各値は初出であり、`blocker₁` は時刻 `s₁ + 2k₁ < s₂` までに既出である。矛盾。よってfresh区間は古いblockerを跨げず、上の二択だけが残る。

- **`blocker₁ < blocker₂` の場合:** この対がそのまま求めるupward resetであり、`cutoff < s₁` とあわせて結論が成立する。
- **`a s₂ < blocker₁` の場合:** entry恒等式 `a s₂ = blocker₂ + k₂ + 1` より `blocker₂ < a s₂ < blocker₁`、すなわち第二blockerは厳密に小さい。第二combはそれ自身target-lowの完了combであり、`s₂ > s₁ + 2k₁ ≥ s₁` より `cutoff < s₂` と `tailStart < s₂` も引き継がれる。よって帰納法の仮定を `blocker₂` に適用できる。

blockerは自然数なので、この降下は無限には続かない。これが強帰納法の停止であり、補助命題が示される。

最後に出発点を作る。streamの成分(ii)を `max cutoff tailStart` に適用すると、`cutoff` と `tailStart` の両方より真に後に開始するtarget-low完了combが得られ、補助命題の仮定を満たす。∎

### `UnboundedRightTerminalStream.exists_upwardReset_entry_le_after` (L79)

**主張:** 前定理の結論に加えて、得られたupward resetでは `a s₁ ≤ blocker₂` が成り立つ。すなわち第一combのfresh区間 `{blocker₁ + 1, …, a s₁}` は、全体が新しいblockerの左側(以下)に収まる。

**証明:** 前定理でreset対を取り、`upward_reset_previous_entry_le_blocker` を合成する。この補題は区間の全順序性 `fresh_intervals_ordered`(`a s₂ < blocker₁` または `a s₁ ≤ blocker₂`)から従う。全順序性の後半枝の理由: `blocker₂ < a s₁` と仮定すると、resetにより `blocker₁ < blocker₂` なので値 `blocker₂ + 1` は第一combのfresh区間 `{blocker₁ + 1, …, a s₁}` に入り、第一combのlow railがそれを時刻 `s₁ + 2i`(`i ≤ k₁`)で踏む。しかし `blocker₂ + 1 = a (s₂ + 2k₂)` は第二combの最終着地であり、その時刻 `s₂ + 2k₂ > s₁ + 2i` での初出である。矛盾。一方前半枝 `a s₂ < blocker₁` は、`blocker₁ < blocker₂ < blocker₂ + k₂ + 1 = a s₂` と矛盾するので起こらない。よって `a s₁ ≤ blocker₂` である。∎

### `MissingPermanentAboveTail.eventualHigh_or_infinitelyManyUpwardResets` (L101)

**主張:** 大域kernelの精密化。仮想反例 `MissingPermanentAboveTail target tailStart` のもとで、次のいずれかが成り立つ。

1. `EventualHighCandidateTail target tailStart`: あるcutoff以後、すべての減算候補がtarget超になる(A枝)。
2. `target < root` を満たすpre-tail初出の分離root(`FirstAt a root rootFirstTime`、`rootFirstTime ≤ tailStart`)と `UnboundedRightTerminalStream target tailStart root` が存在し、さらに**任意の**cutoffに対しcutoff後のupward reset付き連続macro対が存在する(B枝)。

**証明:** `TargetTailResidualKernel.lean` の二分法 `eventualHigh_or_unboundedRightTerminal` で場合分けする。A枝はそのまま。B枝ではroot・初出証明・streamを引き継ぎ、各cutoffに対して `exists_upwardReset_after` を適用するだけである。∎

## 全体の中での位置づけ

Round 16の6-gate分解のうちGate 5「無限個のupward reset」を完全にLean化したモジュールである。Gate 3〜4(packing → blocker非有界)は姉妹モジュール `TargetStreamBlockerUnbounded.lean` が担う。本モジュールの `exists_upwardReset_entry_le_after` は `SharpResidualKernel.lean` の `SharpResetStream.upward_resets` フィールドにそのまま供給され、`eventualHigh_or_infinitelyManyUpwardResets` は受け渡しkernel `sharpResidualKernel` の原型である。

この結果により、B枝の残余は「無限個のupward resetがひとつも返済されない(resetのblockerの下に後のtarget-low entryが二度と戻らない)」ことのexactな排除、すなわちreset repayment予想だけに絞られた。この予想は独立なcausal補題が見つからず `STOPPED` 中である(docs/RESET_REPAYMENT_AUDIT_2026-09-01.md)。証明地図では docs/PROOF_MAP.md の「2026-09-01 午後: sharp residual kernel(A/B両枝の並列精密化)」のB枝に対応する。
