# Round 16: parallel residual decomposition

Date: 2026-09-01 (JST)

> Round 17のsemantic auditで、stream型が構築時に持っていたtarget-low startとuniversal
> fixed-root no-escapeを落としていたことを修正した。またreset repaymentの唯一の有限資源候補は
> seeded exact continuationで反証され、枝は15/100・`STOPPED`へ更新された。最新判断は
> [RESET_REPAYMENT_AUDIT_2026-09-01.md](./RESET_REPAYMENT_AUDIT_2026-09-01.md)を参照。

## 結論

既存のfinite-root no-escape、canonical separator、proof architectureを独立に監査した。
全射性へのactive direct branchはまだ0本だが、仮想反例の残余を次の二本へ分ける構成が最も明瞭である。

1. low candidateが有限回しか現れない`eventual-high corridor`
2. ある有限pre-tail rootより右側を、同一targetのterminal combが無限に走る`unbounded right-terminal stream`

finite-root枝は、前処理の大半が既存APIから証明可能である一方、最後のreset repaymentだけが本質的に
新しい数学である。標準prefixだけを再現するcanonical separatorは定義的一意性へ退化し、独立候補ではなかった。

このA/B縮約は`Recaman/TargetTailResidualKernel.lean`としてLean化した。有限pre-tail oracleから
`CoverageOracle`へ直接接続し、全rootがterminal escapeする仮定をtarget occurrenceとの矛盾へ運ぶことで、
固定no-escape rootを抽出する。semantic closureやtail-return仮説はtarget occurrenceと同値なので使っていない。

## 1. finite-root no-escapeの6段分解

### Gate 1: terminal stream extraction

`MissingPermanentAboveTail`のもとでlow candidateが任意に遅く現れるなら、
`unbounded_historyTerminatedFinal_of_unbounded_candidateBelow`により同一targetの
`HistoryTerminatedComb`を任意に遅い時刻へ抽出できる。無限列化はchoice/recursionのproof engineeringであり、
新しい数学ではない。

### Gate 2: fixed-root separator

pre-tailで初出したroot `r`と未来terminal combについて

```text
entry < r  or  r ≤ blocker
```

が`entry_below_or_anchor_le_blocker`からexactに得られる。左枝は
`blockerNormalProgress_or_anchor_le_blocker`によりsemantic progressへ接続済みである。

### Gate 3: finite packing

最初の`n` episodeがすべてblocker側に残るなら、fresh interval幅
`q_i=entry_i-blocker_i`について

```text
n ≤ Σ q_i ≤ maxEntry-r
```

が成立する。pairwise orderと`two_interval_mass_le_hull`の有限list版であり、Lean化可能性は高い。

### Gate 4: no-escape implies unbounded hull

Gate 3から、永久に`entry<r`が起きなければfresh mass、entry hull、blocker側の値域が非有界になる。
これは矛盾ではなく、right ladderが満たすexact residualである。

### Gate 5: infinitely many upward resets

terminal blockerのone-useと自然数の整礎性により、無限right streamは有限下降だけでは続かない。
従ってupward resetを無限に必要とする。この段階も抽象的に導出可能である。

### Gate 6: canonical reset repayment

必要なのは各upward resetについて、次のいずれかを得る新定理である。

```text
target occurs
or
a later terminal entry lies below the reset blocker
```

既存`finiteBasin_rightLadder_countermodel`はGate 1--5をすべて満たし、Gate 6だけを破る。
singleton right ladderはrecord gapが0でも永久無逃避なので、record-gap paymentだけではこのgateを閉じない。

## 2. terminal-anchor nonuniform return audit

pre-tail ancestry rootだけでなく、各terminal blocker自身をhistorical anchorとして、同一targetの後続entryが
初めてanchor未満へ戻るまでを監査した。

| horizon | terminal anchors | resolved | unresolved | no later terminal | max wait |
|---:|---:|---:|---:|---:|---:|
| 20M | 2,660 | 2,642 | 18 | 5 | 653 |
| 200M | 7,922 | 7,904 | 18 | 5 | 3,892 |
| 2B | 21,510 | 21,495 | 15 | 5 | 20,097 |

違反は0だが、最大待ちは増加するためuniform episode boundは再び棄却する。また、これらは実際にはtargetが
後で出現する有限mex epoch、またはhorizon末尾でcensorされた標準prefixであり、permanent-missing tailの
直接観測ではない。

upward reset自身に限定すると次の結果だった。

| horizon | upward reset anchors | later entry below | unresolved | resolved max wait |
|---:|---:|---:|---:|---:|
| 20M | 20 | 18 | 2 | 1 |
| 200M | 24 | 22 | 2 | 1 |
| 2B | 28 | 26 | 2 | 1 |

未解決2件はどちらもtarget 4の初期epochで、reset `(start,anchor)=(23,13),(38,25)`である。
後続entryはanchor未満へ戻らないままtarget 4が実際に出現してepochが終了する。従って標準prefixでは
「target出現またはreset直後の返済」が強く見えるが、これをpermanent-missing仮定で証明する機構は未発見である。

## 3. record-gap future consumption

record生成時に未訪問だったgap値を、後続の標準軌道がhorizonまでに初出する割合をcohort固定で測った。

| cohort | observation horizon | unvisited at record | consumed later | still unvisited | future consumption |
|---|---:|---:|---:|---:|---:|
| gaps completed by 200k | 200k | 44,341 | 34,331 | 10,010 | 77.42% |
| gaps completed by 200k | 2M | 44,341 | 43,881 | 460 | 98.96% |
| gaps completed by 200k | 20M | 44,341 | 44,290 | 51 | 99.88% |
| gaps completed by 2M | 2M | 1,198,921 | 343,897 | 855,024 | 28.68% |
| gaps completed by 2M | 20M | 1,198,921 | 1,103,735 | 95,186 | 92.06% |

古い有限gapがほぼ消費される現象は強い。ただし「各固定gap値がいつか現れる」を一般化すると全射性の
再符号化になりやすく、消費はterminal comb外でも起きる。現時点では診断用のqueue/backlog統計に留め、
これだけをLean仮定へ昇格させない。

## 4. canonical separator audit

既知seeded record-subtraction反例は、標準prefixとclock 4で初めて分岐する。標準は未見candidate 2を
必ず減算して初出させる一方、seeded signed walkは`6+4=10`を選ぶ。

`FirstAt(2,4)`、有限canonical kernel包含、標準prefixのexact maximum envelopeを比較したが、いずれも
独立不変量にならなかった。特にexact canonical state/historyから`Basic.step`を続けると軌道は決定的であり、
cutoff 8/16/32からの「holdout」はすべて同じ標準suffixである。これはseparatorの証拠でなく、canonical
reachabilityそのものの言い換えである。

従ってcanonical separator枝は20/100から5/100へ下げ、独立枝として停止する。

## 5. 更新した評価

| branch | empirical status | proof usefulness | score | decision |
|---|---|---|---:|---|
| residual kernel decomposition | A/B二枝へexact縮約可能 | 循環を避ける最短architecture | 80/100 | Lean化する |
| eventual-high corridor discharge | 任意長seeded high corridorあり | canonical入力候補なし | 12/100 | A枝として保留 |
| finite-root/right-terminal no-escape | 2Bで21,495/21,510 return | reset repaymentが未証明 | 30/100 | 孤立residualとして保持 |
| upward reset repayment | 26/28は次terminalで返済、2件はtarget出現 | permanent tailでは未検証 | 40/100 | 最小の新数学候補 |
| record-gap future consumption | old cohortは20Mで92--99.88%消費 | 全射性の再符号化リスク | 20/100 | 診断のみ |
| canonical reachability separator | exact continuationは一意 | 独立不変量0件 | 5/100 | 停止 |

## 6. 次のgate

形式化する価値があるのは、仮想反例をA/Bへexactに分ける残余kernelまでである。その後は次をgateとする。

- Aを進めるには、arbitrary finite seeded high corridorが満たせないcanonical eventual-high不変量が必要。
- Bを進めるには、upward resetごとに`target occurs ∨ later entry < blocker`を与える、target出現と同値でない
  causal lemmaが必要。
- fresh token、record gap、fixed prefix replayを別名で再導入しない。

いずれのgateも通らなければ、現在のmacro familyによる直接攻略は再停止する。

Leanで得た主要APIは次である。

- `MissingPermanentAboveTail.coverageOracle_of_preTail`
- `MissingPermanentAboveTail.exists_finiteRootTerminalNoEscape`
- `MissingPermanentAboveTail.eventualHigh_or_unboundedRightTerminal`
