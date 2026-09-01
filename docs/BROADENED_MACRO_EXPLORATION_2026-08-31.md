# Target-comb macro 幅広探索

最終更新: 2026-08-31

## 結論

upward reset provenanceだけに固定せず、first-occurrence ancestry、fresh intervalの値順序、
interval traversal、record gap fluxを同じ20M exact軌道で比較した。

一つの新しいLean定理が残った。時間順の任意二つのhistory-terminated combのfresh intervalは、
値軸上で必ず完全に分離する。

```text
laterEntry < earlierBlocker
  または
earlierEntry ≤ laterBlocker
```

一方、短い祖先鎖、一回消費ancestry、隣接intervalだけを辿るstack構造は棄却された。
次に試す価値があるのは、経験的な**upward resetは過去全体のright recordになる**という法則と、
そのrecord拡張が作る未訪問gap massの流れである。

## 1. first-occurrence ancestry

各値を、そのfirst occurrenceを作った直前値へ戻す。first timeは毎回厳密に下がるので有限だが、
有限であること自体は新しいcapacityを与えない。

20Mまでのupward reset 20件について、新blockerから旧blocker以下へ戻る祖先鎖を追跡した。

| quantity | result |
|---|---:|
| ancestry total steps | 181,442 |
| maximum path length | 60,651 |
| maximum subtraction-origin steps in one path | 30,318 |
| exact old-blocker hit | 2 / 20 |
| ancestry edge maximum reuse | 7 |
| threshold-crossing edge maximum reuse | 4 |

従って「resetごとに短い祖先鎖」「crossing edgeを一回だけ課金」という候補は停止する。
forced-addition originの一歩目が`EarlierSmaller`へ入る事実は有効だが、祖先全体を固定容量として
数えることはできない。

## 2. fresh intervalの全順序

history-terminated comb `(s,k,b)`のfresh low railは連続整数区間

```text
[b+1, a_s]
```

を一度ずつ着地する。後のcombも同様で、両区間が交われば後のfirst occurrenceに反する。
この連続性を使い、`HistoryTerminatedComb.fresh_intervals_ordered`をLeanで証明した。

これは従来の

```text
laterEntry < earlierBlocker ∨ earlierBlocker < laterBlocker
```

を、後者では**earlier interval全体がlater blocker以下**という完全な区間順序へ強化する。

## 3. global right-record則

20Mの連続macro辺2,655本について、upward reset 20件はすべて新intervalを過去全intervalより
右へ置くglobal right recordだった。gap insertion型upward resetは0である。

| interval motion | count |
|---|---:|
| upward global-right record | 20 |
| upward insertion into an old gap | 0 |
| downward global-left record | 293 |
| downward insertion into an old gap | 2,342 |

ただしこれはpairwise interval orderだけからは出ない。抽象的には

```text
I₁=[101,110], I₂=[11,20], I₃=[31,40]
```

という互いに素な時間順intervalが、down後のupを古いgapへ挿入する。従ってglobal right-record則を
証明するには、terminal blockerのactual first-transition provenanceが不可欠である。

またupward 20件中17件は、直前intervalとの間に既存intervalを飛び越え、最大2,237本を跨いだ。
downwardでも1,142件が介在intervalを跨ぎ、最大71本だった。単純な隣接stack / depth-first traversalは
実軌道上でも偽である。

## 4. record gap flux

upward recordが旧right hullと新blockerの間に作ったgapを集計した。

| quantity | result |
|---|---:|
| total record-gap mass | 17,820,564 |
| reset時点で未訪問 | 14,775,263 |
| horizon 20Mでも未訪問 | 9,518,181 |
| smallest record expansion | 1 |
| origin predecessor inside / above prior fresh hull | 2 / 18 |

fresh intervalだけを閉じた保存系とみなすことはできない。18件ではreset blockerの加算元predecessorが
prior fresh hullよりさらに上にあり、高値reservoirがrecord拡張を供給している。さらに大量のgapが
horizon後も未訪問なので、gap massが即座に減る単調量でもない。

一方で、record expansionと後続downward gap insertionを同じ値軸上で測れることは残る。
次にgap fluxを試すなら、fresh interval massだけでなく、high-value predecessor reservoirを明示した
二成分収支が必要である。

## 5. 分岐評価

| branch | evidence | score | decision |
|---|---|---:|---|
| pairwise fresh-interval order | Lean証明済み | 80/100（部分構造） | 保存・基盤化 |
| global upward right-record | 20/20、反例0 | 55/100 | 最優先の未証明候補 |
| record-gap / high-reservoir flux | 大量gapと後続fillを分離 | 45/100 | secondary探索 |
| two-phase origin rank | addition枝は`EarlierSmaller` | 40/100 | subtraction liftの接続待ち |
| bounded ancestry charging | max path 60,651、reuse 7 | 10/100 | 停止 |
| interval stack traversal | 介在最大2,237 | 5/100 | 棄却 |
| uniform exit margin | slack 1まで飽和 | 5/100 | 棄却済み |

## 6. 次の限定探索

次の一回は次の順で行う。

1. `global upward right-record`をactual blocker provenanceから導けるか紙上で試す
2. 導けない場合、有限のabstract orbit prefixでgap-insertion resetを作り、候補を棄却する
3. right-recordが通った場合だけ、record gap massとhigh predecessor reservoirの二成分potentialを設計する

right-record単独ではrecord値が無限に増える可能性を排除しない。従ってこれを証明できてもdirect branchは
再開せず、gap fluxにstrict driftが得られた時だけ全域性への接続を再評価する。
