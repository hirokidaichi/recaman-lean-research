# Causal run / gap sprint

最終更新: 2026-08-31

## 結論

連続加算runは独立の符号列現象ではなく、visited setの「左隣が既出か」を走査するgap-filling過程である。
この見方から、最大加算runの長さがちょうど2になることは不可能だと紙上で証明できた。

一方、run深部だけを数える高さ評価は10億項で実値より3桁以上緩く、全域性には接続しない。
`NoSevenAdditions`も、gapが逐次充填される機構から見て永続的な定数上界としては疑わしい。
次に残す候補は、長runの正surplusをsingleton runと追加subtractionの負surplusへ割り当てる
**run-level gap flow**である。

## 1. 加算runのshadow predecessor

時刻`s`で`a_s=x`とし、clock `s+1,…,s+L`がすべて加算なら

```text
a_(s+i) = x + i*s + i*(i+1)/2.
```

clock `s+i`の減算候補は、`i≥2`で

```text
a_(s+i-1) - (s+i) = a_(s+i-2) - 1.
```

従ってrunは、2 clocks前に通った値の左隣がvisited setに含まれる限り継続する。

## 2. 最大runの出口はgapを一つ埋める

加算runがclock `s+1,…,s+L`まで続き、次のclock `s+L+1`で減算するなら、着地値は

```text
a_(s+L) - (s+L+1) = a_(s+L-1) - 1.
```

減算が合法なので、この値は正かつ未訪問である。つまり最大runは、shadow predecessor列を既出で
ある限り走査し、最初の未訪問左隣を出口で新規訪問する。

この機構はrunごとにpredecessor gapを減らす。その一方、新しい高値の訪問は別のgapを作れるため、
単純なgap個数は単調量にならない。

## 3. 長さ2の最大加算runは存在しない

clock `s`が減算で、続く`s+1,s+2`が加算だと仮定する。減算式から

```text
a_(s-1) = a_s + s.
```

二回の加算後、clock `s+3`の減算候補は

```text
a_(s+2) - (s+3)
  = a_s + (s+1) + (s+2) - (s+3)
  = a_s + s
  = a_(s-1).
```

これは実prefixで既出かつ正なので、clock `s+3`も強制加算になる。従って

```text
subtraction, addition, addition, subtraction
```

という符号patternは不可能であり、最大加算runの長さは`1`または`3以上`である。

この補題は局所的には新しく明快だが、free-history modelでも正確な直前減算を保持すれば成立する。
従って単独ではjoint-history識別子ではない。

## 4. 深さ別exact scan

`causal_blocker_probe --saturation-lite`で、runの2個目以降、3個目以降、…のclock重みを集計した。

| horizon | final `a_n` | `++` weight | `+++` depth weight | depth≥6 count |
|---:|---:|---:|---:|---:|
| 1,000,000 | 2,057,164 | 632,757,699 | 362,504,492 | 0 |
| 20,000,000 | 16,651,896 | 51,062,458,546 | 29,373,840,960 | 2 |
| 1,000,000,000 | 3,802,905,932 | 14,885,373,832,077 | 8,880,045,218,555 | 13 |

10億項では`+++`深部weightだけでも最終値の約2,335倍ある。したがって「3個目以降の加算だけを
上から数える」という評価も極端に緩い。実際の線形級の高さは、長runの正surplusと、singleton
addition run・連続subtractionの負surplusの大規模な相殺から生じている。

またscan上も完成した長さ2 runは0であり、紙上補題と一致した。

## 5. `NoSevenAdditions`の格下げ

10億項まで最長runは6だが、最大runは出口で「次に必要だった左隣」を新規訪問する。履歴が成長するほど
predecessor-saturationは蓄積し得るため、定数6を普遍上界とみなす理論的根拠は弱い。

判定:

- 経験的回帰テストとして保存
- 全域性の直接枝: **停止**
- Lean化: **見送り**
- 7連続加算の6-blocker全列挙: run-level flowに新しい不等式を与えない限り実施しない

## 6. 新しい候補: run-level gap flow

各最大加算runを一つのepisodeに圧縮する。

- 長さ1: 直後の減算と組にすると負surplus
- 長さ2: 不可能
- 長さ3以上: predecessor-saturationが作る正surplus
- run外の追加subtraction: 純粋な負capacity

job単位の`TailHall₃`では数百万のblocker edgeを扱った。run-level formulationでは、正surplusを持つ
episodeだけを需要とし、singleton runと追加subtractionを容量とする。この圧縮が有望なのは、
長さ2の中間episodeが存在しないという新しい局所事実を使えるためである。

### 継続ゲート

類似問題の[一次文献調査](./LITERATURE_REVIEW_2026-08-31.md)を受け、この枝は単純なrun surplus評価ではなく、
符号付き減算候補`c_n=(a_(n-1):ℤ)-n`のtarget-relative `01/10` transition chargingとして試す。Binary Enots Wolleyの
二側計数とEKGのwindow entry/exit balanceを移植し、同じepisode集合に相反する上下界を作れるかを見る。

次の一回だけ、exact interval Hall scanをこのtarget-relative run episodeへ置き換える。

1. tailで必要な容量定数がclock非依存になる
2. 自由履歴countermodelで同じ不等式が破れる
3. その帰結が既存`liminf a_n/n≤3`より強い

3を満たさなければ、run-level gap flowも全域性枝として停止する。

## 7. target-relative exact probe と最初の有限消費定理

`experiments/target_transition_probe.cpp`で、各時刻のmexを固定targetとみなし、
`nextSubtractionCandidate n = a n - (n+1)`を`L/E/H`（target未満・一致・超過）へ分類した。
高側から低側への減算のあとに現れる

```text
subtraction, forced addition, subtraction, forced addition, ...
```

を一本のdescending comb episodeへ圧縮し、target着地またはhistorical predecessor blockerで
止まるまでを追跡した。20,000,000項のexact scanは次を返した。

| quantity | result |
|---|---:|
| low candidate states | 5,779,960 |
| lowなのにlegal subtractionとなる違反 | 0 |
| `LL` transition | 0 |
| `HL` transition | 5,779,954 |
| completed comb episodes | 2,661 |
| historical blocker termination | 2,660 |
| target termination | 1 |
| horizonで継続中 | 1 |
| protocol violation | 0 |
| terminal blockerの最大再利用 | 1 |
| 最長episodeのfresh landings | 159,583 |

最大の発見は、raw forced-addition jobで偽だった「blockerの有限消費」が、**最大comb episodeの
terminal blocker**では真になることである。terminal blockerを`b`とすると、episode最後の
low-rail landingは`b+1`であり、これはlegal subtractionによるfirst occurrenceである。同じ`b`を
別episodeの終端に再利用するには`b+1`へ再びfresh landingする必要があり、不可能である。

この機構を`Recaman/TargetCandidateTransitions.lean`で形式化した。

- below-target candidateは永久上側tailで強制加算を起こす
- target omissionの下で次のcandidateはtargetを厳密に上回る
- target-relative candidate wordに`LL`はない
- fresh combの全low railはfirst occurrence
- 時間的に分離したfresh combのlow railは値集合として互いに素
- 同じterminal blockerは異なる完了時刻のcombを止められない

### 更新した継続gate

有限消費の部品は得られたので、この枝は停止しない。ただし全域性のdirect branchへ戻すにはまだ早い。
terminal blockerは一回しか使えなくても、blocker値そのものが上へ逃げ続ける可能性がある。

次の一回の紙上課題は、二つのcombの間にある**high-only excursion**をmacro stepとして記述することである。

1. low railのfresh intervalをepisode demandとする
2. terminal blocker `b`を一回消費の境界資源とする
3. high-only excursion内の`HH` addition/subtractionを重み付きentry/exit balanceへする
4. disjoint fresh intervalsとterminal blockerの注入から、同じmacro event集合への上界を作る

20,000,000項ではmex 1355の長区間で`HH=8,296,887`、そのうちsubtraction-causedが
`4,148,440`だった。ほぼ半々という数値だけは証明材料にしない。必要なのはclock重みを含む
厳密なmacro balanceであり、単なる符号個数の近似一致なら棄却する。

## 8. high excursion macro gate とreset provenance

次のエポックでは、連続するhistory-terminated combを時間順に辺で結んだ。前blockerを`b`、
次entryを`y`、次blockerを`b'`とすると、fresh intervalのdisjoint性からLeanで

```text
y < b  または  b < b'
```

を証明した。つまり次のfresh intervalは旧blockerより完全に下へ移るか、blocker自体が上へresetする。
旧blockerをfresh intervalが跨ぐ第三形はない。

20M exact scanの結果は次の通り。

| macro quantity | result |
|---|---:|
| chronological historical-comb edges | 2,655 |
| blocker down / up / equal | 2,635 / 20 / 0 |
| fresh interval separator violation | 0 |
| subtraction-origin terminal blockers | 1,260 / 2,660 |
| subtraction predecessor `≤ entry` violation | 0 |
| smallest strict predecessor lift | 37 |
| upward reset origin: subtraction / addition | 0 / 20 |

signed excess

```text
E_m(n) = a_n - (n+1) - m
```

は加算で`+n`、減算で`-(n+2)`だけ変化する。maximal high excursionの出口はlegal subtractionで、
直前には`0 < E_m(n) < n+2`が成立する。全prefixのstrict ledger corridorもLean化した。しかし総和は
既存ledger identityの望遠和であり、新しい容量制約ではない。さらに5,779,954個のhigh-to-low出口で
window違反0だった一方、最小slackは1、最大利用率99.9999%だった。従って一様margin枝は棄却する。

terminal blockerの初出生成には次のexact dichotomyが残る。

- legal subtraction origin: 生成元predecessorはcomb entryより厳密に上。さらにそのfirst timeはblockerより前
- forced addition origin: 生成元predecessorはblockerより厳密に小さく、そのfirst timeも前

20Mのupward resetは全て後者だった。次の研究gateは、upward resetのsubtraction originを一般に排除するか、
value liftとfirst-time descentを組み合わせたwell-founded macro rankへ送ることである。
