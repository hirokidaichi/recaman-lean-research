# Causal invariant sprint 1

最終更新: 2026-08-30

## 目的

Leanのstructureやcase splitを増やす前に、実Recamán軌道では成立し、自由履歴モデルでは破れる
因果的不変量を紙上・計算で一つ抽出する。最初の対象はpositive blocker jobの容量所有権と、
連続加算runが要求するpredecessor historyである。

## 1. 単純なblocker所有権は棄却

positive blocker job

```text
(release, deadline, demand) = (lastOccurrence + 1, clock - 1, clock)
```

を、そのwindow内のfirst subtractionまたはlast subtractionへ丸ごと割り当て、clock `k` に
容量 `k+3` を持たせる二つの局所説明を試した。

20,000,000項、`release≥7`での最大overloadは次の通り。

| 所有権 | 最大overload | subtraction clock | load | jobs |
|---|---:|---:|---:|---:|
| first subtraction | 90,268,343 | 832,511 | 91,100,857 | 9 |
| last subtraction | 65,670,373 | 16,417,589 | 82,087,965 | 5 |

したがって`TailHall₃`を一つの代表subtractionへの局所写像として証明する路線は棄却する。
必要なら容量を複数clockへ分割するinterval flowとして扱う必要がある。

## 2. 連続加算runの正確な因果式

時刻`s`で`a_s=x`とし、clock `s+1,…,s+L`がすべて加算だとする。紙上のtelescopingから、
`1≤i≤L`について

```text
a_(s+i) = x + i*s + i*(i+1)/2
```

である。さらに`2≤i≤L`ならclock `s+i`の減算候補は

```text
a_(s+i-1) - (s+i)
  = x + (i-2)*s + i*(i-3)/2
  = a_(s+i-2) - 1.
```

従って`i≥3`ではこの候補は正であり、加算が続くためには

```text
a_(s+i-2) - 1 ∈ valuesThrough(s+i-1)
```

が必要である。長い加算runは、自由に選べるblocker列ではなく、run中の各値の直下`−1`が
過去に共同生成されているというpredecessor-saturation chainを要求する。

これはarbitrary-history countermodelが明示的にseedしていた値列そのものであり、局所条件と
実軌道の差を一つの式にしたものである。

## 3. exact scan

`experiments/causal_blocker_probe.cpp`のdense bitset scanで、次を得た。

| horizon | 最長加算run | 最初の記録区間 |
|---:|---:|---:|
| 100 | 3 | `[1,3]` |
| 1,000,000 | 5 | `[30049,30053]` |
| 20,000,000 | 6 | `[5026070,5026075]` |
| 1,000,000,000 | 6 | `[5026070,5026075]` |

長さ6のrunは、最初がnonpositive additionで、その後のpositive blockerが

```text
1142242, 6168312, 11194383, 16220455, 21246528
```

である。10億項まで7連続加算は存在しない。

この観測は有限計算であり、`NoSevenAdditions`を主張する証明ではない。任意長の自由履歴suffixは
既に構成できるため、少なくともstatic seen-setだけから自動的に従う性質ではない。

## 4. 候補評価

### Candidate C1: `NoSevenAdditions`

```text
任意のsについて、s+1,…,s+7の全てが加算になることはない。
```

- 実軌道での真らしさ: **78/100**
- 紙上証明の見込み: **35/100**
- causal historyの識別力: **75/100**
- 全域性への直接寄与: **15/100**

有限の加算run上界`K`からは、各`K+1` clocksに少なくとも一回のsubtractionが従う。しかし
subtraction massの下界は依然として三角和の定数割合に留まり、固定missing targetとの矛盾や
線形成長は単独では出ない。従って、経験的に強くても直接証明枝へは戻さない。

### Candidate C2: predecessor-saturation budget

run長そのものを固定定数で抑える代わりに、既出条件

```text
a_t - 1 ∈ valuesThrough(t+1)
```

が連続して使われるたび、再利用不能な資源またはgap massが減るという償却則を探す。

- 現時点の有望度: **45/100**
- 利点: free-historyとの違いを直接使う
- リスク: adjacencyは単調に蓄積し、別runから再利用できる可能性がある

こちらを次の紙上スパイクとする。ただし、単なる「隣接既訪問pairの個数」は単調増加するだけなので
不十分である。pairのfirst-occurrence time、再利用clock、介在subtractionのいずれかを重みに入れる。

## 5. 次のゲート

Lean化はまだ行わない。次のどちらかを満たした場合だけ再検討する。

1. predecessor-saturation edgeの再利用ごとに厳密に消費される量を紙上で定義できる
2. `NoSevenAdditions`から既存ledger密度より強く、permanent-above tailに固有の帰結を導ける

いずれも得られなければ、加算run上界は独立した経験則として保存し、gap dynamicsの別状態量へ移る。

## 6. predecessor-saturation edge の再利用監査

連続する二加算がclock `t+1,t+2`で起きるとき、sourceを`v=a_t`とする。`v>1`なら二番目の
加算候補は`v-1`であるため、因果辺

```text
(t,v) → lastOccurrence_t(v-1)
```

を張れる。`causal_blocker_probe --saturation`で、この辺とsource valueの再利用を調べた。

| horizon | saturation events | distinct sources | fresh / revisit | max source reuse |
|---:|---:|---:|---:|---:|
| 1,000,000 | 1,724 | 1,720 | 952 / 772 | 2 |
| 20,000,000 | 7,464 | 7,454 | 3,851 / 3,613 | 2 |
| 1,000,000,000 | 45,819 | 45,798 | 23,009 / 22,810 | 2 |

20,000,000項の詳細scanでは、同じlast-predecessor timeへのedge再利用も最大2だった。一方、
predecessor ageは18,378,765 clocksまで伸びた。また同じ軌道値の総出現回数は最大48であり、
source reuse 2は「値そのものがほとんど再訪しない」ことの言い換えではない。

しかし、この結果だけでは償却potentialにならない。長さ`L`の一つの加算runは`L-1`個の異なる
source valueを使えるため、各sourceの再利用回数を2で抑えてもrun長やsubtraction massは抑えられない。
predecessor ageも一様に大きくなるので、時間差による減衰も使えない。

判定:

- fixed source multiplicity potential: **停止**
- predecessor age potential: **停止**
- 「再利用回数≤2」自体: 経験的構造候補として保存、Lean化しない

## 7. 最長runのblocker install

10億項までの最長加算run `[5026070,5026075]` が要求するpositive blockerの初出は次の通り。

| blocker | first time | generation |
|---:|---:|:---:|
| 1,142,242 | 519,475 | addition |
| 6,168,312 | 5,026,068 | subtraction |
| 11,194,383 | 5,026,061 | addition |
| 16,220,455 | 5,025,398 | subtraction |
| 21,246,528 | 5,025,859 | subtraction |

最初の一個を除く四個はrun開始の677 clocks以内に共同生成されている。これは長runの障害を
「古いblockerの固定予算」ではなく、短いprefix内でaffine predecessor群を同時にinstallする
congestionとして見るべきことを示す。

次の紙上候補は、長さ`L`の加算runが要求する

```text
B_i = x + (i-2)*s + i*(i-3)/2,  2≤i≤L
```

のfirst-installation windowsに対するHall型不等式である。まず`L=7`の六blockerを試験問題にし、
ledger・parityだけでなく同じprefixでのjoint generationを使う不等式が出るかを見る。これは
`NoSevenAdditions`の紙上証明候補ではあるが、証明できても全域性への寄与は小さいため、
大規模Lean化は行わない。
