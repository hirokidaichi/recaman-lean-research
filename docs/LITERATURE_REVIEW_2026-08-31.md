# 類似 greedy 数列の解決例 — 文献レビュー

最終更新: 2026-08-31

## 結論

今回確認した解決例のうち、標準 Recamán 数列へ最も近い証明機構は
**Binary Enots Wolley の opportunity counting** である。目標値が候補になる時刻を数え、
候補になったのに選ばれない各回を、それより小さい既出候補へ課金し、最後に二種類の出現数の
相反する評価を作って全射性を示している。

次に重要なのは EKG sequence の **least-unused frontier / sandpile ladder** と、Yellowstone
permutation の **最小未出値 + 状態遷移** である。ただし両者は「条件を満たす全未使用整数の中から
最小を選ぶ」。標準 Recamán は時刻ごとに候補が二つしかない。この差のため、最小未出値論法を
そのまま移植することはできない。

文献から得た研究上の判断は次の通り。

- 既存の run-level gap flow を、そのまま総 surplus 評価として続けるのではなく、
  **target-relative transition charging** に組み替える価値がある。
- 課題は「候補が十分多く現れる」ことではない。Recamán では、未出目標が一度でも減算候補に
  なれば即座に選ばれる。課題は、その **opportunity を少なくとも一度生成する輸送補題** である。
- positive blocker は何度も再利用され、競合候補のようには消費されない。従って Binary Enots
  Wolley 型の単純な有限課金は偽であり、gap class・初出時刻・reset を含む二側の計数が必要である。
- 文献レビューだけで direct branch を再開する根拠にはならない。まず exact probe と紙上補題で
  free-history model を分離する必要がある。

## 1. 調査した一次文献

### 1.1 EKG sequence — 全射性と線形上下界

J. C. Lagarias, E. M. Rains, N. J. A. Sloane,
[The EKG Sequence](https://arxiv.org/abs/math/0204011), Experimental Mathematics 11 (2002), 437–446.

定義は、直前項と非自明な公約数を持つ未使用自然数のうち最小を選ぶもの。論文は自然数の
permutation であることと線形上下界を証明している。

全射性証明の核は、各素数 `p` に対する frontier

```text
B_p(n) = 時刻 n までに未使用な最小の p の倍数
```

を導入することである。次項は直前項を割る素数 `p` についての `B_p(n)` の最小値になる。
これにより、ある素数の倍数が無限に現れれば、その素数の全倍数が現れ、さらに全自然数が現れる。
新しい素数の導入順序も単調に制御できる。

線形上界の証明はさらに示唆的である。未使用最小倍数を ladder の頂点とみなし、値の window への
entry と exit の個数が等しいことを使う。多数の exit があれば、それらを作った別の controlling
prime ladder が多数必要になり、sieve / inclusion-exclusion で既出項が時刻数を超える矛盾を出す。

**Recamán への転用可能性: 高。** `B_p` そのものは存在しないが、最大加算runが「2 clocks 前の値の
左隣」を既出である限り走査し、最初の未訪問左隣で終了することは、局所的な least-unused frontier
と読める。特に entry/exit の釣合いを使う点は、現在の interval Hall と run-gap flow の統合候補である。

### 1.2 Yellowstone permutation — 最小未出値を状態遷移で露出させる

D. L. Applegate, H. Havermann, R. G. Selcoe, V. Shevelev, N. J. A. Sloane, R. Zumkeller,
[The Yellowstone Permutation](https://cs.uwaterloo.ca/journals/JIS/VOL18/Sloane/sloane9.html),
Journal of Integer Sequences 18 (2015), Article 15.6.7.

次項は、二つ前の項と公約数を持ち、直前項とは互いに素な未使用整数のうち最小のもの。
論文は次の段階で全射性を示す。

1. 常に候補があり、列は無限に続く。
2. 項を割る素数は無限種類ある。
3. 任意の素数 `p` が少なくとも一項を割る。
4. 任意の素数 `p` が無限個の項を割る。
5. 各素数 `p` 自身が項として現れる。
6. 最小未出値 `k` を取り、`gcd(a(n),k)>1` から `=1` への遷移があれば二時刻後に `k` が選ばれる。
   遷移が永遠にないという残余は、素数項が無限に現れることと矛盾する。

**Recamán への転用可能性: 中。** 「最小未出値を選ばせる局所状態遷移」を作る構図は近い。
しかし Yellowstone は全整数から最小候補を選べるため、遷移さえ起これば `k` が露出する。
Recamán では `a_(n-1)-n=k` という一つの対角等式を実際に通過させる必要がある。

### 1.3 Binary Enots Wolley — opportunity counting と二側課金

Nathan Nichols,
[Surjectivity of a Binary Analog of the Enots Wolley Sequence](https://arxiv.org/abs/2207.01448),
arXiv:2207.01448 (2022).

素因数集合の代わりに二進 support を使う greedy sequence で、binary weight が2以上の全正整数が
現れることを証明している。

最も重要な補題は次の有限消費則である。

```text
目標 k が候補になる時刻が k 回以上あれば、k は必ず現れる。
```

`k` が候補なのに選ばれないときは、`k` より小さい別候補が選ばれる。小さい正整数は `k-1` 個しかなく、
列に重複がないため、妨害は高々 `k-1` 回しか続かない。

論文は各目標 support に対する0/1 truth tableを導入し、`01` 遷移が無限にあることを示す。weight 2 の
場合には、一方のbitだけを含む既出項の個数 `P,Q` と、両方を含む既出項の個数 `PQ` を数える。
目標が現れないと仮定すると局所patternから `PQ` が `P` または `Q` より速く増える一方、greedy最小性は
各 `PQ` event より前に一方だけを持つ小候補が両方とも消費済みであることを要求し、
`P,Q ≥ PQ` を与えて矛盾する。

**Recamán への転用可能性: 最も高い。** 現在の Hall / blocker の考え方に、単なる総容量ではなく
「同じevent集合から相反する上下界を作る」という欠けていた形を与える。ただし Recamán の blocker は
再利用可能なので、`k-1` 個の小候補という有限資源をそのまま置き換えることはできない。

### 1.4 Binary Two-Up — finite atoms による大域構造

M. De Vlieger, T. Scheuerle, R. Sigrist, N. J. A. Sloane, W. Trump,
[The Binary Two-Up Sequence](https://arxiv.org/abs/2209.04108), arXiv:2209.04108 (2022).

過去の一定割合の項とbinary supportが交わらない最小未使用整数を選ぶ列。論文は列を長さ4, 6, 8の
有限種類の atoms に分解し、有限区間を長さ2倍の区間へ送る local algorithm と atom substitution により
大域構造を証明する。その帰結として、全非零項のbinary weightが高々2であることなどが得られる。

**Recamán への転用可能性: 低から中。** addition runをepisodeへ圧縮する方向は同じだが、現在の実験は
run長に普遍的な定数上界がある根拠を与えていない。atoms を作るなら run長ではなく、入口gap・出口gap・
blocker provenance を含む状態で閉じる必要がある。

### 1.5 Three Cousins of Recamán's Sequence — 履歴を消去できた変種

M. A. Alekseyev, J. S. Myers, R. Schroeppel, S. R. Shannon, N. J. A. Sloane, P. Zimmermann,
[Three Cousins of Recaman's Sequence](https://arxiv.org/abs/2004.14000),
Fibonacci Quarterly 60 (2022), 201–219.

三つの「遠い従兄弟」を扱う。最初の加算型停止問題は三角数の Diophantine 条件へ変形することで明示的に
解かれ、停止時刻に二次上界を与える。一方、他の変種には予想が残る。

**Recamán への転用可能性: 低。** 成功した理由は visited history を静的な除法条件へ消去できたことにある。
標準 Recamán の難所はまさにその履歴依存なので、これは「代数変形だけで解ける形への還元が見つからない限り
近道にはならない」という negative control になる。

## 2. 解決例に共通する証明部品

文献の成功例は、概ね次の5部品のいずれかを持つ。

1. **frontier** — 各制約クラスについて、次に消費される最小未使用要素を単調量として持つ。
2. **opportunity lemma** — 目標が候補になる機会が十分あれば、greedy性により必ず選ばれる。
3. **recurrence of opportunities** — 各制約クラスまたは0/1状態遷移が無限に再来する。
4. **finite consumption / two-sided count** — 目標を妨害する小候補が一度しか使えない、または同じeventに
   相反する上下界を与えられる。
5. **finite atomization** — 局所状態が有限種類に閉じ、置換・帰納で全履歴を生成できる。

標準 Recamán に既にあるのは局所 frontier の一部と、fresh subtraction の一回消費性である。
欠けているのは 3 と 4 を同じ target-relative event 集合上で結ぶ定理である。

## 3. Recamán への翻訳

clock `n≥1` の符号付き減算候補を整数上で

```text
c_n ∈ ℤ := (a_(n-1) : ℤ) - n
```

と置く。未出の正目標 `m` に対して `c_n=m` となれば、減算は合法かつ未使用なので、そのclockで
必ず `m` が選ばれる。従って、Binary Enots Wolley の「`k` 回候補になれば十分」より強く、Recamán では

```text
一回の opportunity で十分。
```

一方、`c_n` の遷移は

```text
addition at clock n:     c_(n+1) = c_n + n - 1
subtraction at clock n:  c_(n+1) = c_n - n - 1
```

である。`c_n=m` を避ける軌道は、target level `m` を大きなjumpで飛び越え続ける。上向きcrossingは
forced additionであり、その時の `c_n` は非正か既出のblockerである。下向きcrossingは合法減算で、
fresh landing を一つ消費する。

この記述は既存の diagonal / blocker / ledger を言い換えただけではある。しかし文献が示す新しい焦点は、
総jump massを一方向に評価することではなく、同じ target-level crossing event について

- dynamics が要求する event 数の下界
- blocker / gap resource が許す event 数の上界

を別々に作ることである。

## 4. 次に試す一枝: target-relative transition charging

固定目標 `m` ごとに

```text
χ_m(n) = 1[c_n > m]
```

を記録し、`01` と `10` の遷移を最大加算run単位へ圧縮する。

各 `01` event には次を付与する。

- crossing直前の `c_n`
- positive old blocker か nonpositive reset か
- blockerのfirst/last occurrence時刻
- 同じrunが走査したshadow predecessor gap
- crossing overshootと、その後の最初の`10`までのsubtraction mass

各 `10` event にはfresh subtraction landingと、直前runが埋めた最初の未訪問左隣を付与する。

狙う形は、Binary Enots Wolley の `P,Q,PQ` に対応する二側不等式である。具体的には、同じcrossing
episode集合 `E` に対し

```text
dynamics / recurrence:       full-gap events(E) > one-sided resources(E)
greedy / provenance charge:  full-gap events(E) ≤ one-sided resources(E)
```

を得る。ここで resource を個々のblocker値にすると再利用で破れるため、first-occurrence interval、
gap endpoint、またはreset-separated provenance classを使う必要がある。

### 継続ゲート

次の exact probe は一回だけ行い、以下をすべて要求する。

1. target-relative `01/10` episodeを数えると、既存の総ledger / `TailHall₃` より強い不等式候補が出る。
2. resource を値だけでなく provenance class にしたとき、必要容量がclockに依存しない。
3. 同じ不等式が実軌道の別horizonで再現し、free-history countermodelでは破れる。
4. permanent-above least-missing tail のどの残余ケースを排除するかが明示できる。

満たさなければ、この枝も全域性の直接候補として停止する。有限atom化は、上のprobeで状態種類が
実際に閉じる兆候が出た場合だけ再開する。

## 5. 有望度更新

| 方法 | 文献上の成功機構 | Recamánへの有望度 | 判定 |
|---|---|---:|---|
| target-relative transition charging | Binary Enots Wolley の opportunity + 二側計数 | 45/100 | 次の探索枝 |
| frontier-window entry/exit | EKG の ladder + sieve | 35/100 | 上枝へ統合 |
| global least-missing transition | Yellowstone の状態遷移 | 20/100 | 単独移植は停止 |
| provenance-aware finite atoms | Binary Two-Up の局所倍化 | 15/100 | データ依存の保留 |
| static Diophantine collapse | Three Cousins の代数化 | 5/100 | negative control |

ここでのスコアは全域性への直接到達見込みではなく、**次の一回の研究投資先としての相対評価**である。
紙上補題はまだ得られていないので、direct branch の本数は0のままとする。
