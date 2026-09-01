# Record-gap / high-reservoir potential 監査

最終更新: 2026-08-31

## 結論

静的な二成分 potential

```text
fresh hull 内の未訪問穴  ±  fresh hull 外の既訪問 reservoir
```

は全域性に必要な新しい因果情報を持たない。個数差は `hull endpoint - distinct visited count`、
一次モーメント差は三角数と既訪問値の総和へ厳密に潰れる。符号を和に変えても upward reset で
一定方向の drift は出ない。従って、このままの gap/reservoir potential は停止する。

一方、high predecessor は捨てるべき外乱ではない。addition-origin record blocker
`b = p + t` を first-occurrence ancestry へ展開すると、record gap は ancestry edge が値軸上の
cut を横切る**符号付き長さ**として厳密に表せる。異なる right-record gap は互いに素なので、
同じ ancestry edge が複数 path で再利用されても、gap との交差長の総和は edge の clock weight を
越えない。unweighted edge reuse が最大7だったという反例を回避する、現時点で唯一残る会計である。

ただし得られる上界は今のところ「first-occurrence addition clock weight 以下」であり、最悪
`O(N^2)` の既存 ledger 容量へ戻る。全域性へ進むには、同じcut上の subtraction-origin crossing を
落とさず、正味 flux に線形級以下の上界を与える追加補題が必要である。

## 1. 記法

固定 target の時間順 history-terminated comb が作る fresh interval を

```text
I_j = [b_j + 1, e_j]
```

とする。`b_j` はterminal blocker、`e_j` はentryである。既存Lean定理
`HistoryTerminatedComb.fresh_intervals_ordered` により、これらは値軸上で互いに素かつ全順序である。

最初の `j` 個のintervalの右端を `U_j = max_{i≤j} e_i` とする。upward resetがglobal right record
である場合は `U_{j-1} ≤ b_j` であり、新しく開くrecord gapは

```text
G_j = (U_{j-1}, b_j],    g_j = |G_j| = b_j - U_{j-1}
```

である。以下でright-recordを使う主張は、現時点ではその未証明仮定の下での条件付きexact主張である。

## 2. exact な会計

### 2.1 interval hull の幾何学的 gap

fresh interval の被覆だけを見る。現在の左右hull内でintervalに覆われない長さを `H` とすると、
新interval追加時の変化は厳密に次の三形になる。

```text
right record [b+1,e] : ΔH = b - U
left record  [b+1,e] : ΔH = L - e - 1
internal insertion    : ΔH = -(e-b)
```

従って、固定missing targetのtailでleft recordが有限回しか起きないことまで使っても、得られるのは

```text
internal fresh mass ≤ initial holes + right-record gap mass
```

だけである。right record が無限に新しい予算を作れるので、向きが全域性の矛盾と逆である。

### 2.2 actual visited set による gap の三分割

right reset時の `G_j` は互いに素で、各値は次の三つへ一意に分かれる。

1. reset前から既訪問
2. reset時は未訪問だが後のhorizonまでに訪問
3. horizonでも未訪問

20M exact scanでは

```text
3,045,301 + 5,257,082 + 9,518,181 = 17,820,564
```

である。割合はそれぞれ約 `17.1% / 29.5% / 53.4%`。これは単なる近似ではなく、probeが返した
`gapMass`, `unseenAtReset`, `unseenAtHorizon` の差から得る有限horizon上のexact partitionである。

### 2.3 count potential の退化

有限visited setを `V`、right hullを `U` とし、

```text
M_U = |[0,U] \ V|              -- hull内の未訪問穴
R_U = |V ∩ (U,∞)|              -- hull外の既訪問reservoir
D   = |V|
```

と置くと、常に

```text
M_U - R_U = (U + 1) - D
```

である。right hullをgap越しに拡張したとき、旧gap中の未訪問数を`u`、既訪問数を`q`とすれば、
`M`は`u`増え、旧reservoirは`q`減るので `M-R` は `u+q=g` 増える。しかしこれは上式の
`U`更新を別表現しただけで、causal invariantではない。

任意の固定weight `w` に対しても

```text
Σ_{x≤U,x∉V} w(x) - Σ_{v>U,v∈V} w(v)
  = Σ_{x=0}^U w(x) - Σ_{v∈V} w(v)
```

へ潰れる。特にhullからの距離をweightにした差も、三角数・`|V|`・`ΣV`の一次モーメント恒等式に
過ぎない。静的なper-value加法potentialをさらに係数探索する枝は停止する。

### 2.4 addition-origin predecessor の gap 分解

record blocker `b` のfirst occurrenceがclock `t`のadditionで、直前値が`p`なら

```text
b = p + t
g = b - U = t + (p-U)
```

である。従って

```text
p ≤ U なら g ≤ t
p > U なら g = t + (p-U)
```

がexact。後者の`p`は旧reservoir内にあり、reset後はfresh hullの内側へ飲み込まれる。right hullが
単調に更新される限り、後続right resetの「hullより上の選択predecessor」として同じ値を再利用できない。

これはcount tokenとしては一回消費だが、高さ`p-U`に一様上界がないため、それだけではgap massを
抑えない。20Mの `inside/above = 2/18` はこのexact二分の経験的分布である。

### 2.5 ancestry cut identity

`b=x_0`からfirst-occurrence predecessorを辿り、初めて`x_K≤U`となるpath

```text
x_0, x_1, ..., x_K
```

を取る。各edge `x_i -> x_{i+1}` は、`x_i`のfirst occurrenceがadditionなら値軸を下向きに
`t_i`、subtractionなら上向きに`t_i`進む逆向きedgeである。cut `G=(U,b]` とedge区間の交差長を
`ell_i`とすると、各levelのcrossing回数を望遠和することで

```text
b-U = Σ(addition-origin ell_i) - Σ(subtraction-origin ell_i)
```

が厳密に成り立つ。pathが何度上下してもよい。

複数のglobal right-record gap `G_j` は互いに素である。同じancestry edgeが複数pathに現れても、
そのedgeと異なる`G_j`との交差部分も互いに素なので、正の交差長の総和はedge全長`t_i`以下である。
従って有限個のresetについて条件付きで

```text
Σ_j g_j
  ≤ Σ { t(e) | 少なくとも一つの G_j を横切る distinct addition-origin edge e }
```

を得る。high predecessor項`p-U`は、そのpredecessorのさらに古いancestryがcutを横切るfluxへ
変換される。これは「reservoirを別勘定で無制限に足す」必要をなくす。

## 3. exact / empirical / false の分類

| statement | status | 判定 |
|---|---|---|
| fresh intervalsは互いに素・全順序 | Lean exact | 基盤として保存 |
| upward resetはglobal right record | 20/20 empirical | provenance証明待ち |
| upward reset blockerはaddition origin | 20/20 empirical | 一般排除定理なし |
| record gapの三分割 | finite-horizon exact | 観測量として保存 |
| `M-R = U+1-|V|` | exact identity | static count potentialを棄却 |
| height-weighted差は一次モーメントへ退化 | exact identity | static linear weight探索を棄却 |
| `M+R`に一方向driftがある | false / unsupported | reset時変化は`u-q`で符号不定 |
| high predecessorは一回消費token | conditional exact | 個数には有効、massには不足 |
| ancestry pathは短い | false | max 60,651 |
| ancestry edgeは一回だけ使われる | false | max reuse 7 |
| disjoint cutとの**交差長**はedge長以下 | conditional exact | 再利用を重み付きで回避 |
| gap massはraw addition clock massで矛盾する | false as a strategy | RHSは最悪`O(N^2)` |

## 4. 棄却するpotential

次は追加実験なしで停止する。

- `holes - reservoir count`: distinct-count恒等式
- `weighted holes - weighted reservoir`: visited-set moment恒等式
- `holes + reservoir`: resetごとの符号が不定
- selected predecessor一個へのgap全量課金: `p-U`が無界
- unweighted ancestry token: 実測reuse 7、path長60,651
- record gapが短期間で埋まるというdrift: 20M時点で53.4%が未訪問

## 5. 残す枝と最小の次補題

残すのは静的potentialではなく、**first-occurrence ancestry の値cut flux**である。有望度は
`45/100 → 50/100`へ小幅更新する。理由は、high-reservoirをexactに再帰展開し、unweighted reuseの
反例を幾何学的disjointnessで無効化できるため。ただし二次ledgerへ退化する危険がまだ大きい。

最小の次補題は、軌道意味論を持ち込む前の有限整数path補題である。

```text
path_cut_balance:
  x_0 > U, x_K ≤ U
  → |(U,x_0]| = downwardCrossLength - upwardCrossLength
```

次に互いに素なcut族へ上げる。

```text
disjoint_record_cuts_addition_capacity:
  pairwiseDisjoint G_j
  → Σ |G_j| ≤ Σ (distinct addition-origin edge clock weights)
```

Lean化より先にprobeへ各upward resetの `addCross`, `subCross`, distinct-edge weighted capacityを追加し、
`1M / 5M / 10M / 20M`で次を判定する。

1. `gap = addCross - subCross` が実装上exactに一致する
2. edge reuse後もdistinct addition capacityで上界が成立する
3. `subCross/addCross` またはcut外addition massに、horizonとともに強くなる境界がある

3が見えず、上界が単に全addition clock ledgerへ戻るなら、この枝も全域性approachとして停止する。

## 6. 第2ラウンド: cut balance の形式化と敵対的上界

### 6.1 独立Lean module

軌道意味論を使わない有限整数path部分を `Recaman/RecordGapCutFlux.lean` に分離した。主要定理は次である。

- `cutClip_monotone_lipschitz`: 一つのedgeが一つのcutへ与える長さはedge全長以下
- `pathSignedFlux_eq`: 隣接差の再帰和はpath両端差へ望遠和
- `path_cut_balance`: cut上端から下端へ抜けるpathのsigned fluxはcut幅と一致
- `path_cut_positive_negative_balance`: downward mass − upward mass = cut幅
- `path_cut_le_positive_crossing`: cut幅 ≤ downward crossing mass

`lake build Recaman.RecordGapCutFlux` は2 jobsで成功した。moduleは既存orbit coreやimport graphを変更しない。

定理の正確な有限statementは、整数path `x_0,...,x_K` と `L≤U`, `U≤x_0`, `x_K≤L` に対して

```text
clip(x) = projection of x to [L,U]

Σ_{i<K} (clip(x_i) - clip(x_{i+1})) = U-L

Σ positivePart(clip(x_i)-clip(x_{i+1}))
  - Σ positivePart(clip(x_{i+1})-clip(x_i))
  = U-L.
```

addition-origin ancestry edgeは第一和、subtraction-origin edgeは第二和に対応する。

### 6.2 disjoint record cuts のcapacity

有限個のright-record gapを `G_j=(U_j,b_j]`、対応ancestry pathを`P_j`とする。各ancestry edge
`e`の値区間を`J_e`、first clockを`t(e)=|J_e|`とすると、有限path定理を足して

```text
Σ_j |G_j|
 = Σ_j Σ_{e∈P_j, add} |G_j ∩ J_e|
   - Σ_j Σ_{e∈P_j, sub} |G_j ∩ J_e|.
```

right-record gap族はpairwise disjointなので、同じedgeが複数pathに再利用されても

```text
Σ_{j:e∈P_j} |G_j ∩ J_e| ≤ |J_e| = t(e).
```

従って、path族に現れるdistinct addition-origin edge集合を`E_N^+`とすれば

```text
Σ_j |G_j| ≤ Σ_{e∈E_N^+} t(e).
```

これはunweighted reuseを完全に除く正しいfamily statementである。有限族の二重和・pairwise-disjoint
intersection部分は紙上exactで、Leanにはまず上のper-path核だけを入れた。family wrapperは軌道側で
right-record theoremと有限reset列のinterfaceが決まってから追加する。

### 6.3 reset希少性ではsubquadraticにならない

1B scanでupward resetが27件しかないことは経験的には強いが、この上界には件数だけでは効かない。
一つのreset pathだけで次の敵対形が可能だからである。

```text
x_0 = upperTri(N)
x_1 = upperTri(N-1)
...
x_N = 0
```

各逆向きedgeはaddition-originで、first clock weightが順に`N,N-1,...,1`。一つのcut
`(0,upperTri(N)]`に対して

```text
gap mass = N+(N-1)+...+1 = upperTri(N) = Θ(N²).
```

これは実Recamán prefixそのものではないが、現在cut lemmaが利用する条件

- first timeのstrict descent
- origin edge length = first clock
- record gapのdisjointness
- addition/subtraction origin label

をすべて満たす。従ってactual blocker causalityを追加しない限り、resetが1件でもquadraticが残る。

raw addition ledgerへ広げる方法はさらに明確に失敗する。clock massをaddition/subtractionで`A_N,S_N`と
分けると

```text
A_N + S_N = upperTri(N)
A_N - S_N = a_N
A_N = (upperTri(N)+a_N)/2 ≥ upperTri(N)/2.
```

よって全addition clock massは常に `Θ(N²)` であり、これをcapacityにした時点でsubquadratic boundは
原理的に得られない。

### 6.4 subquadratic化に必要な最小条件

`E_N^+`を、N時刻までのrecord gap path族に実際に現れ、gap cutと正の長さで交わるdistinct
addition-origin edgeとする。現在の結果からsubquadraticを得るための最小十分条件は

```text
Σ_{e∈E_N^+} t(e) = o(N²).
```

件数だけで表すなら `|E_N^+|=o(N)` が十分だが、20Mでpath長最大60,651、総steps 181,442であり、
asymptoticな証拠にはならない。upward reset件数が少なくても一本のpathが長くなれる。

よりRecamán固有で、証明を狙う価値がある最小条件は正負を残した**cut cancellation bound**である。

```text
A_X(N) ≤ S_X(N) + C N
```

ここで`A_X,S_X`はrecord-gap union `X=⋃G_j`と、選択ancestry subgraphのaddition/subtraction edgeの
交差長総和である。これが成り立てばexact balanceから直ちに

```text
Σ_j |G_j| = A_X(N)-S_X(N) ≤ C N
```

となる。この条件を作るには、forced addition edgeごとにその原因blockerを生成した過去の
subtraction massへ戻すcausal paymentが必要である。静的visited set、reset件数、first-time descentの
いずれも単独では不足する。

別の十分条件 `max_{t≤N} a_t=o(N²)` もdisjointnessからgap総量を直ちに抑えるが、軌道全体の
subquadratic height envelopeを先に要求するため研究gateとしては強すぎる。

### 6.5 更新判定

- finite path cut identity: **証明済み、保存**
- disjoint-cut weighted reuse elimination: **紙上exact、保存**
- raw positive ancestry capacity: **quadratic退化、direct branch停止**
- 次の一回: `A_X≤S_X+CN`型のcausal cut cancellationだけを試す
- これがfree-historyでも成立するか、RHSが`Θ(N²)`に戻るならcut-flux枝全体を停止

## 7. 第3ラウンド: RLR discharge との交差監査

### 7.1 RLRが持つ有限gap debt

future terminal blockerを`b`とするtarget-macro `R-L-R`を考える。最初のR intervalを

```text
I_old = [c+1,e_old],    b < c
```

最後のR intervalを、blocker `b`で終端するcurrent comb

```text
I_new = [b+1,e_new]
```

とする。fresh interval全順序から`e_new≤c`である。従って

```text
d_before = c-b
fresh_consumption = e_new-b ≥ 1
d_after = c-e_new
d_before = fresh_consumption + d_after
d_after < d_before
```

がexactに成り立つ。つまりRLRは、過去right intervalの直下にある有限gapの左端から、current
fresh intervalの長さだけ確実に消費するeventではある。

しかしこのdebtはtarget return rankとして閉じない。

1. 同じterminal blocker `b`は再利用不能なので、次episodeでは比較軸そのものが変わる。
2. future intervalは残余gapを埋めず、新しいright recordを作ってdebtを増やせる。
3. `d_after=0`でも「二つのintervalが隣接した」だけで、`target<b`の着地は従わない。
4. gap消費量は最小1であり、次のtarget-candidate crossingまでのclock距離を抑えない。

従って得られたstrict decreaseは、既存のinterval-hull gap ledgerにおけるinternal insertion paymentの
RLR版であり、新しいbase caseを持たない。

### 7.2 blocker forcing/repayment とのinterface不一致

cut flux `A_X,S_X` はblockerの**first-occurrence ancestry**に属する過去edgeを数える。一方、
`HistoryTerminatedComb.final_forced` と `repayment_forced` はcurrent final landingの後の実stepを記述する。
両者を結ぶ定理は現在ない。

final low landing timeを`T`とすると

```text
a_T = b+1
clock T+1 : forced addition
clock T+2 : blocker b が既出なので再び forced addition
```

である。従って既存の「repayment forced」は負のpaymentを供給する定理ではなく、局所的には二本の
正clock debtを確定する定理である。最速でclock`T+3`がsubtractionになっても、三stepのsigned clock
surplusは

```text
(T+1)+(T+2)-(T+3)=T
```

残る。episodeごとの定数marginやfresh interval長だけでは償却できない。

### 7.3 最小の具体的false example

addition-origin seeded RLR

```text
old record gap = [11,20]
old R interval = [21,24]
L interval     = [7,7]
new R interval = [15,17]
new blocker b  = 14 = 2 + 12
```

では、blocker ancestryのaddition edge `2→14` がold gapの`[11,14]`へ正flux 4を持つ。しかし
current RLR episodeはclock 54--60で

```text
71→17→72→16→73→15→74→134
```

と進み、fresh interval `[15,17]` と二本のforced additionは`[11,14]`を一度も横切らない。
従ってこのhistorical cut debt 4に対するcurrent-episode local subtraction paymentはexactに0である。

old gap全体`[11,20]`で実transitionを見るとcomb内のdown/up crossingは相殺するが、それは
first-occurrence ancestryの`A_X,S_X`とは別のledgerである。二つを同一視して
`A_X≤S_X+C·freshLength`を導くことはできない。

### 7.4 return delay の敵対的有限監査

RLRからtarget returnまでが短いという補助仮説も弱い。random signed-clock prefix 100,000本を
greedy continuationした監査では次を得た。

```text
RLR witnesses                    118
20,000 steps内にtarget return    108
20,000 steps時点censored          10
20,000,000 stepsまでに追加return   6
20,000,000 stepsでもcensored       4
最大確認delay                  10,787,228
```

これは`RLR ⇒ eventually target occurs`の反例ではない。有限censoringは永久欠落を示さないためである。
しかしRLR gap幅やlocal comb長から作る小さい有限debtではreturn timeを支配できないことは強く示す。

### 7.5 判定と必要な追加情報

| branch | score | decision |
|---|---:|---|
| RLRの内部gap消費恒等式 | 55/100（部分構造） | exact、保存 |
| RLR gap debt単独からtarget return | 10/100 | base caseなし、停止 |
| local episode `A_X≤S_X+C·freshLength` | 5/100 | seeded exact exampleで棄却 |
| standard-prefix `RLR⇒eventually target` | 22/100 | 未反証だがcut-flux支援なし |
| global causal cut cancellation | 18/100 | full-prefix provenanceが入る場合のみ保留 |

RLR dischargeを続けるなら必要な最小追加情報は、gap massではなく次のどちらかである。

1. RLR後のfuture macroが「同じouter bracket内のstrict debt drop」または`target`着地へ進むという
   **successor closure**。right-record escapeを同時に排除する必要がある。
2. blocker first-origin edgeのhistorical positive cut massを、current episodeではなく、そのedgeを
   forced additionにした**原因blockerの過去生成episode**へ戻すcausal payment。

既存の`positive_blocker_origin`、`EarlierSmaller`、`repayment_forced`は時刻下降または二連続additionを
与えるだけで、1・2のどちらも供給しない。従ってcut-flux枝からRLR dischargeへ追加Lean定理を作る
段階にはまだ達していない。

## 8. 第4ラウンド: low candidate 有限alphabet二分法

固定missing target `m>0`について

```text
c_n = nextSubtractionCandidate n = a_n - (n+1)
```

を考える。target omissionの下では`c_n=m`なら次clockで`m`へ合法減算できるため、tail上で
`c_n≠m`である。従って論理的には次の二分になる。

```text
A. c_n<m が無限回
B. あるN以後すべて c_n>m
```

二分自体は正しいが、どちらも既存の停止枝へ戻る。

### 8.1 A: 同じlow valueの反復

有限alphabet `{0,...,m-1}`により、ある`r<m`が無限回現れる。ただし最初に

```text
r=0
r>0
```

を分ける必要がある。`c_n=0`はNat subtractionのtruncationを含むので、分かるのは
`a_n≤n+1`だけであり、対角線上の等式は得られない。長いdescending combではlow railの多くが
まさにcandidate 0を反復するため、有限alphabet argumentが選ぶ唯一の無限値が0でも不思議はない。

`0<r<m`なら

```text
c_p=c_q=r, p<q
→ a_p=p+1+r, a_q=q+1+r
→ a_q-a_p=q-p.
```

`ledger_interval_balance`からexactに

```text
(q-p) + 2(subSum(q)-subSum(p)) + upperTri(p) = upperTri(q)
```

を得る。consecutive occurrenceを取り、その間でcandidateがlevel `r`より上にあるなら、これは
relative excessのfirst-passage ballot equalityになる。

しかし新しいcapacityではない。同じ`r`はterminal blockerではなく、各low stateでadditionを強制する
**raw candidate**である。terminal blocker一回消費がfresh `b+1`を使うのに対し、raw `r`が強制した
直後の値はclock依存で、`r+1`を消費しない。同じraw blockerの固定容量が偽であることは既存
`PARALLEL_RESEARCH_2026-08-30.md`のblocker償却監査ですでに確認済みである。

標準軌道自身がpairwise contradictionを否定する。target 19はclock 99,734まで出現しないが、

```text
c_444   = 17  (a_444   = 462)
c_1508  = 17  (a_1508  = 1526)
c_9305  = 17  (a_9305  = 9323)
c_31209 = 17  (a_31209 = 31227)
```

と同じpositive low valueが少なくとも4回反復する。従ってexact ledger、first-passage、fresh landingを
二時刻だけ比較してもtarget出現は強制できない。

### 8.2 low stateはfreshでも容量超過しない

tail開始より後のlow state `c_n<m`は、clock `n`のforced additionでは到達できない。もしadditionなら
既存`forcedAddition_candidate_strictAbove`が`m<c_n`を与えるからである。従って到着stepはlegal
subtractionで、`a_n`はfirst occurrenceである。

これは無限lowから無限fresh landingを与えるが矛盾ではない。

- `r>0`の反復なら landing は `n+1+r`で時刻とともにstrict増加
- `r=0`でも landing は`(m,n+1]`内のfresh値だが、利用可能区間も時刻とともに線形拡大
- low stateは連続しないので、個数密度は最初から高々1/2

さらにpositive `r`のlowが時刻`n`にsubtraction landingとして現れた場合、そのpredecessorは
`2n+1+r`。同じ`r`が時刻`2n`に再来するとlandingがこのpredecessorと一致してfreshnessに反する。
従って`n`と`2n`の同時出現は禁止できる。しかしdoubling-freeな無限集合は多数存在するので、これは
有限化rankにならない。

無限lowをmaximal combへ圧縮すると、各combは有限、terminal blockerは一回消費だが、異なるblockerが
無限に上へ逃げられる、という現在のtarget-macro residualそのものになる。

### 8.3 B: eventually high-only

ある`N`以後 `m<c_n`なら、signed excess

```text
E_m(n) = a_n-(n+1)-m
```

は永久に正である。既存step則は

```text
addition    : E_m(n+1)=E_m(n)+n
subtraction : E_m(n+1)=E_m(n)-(n+2)
```

を与える。`TargetHighCandidateExcursion.prefix_ledger_strict`の証明は任意の有限prefixへそのまま適用でき、

```text
m+(n+1)+2(subSum(n)-subSum(N))+upperTri(N)
  < a_N+upperTri(n)
```

を全`n≥N`で得る。しかしこれは`m<c_n`と`ledger_interval_balance`の線形結合に過ぎない。

有限excursionで使えた次の情報は失われる。

- `exit_canSubtract`: exitが存在しない
- `exit_window`: crossing windowが存在しない
- `exit_ledger_strict`: inequalityを反転する最初のlowが存在しない

算術的にも永久正は可能である。例えば十分大きい正excessから、三addition・一subtractionの周期は
一周期あたり `2n-2` の正surplusを持ち得る。実Recamán ruleで各addition candidateが過去に生成された
ことは別問題だが、ledger/first-passageだけでは排除できない。

eventually high-onlyでは、全subtraction landingも全forced blockerもtargetより上にあり、問題は
high-value causal blocker graphへ完全に戻る。これは既存のcausal graph / permanent-tail minimum枝と
同型である。既存見込み`liminf a_n/n≤3`も`a_n>n+1+m`と両立する。

### 8.4 最小Lean補題

二分を正確に使うために抽出する価値がある最小補題は一つだけである。

```text
candidate_eq_target_occurs_next:
  0<m
  ∧ nextSubtractionCandidate n = m
  ∧ m ∉ valuesThrough n
  → CanSubtract (n+1) (stateAt n)
    ∧ a (n+1)=m
```

そのcorollaryとして`MissingPermanentAboveTail.candidate_ne_target`が出て、「lowが有限ならeventually
strict high」を書ける。この証明は`forcedAddition_candidate_strictAbove`内部ですでに同じ形を使って
おり、新しい数学ではなくinterface抽出である。

反復candidateのledger equalityは`ledger_interval_balance`の代入だけ、low landing freshnessは
`forcedAddition_candidate_strictAbove`と`firstAt_succ_of_canSubtract`の合成だけなので、この枝が
再開しない限りLean wrapperを追加しない。

### 8.5 有望度

| branch | score | decision |
|---|---:|---|
| candidate `=m` exclusion interface | 75/100（小補題） | 必要時に抽出 |
| infinite low / finite alphabet repeat | 12/100 | raw blocker再利用へ退化、停止 |
| repeated positive low exact ledger | 15/100 | 標準prefixに多数実例、停止 |
| low landing freshness / no doubling | 25/100（部分構造） | 保存、容量不足 |
| eventually high-only prefix ballot | 8/100 | exitなし、既存identityへ退化 |
| eventually high-only causal provenance | 20/100 | 独立枝でなくcausal graphへ統合 |

この二分法から全域性へ進む新しい枝はない。再開条件は、zero candidate反復を含む無限comb列の
blocker escapeを抑える定理、またはhigh-only tailでhistorical high blockerの生成を有限容量にする定理である。

## 9. time-only ancestry と fresh-time 二重計数

### 9.1 origin の符号分岐は時間順序へ統一できる

`MissingPermanentAboveTail target tailStart`を仮定し、値`child`のfirst occurrenceを
`childFirstTime`とする。`tailStart < childFirstTime`なら、その直前値を`parentValue`として、
subtraction/additionの別によらずexactに

```text
target < parentValue
parentFirstTime < childFirstTime
```

を満たす`parentFirstTime`が存在する。前半は
`strictly_above (childFirstTime-1)`、後半は
`current_mem_valuesThrough`と`history_member_has_firstAt`だけで出る。従ってin-tail ancestryは、
first-timeがstrictに減少する有限pathとして統一できる。最小Lean interfaceは次である。

```text
inTail_origin_has_older_above_parent :
  MissingPermanentAboveTail target tailStart
  -> tailStart < childFirstTime
  -> FirstAt a child childFirstTime
  -> exists parentFirstTime,
       target < a (childFirstTime-1)
       and FirstAt a (a (childFirstTime-1)) parentFirstTime
       and parentFirstTime < childFirstTime
```

これは有用な正規化だが、path長の容量を新設しない。

### 9.2 単一combでは分離、複数combでは共有

単一のhistory-terminated combのstartを`s`とする。blocker ancestryのin-tail first timesは
すべて`s`未満、fresh low-rail timesはすべて`s`以上なので、両集合はdisjointである。

しかし複数combをまとめると、後のblocker ancestryは以前のfresh landingを祖先として再利用できる。
標準prefixに既に最小の具体例がある。

```text
target = 4, tailStart = 5
comb 1: start=8, fresh times={8,10,12,14,16}, blocker=7
comb 2: start=38, blocker=25, blocker first time=17
25@17 was created from parent 8@16
```

従って時刻16はcomb 1のfresh timeであると同時にcomb 2のblocker ancestry first timeである。
しかも`4 < 8`かつ`firstTime(8)=16 < firstTime(25)=17`であり、上の統一origin条件を完全に
満たす。200k prefixでは、全targetを合算したdistinct fresh times 55,853、distinct blocker-ancestry
first times 32,892のうち5,001時刻が重なった。共有は例外ではない。

### 9.3 最小exact inequality

`F`をhorizon内の全fresh landing clockの集合、`A`を選択blocker ancestryのdistinct in-tail
first-time集合とする。combが時間順にdisjointなら`|F| = sum freshLength`である。常にexactなのは

```text
sum freshLength + |A|
  = |F union A| + |F intersection A|
  <= (horizon-tailStart) + |F intersection A|,
```

または同値な

```text
sum freshLength + |A \\ F| <= horizon-tailStart.
```

だけである（端点規約により右辺へ1を足す場合がある）。terminal blockerの一回消費はblocker値、
従ってそのfirst timeの単射を与えるが、そのfirst timeや深い祖先timeが以前の`F`に入ることを防がない。

補正なしの式はtime-only axiomsからは偽である。任意の`K>=3`について、最初のcombへ`K`個の
fresh timesを置き、その直後までの`2K+1`時刻すべてを、次combのblockerへ至るstrictly decreasing
first-time ancestry pathとして選ぶ。次combをfresh length 1とすると、相対horizonは`2K+4`なのに

```text
sum freshLength + |A| = (K+1) + (2K+1) = 3K+2 > 2K+4.
```

各edgeには`target<parentValue`と`parentFirstTime<childFirstTime`を割り当てられ、blocker first timeも
次comb startより前、二blockerもdistinctにできる。これはRecaman recurrence全体の反例ではないが、
提案された**time-only**情報から不等式を導けない最小countermodelである。

### 9.4 判定

| branch | score | decision |
|---|---:|---|
| in-tail originのtime-only統一 | 80/100（整理補題） | 保存 |
| 単一comb `fresh + ancestry <= time` | 70/100（exact） | 局所用途のみ |
| 複数combの補正なし二重計数 | 5/100 | 共有反例により停止 |
| overlap補正付きinclusion-exclusion | 100/100（exact） | tautology、証明力なし |
| terminal count + fresh count | 15/100 | 単なる`count<=time`へ退化 |

この枝を再開する最小条件は、`|F intersection A|`への非自明な上界、またはoverlap一件ごとに
fresh/ancestryの外側へinjectできるRecaman固有の追加時刻である。time precedenceとterminal blocker
単射だけでは足りない。

## 10. fresh--ancestry overlap multiplicity の敵対監査

### 10.1 測定量

各history-terminated combのterminal blockerから、そのtarget epoch startより後にfirst occurrenceした
祖先だけを辿る。fresh first-time `t`に対し

```text
mu(t) = #{later terminal-blocker ancestry paths containing t}
W = sum_{t in F} mu(t)
```

と置いた。`mu(t)>0`の時刻数が前節のepoch-cut版`|F intersection A|`、`W`がpath再利用を
重みとして戻したoverlap chargeである。同じpathで同じ時刻はfirst-time strict decreaseにより二度現れない。

### 10.2 200k / 2M exact replay

| metric | 200k | 2M |
|---|---:|---:|
| historical terminal paths | 269 | 848 |
| fresh first-times | 55,853 | 569,399 |
| ancestry path nodes（multiplicity込み） | 154,806 | 1,198,144 |
| maximum path length | 3,672 | 22,391 |
| overlap union `#{t:mu(t)>0}` | 2,648 | 12,752 |
| weighted overlap `W` | 30,535 | 224,017 |
| excess reuse `sum(mu-1)` | 27,887 | 211,265 |
| max `mu(t)` | 170 | 170 |
| positive `mu` p50 / p90 / p99 | 4 / 9 / 147 | 12 / 32 / 128 |
| `W / overlapUnion` | 11.53 | 17.57 |

最大witnessは両horizonで同じで、target 19のfresh landing

```text
value 248 at time 247
```

が186本の同target terminal pathのうち170本（91.4%）に含まれる。fresh token一個一回消費どころか、
ancestry mergerのhubになっている。

2Mのtarget別内訳は次である。

| target | terminals | fresh | overlap union | `W` | max `mu` |
|---:|---:|---:|---:|---:|---:|
| 4 | 5 | 37 | 9 | 19 | 3 |
| 19 | 186 | 27,620 | 2,639 | 30,516 | 170 |
| 61 | 70 | 22,831 | 0 | 0 | 0 |
| 879 | 92 | 41,911 | 0 | 0 | 0 |
| 1,355 | 495 | 477,000 | 10,104 | 193,482 | 32 |

特にtarget 19だけで`W=30,516 > fresh=27,620`なので、係数1のweighted fresh boundは
標準軌道自身で偽である。globalな`W/fresh`が200kで0.547、2Mで0.393へ下がるのは、target 61/879の
zero-overlapとtarget 1,355の巨大fresh massが希釈したためで、target-uniform amortizationではない。

### 10.3 within-target制限はexactに同じ

epoch startより後、対応terminal combより前のancestry first-timeは同じmex epoch内にある。その時刻が
別のcompleted fresh combに属するなら、そのcombのtargetも同じmexである。従ってこの監査では

```text
cross-target overlap incidence = 0
within-target multiplicity = global multiplicity
```

が構造的に成立する。within-targetへ制限してもtarget 19の170-fold hubは消えない。

### 10.4 uniform / weighted bound のtime-only countermodel

前節の二comb countermodelを分岐させる。最初に`K`個のfresh nodeを一本のancestry chain上へ置き、
その後`R`個のdistinct terminal blockerを、それぞれ固有の新nodeからその共通chainへmergeさせる。
各blockerには別のlength-1 combを対応させる。全て同じtargetとし、各edgeは

```text
target < parentValue
parentFirstTime < childFirstTime
```

を満たせる。このとき共通fresh nodeごとに`mu=R`、従って

```text
max mu = R
W = K*R.
```

一方、distinct time/node/terminal/fresh容量は`O(K+R)`である。従ってtime-only axiomsからは
uniform multiplicity boundも`W <= C*(fresh + time)`型の任意の固定係数boundも出ない。唯一の一般上界は

```text
mu(t) <= number of later terminals
W <= |F| * number of terminals,
```

というquadraticな自明上界である。

### 10.5 判定

| candidate | result | decision |
|---|---|---|
| uniform `mu(t)<=C` | 実測170、抽象的にunbounded | 停止 |
| weighted `W<=|F|` | target 19で30,516 > 27,620 | false |
| weighted fixed-constant linear bound | branching countermodelで`KR/O(K+R)` unbounded | 停止 |
| within-target bound | globalとexactに一致、max 170 | 改善なし |
| `mu<=#later terminals` | exact | quadratic退化 |

新しいLean補題は追加しない。`mu`をdescendant terminal countとして定義するwrapperは書けるが、
得られるのは上のquadratic boundだけである。このoverlap枝の再開条件は、Recaman固有にancestry merge後の
terminal descendantsを有限化する定理であり、それ自体がblocker escape問題と同程度に強い。

## 11. Round 7B: pre-tail root obstruction と cut-flux

### 11.1 obstruction pathのcutは二種類とも進捗を作らない

`FirstAt.preTail_anchorObstruction_or_normalProgress`の左枝で、starting valueを`x_0`、pre-tail rootを
`x_K`、active anchorを`alpha`とする。探索は最初のstrict anchor crossingで右枝へ抜けるため、左枝では

```text
alpha <= x_i  (0 <= i <= K),
alpha <= x_K = root
```

がpath全体で保存される。

従ってupper endpointが`alpha`以下の任意のcutでは、全vertexのclipがupper endpointに等しく、

```text
positive cut flux = negative cut flux = 0.
```

anchorより上のcutについても、pathの両端がupper sideにある限り

```text
signed cut flux = 0
positive cut flux = negative cut flux
```

である。内部でfresh intervalを何度横切ってもround tripとして完全相殺される。これを独立module
`Recaman/RecordGapCutFlux.lean`へ次の二定理として追加した。

```text
path_cut_zero_of_endpoints_above
path_positive_eq_negative_of_endpoints_above
path_positive_negative_zero_of_all_above
```

`lake build Recaman.RecordGapCutFlux`は2 jobsで成功した。

### 11.2 disjoint fresh intervalsはcrossingを強制しない

fresh intervalのpairwise disjointnessは値軸packingであって、blocker ancestry pathが各intervalを
横切ることを含まない。

- intervalが`min(x_0,root)`より下なら、pathはその上に留まったまま完全に回避できる。
- pathが内部でintervalを下向き・上向きに横断しても、両endpointが上なら正負massが等しい。
- signed massが残るのはcutが`x_0`と`root`を分離するときだけで、その量は
  `clip(x_0)-clip(root)`というendpoint差そのものである。

小さいlocal countermodelは

```text
activeAnchor = 10
ancestry values: 20 -> 10 -> 19
child first clocks: 10 > 9 > rootFirstTime
fresh cuts: [12,14], [16,18]
```

である。edge equationsは`20=10+10`（addition origin）と`10=19-9`（subtraction origin）を満たす。
各fresh cutでdownward mass 2、upward mass 2、signed mass 0で、disjoint fresh総幅4を横切るが
`root=19 >= activeAnchor`のままである。scaleを上げれば任意幅のround-trip cancellationを作れる。

従ってcutからstrict anchor dropを出すには、anchor直下のcutでpositive signed fluxを示す必要がある。
しかしそのendpoint条件はまさに`root<activeAnchor`であり、欲しい結論の言い換えに過ぎない。
absolute crossing massへ逃げると正負を足すため、Round 2のraw clock-weight `O(N^2)`上界へ戻る。

### 11.3 finite ceiling / unbounded blockerの方が強い

pre-tail rootのfirst timeは`tailStart`以下なので、prefix maximumを`M`とすればexactに`root<=M`。
明示的には既存orbit boundから

```text
root <= upperTri(tailStart)
```

も得られる。従って`activeAnchor>M`ならroot obstructionは即座に不可能である。このfinite-ceiling
argumentはcut-fluxよりstrictに強く、cutを経由しない。

またcompleted combのterminal blockerは、同じblockerならfinal fresh timeが同じという既存定理
`HistoryTerminatedComb.same_blocker_finalTime_eq`により、異なるchronological comb間で一回しか使えない。
ゆえに

```text
infinitely many completed terminal combs
  -> infinitely many distinct blockers
  -> blockers are unbounded.
```

これは純粋なpigeonholeでありcut-fluxを必要としない。blocker自身をactive anchorとしてmountできるなら、
いつか`blocker>M`となりfinite obstructionを消せる。ただし現行rankのactive anchorがblockerと一致する、
またはblocker以上へ上がるというsemantic bridgeは別に必要である。

さらに共有worktreeの`HistoryTerminatedComb.tail_blocker_debtNormalProgress`は、tail内の任意のcompleted
combについて`target<blocker<a s`を直接使い、自然なentry anchor `a s`からblocker normal nodeへの
rank progressを構成する。terminal combが既に与えられた局面では、これはroot ancestryもfinite ceilingも
迂回する、より強い局所接続である。

### 11.4 cut側はterminal combの無限発生を補えない

cut identityは選択済みcomb / blocker / ancestry pathに対する条件付き恒等式である。terminal comb族が
有限または空なら全statementは空和として成立するため、そこから新しいcomb eventを生成できない。

永久missing tailではcandidateについて

```text
infinitely many low states  /  eventually high-only
```

の二分が残る。前者をmaximal combへ圧縮すれば、各combのlandingは1ずつ下降し永久missingにより有限に
history-terminateするので、無限terminal combとunbounded blockerへ進める。しかし後者ではeventually
terminal-comb-freeとなり得て、cut-fluxは完全にvacuousになる。これはRound 4の
`TargetHighCandidateExcursion` exit欠如と同じ停止枝である。

### 11.5 有望度更新

| branch | score | decision |
|---|---:|---|
| below-anchor cut crossing | 100/100（zero theorem） | exact no-go |
| above-anchor internal fresh crossing | 100/100（正負相殺） | exact no-go |
| disjoint fresh intervalsからsigned下降 | 5/100 | endpoint identityへ退化、停止 |
| absolute crossing mass | 8/100 | raw clock `O(N^2)`へ退化 |
| finite pre-tail ceiling | 85/100（conditional exact） | 保存、cut不要 |
| infinite comb `=>` unbounded blocker | 90/100（conditional exact） | 保存、pigeonhole |
| cut-flux `=>` infinitely many combs | 0/100 | empty-family反例、停止 |
| completed combのdirect blocker progress | 90/100（局所） | 最有望な既存接続 |

cut-fluxとterminal combを結ぶ枝はここで停止する。残る実質的なgateは、terminal combの存在しない
eventually-high-only tailを排除すること、またはcompleted combから得た局所progressを反復可能なsemantic
domainへmountすることである。

## 12. Round 8B: eventual-high-candidate corridor の weighted no-go

### 12.1 signed excessの全情報

```text
E(n) = a_n - (n+1) - target
```

と置く。`target < nextSubtractionCandidate n`はexactに`0<E(n)`である。transition `n -> n+1`で

```text
forced addition : E(n+1) = E(n) + n
legal subtraction: E(n+1) = E(n) - (n+2).
```

start `N`からendpoint `q`まで、addition incrementの総和を`A(N,q)`、subtraction decrementの総和を
`S(N,q)`とすれば

```text
E(q) = E(N) + A(N,q) - S(N,q).
```

従ってeventual-high仮定が与えるweighted制約は全prefixについて

```text
S(N,q) < E(N) + A(N,q)
```

だけである。subtraction massをaddition massより大きくする逆向きのforceはない。

### 12.2 prefix inequalityは仮定とのiff

既存`TargetHighCandidateExcursion.prefix_ledger_strict`は有限high block内で

```text
target + (q+1) + 2*(subSum(q)-subSum(N)) + upperTri(N)
  < a_N + upperTri(q)
```

を返す。しかし`ledger_interval_balance`を代入すると、この不等式はpointwiseな
`target < nextSubtractionCandidate q`と**同値**である。forward consequenceですらなく、情報量は完全に同じ。

これを独立module `Recaman/EventualHighCandidateLedger.lean`へ

```text
target_lt_candidate_iff_interval_ledger_strict
eventuallyHighCandidate_iff_forall_interval_ledger_strict
```

としてLean化した。`lake build Recaman.EventualHighCandidateLedger`は169 jobsで成功した。

### 12.3 exit lemmaでのみstrictな向きが反転する

有限`TargetHighCandidateExcursion target start finish`にはfirst low state `finish+1`がある。
permanent missing tailではそのexitはlegal subtractionであり、既存定理が

```text
0 < E(finish) < finish+2
```

を与える。さらに`exit_ledger_strict`は、全prefixで成立したweighted不等式をfirst low endpointで
strictに逆転する。ここで初めてfirst-passage windowが生じる。

eventual-high corridorにはexitがないため、次の三情報が同時に消える。

- `exit_canSubtract`: target lineを横切る指定subtraction edge
- `exit_window`: crossing直前excessへのclock上界
- `exit_ledger_strict`: prefix inequalityの逆転

従って有限excursion lemmaを「finishを無限へ送る」ことはできない。残るforall-prefix式は12.2のiffだけである。

### 12.4 infinite weighted countermodel

weighted step則だけではhigh-onlyを排除できない。例えば`N>=2`, `E(N)=1`から、各4-step block
`q=N+4j`でsignを

```text
addition, addition, addition, subtraction
```

とする。block内のincrementは

```text
q + (q+1) + (q+2) - (q+5) = 2q-2 >= 2.
```

途中三点はadditionで上がり、最後のsubtraction後もblock開始より高いので、`E(n)>0`は永久に保存される。
subtractionは無限回起き、weighted subtraction massもquadraticに増えるが、addition surplusがそれを上回る。

任意のpositive target `m`について

```text
a_n = m + (n+1) + E(n)
```

と戻せば、addition stepは`a_(n+1)=a_n+(n+1)`、subtraction stepは
`a_(n+1)=a_n-(n+1)`をexactに満たし、candidateは常に`m+E(n)>m`である。例えば
`N=10,m=1,E(N)=1,a_N=13`なら`upperTri(10)=55`かつ初期subtraction ledgerを21として
`a_N+2*21=55`も満たす。その後のstep則によりledger identityは永久に保存される。

このtraceはforced-addition candidateのhistory membership / subtraction landingのfreshnessまでは主張しない。
だからこそ、**weighted balance・step magnitude・triangular orbit boundだけ**では矛盾が出ず、追加するなら
causal history情報でなければならないことを示すcountermodelである。実際このpatternは
`a_n`を漸近`n^2/4`程度に保ち、一般上界`a_n<=upperTri(n)~n^2/2`とも両立する。

### 12.5 cut-fluxもtarget boundaryでvacuous

excess path `E(n)`はeventual-high tailで常にpositive sideにある。target boundaryに置いたcutは全vertexが
上側なので、Round 7Bの
`path_positive_negative_zero_of_all_above`によりcrossing mass自体が0である。positive corridor内部へ
cutを置けば往復crossingは作れるが、signed fluxはendpoint clip差へ望遠和されるだけである。

有限excursionではexit subtractionがtarget boundaryを横切るためcutに幅が生じる。eventual-highでは
そのedgeが存在せず、value-axis cutへ移しても「historical high blockerの生成をどう支払うか」という
causal ancestry問題へ戻る。そこでは既にpath merger、170-fold fresh reuse、raw clock `O(N^2)`退化を確認済みである。

### 12.6 判定

| branch | score | decision |
|---|---:|---|
| forall-prefix weighted inequality | 100/100（exact iff） | 新情報なし |
| weighted subtraction density contradiction | 3/100 | `+++−` infinite traceでfalse |
| triangular height upper boundとのsandwich | 5/100 | `n^2/4` traceが両立 |
| target-boundary cut flux | 0/100 | all-aboveでzero |
| internal positive-excess cuts | 5/100 | endpoint telescope / cancellation |
| finite excursion exit window | 85/100（既存exact） | exitがある枝だけ保存 |
| forced-addition history causality | 25/100 | 唯一の未使用情報だが既存reuse壁へ戻る |

eventual-high-candidate corridorに対するweighted ledger / cut-flux枝は停止する。再開条件は、high candidateを
強制したhistorical blocker membershipから、有限excursionのexitに相当する実際のtarget-line crossingを
生成する新しいcausal theoremである。これはweighted identityからは導けない。

## 13. Round 9B: high candidate の causal reuse 監査

### 13.1 earlier first-time map はexactだがmany-to-one

時刻`n`の次時計を`u=n+1`、正のforced subtraction candidateを

```text
c = a_n-u > 0
```

とする。forcednessの非正値分岐は排除されるので、`c∈valuesThrough(n)`である。従ってexactに

```text
exists f<u, FirstAt(a,c,f).
```

を得る。これは`HighCandidateCausalReuse.forcedAddition_positive_candidate_has_earlier_firstAt`として
Lean化した。eventual-high仮定を加えると新しく得るのは`target<c`だけで、`f`の下界、tail内first-time、
または`f↦u`の逆向き一意性は得られない。

同じcandidate `c`が二つのforced clocks `u<v`で使われると、各addition outputは

```text
a_u = c+2u,     a_v = c+2v,
```

なので`a_u<a_v`である。これは同一`c`に限れば**raw output valueへのinjective charge**であり、
`forcedAddition_same_candidate_outputs_strict`としてLean化した。しかしraw outputのfirst occurrenceは
保証されないので、有限fresh-value budgetへは載らない。

さらにforced use直後のcandidateはexactに

```text
nextCandidate(u) = c+u-1
```

であり、Lean定理`nextCandidate_after_positive_forcedAddition`を追加した。従って`u>1`では同じ`c`を
連続時計で再利用できない。ただしこれは利用回数を高々時間幅の半分にするだけで、有限one-use boundではない。

### 13.2 certified standard-prefix反例

標準Recamán列についてLeanの`decide`で次を証明した。

```text
FirstAt(a,285,169)
19 is missing through time 1325
clock 173 : high candidate 285 forces addition, output 631
clock 1325: high candidate 285 forces addition, output 2935
a_1313=2935=a_1325
```

従って次の二つは同時にfalseである。

- high candidateのone-use / injective first-time charging
- high forced-addition outputはfreshである、というfresh deposit charging

これは`highCandidate_forcedReuse_and_nonfreshOutput_counterexample`でcertificate化した。同じoutput値への
chargeもcandidateを跨ぐとinjectiveでない。target `4`が未出現の間、clock `101`のcandidate `63`と
clock `113`のcandidate `39`はいずれもhighかつforcedで、両方ともoutput `265`へ着地する。この反例も
`highCandidate_distinctCandidates_sameOutput_counterexample`としてLean化した。

### 13.3 200k / 2M replay: reuseは成長し、fresh率は低下する

標準列を同じkernel ruleでreplayし、正のforced additionsのうちcandidateがその時点のmissing targetより
上にあるeventを数えた。以下は計算観察でありLean theoremではない。

| quantity | 200k | 2M | class |
|---|---:|---:|---|
| positive forced additions | 43,101 | 431,047 | empirical |
| high forced additions | 43,032 | 430,600 | empirical |
| high output fresh | 33,945 (78.88%) | 332,007 (77.10%) | empirical |
| high output revisit | 9,087 | 98,593 | empirical |
| distinct high candidates | 28,644 | 261,717 | empirical |
| max reuse of one candidate | 10 | 13 | empirical |
| max reuse within one fixed target | 9 | 13 | empirical |
| max reuse of one output value | -- | 16 | empirical |

2Mで最大reuseのcandidateは`2060700`、targetは`1355`、first timeは`1005992`で、clock
`1133180`から`1388552`まで13回使われた。first-timeから利用までのageも有界に見えず、2M内最大は
`1,785,560`（candidate `5551`, first time `1305`, use clock `1786865`）だった。小さいfirst-timeに対する
clock比もcandidate `22`で`99732/11>9000`に達する。

従って`ReturnFrequency.return_time_lower_bound`型の定理は向きが逆である。再訪までには時間が必要だと
示しても、古いcandidateが後で何度使えるか、またはいつまでに再訪するかの上界にはならない。

### 13.4 high-onlyを加えても局所injectivityは戻らない

2M replayでは、同一のcontiguous high-candidate block内ですら同じcandidateが再利用される。最初の例は

```text
target 19, candidate 34329, first time 16585,
forced clocks 16777 and 17301,
high block states [16774,17331].
```

同一high block内の観測最大reuseは3だった。これはpermanent high-onlyそのものの反例ではないが、
「区間全体がhigh」という局所仮定だけからinjectivityを導く補題はfalseである。

この失敗は標準列固有でもない。任意の`c-6>target`について、state time `2`の値を`c+3`とし、初期historyに
`c,c-3,c-6`を置き、`c+2,c+1`を置かない局所seeded traceを考える。clock `3,...,7`のsignは

```text
+ - + - +
```

となり、candidate displacementは

```text
0, 2, -3, 1, -6, 0.
```

従ってclock `3`で使った`c`がclock `8`で再びforced candidateになる。この区間の全candidateは
`target`より上であり、Recamánの局所history ruleとも整合する。これはcanonical seed `a_0=0`からの
標準列を主張するものではないが、high-onlyと局所step/history axiomsだけではone-useを証明できない
algebraic no-goである。

### 13.5 既存blocker定理を適用できない理由

`ActualDescent.ActualBlocker`のone-use機構は、certified descending runとfresh successor / terminal relationを
持つblockerに対するものである。raw high candidate `c`にはそのterminal certificateがない。
`DebtAddition.firstAt_forcedAddition_extract_candidate`も、forced-addition **output自体**が`FirstAt`であることを
前提にする。Round 9Bの2935反例はまさにこの前提が一般には作れないことを示す。

`ReturnFrequency.drop_le_upperTri_gap`と`return_time_lower_bound`は再訪時刻のlower boundであり、reuse countを
抑えない。`forced_addition_run_defects`は連続forced run内のdeposited candidatesを増加させるが、subtractionを
挟んだ同一raw candidateの再利用には適用できない。

### 13.6 分類と停止判定

| proposed statement | class | score | decision |
|---|---|---:|---|
| positive forced candidate `=>` earlier `FirstAt` | exact / Lean | 100/100 | 保存 |
| same candidate, later clock `=>` larger raw output | exact / Lean | 100/100 | 保存、fresh budgetではない |
| same candidate cannot occur on consecutive clocks | exact / Lean | 100/100 | 保存、linear capacityのみ |
| candidate first-timeへのinjective charge | false / Lean counterexample | 0/100 | 停止 |
| forced outputはfresh | false / Lean counterexample | 0/100 | 停止 |
| raw outputへのglobal injective charge | false / Lean counterexample | 0/100 | 停止 |
| high-only intervalならcandidate one-use | false / replay + seeded no-go | 0/100 | 停止 |
| uniform bounded reuse | unsupported; max `10→13` | 10/100 | 成長中、証明根拠なし |
| first-time/use ageのuniform bound | false as observed route | 0/100 | 既存定理は逆向き |
| causal membershipだけでeventual-highを排除 | no-go under current interfaces | 12/100 | 停止 |

結論として、earlier first-time mapは完全に正しいが、同じ古い値へ多数のforced clocksが合流するため、
time/fresh budgetへのchargingとしては退化する。再開に必要な最小追加条件はraw candidate membershipではなく、
各利用に対して相異なる**fresh terminal certificate**を生成するか、各candidateの全利用をまとめて支払う
strictly decreasing rankである。現行`ActualBlocker`が持つのは前者だが、eventual-high raw candidateからそこへ
変換するadapterはなく、2935反例により無条件adapterは不可能である。

## 14. Round 11B: candidate-reuse bundle と subtraction payment

### 14.1 標準列固有の候補: 同一candidateの全reuseを一区間収支へ束ねる

同じpositive candidate `c`がpre-state times `p<q`で露出すると

```text
a_p = c+(p+1),     a_q = c+(q+1),
```

なので、二時点間の値の増分は時計差`q-p`に固定される。これを一般ledgerへ代入するとexactに

```text
2*(subSum(q)-subSum(p)) + (q-p) + upperTri(p) = upperTri(q).
```

時計`p+1,...,q`の総量を`W(p,q)`、そのうちsubtraction時計の総量を`S(p,q)`と書けば、同じ式は

```text
2*S(p,q) + (q-p) = W(p,q)
```

である。すなわち同一candidateへ戻る区間は、全時計質量のほぼ半分を実際のsubtractionで支払う。
これはRound 8の「各pointがhigh iff prefix inequality」という言い換えとは異なり、実際に同じhistorical
candidateが再利用された二endpointを選ぶことで値差が`q-p`へ固定される標準Recamán固有のspecializationである。

独立module `Recaman/ForcedCandidateReuseBalance.lean`に次をLean化した。

```text
same_positive_candidate_reuse_subtraction_balance
same_positive_forcedCandidate_reuse_bundle
```

後者は、二つのforced useが同じearlier `FirstAt(a,c,f)`を共有することと上のpayment式を一つのcertificateに
まとめる。`lake build Recaman.ForcedCandidateReuseBalance`は171 jobsで成功した。

### 14.2 candidate単位のtelescopingではreuse回数が消える

固定`c`の利用時計を`u₁<u₂<...<uᵣ`とする。隣接利用間のpayment区間は`c`ごとにはdisjointなので足せる。
しかし総和は最初と最後のendpointへ望遠和され、14.1を`u₁,uᵣ`へ一度適用した式と全く同じになる。

```text
sum of all consecutive-use payments
  = payment between first and last use.
```

中間reuse数`r-2`は式から完全に消える。従ってcandidateごとのrank候補は次のどれも下降しない。

- candidate value `c`: reuseで不変
- canonical first time `f(c)`: reuseで不変
- forced output `c+2u`: strict増加し、Natのwell-founded向きと逆
- subtraction ledger: monotone増加するが、finite budgetではなく`O(N²)`

「同じcandidateの全利用をまとめる」操作自体はexactだが、利用回数を数えるpotentialにはならない。

### 14.3 candidate間のinterval overlapはLean反例で既に5重

異なるcandidate間でpayment区間がdisjoint、という次の集約条件はfalseである。標準prefixでtarget `19`が
未出現の間に

```text
c=502 : clocks 296,340
c=499 : clocks 298,342
c=496 : clocks 300,344
c=493 : clocks 302,346
c=490 : clocks 304,348
```

という5本のreuse intervalが共通部分を持つ。全10 endpointがpositive high candidateかつforcedであることを
`five_high_candidate_reuse_intervals_overlap_counterexample`としてLeanの`decide`でcertificate化した。

この小反例の区間全体はhigh-onlyではないため、eventual-high仮定下のoverlapをそれ単独で棄却するものではない。
そこでreplayでは、low stateを一つでも跨いだintervalを捨て、同じcontiguous high block内で完結するreuseだけを
別集計した。

### 14.4 high-only block内でもoverlap multiplicityが成長する

各reuse arc `[u,v)`について、その内部clockに1を加えたactive depth `D(k)`を測った。

| scope | horizon | reuse arcs | max active depth | total arc length |
|---|---:|---:|---:|---:|
| same current target epoch | 200k | 10,681 | 2,125 | 148,326,489 |
| same current target epoch | 2M | 141,778 | 26,888 | 23,130,175,357 |
| one contiguous high block only | 200k | 68 | 21 | 20,324 |
| one contiguous high block only | 2M | 1,094 | 427 | 5,595,024 |

strict high-block集計の最初のparallel familyはtarget `19`で

```text
[16777,17301), c=34329
[16779,17303), c=34326
[16781,17305), c=34323
...
```

と現れる。2Mで`D(k)`は427まで増えた。従って「high-onlyなら各subtraction clockが高々小定数個のreuseを
支払う」という期待は標準列データと合わない。

集約式を`D(k)`で書けばexactに

```text
2 * sum_{subtraction clock k} D(k)*k + sum_arc length(arc)
  = sum_all_clock k D(k)*k.
```

200k / 2M replayでも左右差はそれぞれexactに総arc length `20,324` / `5,595,024`となり、個別payment式を
検算できた。しかし右辺はraw clock massではなくmultiplicity付きmassである。同じsubtraction clockが427本を
同時に支払えるため、既存の`subSum`上界へ落とす際にまさに必要な係数を失う。

### 14.5 no-goと再開条件

| branch | class | score | decision |
|---|---|---:|---|
| same-candidate interval payment | exact / Lean | 100/100 | 保存 |
| common first-time + payment bundle | exact / Lean | 100/100 | 保存 |
| candidate-local reuse rank | exact telescope | 5/100 | reuse countが消える、停止 |
| reuse intervals are disjoint | false / Lean | 0/100 | 5重反例 |
| high-block overlap has a small bound | empirical against | 8/100 | max `21→427`、停止 |
| raw `subSum` pays aggregate reuse | false interface | 0/100 | multiplicity `D(k)`が必要 |
| subtraction-mass contradiction | endpoint identity | 8/100 | weighted ledgerへ戻る |

この候補は、raw membershipより強い「同じcandidateへ戻るには大量のsubtraction clock massが必要」という
新しいexact事実を与えた。しかし一candidate内で束ねると回数が消え、candidate間で足すとunbounded-lookingな
overlap multiplicityが現れるため、eventual-high排除には至らない。

最小の再開条件は、各clockのactive reuse depthに対するtarget依存でもよい**証明済み上界**と、選択された
reuse arcsの総需要に対するそれを上回るlower boundの組である。前者だけでも2Mで427以上が必要で、現行履歴・
ledger定理からは出ない。したがってcandidate-reuse weighted rankは18/100とし、独立なoverlap制御が
見つかるまで停止する。

## 15. Round 12B: reuse interval graph の最終構造監査

### 15.1 crossing / nesting / disjoint の分離

同一contiguous high block内で、同じcandidateの連続するforced useをarc `[l,r)`で結んだ。二arcを
`l₁<l₂`の順に並べると、関係は次の三つである。

```text
disjoint : r₁ <= l₂
crossing : l₁ < l₂ < r₁ < r₂
nesting  : l₁ < l₂ < r₂ < r₁
```

laminar / stackはcrossingを禁止し、queue / proper interval orderはnestingを禁止する。paymentをraw
`subSum`へ戻すため本当に必要なのは同一clockを覆うarc数、すなわちinterval graphのactive depthである。

### 15.2 exact prefixでlaminar / one-stackはfalse

Round 11Bの標準prefixには

```text
[296,340), candidate 502
[298,342), candidate 499
```

があり、endpoint順は`296<298<340<342`でproper crossingである。両candidateがtarget `19`より上で、
両endpointともactual forced useであり、targetが時刻342まで未出現であることを、新Lean定理

```text
high_candidate_reuse_intervals_cross_counterexample
```

としてcertificate化した。従って一般のreuse familyに対するlaminar / one-stack仮説はexactにfalseである。
この小区間全体はstrict high blockではないため、strict high版は次のreplayで別に監査した。

### 15.3 strict high blockの2M interval relations

low stateを跨ぐarcを全て捨てたstrict high-block familyについてpair関係と最大cliqueを再計算した。

| horizon | arc-containing blocks | arcs | crossing pairs | nesting pairs | disjoint pairs | max crossing clique | max nesting chain |
|---|---:|---:|---:|---:|---:|---:|---:|
| 200k | 6 | 68 | 489 | 0 | 0 | 21 | 1 |
| 2M | 19 | 1,094 | 181,987 | 418 | 340 | 427 | 2 |

strict high内の最初のcrossingは既出の

```text
[16777,17301), c=34329
[16779,17303), c=34326
```

である。2Mの最大familyはtarget `1355`で、共通clock `1755086`を覆う427本だった。最初と最後は

```text
[1746611,1755087), c=3578516
...
[1747463,1755939), c=3577238.
```

left endpoint順とright endpoint順が一致するため、427本は単にactiveなだけでなく**pairwise crossing
clique**である。従ってstrict-high familyもlaminarではなく、stack / laminar分解には少なくとも427色が要る。

queue仮説も完全には成立しない。2Mで最初のnestingはtarget `1355`の

```text
[561453,563021), c=1168259
  contains [561475,561635), c=1168224.
```

であり、one-queue / globally proper familyはfalseである。一方、観測最大nesting chainは2なので、2M familyは
包含posetのrankで2 queuesへ分けられる。これは残った唯一の弱いorder structureである。

### 15.4 2-queue構造はledgerのmultiplicityを減らさない

queueはnestingを禁止するだけでcrossingを許す。実際、上の427-cliqueはright endpointsも増加するため、
全体が**一つのqueue class**に入る。それでも427本すべてが同じsubtraction clocksを共有する。

従ってqueue数`Q`がuniformに2、あるいは1と証明できたとしても

```text
sum_arc S(arc) <= Q * globalSubSum
```

とはならない。必要な係数はqueue数ではなくactive depthである。pairwise disjoint subfamiliesへ分ける場合、
interval graphの色数は最大active depthに一致するので、2M prefixだけで427 layersが必要になる。

同様にcrossing numberを「一arcと交差するarc数」またはpairwise crossing clique sizeで抑える案も、観測値が
`21 -> 427`と成長して棄却される。nestingが浅いことは、payment overlapの主成分がnestingではなくparallel
crossingであることを示すだけである。

### 15.5 最終判定

| proposed structure | class | score | consequence |
|---|---|---:|---|
| laminar reuse arcs | false / Lean + replay | 0/100 | crossing反例 |
| one-stack / bounded small stacks | false / replay | 0/100 | crossing clique 427 |
| one-queue / proper intervals | false / replay | 0/100 | nesting pairあり |
| two queues | empirical through 2M | 45/100 as structure | ledgerには無効 |
| bounded nesting depth | empirical `<=2` | 35/100 as structure | active depthを抑えない |
| bounded crossing clique | empirical strongly against | 3/100 | `21→427` |
| bounded active depth | empirical strongly against | 2/100 | raw ledgerへの必要条件が失敗 |
| interval-order rescue of reuse payment | no-go | 3/100 | 完全停止 |

結論として、reuse arcは「浅いnesting・巨大なparallel crossing」というqueue-like形を強く示す。しかし
subtraction paymentを何重にも再利用させるのはまさにparallel crossing側であり、弱いqueue構造は会計上の
利点を一切与えない。candidate-interval集約枝はここで完全停止する。

再開条件はinterval orderの改良ではなく、427本のparallel arcsのうち証明上必要なarcを一つへ圧縮する
semantic representative theorem、または同一clockを共有しても各arcへ別々のfresh resourceを割り当てる
新しいchargeである。これはRound 9Bで停止したfresh terminal certificate問題そのものであり、interval
graphからは生成できない。

## 16. Round 13B: arbitrary-long seeded high corridor no-go

### 16.1 weighted sign traceからactual `Basic.step` traceへ強化

Round 8Bの`+++−` countermodelはweighted step equationだけを満たし、forced addition candidateのhistory
membershipを持たなかった。最終監査ではこの差を縮め、任意の有限長`L`について**実際の有限`State.seen`と
`Basic.step`**で長さ`L`のhigh-only all-addition corridorを構成した。

local clockを`1,2,...`、missing targetを`1`とし、初期値を

```text
v_0 = L+2
```

に置く。全additionを仮定したlocal time `j`の値と次candidateは

```text
v_j = L+2+upperTri(j),
c_j = v_j-(j+1) = L+2+upperTri(j)-(j+1).
```

`j<L`なら`1<c_j`である。そこで有限初期historyを

```text
[v_0, c_0, c_1, ..., c_(L-1)]
```

とseedする。各clockで`c_j`はpositiveかつ既出なので、`CanSubtract`はactualにfalseとなり、`Basic.step`は
`v_(j+1)=v_j+(j+1)`を選ぶ。step outputをhistory先頭へ加えてもtarget `1`は一度も入らない。

この構成を新module `Recaman/SeededHighCorridorNoGo.lean`へ、主定理

```text
arbitrarilyLong_seededHigh_forcedAdditionCorridor
```

として任意`L`についてLean化した。補助不変量は、値のtriangular formula、初期blocker listの永続membership、
target `1`のhistory非所属を同時に帰納する。`lake build Recaman.SeededHighCorridorNoGo`は172 jobsで成功した。

### 16.2 符号語・剰余・有限局所状態だけでは有限上界すら出ない

このfamilyのsign wordは任意長の

```text
+++...+
```

であり、各文字は抽象的な符号選択ではなくhistory membershipによって強制されたreal `step`である。局所interval
ledgerもexactに

```text
v_j = v_0 + upperTri(j)
```

を満たす。さらに偶数`L`を選べば

```text
v_j + upperTri(j) = L+2+2*upperTri(j)
```

は常に偶数なので、標準列のmod-2 triangular parity patternとも両立する。従って次の情報の任意の組合せから、
high corridor長のuniform finite boundは導けない。

- 各stepの`±clock` equation
- candidateがtargetより上というhigh condition
- targetが現在の有限historyに無いこと
- forced candidateが実際にfinite history memberであること
- interval ledgerとmod-2 parity
- finiteであるが長さを事前固定しないseen list

これはinfinite traceを一つ構成した主張ではない。`L`ごとにseed listが大きくなるため、同じ有限seedから
all-additionを永久に続けるcompactnessは与えない。その差がまさに残ったglobal-history入力である。

### 16.3 canonical standard orbitに残る唯一の入力

seeded stateは`initial = ⟨0,[0]⟩`から到達可能とは主張しない。標準Recamán列でeventual-highを排除するには、
局所step legalityではなく次の少なくとも一つを本質的に使う必要がある。

- tail開始時の有限historyがcanonical prefix `valuesThrough(N)`であるというreachability / chronology
- tail内で新しく生成された値だけが将来blockerを補充できるというgeneration-rate bound
- blockerのfirst occurrenceと後続利用を結ぶ、再利用不能なfresh terminal resource
- fixed initial prefixとin-tail depositsを分離するstrict rank

all-forced runだけなら既存`forced_addition_run_defects`により必要blockerが増加し、固定seedからの永久継続は
期待できない。しかしeventual-high branchはsubtractionを挟んでfresh valuesを補充できる。従って「長いforced
runを禁止」してもhigh-only自体は排除できず、generationとlater reuseのglobal chronologyがなお必要である。

### 16.4 最終有望度

| branch | class | score | decision |
|---|---|---:|---|
| arbitrary finite high corridor under real `Basic.step` | exact / Lean family | 100/100 | no-go certificate |
| finite sign-word contradiction | false | 0/100 | all-`+` family |
| parity / residue finite bound | false at mod 2 | 0/100 | even `L` family |
| local finite-history cardinality bound | false uniformly | 0/100 | seed grows with `L` |
| one fixed seed gives infinite all-addition | not claimed | 20/100 | fixed-prefix finiteness may stop it |
| canonical generation-vs-reuse chronology | unresolved | 30/100 | 唯一のglobal再開点 |

最終結論は、eventual-high branchは局所符号語、weighted ledger、剰余、あるいは`Basic.step`のhistory legalityを
有限窓ごとに調べても閉じない、ということである。必要なのはcanonical prefixから生成されたhistoryに固有の
global provenance theoremであり、これはRound 9Bのfresh terminal adapterまたはgeneration-rate boundと同型である。
