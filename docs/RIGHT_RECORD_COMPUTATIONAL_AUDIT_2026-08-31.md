# Global right-record computational audit

最終更新: 2026-08-31

## 結論

memory-light exact probeで標準Recamán軌道を2Bまで延長した。upward blocker resetは
28件あり、全28件がglobal right record、gap insertionは0だった。20Mの20件から
8件増えたが反例は出ていない。

さらに、新upward blocker `b`を固定し、同じtargetのfresh intervalを

```text
L : entry ≤ b
R : intervalLower ≥ b+1  (equivalently intervalBlocker ≥ b)
```

で符号化した。一般のterminal blockerではfirst occurrence後の`RLR`再横断が頻発するが、
upward blocker 28件では全てside wordが`L*R`で、switchはちょうど1回だった。
従って一般的なno-recross法則は偽であり、証明候補は
**upward-terminalに限定したRLR禁止**でなければならない。

## Exact orbit horizon比較

| horizon | macro edges | upward | up right record | up gap insertion | record-gap mass |
|---:|---:|---:|---:|---:|---:|
| 20M | 2,655 | 20 | 20 | 0 | 17,820,564 |
| 50M | 3,785 | 21 | 21 | 0 | 31,563,368 |
| 100M | 5,966 | 22 | 22 | 0 | 57,468,317 |
| 250M | 8,354 | 24 | 24 | 0 | 172,490,820 |
| 500M | 11,709 | 25 | 25 | 0 | 301,987,785 |
| 1B | 15,960 | 27 | 27 | 0 | 903,055,829 |
| 2B | 21,505 | 28 | 28 | 0 | 1,608,068,953 |

2Bでのupward resetには次の追加相関がある。

| property | result |
|---|---:|
| new blocker first origin is addition | 28 / 28 |
| origin predecessor `≤ old blocker` / between / above prior hull | 2 / 0 / 26 |
| `firstTime(new blocker) < previousComb.start` | 28 / 28 |
| post-first side word switches 0 / 1 / 2+ | 0 / 28 / 0 |
| post-first `RLR` | 0 / 28 |
| pre-firstに`R`がある | 0 / 28 |

特に、当初の`firstTime(b) < previous_end`はさらに強く、全28件で
`firstTime(b) < previous_start`だった。

2Bで新しく増えた例はtarget 1355、new blocker 1,609,049,397、first time
334,928,229である。直前comb開始は1,610,189,034なので、時刻分離にも十分な余裕がある。

## Birth前後のhull分解

各upward blocker `b`について、同じtargetの過去intervalを`firstTime(b)`より前に完了、
first timeを跨ぐ、first time後から直前combまでの三群に分けた。

| quantity | 2B result |
|---|---:|
| birth前に完了したintervalがない | 5 / 28 |
| birth前hullが`b`を越える | 0 / 28 |
| birth前record slack min / max（非空23件） | 51 / 1,306,157,735 |
| birthを跨ぐintervalがある | 15 / 28 |
| post-birth hullが`b`を越える | 0 / 28 |
| post-birth remaining slack min / max | 1 / 705,013,124 |

つまり経験的には二つの独立した無交差が見える。

1. blockerが生まれた時点で、すでに完了したtarget intervalの右recordである。
2. blocker誕生後も直前combまでのintervalはblockerを越えず、最後にcurrent intervalが`R`へ移る。

ただし15件ではblocker誕生時刻を跨ぐcombがあるので、単純な「comb境界で生まれる」証明には
できない。証明ではbirthを跨ぐcombのhigh stateも別途処理する必要がある。

## 全terminal blockerとの対照

2Bまでのhistory-terminated blocker 21,510件を同じ方法で調べた。

| quantity | result |
|---|---:|
| post-first switch 0 / 1 / 2 / 3+ | 303 / 9,528 / 80 / 11,599 |
| maximum post-first switches | 28 |
| post-first `RLR` | 11,679 |
| post-first `LRL` | 11,599 |
| maximum pre-first switches | 26 |
| pre-first `RLR` | 4,025 |

従って「既出値をfresh intervalが一方向にしか横切らない」という一般補題は棄却される。
RLR禁止が残るのは、後続terminal blockerが直前blockerより上昇した27例だけである。

## Provenanceを弱めた反例

### 任意seed state + addition origin

次の有限seedからは、その後を正確なRecamán ruleで走らせてもgap-insertion upward resetが出る。

```text
seen = {0,1,6,8,13}, current = 13, nextClock = 7
target = 4
previous interval = [7,7], previous blocker = 6
old right hull = 24
new interval = [15,17], new blocker = 14
new blocker first origin = addition at clock 12: 2 + 12 = 14
```

`6 < 14 < 24`なのでblockerは上昇するがglobal right recordではない。このseedは
visited数、三角数上界、currentのparityという genuine prefix の必要条件を満たす。
従ってpairwise interval orderだけでなく、**new blockerがaddition-originであることまで加えても**
right-recordは導けない。

### 正しい±clock walk prefix

さらに、clock 1..8を全て加算した正しいsigned-clock walk

```text
0,1,3,6,10,15,21,28,36
```

をseedとし、clock 9以後だけRecamán ruleに従うと、target 2について

```text
previous interval = [8,8], previous blocker = 7
old right hull = 22
new interval = [18,18], new blocker = 17
```

というgap insertionが出る。ただしこの新blocker 17のfirst originは
`27 - 10 = 17`というsubtractionである。これは「時計付き実軌道である」だけでも不十分だが、
addition-origin条件がこの小さいsigned-walk反例を除くことも示す。

## 次の証明候補

経験的候補を次の強さに分離する。

1. 一般のfixed-blocker no-recross: 1Bで大量反例、停止。
2. addition-origin blockerのno-recross: arbitrary seedで反例、単独では停止。
3. exact greedy prefix上のupward-terminal `RLR`禁止: 1Bで27/27、継続。
4. さらに強い時刻形
   `firstTime(new blocker) < previousComb.start`: 2Bで28/28。ただし下記の通り単独では非十分。

前節の両seeded反例はどちらもこの時刻形を満たす。addition-origin反例では
`firstTime(14)=12 < previousStart=37`、signed-clock walk反例では
`firstTime(17)=10 < previousStart=31`である。従ってこの時刻不等式は経験的には安定だが、
right-recordを単独で含意せず、proof usefulnessは低い。必要なのはbirth時のglobal hull recordと
post-birth no-crossingのどちらかをactual greedy provenanceから導くことである。

## Orbit全体のenvelopeは使えない

target fresh-interval hullより強い候補として、new blockerがfirst occurrence時のorbit running
maximumか、その後current comb開始までorbit全体が`b`以下かを2Bで調べた。

| quantity | result |
|---|---:|
| first occurrence時にorbit running record | 6 / 28 |
| running recordでない | 22 / 28 |
| maximum birth deficit `priorOrbitMax - b` | 892,674,758 |
| firstTime後〜current.start前にorbit値が`b`を越える | 28 / 28 |
| maximum post-birth orbit excess | 10,991,026,723 |

従って標準prefix provenanceを「orbit全体のrecord」へ強化する枝は即時棄却する。成立しているのは
targetのfresh low railだけに限定したhull recordである。high-state reservoirは全28件でbirth後に
`b`を越えるため、証明はorbit envelopeではなく、high stateが後続fresh intervalへ着地する条件を
追跡しなければならない。

## RLR後のtarget return監査

right-record自体を証明する代わりに、gap-insertion RLRが起きたらmissing targetが将来出現する、
という弱いreturn certificateをseeded orbitで監査した。

| seed family | seeds | RLR witnesses | origin add/sub/seed | returned | censored | maximum observed delay |
|---|---:|---:|---:|---:|---:|---:|
| necessary-condition grid | 767,344 | 18 | 18 / 0 / 0 | 18 | 0 at 15k | 6,536 |
| random nonnegative ±clock prefix | 100,000 | 75 | 0 / 37 / 38 | 73 | 2 at 1B | 14,473 |

gridでは全てaddition-origin RLRで、18/18が15,000 step以内にtargetへ帰還した。一方、
signed-clock prefixの2例は1B follow-upでもtarget 2が未帰還だった。

```text
sample 51649: nextClock=74 current=59
  witness clock=150, blocker 6 -> 45, priorUpper=58

sample 57653: nextClock=30 current=203
  witness clock=95, blocker 18 -> 26, priorUpper=41
```

両censored例のnew blockerはseed由来であり、標準軌道のupward 28件に共通するaddition-originではない。
有限計算なので「決して帰還しない」という反例ではないが、一般RLR return則は局所公理から容易に
出るほど安定ではない。現時点では **addition-origin RLR ⇒ target return** が、right-recordより
弱く直接的な限定候補として残る。

## Round 3時点の暫定分離スコア

以下はadversarial evolution前の暫定値である。最終評価は後段で更新する。

| candidate | empirical stability | proof usefulness | assessment |
|---|---:|---:|---|
| global upward right-record | 88/100 | 55/100 | exact 2Bで28/28だが単独ではsurjectivityに不足 |
| upward-terminal RLR禁止 | 88/100 | 65/100 | right-record失敗の正確な局所形だがcausal証明が必要 |
| `firstTime(b) < previous.start` | 92/100 | 15/100 | exact 28/28、seed反例により単独非十分 |
| orbit running-record envelope | 10/100 | 10/100 | 22/28がbirth時非record、停止 |
| general RLR ⇒ target return | 62/100 | 80/100 | 73/75帰還、2例は1B censor。証明できれば直接閉包 |
| addition-origin RLR ⇒ target return | 76/100 | 85/100 | grid 18/18帰還、signed sampleには該当例なし |

proof usefulnessではreturn certificateがright-recordを上回る。right-record違反そのものを排除する
必要がなく、違反がtarget出現を強制すればmissing-target仮定と直ちに矛盾するためである。ただし
empirical stabilityはright-recordより低く、次のラウンドはaddition-originとexact greedy prefixを
statementに保持した限定return補題に絞る。

## Adversarial return-delay evolution

addition-origin RLR return候補を敵対的に調べた。開始seedは

```text
seen={0,1,6,8,13}, current=13, nextClock=7
```

で、target 4に対してclock 60で同じaddition-origin RLRを作る。

```text
old interval     [21,24], blocker 20, clocks 23..31
previous interval [7,7], blocker 6, clocks 37..39
current interval [15,17], blocker 14, clocks 54..60
```

evolutionary mutationは、各generationでtargetがclock `t`に帰還したら`seen`へ
`t + target`を一つ追加する。この値はtarget landing直前の値であり、初回installationをseedで
既出にすることで軌道を分岐させる。fitnessは同じclock 60のRLRからtarget 4が次に出るまでのdelay。

14 generationの追加値列を再現した。

```text
1111, 2024, 6424, 11955, 20908, 36687, 66572,
209840, 373139, 1195679, 3501447, 5708532,
10370243, 18472704
```

これでnext hitは31,581,807、delayは31,581,747になる。さらに同じmutationを4回続けた。

| total seed size | newly added blocker | next target hit | delay from RLR clock 60 |
|---:|---:|---:|---:|
| 19 | 18,472,704まで | 31,581,807 | 31,581,747 |
| 20 | 31,581,811 | 55,703,076 | 55,703,016 |
| 21 | 55,703,080 | 304,835,267 | 304,835,207 |
| 22 | 304,835,271 | 517,297,628 | 517,297,568 |
| 23 | 517,297,632 | 4Bまで未帰還 | censored |

最後の23-value seedでもRLR blocker 14はclock 12のaddition-originのままで、RLR witnessもclock 60の
ままである。4,000,000,000 step exact follow-upではtarget 4は出なかった。実測は約15.5秒、
maximum resident set size約23.8GBだった。

これはeventual returnの数学的反例ではない。4Bは有限censorにすぎない。しかし、有限のRLR局所形、
addition-origin、firstTime分離だけから実用的なreturn boundを得る方針には明確な反証である。
わずか18個の追加history blockerでdelayを1,000から5億超へ伸ばせ、19個目では4B horizonを越えた。

### 保守的な再評価

| candidate | empirical stability | proof usefulness | updated decision |
|---|---:|---:|---|
| global upward right-record on exact orbit | 88/100 | 55/100 | 保持。2Bで28/28 |
| general RLR ⇒ return | 25/100 | 45/100 | seeded局所定理として停止 |
| addition-origin RLR ⇒ return | 30/100 | 55/100 | 4B censor。exact-prefix条件なしでは停止 |
| exact-greedy-prefix addition-origin RLR ⇒ return | 50/100 | 65/100 | 論理的には有用だが標準軌道では該当例0でempirical supportなし |

return certificateが成立すれば直接的に有用である点は変わらないが、proof usefulnessを85から55へ
下げる。seeded historyに対するrobust lemmaにはならず、exact standard prefixをstatementへ戻す必要が
あるため、証明負担が元のglobal problemへ近づくからである。次の探索ではgeneric return branchを
停止し、right-recordのtarget fresh-interval因果性、または4B delay mutationを排除できる
standard-prefix固有の有限資源を先に要求する。

## Pre-tail ancestry capacity audit

各history-terminated target combのblockerからfirst-occurrence parentを遡り、nodeのfirst timeが
そのtargetのmex epoch開始以前になった最初の値をpre-tail rootとした。first occurrence `v`がclock
`t`のadditionならparent=`v-t`、subtractionならparent=`v+t`なので、first timeとbranchを32 bitへ
packingしたdense metadataで20Mを一回走査した。

| quantity | 2M | 20M |
|---|---:|---:|
| terminal ancestry paths | 848 | 2,660 |
| distinct pre-tail roots | 559 | 860 |
| maximum root reuse | 170 global / 32 for target 1355 | 629 |
| maximum first-time node reuse | 170 | 629 |
| maximum time-edge reuse | 170 | 629 |
| path length p50 | 0 | 5,820 |
| path length p90 | 3,765 | 46,284 |
| path length p99 | 18,776 | 83,040 |
| maximum path length | 22,391 | 196,458 |
| ancestry nodes total / union | 1,198,992 / 176,188 | 45,234,733 / 2,222,562 |
| fresh interval mass | 569,399 | 5,776,535 |
| ancestry union ∩ fresh interval union | 12,889 | 157,336 |
| distinct ancestry overlap rate | 7.315% | 7.079% |
| weighted ancestry/fresh overlap | 224,154 | 7,474,365 |

target 1355だけを見ると、2Mから20Mでroot reuseは32から629、maximum pathは22,391から
196,458へ増えた。20Mの一つのpre-tail root `657846`には629本のterminal pathが集中し、同じ
first-time nodeとtime-edgeも最大629回再利用される。

従って「tail内の各blockerを有限pre-tail rootへ戻し、rootまたはtime-edgeを一回だけcapacity課金する」
枝は棄却する。root集合は有限でもreuseが全くboundedではなく、pathもhorizonとともに長くなる。
さらにancestry unionの約7%はfresh interval massと重なり、path multiplicityで数えるとoverlap
7,474,365がfresh mass 5,776,535自体を上回る。fresh massとancestryを独立資源として加算する
potentialも二重課金になる。

この否定結果は2M→20Mで十分明瞭なので、約50GBのdense metadataを要する2B runは行わない。
time-only above-target ancestry branchを停止し、再開条件を「標準prefix固有のbounded reuse theorem」
またはmultiplicityを相殺する符号付き収支が先に得られた場合に限定する。

## Final 4B exact-orbit audit

memory-light right-record probeを標準Recamán軌道4,000,000,000 stepまで実行した。これは
最終empirical auditであり、証明ではない。

| quantity | 2B | 4B |
|---|---:|---:|
| history-terminated combs | 21,510 | 29,277 |
| macro edges | 21,505 | 29,272 |
| upward resets | 28 | 29 |
| upward global right records | 28 | 29 |
| upward gap insertions | 0 | 0 |
| total record-gap mass | 1,608,068,953 | 2,786,767,563 |
| general terminal post-first RLR | 11,679 | 15,599 |
| general maximum side switches | 28 | 29 |

4Bで増えたupward例は次である。

```text
target=1355
previous blocker=2404
new blocker=2,788,880,661
prior fresh hull upper=1,610,182,051
record gap=1,178,698,610
firstTime=984,818,805
origin=addition from predecessor 1,804,061,856
current comb start=2,789,157,595
```

29件全体のcausal監査も従来の相関を保った。

| property | 4B result |
|---|---:|
| new blocker first origin addition | 29 / 29 |
| origin predecessor `≤ old blocker` / between / above prior hull | 2 / 0 / 27 |
| `firstTime(new blocker) < previousComb.start` | 29 / 29 |
| upward post-first side word `L*R` | 29 / 29 |
| upward post-first RLR | 0 / 29 |
| upward side switches exactly one | 29 / 29 |
| pre-firstにright intervalがある | 0 / 29 |
| target fresh hull birth violation | 0 / 29 |
| post-birth target hull violation | 0 / 29 |

orbit全体のrecord候補は引き続き偽で、birth時running recordは6/29だけ、birth後current開始前に
`b`を越えるorbit値は29/29だった。従って4Bは新しい証明枝を増やさず、target fresh-intervalに
限定したright-record / RLR禁止だけを経験的に補強する。

実測は46.45秒、maximum resident set size 12,041,224,192 bytes（約12.04GB）、最終dense seen
bitsetは3,808MiBだった。global upward right-recordのempirical stabilityを88から90/100へ微増するが、
rare eventが29件に留まり、証明ではないためそれ以上には上げない。proof usefulnessは55/100のまま。

次の紙上解析では、new blockerのfirst additionが直前comb開始より前であることをまず示し、
その値が一度でも右側intervalに属した後、直前のleft intervalを経てterminal `b`へ戻る
`RLR`をactual greedy provenanceが禁止するかに絞る。

## Round 7: fixed-anchor obstruction and pre-tail envelope audit

### `activeAnchor`とpre-tail rootの正確な意味

`FirstAt.preTail_anchorObstruction_or_normalProgress`の`anchor`はterminal combから自動的に
決まる値ではない。これは`PhaseSearchNode.anchorParent`として呼出側が固定するrankの第2成分であり、
ancestry中は変更されない。`pre-tail root`はterminal blockerから実際のfirst-occurrence parentを遡り、
first timeが`tailStart`以下になった最初のabove-target値である。ただし途中のparentが初めて
`activeAnchor`未満になればそこでnormal progress枝へ退出するため、単に最終rootとanchorを比較する
だけでは不正確である。

現行のterminal macro certificateには`activeAnchor` fieldも、PhaseSearchのnormal parentとの接続定理もない。
そこで標準軌道の各target mex epochをfinite `tailStart`として、terminal blocker ancestryへ適用できる
二つのproxyを分離して監査した。

- `current blocker`: `value=anchor=blocker`。blocker ancestryに許される最大anchor。
- `previous blocker`: 同じtargetのstrict upward macro edgeだけで
  `value=current.blocker`, `anchor=previous.blocker`。
- `entry`: 全terminalで`blocker < entry`なので、blocker ancestryでは定理の
  `anchor <= value`を満たさず適用不能。

標準有限prefixは`MissingPermanentAboveTail`を満たすと仮定していないため、これはLean定理の適用例では
なく、そのexact stopping ruleを用いた敵対的な有限監査である。

| horizon | terminals | current-blocker residual | upward previous-blocker residual | entry inapplicable |
|---:|---:|---:|---:|---:|
| 200k | 269 | 90 / 269 (33.46%) | 4 / 13 (30.77%) | 269 / 269 |
| 2M | 848 | 633 / 848 (74.65%) | 7 / 16 (43.75%) | 848 / 848 |
| 20M | 2,660 | 1,034 / 2,660 (38.87%) | 11 / 20 (55.00%) | 2,660 / 2,660 |

20Mのtarget別内訳は次である。

| target | current-blocker residual | upward previous-blocker residual |
|---:|---:|---:|
| 4 | 0 / 5 | 0 / 3 |
| 19 | 12 / 186 | 4 / 10 |
| 61 | 70 / 70 | 0 / 0 |
| 879 | 92 / 92 | 0 / 0 |
| 1,355 | 860 / 2,307 | 7 / 7 |

previous-blocker proxyの最大`root / anchor`は約220.402で、具体例はtarget 1355、macro
`1789244..1821672`、current blocker `1770560`、anchor `5328`、pre-tail root `1174301`
（first time `274350`、anchor-aware path length `8831`）である。current-blocker proxyでも最大比は
約58.220、同じrootへanchor `20170`から到達した。residual path長の最大はそれぞれ54,288と70,121。
従ってterminal-specificにresidualが常に偽という強化は、自然なproxyでは反証される。とくに最新target
1355のupward例が7/7 residualなので、rare early-target artifactでもない。
20M runの実測は約1.22秒、maximum resident set size 1,106,755,584 bytesだった。

### pre-tail orbit maximumはone-use capacityにならない

各target epochについて

```text
M = max { a(t) | t <= epochStart }
```

をexact orbitから記録し、terminal blockerとupward blockerが`M`を越えるかを調べた。

| horizon | blocker `> M` / `<= M` | upward `> M` / `<= M` | first crossing後の `<= M` 再発 |
|---:|---:|---:|---:|
| 200k | 170 / 99 | 11 / 2 | 11 |
| 2M | 170 / 678 | 11 / 5 | 11 |
| 20M | 953 / 1,707 | 15 / 5 | 793 |

20Mではtarget 4が`M=6`をstart 8のblocker 7で初めて越え、target 19は`M=495`をstart 831の
blocker 843で、target 1355は`M=1942300`をstart 3225015のblocker 3216221で初めて越える。
その後の`<= M`再発はtarget 19で11件、target 1355で782件ある。最大`blocker / M`はtarget 19の
`56257 / 495 = 113.6505...`（start 57058）だった。target 61と879は20Mまで一度も`M`を越えない。

従って「初めてpre-tail envelopeを越えたterminalを一回だけ課金し、以後はその外側に留まる」という
one-use→unbounded potentialは単調性を持たない。upward terminal自体にも`<= M`が20件中5件あり、
upward限定でも修復できない。

### Round 7判定

| candidate | empirical stability | proof usefulness | decision |
|---|---:|---:|---|
| terminal ancestry always crosses below active anchor | 15/100 | 25/100 | proxyで頻繁に偽、かつcertificateにanchor interfaceなし。停止 |
| pre-tail maximum crossing is one-use | 5/100 | 10/100 | 20Mで793回再侵入。停止 |
| generic fixed-anchor dichotomy | 100/100 | 45/100 | Lean exact lemmaとして保持。左residualを消す用途には不足 |

再開条件は、terminal macroと実際の`PhaseSearchNode.anchorParent`を結ぶ新しいexact interfaceが先に得られ、
そのanchorが上記三proxyと異なることを説明できた場合に限る。現状ではpre-tail capacity枝をさらに強化する
より、別のterminal gate不変量へ移るべきである。

## Round 8: target-relative high-candidate runs

### 測定対象

state time `n`で次clockが提示するcandidateを

```text
c_n = max(a(n) - (n+1), 0)
```

とし、その時点のmex target `m`に対し`c_n<m`をlow、`m<c_n`をhigh、`c_n=m`をequalとした。
equalは次stepでtargetを訪れてepochを終えるため、strict-high runには含めない。各mex epoch内で二つの
strict-low state間にある連続high数をinter-low runとして集計した。finite horizon先端のhigh suffixと
epoch開始直後のprefixもmaximum observed runには含めた。

terminal conversionは二つの異なる分母を併記した。

- fresh subtraction landingかつlowで始まる`FreshCombEpisode` startのうちhistory-terminatedになる率
- 全low stateのうちhistory-terminated macro一個へ変換される率

### horizon scaling

| horizon | low / equal / high | low density | maximum high run | macro start / terminal / target / censored | terminal / start | terminal / all low |
|---:|---:|---:|---:|---:|---:|---:|
| 200k | 56,978 / 4 / 143,018 | 28.489% | 2,129 | 271 / 269 / 1 / 1 | 99.262% | 0.4721% |
| 2M | 569,413 / 5 / 1,430,582 | 28.471% | 14,545 | 849 / 848 / 1 / 0 | 99.882% | 0.1489% |
| 20M | 5,779,967 / 5 / 14,220,028 | 28.900% | 109,271 | 2,662 / 2,660 / 1 / 1 | 99.925% | 0.0460% |

完了済みの大きいepochではinter-low runのp50/p90/p99はすべて`1/1/1`だった。例外的な長い
high runはhorizonとともに伸びるが、run分布の99%以上はlowとほぼ交互である。

| 20M epoch target | candidate states | low density | run p50/p90/p99/max |
|---:|---:|---:|---:|
| 4 | 127 | 31.496% | 1 / 6 / 17 / 17 |
| 19 | 99,603 | 27.732% | 1 / 1 / 1 / 1,755 |
| 61 | 81,919 | 27.873% | 1 / 1 / 1 / 2,129 |
| 879 | 146,349 | 28.639% | 1 / 1 / 1 / 4,173 |
| 1,355 | 19,671,998 | 28.912% | 1 / 1 / 1 / 109,271 |

進行中の最新epochを比較すると次になる。

| horizon | target | epoch states | low density | run p50/p90/p99/max | high suffix | tail 10% low density | last 1M low density |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 200k | 879 | 18,347 | 35.319% | 1 / 1 / 1 / 1,945 | 1 | 49.97% | 35.319% |
| 2M | 1,355 | 1,671,998 | 28.529% | 1 / 1 / 1 / 14,545 | 10,299 | 37.31% | 28.307% |
| 20M | 1,355 | 19,671,998 | 28.912% | 1 / 1 / 1 / 109,271 | 1 | 30.23% | 36.493% |

従って標準prefixはeventually-high-onlyを有限的に反証しないが、その兆候も示さない。全体low densityは
約28.5--28.9%で安定し、20Mの末尾でも正密度を保つ。一方、最大gapだけは2,129→14,545→109,271と
伸びるため、bounded-gapやuniform return timeは偽である。
20M runは二回のexact orbit scan込みで約0.17秒、maximum resident set size 213,254,144 bytesだった。

重要な分離は、lowの正密度がterminal macroの正密度を意味しないことである。fresh-entry startが
生じれば99.9%以上がhistory terminalへ完了するが、20Mではterminalは全lowの0.046%にすぎず、比率は
horizonとともに低下した。従って

```text
infinitely many low states -> infinitely many completed terminal combs
```

を使うには、lowからfresh subtraction entryを無限回抽出する別のcausal lemmaが必要である。

### local terminal childのsemantic監査

`HistoryTerminatedComb.tail_blocker_debtNormalProgress`の数値nodeは次である。

```text
parent current : (horizon=s, anchor=value=a(s), normal)
debt           : (horizon=s, anchor=a(s), local=blockerFirstTime)
normal child   : (horizon=s, anchor=value=blocker, normal)
```

normal childのhorizonは`s`のままだが、そのvalueは`a(s)`ではなくhistorical blockerなのでcurrent-state
nodeではない。20Mの2,660 terminalsでは全例で

```text
target < blocker, blockerFirstTime < s, blocker < a(s)
```

が成立し、parent `targetStartNode(s)`のorbit-ready数値条件も2,660/2,660だった。blocker originは
addition 1,400、subtraction 1,260。

blocker first timeを`f`として代替current node `(horizon=f, anchor=value=blocker)`を作る場合、
`target <= f+1`は2,660/2,660で成立した。しかし`f`から`s`へhistory horizonを戻すと
`missingBelowCount`が悪化し得る。`mexAtFirst=target`、すなわち`f`ですでにtarget未満の全値が
coveredで、current nodeをparentへのrank childとして直接使える例は1,829/2,660だけだった。
残る831例はhorizon `s`を保持したhistorical normal childを必要とする。

target別のdirect-current候補は、target 4が5/5、19が178/186、61が0/70、879が0/92、1355が
1,646/2,307。upward terminal 20件は全てaddition-originでdirect-currentは18/20だった。二つの
budget mismatch例は次である。

```text
target 19:   s=235, entry=254, blocker=228,
             firstTime=75, originParent=153, mexAtFirst=4
target 1355: s=591170, entry=587477, blocker=571531,
             firstTime=211310, originParent=360221, mexAtFirst=879
```

従ってlocal terminal adapter自体は強く、全terminalでhistorical semantic childを与える。一方でこれを
常にactual current childへ置換する簡略化は偽である。proof側では`firstTime`、`s`、`a(s)`を消さず、
current-at-firstへ移す枝とhistory horizonを保持する枝をbudget equalityで分ける必要がある。

### Round 8判定

| candidate | empirical stability | proof usefulness | decision |
|---|---:|---:|---|
| eventually-high-only on the standard orbit | 5/100 | 20/100 | 20M末尾までlow正密度。独立主枝として停止 |
| bounded high-run gap | 0/100 | 10/100 | max 109,271まで増加。棄却 |
| fresh entry start `=>` completed terminal | 95/100 | 80/100 | 2,660/2,662。保持 |
| low state `=>` fresh terminal entry at positive density | 20/100 | 75/100 | terminal/lowが0.046%へ低下。新しいcausal lemmaなしでは停止 |
| terminal historical child adapter | 100/100 | 90/100 | exact Lean theoremと2,660/2,660数値監査。最有望 |
| terminal child is always replaceable by current-at-first | 69/100 | 45/100 | 831 counterexamples。budget splitなしの形は棄却 |

## Round 9: low-candidate to maximal terminal-comb extraction

### 最大episode被覆

Round 8の`terminal count / low count`は、長いcomb episodeを一個と数えていたため抽出率を過小評価して
いた。history-terminated combのentry-to-blocker fresh interval長

```text
L = a(s) - blocker = k + 1
```

は、そのepisodeが持つlow rail clock数である。`CombRun s k`自身が持つ成功`CombStep` clockは
`L-1=k`個で、最後のlow clockはhistorical blockerに止められるterminal gateである。

active episode内では新しいstartを選ばないgreedy maximal抽出で被覆を測った。

| horizon | total low | history-terminal rail covered | any detected rail covered | history orphan | true orphan | rail/step overlap |
|---:|---:|---:|---:|---:|---:|---:|
| 200k | 56,978 | 55,853 | 56,967 | 1,125 | 11 | 0 / 0 |
| 2M | 569,413 | 569,399 | 569,400 | 14 | 13 | 0 / 0 |
| 20M | 5,779,967 | 5,776,535 | 5,779,954 | 3,432 | 13 | 0 / 0 |

20Mのhistory orphan 3,432個は、真のorphan 13個、target 4を訪れて終わるepisodeの有効rail 1個、
horizon 20Mで進行中のtarget 1355 episodeの有効rail 3,418個にexact分解される。history terminal、
target terminal、censored episodeをすべて含めると未被覆は13個だけで、この数は2Mから20Mで増えない。
最大episode抽出のrail overlapとCombStep overlapは全horizonで0だった。

20Mではcovered 5,779,954 clocksが

```text
5,777,294 successful CombStep clocks
+   2,660 history terminal gates
```

に完全分解される。target landingが次mex epochへ移るrail 1個と、finite horizon外のcensored rail 1個は
target-index / range validationで明示的に除外した。

### episode length scaling

| horizon | history episodes | low rails total | CombSteps total | rail length p50 / p90 / p99 / max |
|---:|---:|---:|---:|---:|
| 200k | 269 | 55,853 | 55,584 | 51 / 652 / 1,597 / 3,187 |
| 2M | 848 | 569,399 | 568,551 | 112 / 1,505 / 11,445 / 23,974 |
| 20M | 2,660 | 5,776,535 | 5,773,875 | 285 / 4,323 / 33,747 / 159,583 |

episode lengthは強く成長し、macro一個を単位にしたdensityが下がるのは当然だった。low rail massで測れば
被覆率は20Mで99.9998%であり、真のorphanはpermanent-tail仮定がまだ成立しないepoch境界だけに集中する。

### nonfresh orphanのbackward origin

20Mのlow arrivalはinitial 1、legal subtraction fresh 5,779,959、addition fresh 3、addition repeat 4。
current valueがtargetより上かつlegal-subtraction arrivalなのに未被覆なclockは0件だった。4件の
nonfresh lowはすべてepoch開始直後にあり、過去のfirst occurrenceはlegal subtractionだった。

| target | epoch start | repeated low time / entry | first time / parent | mex at first |
|---:|---:|---:|---:|---:|
| 19 | 131 | 132 / 136 | 124 / 260 | 4 |
| 61 | 99,734 | 99,735 / 99,754 | 99,731 / 199,485 | 19 |
| 879 | 181,653 | 181,654 / 181,715 | 181,650 / 363,365 | 61 |
| 1,355 | 328,002 | 328,003 / 328,882 | 327,999 / 656,881 | 879 |

first-to-repeat lagはp50/p90/p99/max=`4/8/8/8`、4件ともfirst timeは現在epoch開始以前で、first時の
candidateは現在targetに対してlowだった。これは標準prefixのmex切替直後にだけ生じる境界現象である。
仮想permanent strict-above tailでは`candidateBelow_entry_first`がforced-addition originを排除するため、
このnonfresh class自体が消える。

### 全suffixを取る場合のmultiplicity

permanent tailの各low clockはfreshなので、最大episodeの内部lowからも同じfinal gateへ向かうsuffix
episodeを開始できる。長さ`L`の最大episodeは`L`本のsuffixを持ち、rail coverage multiplicityは
`1,2,...,L`になる。

| horizon | suffix episodes | union rails | triangular coverage mass | duplicate mass | maximum multiplicity |
|---:|---:|---:|---:|---:|---:|
| 200k | 55,853 | 55,853 | 25,427,922 | 25,372,069 | 3,187 |
| 2M | 569,399 | 569,399 | 1,933,653,289 | 1,933,083,890 | 23,974 |
| 20M | 5,776,535 | 5,776,535 | 84,843,306,542 | 84,837,530,007 | 159,583 |

従って「各lowから得るterminal blockerは一対一」やuniform bounded multiplicityは偽である。しかし
必要なのはuniform boundではなくfinite fiberだけである。low start `s`へ
`candidateBelow_exists_historyTerminatedComb`が返すterminal final time `e=s+2k`を対応させると、固定`e`の
preimageは`0 <= s <= e`に含まれ有限である。よってlow clockが無限ならterminal final timeも無限。
さらに`HistoryTerminatedComb.same_blocker_finalTime_eq`の対偶により、異なるfinal timeは異なるblockerを
持つ。従ってblocker集合は無限、したがってNat内でunboundedになる。

このfinite-fiber wrapperが、Lean側で完成した

- `MissingPermanentAboveTail.candidateBelow_entry_first`
- `FirstAt.exists_maximal_freshCombEpisode`
- `FreshCombEpisode.historyTerminated_of_next_not_step`
- `MissingPermanentAboveTail.candidateBelow_exists_historyTerminatedComb`

から`infinitely many low => unbounded terminal blockers`へ進む次の正確なcombinatorial conditionである。

### Round 9判定

| candidate | empirical stability | proof usefulness | decision |
|---|---:|---:|---|
| low clock `=>` finite terminal suffix | 100/100 | 95/100 | Lean exact + prefix rail被覆。最有望 |
| greedy maximal episodes cover tail lows disjointly | 100/100 | 90/100 | above-sub orphan 0、overlap 0。保持 |
| uniform bound on suffix multiplicity | 0/100 | 10/100 | max 159,583まで増加。棄却 |
| finite-fiber terminal-final map | 100/100 | 95/100 | multiplicity増加を許容。次のLean wrapper |
| infinite low `=>` unbounded blockers | 90/100 | 95/100 | finite-fiber + same-blocker final uniquenessで到達目前 |

20M runは二回のexact orbit scan込みで約0.16秒、maximum resident set size 156,008,448 bytesだった。

## Round 10: finite-basin remount

### 定義とexact separator check

各history-terminal blockerのactual first-occurrence ancestryを遡り、first timeがtarget mex epoch開始以下に
初めてなった値をpre-epoch root `r`とする。そのterminalより後の同target maximal episodesを時系列に
調べ、最初に`entry < r`となるepisodeまでの距離を測った。

`r`はepoch開始以前に既出なので、後続combのfresh interval `[blocker+1, entry]`は`r`を含めない。
従って各後続episodeにはexactに

```text
entry < r  or  r <= blocker
```

が必要である。probeは`entry < r`が初めて出るまで、後者が毎回成立することを独立に検査した。

### path-weightedとdistinct-root集計

同じrootへ多数のterminal ancestryが集中するため、全pathを重み付きで数える集計と、targetごとに
同一rootを一つへ潰しfirst useから測る集計を分けた。wait distance `1`は直後のepisodeでescapeすることを
表す。

| horizon | paths / distinct roots | path resolved / unresolved | path wait p50/p90/p99/max | distinct resolved / unresolved | distinct wait p50/p90/p99/max |
|---:|---:|---:|---:|---:|---:|
| 200k | 269 / 90 | 206 / 63 | 4 / 73 / 91 / 93 | 85 / 5 | 1 / 1 / 12 / 12 |
| 2M | 848 / 559 | 761 / 87 | 1 / 22 / 87 / 156 | 551 / 8 | 1 / 1 / 1 / 156 |
| 20M | 2,660 / 860 | 2,535 / 125 | 1 / 330 / 557 / 653 | 851 / 9 | 1 / 1 / 4 / 653 |

path-weighted unresolved率は23.42%→10.26%→4.70%、distinct-root unresolved率は
5.56%→1.43%→1.05%へ下がった。20Mのmax-wait witnessはtarget 1355、root `18953`、source start
`10201024`からescape start `18394609`まで653 episodesである。uniform bounded waitは否定されるが、
大多数のdistinct rootsは直後のepisodeでescapeする。

20Mのtarget別結果は次である。

| target | paths / roots | distinct resolved / unresolved | maximum wait | unresolved root values |
|---:|---:|---:|---:|---|
| 4 | 5 / 1 | 0 / 1 | 0 | 2 |
| 19 | 186 / 11 | 9 / 2 | 12 | 46, 91 |
| 61 | 70 / 70 | 69 / 1 | 1 | 75 |
| 879 | 92 / 92 | 91 / 1 | 1 | 5,014 |
| 1,355 | 2,307 / 686 | 682 / 4 | 653 | 3,377; 5,328; 9,461; 18,106 |

古いtarget 4/19/61/879の未解決rootは、そのtargetが実際に出現してmex epoch自体が終了したための
censorである。target 1355の4 rootは20M horizonでcensorされる。従ってfinite standard prefix上の
数学的反例ではない。ただし最大waitの成長は、clockまたはepisode数のuniform boundを補題に入れる方針を
否定する。

### finite basinとblocker side

全2,660 pathsで`r <= max_{t<=epochStart} a(t)`が成立し、違反0。最大比は1で、target 19のroot 495が
pre-tail maximum 495に一致した。current episode自身も455件が`entry<r`、残る2,205件が
`r<=blocker`で、fresh separator違反は0だった。

後続escape待ちでは20Mで265,986 episode比較、distinct-root first-useだけでも7,390比較を行い、
`entry>=r`かつ`blocker<r`は0件だった。これは経験則というよりfresh intervalとroot既出性から導くべき
短いexact lemmaである。escapeが起こらない枝でも全後続blockerが`r`以上へ固定されるため、finite basin
から外側blocker側へmountする二択が保たれる。

root reuse自体は最大170→170→629へ増え、path-weighted countingには使えない。一方、distinct rootへ
quotientすると20Mで860個中851個がescape済みであり、reuseはremount存在の判定を汚さない。

### Round 10判定

| candidate | empirical stability | proof usefulness | decision |
|---|---:|---:|---|
| pre-epoch root lies in finite actual-prefix basin | 100/100 | 90/100 | exact finite-prefix boundとして保持 |
| `entry<r or r<=blocker` separator | 100/100 | 95/100 | 265,986比較で違反0、freshnessからLean化候補 |
| every root eventually sees `entry<r` | 88/100 | 70/100 | distinct 851/860。全未解決はcensoredだが証明なし |
| uniformly bounded remount wait | 0/100 | 10/100 | max 12→156→653。棄却 |
| finite-basin remount dichotomy | 92/100 | 90/100 | escapeまたは永続blocker side。次の統合候補 |

20M runは既存ancestry全監査込みで約0.91秒、maximum resident set size 1,103,609,856 bytesだった。

## Round 11: fixed-root fresh-mass potential

### 探索した単調量

fixed pre-epoch root `r`から後続の最初の`entry<r`まで、blocker側に残る各terminal episode `i`へ

```text
I_i = [blocker_i + 1, entry_i]
q_i = |I_i| = entry_i - blocker_i
Q_k = sum_{i <= k} q_i
E_k = max_{i <= k} entry_i
```

を対応させた。各`I_i`はfirst visitからなるfresh intervalなので相互にdisjointであり、Round 10の
separatorによりescape前はすべて`(r, E_k]`内にある。またcombのclock形から
`end_i - start_i = 2 q_i`である。従って有限prefixごとに

```text
number of waiting episodes <= Q_k <= E_k - r
2 Q_k <= escapeStart - sourceStart              (escapeした場合)
```

となる。`Q_k`はepisodeごとにstrictに増えるため、fixed rootでescapeせずepisodesが無限なら
`Q_k`と`E_k`も無限になる。これはeventual escapeそのものではないが、no-escape枝を
「unbounded high-side fresh mass」へ縮約するactual-recurrence固有の単調量である。

### horizon audit

同じ`(target,r)`の重複ancestryはfirst use一件にquotientした。`waiting episodes`はescape episode
自身を含まないので、Round 10のepisode distanceより1小さい。

| horizon | distinct roots | resolved / unresolved | waiting episodes total | fresh mass `Q` total | blocker rise / fall / equal | four inequality violations |
|---:|---:|---:|---:|---:|---:|---:|
| 200k | 90 | 85 / 5 | 387 | 56,716 | 19 / 361 / 0 | 0 / 0 / 0 / 0 |
| 2M | 559 | 551 / 8 | 785 | 595,291 | 20 / 754 / 0 | 0 / 0 / 0 / 0 |
| 20M | 860 | 851 / 9 | 7,390 | 20,006,912 | 31 / 7,341 / 0 | 0 / 0 / 0 / 0 |

四検査は順に `(end-start)=2q`、`Q>=episode count`、`Q<=E-r`、`2Q<=clock gap`。
20Mまで全て違反0。20Mで各sourceの最大hull density `Q/(E-r)`は82.64%、最大clock occupancy
`2Q/gap`は66.05%であり、どちらも1へ収束する兆候はない。

Round 10の653-distance witnessは待機652 episodesについて

```text
target=1355, r=18,953
sourceStart=10,201,024, escapeStart=18,394,609, clockGap=8,193,585
Q=2,319,435, E=10,212,662, E-r=10,193,709
Q/(E-r)=22.75%, 2Q/clockGap=56.62%
blocker min/max=48,956/10,053,079, rises/falls=0/651
```

だった。長い待ちは巨大な初期blocker slackを651回strict descentで消費しており、一様episode boundが
失敗する理由を直接説明する。一方、20Mの最長unresolved witnessはtarget 1355、root 3,377、
2,019 waiting episodes、`Q=5,489,539`、5 rises / 2,013 fallsだった。

### blocker-growth枝の早期no-go

blocker自身は単調ではない。20M distinct-root系列でriseを含むもの6、fallを含むもの17があり、
両方向が実在した。ただし31 riseはすべてその系列の新recordで、rise-not-recordは0だった。これは
既存right-record観測と整合するが、それを使ってもno-escapeなら「有限descentまたは新record riseを
無限反復」の二択になるだけで、eventual escapeは単独では出ない。

### Round 11判定

| candidate | empirical stability | proof usefulness | decision |
|---|---:|---:|---|
| strict fresh-mass potential `Q` | 100/100 | 82/100 | exact finite-prefix lemmaとして保持 |
| `Q<=E-r` and `2Q<=clock gap` | 100/100 | 78/100 | no-escapeをunbounded entry/timeへ縮約 |
| blocker monotonicity | 0/100 | 5/100 | rise/fallとも実在、棄却 |
| fresh-mass alone forces escape | 20/100 | 35/100 | hull density22.75%の653 witness。単独では弱い |
| fresh mass + right-record descent/record split | 94/100 | 88/100 | finite descent対unbounded recordsの統合候補 |

次のproof-facing形は「fixed `r`でno-escape episodesが無限なら、fresh mass/entryがunbounded。さらに
upward right-recordがあれば、blockerは有限descentを挟んでunbounded recordsを作る」である。
eventual `entry<r`を直接主張せず、既存のrecord contradiction枝へ接続するのが安全である。

## Round 12: record-gap / descent-payment decomposition

### exact local geometry

Round 11の`Q + right-record`結合が閉じるかを一回だけ監査した。連続するblocker-side intervalsを
`I_i=[b_i+1,e_i]`とする。fresh disjointnessとright-record観測から、実prefixでは各transitionが
次の二種類へ完全に分かれた。

- descent `b_i < b_{i-1}`: current intervalはprevious intervalの左にあり、
  `q_i=e_i-b_i <= b_{i-1}-b_i`。blocker descentがfresh massを支払う。
- record rise `b_{i-1}<b_i`: `b_i`は全prior blockerのrecordで、さらに
  `b_i >= E_{i-1}=max_{j<i}e_j`。new hull growthは
  `(b_i-E_{i-1}) + q_i`に分かれる。前項`g_i=b_i-E_{i-1}`をrecord gapと呼ぶ。

20M distinct-root first-use系列の7,390 transitionsは42 record rises / 7,348 descents / 0 equalで、
nonrecord rise 0、`b_i<E_{i-1}` record 0、`q_i>descent` 0だった。従ってこの局所分解自体は
強いLean候補である。ただし問題は`g_i`がfresh massでは全く支払われないことである。

### scalingと反例

| horizon | transitions | record / descent | cumulative gap / record fresh `Q` | descent drop / descent fresh `Q` | `gap > Q+r` sources | max `gap/(Q+r)` |
|---:|---:|---:|---:|---:|---:|---:|
| 200k | 387 | 24 / 363 | 112,160 / 4,226 | 243,590 / 52,490 | 3 | 1.986 |
| 2M | 785 | 28 / 757 | 2,272,869 / 53,822 | 2,311,070 / 541,469 | 6 | 8.746 |
| 20M | 7,390 | 42 / 7,348 | 63,702,115 / 1,084,732 | 84,008,226 / 18,922,180 | 9 | 13.724 |

20Mのweighted aggregateではrecord gapは同じrecord episodeのfresh massの58.73倍、descent dropは
descent fresh massの4.44倍だった。個別record riseのsharp witnessは

```text
target=1355, root=3377, sourceStart=1,032,996, riseStart=1,034,085
old entry hull=587,477
blocker=1,033,993, entry=1,035,215
gap=446,516, q=1,222, gap/q=365.40
```

である。source累積のsharp反例は

```text
target=1355, root=18,106, sourceStart=18,394,609
waiting transitions=58
Q=574,192, cumulative gap=8,128,442, cumulative record gain=8,288,025
gap/(Q+r)=13.724
```

だった。`gap <= Q+r`は9 source、`recordGain <= Q+r`は10 sourceで破れる。この反例を
`gap <= Q + C*r`で救うにも既に`C >= 417.22`が必要で、max ratioが
1.986→8.746→13.724とhorizonに伴い増加するため、fixed universal coefficientにも経験的根拠がない。
提案例`Q+O(root/target)`はさらに弱く、停止する。

### 最小残余と停止条件

`Q + right-record`からexactに得られるのは次までである。

```text
descent step: fresh mass is charged to finite blocker descent
record step: fresh mass q is charged, but value-space gap [E_old+1, b] is uncharged
```

従ってno-escape infinite sequenceを矛盾へ運ぶための最小残余は、record gap `g_i`をterminal comb外の
標準軌道資源へinject/chargeする補題である。候補資源はgap内の既出値、first-occurrence time edge、
またはrecord間のnon-comb clocksであり、`Q`、root、targetだけでは不足する。

停止条件を明確にする。`gap`を支払う新しいglobal invariantがない限り、fresh-mass potentialや
root係数の調整、uniform wait boundの探索は再開しない。局所分解は保持するが、現在の
`Q + right-record`枝単独でeventual escapeを主張しない。

### Round 12判定

| candidate | empirical stability | proof usefulness | decision |
|---|---:|---:|---|
| descent payment `q_i <= b_{i-1}-b_i` | 100/100 | 90/100 | exact local lemmaとして保持 |
| record rise lies right of old entry hull | 100/100 | 88/100 | gap定義を正当化。Lean候補 |
| cumulative gap `<= Q+O(r)` | 5/100 | 20/100 | ratio増加、具体反例。停止 |
| `Q + right-record` alone closes contradiction | 25/100 | 45/100 | uncharged record gapが残る |
| charge record gap to global non-comb history | 未検証 | 80/100 | 再開時に必要な唯一の新入力 |

## Round 13: record gapのglobal-history charge監査

### 方法

各targetのunique chronological terminal列でrecord riseを抽出し、直前までのentry hull `E`と新blocker
`b`の間のgap `[E+1,b]`を値単位で走査した。各値についてrecord start/endまでにvisitedか、first timeが
target epoch開始以前かtail内か、first branchがsubtraction/additionか、既存history-terminal combの
fresh intervalに属するかを記録した。またgap interval unionを取り、同一first-occurrence witnessが
複数gapへ課金されるmultiplicityを測った。

### horizon scaling

| horizon | unique record gaps | gap mass | visited by record | visited rate | unvisited | pre-tail / tail first | subtraction / addition first | gap overlaps / max witness reuse |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 200k | 13 | 54,907 | 10,566 | 19.24% | 44,341 | 41 / 10,525 | 5,643 / 4,923 | 0 / 1 |
| 2M | 16 | 1,480,271 | 281,350 | 19.01% | 1,198,921 | 82,190 / 199,160 | 142,265 / 139,085 | 0 / 1 |
| 20M | 20 | 17,820,564 | 3,045,301 | 17.09% | 14,775,263 | 82,206 / 2,963,095 | 1,705,980 / 1,339,321 | 0 / 1 |

全eventでvisited-by-startとvisited-by-endは同数で、record episode中にgap値が初出した例は0。
20M visited witnessesのうちpre-tailは2.70%、tailは97.30%。subtraction firstは56.02%、addition firstは
43.98%で、subtraction witnessでさえgap全体の9.57%しかない。さらに3,045,301 visited valuesのうち
history-terminal comb fresh interval由来は0で、全てその外側の標準軌道historyだった。

gap intervals自身は20件すべてdisjointで、geometric overlap 0、同じfirst-occurrence witnessの再利用も
最大1だった。従って「visited部分」には完全なdistinct chargeが存在する。しかしgap massの82.91%は
record時点で未訪問であり、全gapへ比例するhistory resourceではない。

最大の単一no-go witnessはRound 12と同じtarget 1355の最終recordである。

```text
record=18,400,336..18,514,944
gap=[10,212,663,18,341,104], mass=8,128,442
visited=1,289,390 (15.86%), unvisited=6,839,052 (84.14%)
pre-tail first=0, tail-before-record first=1,289,390
subtraction/addition=727,277/562,113
history-terminal-comb origin=0
```

### 最終判定と停止条件

| candidate | empirical stability | proof usefulness | decision |
|---|---:|---:|---|
| distinct charge for visited part of each gap | 100/100 | 72/100 | overlap0/reuse1。ただし部分課金 |
| pre-tail roots/history pay the gap | 5/100 | 10/100 | 20Mでvisited中2.70%、全gap中0.46%。棄却 |
| terminal fresh intervals pay the gap | 0/100 | 5/100 | origin 0/3,045,301。棄却 |
| all prior visited values pay gap mass proportionally | 15/100 | 20/100 | 82.91% unvisited、最大gap84.14%。棄却 |
| unvisited gap capacity as a new resource | 100/100 | 45/100 | distinctだがNaturals上で無限、単独矛盾なし |

global-history charge枝の最小残余は、record時点で未訪問のgap値を後の軌道が必ず消費する、または
unvisited gap massをclock/first-time capacityで有限に抑える新定理である。現データは逆に巨大な
unvisited gapを安定して許す。従ってその新しいglobal theoremなしには、この枝をここで停止する。

## Round 14: immediate macro-successor equality slack

same-target consecutive history-terminal edgeを20Mで2,655本抽出し、旧entry `e₁`、次blocker `b₂`、
次fresh mass `q=e₂-b₂`、`delta=|b₂-e₁|`を監査した。upward/right 20本、downward/left 2,635本で
`delta=0`は0件、interval-order違反も0だった。

| edge | count | delta min / p50 / p90 / p99 / max | next q p50 / p90 / max | high clocks p50 / p90 / max |
|---|---:|---:|---:|---:|
| all | 2,655 | 1 / 3,995 / 27,824 / 156,585 / 18,322,997 | 285 / 4,323 / 159,583 | 995 / 8,105 / 109,271 |
| upward/right | 20 | 1 / 15,967 / 10,033,967 / 18,322,997 / 18,322,997 | 193 / 57,304 / 159,583 | 268 / 9,966 / 17,960 |
| downward/left | 2,635 | 10 / 3,980 / 27,225 / 122,514 / 483,834 | 286 / 4,277 / 108,641 | 997 / 8,105 / 109,271 |

sharp near-equalityはtarget 4、`8→23` edgeで`e₁=12,b₂=13,e₂=18`、`delta=1,q=5`、
high clocks 6、exit excess `e₂-target=14`、low deficit 10。従って単純候補
`delta≥q`、`delta≥highClocks`、`delta≥lowDeficit`はこの小prefixで全て反例となる。
parity単独も`38→77` edgeの`delta=24`で反例。相関もupwardではdelta対exit excessがほぼ1だが、
clock相関0.60、mass相関0.72に留まり、因果的不等式ではない。

一つだけ生き残ったsharp hybridは

```text
delta is odd  OR  q <= delta
```

である。軌道parityから
`delta % 2 = (upperTri s₁ + upperTri s₂ + q) % 2`が得られるため、左枝はclock congruenceで
equalityを排除する。偶数compatible枝では`q≤delta`がstrict positivityを与える。20Mでは
odd 1,336本、evenかつ`q≤delta` 1,319本、違反0。downward 2,635本の後者はinterval orderから既に
導ける。未知なのはupwardの偶数compatible 4本だけで、全て`q≤delta`だった。

upwardをnext start 2,000で分けると、train 7本はodd 4 / compatible 3、holdout 13本はodd 12 /
compatible 1でhybrid違反はいずれも0。ただしholdout compatibleが1本しかなく、証拠量は弱い。

| candidate | empirical stability | proof usefulness | decision |
|---|---:|---:|---|
| immediate successor `b₂≠e₁` | 100/100 | 55/100 | 0/2,655、sharp slack 1 |
| raw mass/clock/deficit lower bound | 0/100 | 5/100 | target-4小反例で棄却 |
| parity alone | 80/100 | 45/100 | upward 16/20のみ |
| parity-or-mass hybrid | 100/100 | 68/100 | 全2,655、holdout通過。ただし新核心はupward4本 |

Lean化するなら全体を再証明するのではなく、既存interval orderでdownwardを除き、upwardかつ
parity-compatibleなsuccessorに限定して`q≤b₂-e₁`を狙うのが最小残余である。

## Round 15: canonical upward provenanceとlocal no-go

upward terminal resetの生成履歴を専用`target_upward_provenance_probe.cpp`で監査した。各resetについて、
次blockerのfirst occurrence branch、そのforced-addition candidate、target epoch開始までのancestry root、
過去terminal fresh intervalとの所属関係を同時に追跡した。

| horizon | upward | terminal record | blocker origin add/sub | birth after previous terminal | birth-candidate max reuse | candidate in terminal fresh interval | ancestry max path / root reuse |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 20M | 20 | 20 | 20 / 0 | 0 | 1 | 0 | 54,288 / 8 |
| 200M | 24 | 24 | 24 / 0 | 0 | 1 | 0 | 667,802 / 8 |
| 1B | 27 | 27 | 27 / 0 | 0 | 1 | 0 | 1,021,294 / 8 |
| 2B | 28 | 28 | 28 / 0 | 0 | 1 | 0 | 1,064,446 / 8 |

2Bの28 resetでは、blocker初出がtarget epoch以前なのは2件、epoch内が26件だった。forced-additionを止めた
birth candidateもpre-epoch 9、epoch内19で、finite initial reservoirには閉じない。candidateは25件が過去entry
hull内、3件がその外にあるが、実際のterminal fresh intervalに属するものは0件だった。15件は過去terminal
blockerそのものだが、残り13件はcomb外historyである。従って「各upward resetをdistinct terminal fresh
certificateへ課金する」枝は0/28で失敗する。candidate自体の再利用1は安定しているが、epoch内で新candidateを
無限に生成できる可能性を排除せず、単独capacityにはならない。

さらに、このorigin則はactual step legalityやtarget gatingの局所帰結でもない。signed-walkから得たfinite
history seed

```text
seen={0,1,2,3,6,9,10,15,19,29,40}, current=40, nextClock=12
```

から実`Basic.step`を続けると、target 5の連続terminal episode

```text
previous: clocks [221,223], interval [17,17], blocker 16
next:     clocks [228,232], interval [231,232], blocker 230
```

を得る。`230`はprior terminal hull 125を越すglobal record resetだが、first occurrenceはclock 96のlegal
subtraction `326-96=230`である。従って「upward recordならaddition-origin」はarbitrary seeded actual orbitで偽。
標準prefixの28/28則を証明するには`initial=⟨0,[0]⟩`からのcanonical reachabilityを本質的に使う必要がある。

### Round 15判定

| candidate | empirical stability | proof usefulness | decision |
|---|---:|---:|---|
| standard upward reset is a terminal right record | 28/28 through 2B | 40/100 | 診断則として保持 |
| standard upward blocker has addition origin | 28/28 through 2B | 25/100 | seeded record反例。canonical theoremのみ |
| distinct birth candidate pays each reset | max reuse 1 through 2B | 15/100 | epoch内19/28、無限供給を止めない |
| terminal fresh certificate pays reset | 0/28 | 0/100 | 完全停止 |
| local macro/history legality closes right ladder | false | 0/100 | seeded record-subtraction反例 |

結論として、期待した「terminal fresh certificateの消費」は成立しなかった。残るgateはcanonical prefixの
reachabilityが、tail内で生成されるcomb外candidate reservoirを有限化またはsemantic progressへ変換するという
大域命題である。これは現行macro APIの補題追加では得られず、直接有望度を30/100から20/100へ下げる。

## Round 16: terminal-anchor returnとfuture gap consumption

pre-tail rootだけでなく、各terminal blocker自身をhistorical anchorとして、同一targetの後続terminal entryが
anchor未満へ初めて戻る時点を監査した。

| horizon | anchors | resolved | unresolved | no later terminal | max wait |
|---:|---:|---:|---:|---:|---:|
| 20M | 2,660 | 2,642 | 18 | 5 | 653 |
| 200M | 7,922 | 7,904 | 18 | 5 | 3,892 |
| 2B | 21,510 | 21,495 | 15 | 5 | 20,097 |

separator違反は0。一般waitは増えるためuniform boundはない。upward resetだけでは20M/200M/2Bで
`18/20`, `22/24`, `26/28`がreturnし、全resolved resetのwaitは1 episodeだった。未解決2件はtarget 4の
`(start,anchor)=(23,13),(38,25)`で、後続entryがanchor未満へ戻る前にtarget 4が実際に出現してepochが終わる。
従ってproof-facing候補は`target occurs ∨ later entry < reset blocker`である。ただしstandard finite mex epochは
permanent-missing tailの直接観測ではなく、経験則としてのみ保持する。

record gapについてはevent集合をhorizonごとに入れ替えず、古いcohortを固定してfuture consumptionを測った。
200k cohortでrecord時未訪問だった44,341値は2Mまでに43,881、20Mまでに44,290が初出した。
2M cohortの1,198,921値も20Mまでに1,103,735が初出した。old gapは時間とともに強く消費されるが、
任意固定gap値のeventual occurrenceは全射性の再符号化になりやすく、terminal comb外のfirst occurrenceも多い。
このためqueue/backlog診断として保持し、証明仮定にはしない。

並列proof監査の結果、仮想missing tailは`TargetTailResidualKernel`によりeventual-high corridorまたは
fixed-root unbounded right-terminal streamへLeanでexactに二分された。finite-root枝の直接有望度は30/100、
唯一の新数学候補であるreset repaymentは40/100、canonical separatorは決定的一意性の言い換えとして5/100とする。

## Reproduction

```bash
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/target_right_record_probe.cpp \
  -o /tmp/target_right_record_probe
/tmp/target_right_record_probe 20000000 50000000 100000000 \
  250000000 500000000 1000000000 2000000000

c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/seeded_right_record_search.cpp \
  -o /tmp/seeded_right_record_search
/tmp/seeded_right_record_search 14 32 300
/tmp/seeded_right_record_search --walk-any 12 400
/tmp/seeded_right_record_search --return-grid 14 32 15000
/tmp/seeded_right_record_search --return-walks \
  100000 200 20000 20260831 1000000000

/tmp/seeded_right_record_search --return-seed 13 7 4000000000 \
  0 1 6 8 13 1111 2024 6424 11955 20908 36687 66572 \
  209840 373139 1195679 3501447 5708532 10370243 18472704 \
  31581811 55703080 304835271 517297632

c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/target_ancestry_capacity_probe.cpp \
  -o /tmp/target_ancestry_capacity_probe
/tmp/target_ancestry_capacity_probe 2000000
/tmp/target_ancestry_capacity_probe 20000000

# Round 7 fixed-anchor / pre-tail maximum scaling audit
/tmp/target_ancestry_capacity_probe 200000
/tmp/target_ancestry_capacity_probe 2000000
/usr/bin/time -l /tmp/target_ancestry_capacity_probe 20000000

# Round 10 finite-basin remount is emitted by the same ancestry probe.
# Round 11 fixed-root fresh-mass potential is emitted by the same probe.
# Round 12 record-gap/descent-payment audit is emitted by the same probe.
# Round 13 record-gap global-history audit is emitted by the same probe.

c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/target_high_candidate_probe.cpp \
  -o /tmp/target_high_candidate_probe
/tmp/target_high_candidate_probe 200000
/tmp/target_high_candidate_probe 2000000
/usr/bin/time -l /tmp/target_high_candidate_probe 20000000

c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/target_comb_extraction_probe.cpp \
  -o /tmp/target_comb_extraction_probe
/tmp/target_comb_extraction_probe 200000
/tmp/target_comb_extraction_probe 2000000
/usr/bin/time -l /tmp/target_comb_extraction_probe 20000000

c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/target_successor_slack_probe.cpp \
  -o /tmp/target_successor_slack_probe
/tmp/target_successor_slack_probe 20000000 2000

c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/target_upward_provenance_probe.cpp \
  -o /tmp/target_upward_provenance_probe
/tmp/target_upward_provenance_probe 20000000
/tmp/target_upward_provenance_probe 2000000000

# Seeded actual-orbit no-go for the local upward-origin law.
/tmp/seeded_right_record_search --walk-record-sub 12 250

/tmp/target_right_record_probe 2000000000 4000000000
```

この計算はLean証明の仮定ではなく、次に形式化する命題を選ぶための監査である。
2B right-record passの実測は約17.5秒、maximum resident set size約3.57GBだった。
orbit-envelope replay込みでは約22.3秒、約5.18GBである。
