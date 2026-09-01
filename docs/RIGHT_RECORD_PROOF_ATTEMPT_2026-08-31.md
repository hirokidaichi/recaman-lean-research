# Global upward right-record: proof attempt, round 1

最終更新: 2026-08-31

## 結論

`HistoryTerminatedComb`を時刻順に並べただけのglobal upward right-recordは、
**実際のRecamán軌道上ですでに偽**である。従って現在の予想は、固定targetに対する
H→L entryから始まる最大combを漏れなく並べたmacro列に限定しなければならない。

限定後の予想は20Mまで生きているが、既存Lean interfaceには「固定target」「H→L entry」
「隣接する最大macro episode」という情報が入っていない。`PositiveTerminalBlockerOrigin`だけを
追加しても証明できない。次に必要なのは、comb間のhigh-candidate区間を支配する
barrier/no-gap-return補題である。

この結果から、無修飾予想の有望度は0、target限定予想の有望度は55から35程度へ下げる。
反例がまだないという計算的価値は残るが、現行補題からの短い証明は期待しにくい。

## 1. 無修飾予想の実軌道反例

`k = 0`では`FreshCombEpisode s 0`のrun部分は空であり、次が成り立てば
`HistoryTerminatedComb s 0 b`になる。

- `a s = b + 1`がfirst occurrence
- clock `s+1`がforced addition
- `b`は時刻`s`までに出現済み

実軌道には次の3本がある。

| role | `s` | `k` | blocker `b` | fresh interval | blocker first time |
|---|---:|---:|---:|---:|---:|
| old right interval | 187 | 0 | 265 | `[266,266]` | 101 |
| immediate previous | 222 | 0 | 46 | `[47,47]` | 32 |
| new local rise | 285 | 0 | 228 | `[229,229]` | 75 |

直接計算では次の遷移である。

```text
clock 187: 453 - 187 = 266  (legal, first occurrence)
clock 188: from 266, subtraction is blocked; forced addition

clock 222: 269 - 222 = 47   (legal, first occurrence)
clock 223: from 47, subtraction is nonpositive; forced addition

clock 285: 514 - 285 = 229  (legal, first occurrence)
clock 286: from 229, subtraction is nonpositive; forced addition
```

また`265,46,228`のfirst occurrenceはそれぞれ`101,32,75`である。
従って

```text
46 < 228
```

という局所upward resetが起きる一方、さらに古いfresh intervalの上端は

```text
266 > 228
```

である。これはglobal right-recordに反する。

この反例の時刻187ではmex targetは19だが、次候補は

```text
266 - 188 = 78 >= 19
```

なのでtarget-relative low entryではない。対して、probeが数えるmacro combは固定targetに対し
entry直後の候補がtarget未満になるH→L episodeだけである。従って20Mの`20/20`と反例は
矛盾しない。

## 2. 正確に作り直すべき予想

まずtarget-gated episodeを定義する必要がある。

```lean
structure TargetHistoryTerminatedComb
    (target tailStart s k blocker : Nat) : Prop where
  comb : HistoryTerminatedComb s k blocker
  tail_le : tailStart <= s
  entry_above : target < a s
  entry_low : nextSubtractionCandidate s < target
```

共通の`MissingPermanentAboveTail target tailStart`は外から仮定する。
ただしこれだけでは同じ最大combのsuffixを複数選べる。global列にはさらに、

```text
TargetMacroSuccessor previous next
```

として次が必要である。

1. previousのfinal landingよりnext entryが後
2. 両者の間に別のtarget-gated maximal episodeがない
3. H→Lで始まるmaximal episodeであり、suffixの任意選択ではない

この列に対する予想は次である。

```text
TargetMacroSuccessor I_i I_(i+1)
and b_i < b_(i+1)
implies
for every j <= i, upper(I_j) <= b_(i+1).
```

## 3. 区間順序から得られる正確な縮約

既証明の`HistoryTerminatedComb.fresh_intervals_ordered`により、任意の古い区間`I_j`と
新区間`I_new`は

```text
upper(I_new) < b_j
or
upper(I_j) <= b_new
```

のどちらかである。新区間は`b_new+1`以上なので、古いblockerについて
`b_j <= b_new`が分かれば第一分岐は不可能になり、`upper(I_j) <= b_new`が出る。

従ってglobal right-recordの本体は区間packingではなく、blocker列の次のpattern avoidanceである。

```text
b_i < b_(i+1)  ->  max { b_j | j <= i } < b_(i+1)
```

すなわちblocker列は、running record未満に落ちた後は厳密降下を続け、上昇するときは
過去recordを一度に越える。禁止される最小patternは

```text
high, low, middle
```

である。abstract interval反例`[101,110], [11,20], [31,40]`はまさにこのpatternを持つ。

## 4. provenance splitで届く所と届かない所

20Mの20 upward resetsでは新blockerのfirst transitionはすべてforced additionで、

```text
b_new = predecessor + firstTime
predecessor < b_new
```

である。19件ではpredecessorはprior fresh intervalの外にあり、18件ではprior upper hullより
上にある。後者なら`priorUpper <= predecessor < b_new`でright-recordは直ちに出る。

残る2件は次である。

```text
target 4: b_new=13, firstTime=6,  predecessor=7, priorUpper=12
target 4: b_new=25, firstTime=17, predecessor=8, priorUpper=18
```

ここではaddition量`firstTime`が不足分を越える。しかし
`PositiveTerminalBlockerOrigin.forced_addition`が与えるのは
`predecessor < b_new`とfirst-time降下だけであり、

```text
priorUpper - predecessor <= firstTime
```

を与えない。従ってorigin split単独からright-recordは証明できない。

またsubtraction-originの場合はpredecessorが新entryより上になる既存補題があるが、
そのpredecessorがprior target hullに属するとは限らない。high-value reservoirが外部にあるため、
subtraction-origin排除も現行interfaceだけからは出ない。

## 5. 次の補題候補

最も情報量のある次候補は、target macro間のhigh-candidate区間を明示する
`no_gap_return`である。

概念形は次である。

```text
fixed missing target m,
old target interval lies above historical b,
a later target interval lies below b,
b+1 is still fresh
-------------------------------------------------
the next target-macro interval cannot terminate at b
```

これが証明できれば、古いright intervalから下へ落ちた後にmiddle blocker `b`へ戻る
`high, low, middle` patternを排除できる。

証明にはcomb内部だけでなく、二つのcombの間の候補

```text
c_n = a n - (n+1)
```

のH→H遷移を記録する必要がある。現行`HistoryTerminatedComb`はこの区間を完全に捨てている。
従って次のLean作業は、いきなりglobal theoremを書くことではなく、

1. `TargetHistoryTerminatedComb`
2. maximal H→L entry
3. `TargetMacroSuccessor`（中間H区間を含む）
4. historical separator `b`とfresh successor `b+1`のbarrier lemma

の順になる。

## 6. Lean化可能性

| item | possibility | note |
|---|---:|---|
| k=0の実軌道反例 | high | 既存trace certificateまたは小さい決定計算で閉じられる |
| target-gated structure | high | 既存定義の薄いwrapper |
| blocker patternへの縮約 | high | `fresh_intervals_ordered`と`omega`で短い |
| upwardはaddition-origin | low-medium | 20/20だが、外部reservoirを排除する補題がない |
| `no_gap_return` barrier | low-medium | comb間H→H traceを新規に保持する必要がある |
| global right-record本体 | low until barrier | barrierが通れば有限帰納で可能 |

## 7. 判定

- 停止: 無修飾`HistoryTerminatedComb`のglobal right-record
- 保持: 固定targetのmaximal macro列に限定した経験則
- 次の一手: high-candidate bridgeを計測し、`high, low, middle`を排除しうるseparator量が
  実際に単調かを先に検査する

紙上では現時点で証明ではなく、**正しい定理文への修正と、必要な新interfaceの同定**まで進んだ。

---

## Round 2: target限定版の最小interfaceと局所反例

### 8. 最小のtarget-macro構造

probeが数えているepisodeを`HistoryTerminatedComb`から正確に切り出すには、少なくとも
次の情報が要る。

```lean
structure TargetMacroComb
    (target tailStart s k blocker : Nat) : Prop where
  comb : HistoryTerminatedComb s k blocker
  tail_le : tailStart <= s
  entry_positive_time : 0 < s
  entry_subtraction : CanSubtract s (stateAt (s - 1))
  entry_above : target < a s
  entry_low : nextSubtractionCandidate s < target
  left_maximal : s < 2 ∨ ¬ CombStep (s - 2)
```

`entry_subtraction + entry_above`はentry直前の候補がhighであることを表し、`entry_low`は
着地直後がlowであることを表す。`left_maximal`がないと、同じcombの後続low railを別の
episodeとして選べる。右側のmaximalityは`HistoryTerminatedComb.final_forced`と
`repayment_forced`がすでに与える。

共通仮定は

```lean
MissingPermanentAboveTail target tailStart
```

である。隣接性には、前episodeのfinal low timeを`e = s + 2*k`として、少なくとも

```lean
structure TargetMacroSuccessor (old new : TargetMacroComb ...) : Prop where
  separated : old.e + 2 < new.s
  bridge_high : ∀ n, old.e + 2 <= n -> n < new.s ->
    target < nextSubtractionCandidate n
```

が必要になる。`old.e+2`はterminal blockerをcandidateとして二度目のadditionが強制された
直後である。そこからnew entry直前まではcandidate-highであり、new entryのsubtractionで
初めてcandidate-lowへ落ちる。

### 9. counterexample 265→46→228を除く一般補題

target-low entryは値を斜めのcone内に置く。

```text
nextSubtractionCandidate s < target
implies
a s < s + 1 + target.
```

これは`a s <= s+1`なら自明で、そうでなければNat subtractionを戻して`omega`で出る。
`k=0`かつ`a s=b+1`なら

```text
b < s + target.
```

反対に`target < nextSubtractionCandidate s`なら

```text
s + target <= b.
```

時刻187のepisodeでは`target=19, b=265`で

```text
187 + 19 = 206 <= 265
```

であり、target-entry coneの外側にある。したがってこれは一般補題

```lean
theorem TargetMacroComb.entry_below_diagonal :
  a s < s + 1 + target
```

だけで機械的に除外できる。

しかしこのconeはright-recordを証明しない。次のseeded反例は全macro intervalがcone内にある。

### 10. fixed-target・maximal・same-targetでも有限局所法則は不足

任意の有限history state

```text
seen = {0,1,6,8,13}
current = 13
next clock = 7
```

から同じRecamán更新則を再開する。clock 11で`2`を訪れてmexは4になり、clock 12以後
少なくとも反例完成のclock 60までは値が4より上、4は未訪問である。この固定target 4に
対して、H→Lから始まるleft/right maximal macro列は次になる。

| start | finish | fresh interval | blocker | blocker origin |
|---:|---:|---:|---:|---|
| 16 | 20 | `[9,10]` | 8 | seed |
| 23 | 31 | `[21,24]` | 20 | add@7 from 13 |
| 37 | 39 | `[7,7]` | 6 | seed |
| 54 | 60 | `[15,17]` | 14 | add@12 from 2 |

最後のedgeは

```text
6 < 14
```

というupward resetだが、prior upperは24なので

```text
14 < 24
```

となりgap insertionである。新blocker 14はforced-addition originで、first time 12は
直前macro start 37より前にある。各entryも

```text
24 < 23+1+4
7  < 37+1+4
17 < 54+1+4
```

とtarget-entry coneを満たす。検出器はactive episode中のH→L suffixを再開始しないため、
これらはprobeと同じmaximality/successor規約である。

従って次の有限局所仮定を全部置いてもright-recordは導けない。

1. fixed least-missing target
2. targetより上のtail（反例完成時点まで）
3. H→L maximal entry
4. same-target high bridge
5. new blockerのforced-addition origin
6. blocker first timeがprevious macroより前

このseedは標準初期値`a 0=0`からの実prefixとは限らない。またdeterministic continuationでは
target 4をclock 1107で訪れる。従ってこれは`MissingPermanentAboveTail`を含む無限仮定への
反例ではない。一方、**現行の局所comb法則だけからの証明が不可能**で、標準prefix provenance
または永久欠落を本質的に使わなければならないことは示す。

### 11. side-wordによるright-recordの正確な分解

固定した将来terminal blocker `b`に対し、各target macro intervalを

```text
L : interval upper <= b
R : b <= interval blocker
```

で分類する。`b`のfirst timeより後のintervalはfreshnessにより必ずLかRである。

1B監査では一般terminal blockerにpost-first `R-L-R`が8,948件ある一方、upward terminal
27件はすべて

```text
post-first switches = 1
post-first RLR = 0
pre-first R = 0
```

だった。upward edgeではprevious intervalがL、current intervalがRなので、post-firstの
switchが高々1なら、それ以前にRはない。pre-first Rもなく、first timeを跨ぐintervalについては
addition-originならそのaddition high railがentry upperを越えるためLになる。
従って全prior intervalがLとなりglobal right-recordが出る。

この縮約のLean部分は容易である。しかし核心の

```text
upward terminal b  ->  target macro side word relative to b has no RLR
```

はright-recordのpattern-avoidanceをほぼそのまま言い換えたbarrierであり、seeded反例では実際に

```text
[21,24] : R
[7,7]   : L
[15,17] : R
```

となる。

### 12. 更新した研究判断

- 一般`HistoryTerminatedComb`版: 反例により停止
- finite/local target-macro版: seeded反例により停止
- 標準prefixまたは`MissingPermanentAboveTail`を本質使用する版: 未反証だが有望度25/100
- 次の非同値な候補: `RLR witness -> target eventually occurs`

seeded反例でもtarget 4はclock 1107で実際に出現する。従ってbarrierを「RLRは不可能」と
局所的に言うのではなく、

```text
target-macro RLRがあれば、有限将来にtarget landingを構成できる
```

というdischarge lemmaに変える余地がある。これなら`MissingPermanentAboveTail`と組み合わせて
right-recordを導け、seeded有限反例とも矛盾しない。ただしclock 60のRLRからclock 1107のtarget
まで長いので、短いcomb bridgeだけで閉じる見込みは低い。

---

## Round 3: RLRからtarget returnを抽出できるか

### 13. RLR witnessの正確な形

gap-insertion型upward resetを直接表すには、固定targetのmacro列から次を取ればよい。

```lean
structure TargetMacroRLRWitness (target tailStart b : Nat) : Prop where
  oldRight previous current : TargetMacroComb target tailStart ...
  old_before_previous : oldRight.finish < previous.start
  previous_successor_current : TargetMacroSuccessor previous current
  current_blocker : current.blocker = b
  old_on_right : b <= oldRight.blocker
  previous_on_left : previous.entry <= b
  local_rise : previous.blocker < b
```

`old_on_right`はold interval全体が`b`の右、`previous_on_left`はprevious interval全体が
`b`の左にあることをいう。current intervalは定義上`[b+1,current.entry]`なので右にある。
従ってside wordは`R-L-R`となる。oldとpreviousの間には他のmacroを許してよいが、
currentはpreviousの直後でなければならない。

将来discharge候補は、永久欠落を仮定せず次の形で置く。

```lean
conjecture TargetMacroRLRWitness.eventually_target :
  ∃ time, current.finish < time ∧ a time = target
```

`MissingPermanentAboveTail`と同時に仮定してしまうと結論を最初から否定しているため、
有限prefix上のRLRから将来landingを構成し、最後に永久欠落と矛盾させる順序が必要である。

### 14. seeded witnessのclock 1107 returnはexact gate

seeded RLRはclock 60で完成するが、target 4が現れるのはclock 1107である。最後の4 stepは

```text
clock 1104: a_1104 = 1112
clock 1105: candidate = 1112 - 1105 = 7  (seen, so forced addition)
            a_1105 = 2217 = 2*1105 + 4 + 3
clock 1106: 2217 - 1106 = 1111          (fresh subtraction)
clock 1107: 1111 - 1107 = 4             (fresh subtraction)
```

これは既存`exactGate_sufficient`そのものである。`u=1105, m=4`とすると

```text
gateIntermediate u m = u + m + 2 = 1111.
```

さらにforced additionを起こした候補7は

```text
target + 3 = 7
```

であり、RLRのleft episode `[7,7]`がclock 37でfirst occurrenceを作っていた。
従ってこの具体例の因果鎖は

```text
left macro consumes target+3
  -> candidate target+3 returns at clock u
  -> historical block forces exact-gate height
  -> fresh intermediate and fresh target give two subtractions
  -> target landing
```

である。

この3-step末端を一般化した補題はLean化しやすい。

```lean
theorem blocked_target_add_three_gate
    (hmpos : 0 < m)
    (hcandidate : a (u-1) - u = m+3)
    (hseen : m+3 ∈ valuesThrough (u-1))
    (hintermediate : u+m+2 ∉ valuesThrough u)
    (htargetFresh : m ∉ valuesThrough (u+1)) :
    a (u+2) = m
```

まず`hcandidate+hseen`からclock `u`のsubtractionがforcedであることを示す。
そのaddition後の値が`2*u+m+3`になるので、残りは`exactGate_sufficient`へ渡せる。

### 15. RLRだけではgate certificateを供給しない

上の因果鎖にはRLRから導けない条件が3つある。

1. left intervalが`target+3`を含むこと
2. 候補`target+3`が将来もう一度現れること
3. そのreturn時の`gateIntermediate u target`がfreshであること

一般のRLRではleft intervalはtargetより上の任意の区間であり、`target+3`を含まない。
seeded例でもcandidate 7のpost-first returnはclock 1105が最初で、RLR完成から1,045 clocks以上
離れている。candidate-high bridgeのfirst-passage法則は、このreturnの存在を与えない。

またRLRが保持していたfresh separator `b+1`はcurrent intervalの最終low landingで必ず消費される。
seeded例では`b=14`に対して`15`がclock 58で着地済みである。従ってRLR完成後には
`b+1` freshnessという未払いtokenは残らず、それを将来targetまで運ぶpotentialは作れない。

実際、clock 60以後にもblocker 14に対するside wordは再びR-L-Rを作れる。separator消費後は
同じcutを横切ることに矛盾がない。

### 16. 同じRLR prefixからtarget returnを任意に遅らせられる

任意seed stateの設定では、初期seenへ将来のgate intermediate `1111`を追加してもclock 60までの
軌道とRLR witnessは全く変わらない。この一個の追加だけでclock 1107のgateは失敗し、target returnは
clock 2020へ遅れる。

さらに、その時点でtargetへの最終subtraction元になる値をあらかじめseenへ追加する操作を繰り返すと、
同じclock-60 RLR prefixを保ったままreturn時刻は次のように延びた。

```text
1107, 2020, 6420, 11951, 20904, 36683, 66568,
209836, 373135, 1195675, 3501443, 5708528,
10370239, 18472700, 31581807, ...
```

各例のinitial seenは有限だが、clock 6までの標準Recamán prefixとしては不可能な巨大値を含む。
従ってeventual return自体の反例ではない。しかし、RLR tripleの時刻・区間・blockerだけに依存する
有限boundやfinite certificateは存在しない。`seen = valuesThrough clock`という標準prefix provenance、
少なくとも全seen値のorigin/upper boundが不可欠である。

### 17. target 4 returnまでのmacro情報

RLR完成後、target landingまでにさらに24本のhistory-terminated target macroがある。
blocker列は概略

```text
14,
51,24,84,28,199,168,140,115,74,61,41,31,10,
334,265,195,150,77,17,598,440,200,117,45,
target landing
```

となる。複数のrecord expansionと長い下降runを経ており、RLR直後の一つのhigh bridgeから
targetへ直結するfirst-passage certificateはない。

### 18. Round 3判定

- `RLR -> eventually target`: 標準軌道上では未反証だが、有望度15/100
- `RLR -> bounded-time target`: arbitrary-state familyにより棄却
- `RLR -> barrier b+1を将来まで保持`: current intervalが即消費するため棄却
- `target+3 return + fresh gate intermediate -> target`: exactでLean化可能、ただしRLRからは導けない

従ってright-recordを救うためにRLR dischargeへ進むより、既存のgate/debt recursionで
`target+3` candidate returnまたはgate-intermediate obstructionを直接扱う方が情報損失が少ない。

---

## Round 4: orbit running maximum監査と枝の終了

### 19. upward blocker birthはorbit recordではない

2Bのupward terminal blocker 28件について、そのfirst occurrence直前の全軌道running maximumを
監査した。

| birth property | count |
|---|---:|
| orbit running record | 6 / 28 |
| non-record | 22 / 28 |

最初の反例はtarget 19のupward blocker 458である。

```text
firstTime(458) = 172
origin predecessor = 286
286 + 172 = 458

a 117 = 495 > 458
```

従ってforced-addition originでもrunning record生成は保証されない。2Bではbirth時の最大deficitは
約8.93e8であり、さらに全28件でbirth後terminal使用前にblockerを越える軌道値が再び現れた。

addition birth `b=p+f`がorbit recordになるための正確な条件は単に

```text
max_{t<f} a(t) < p+f,
```

すなわちprior maximumが`p`より上なら

```text
max_{t<f} a(t) - p < f
```

である。Recamán addition rule自体はこの差を制御しない。

既存の`crossingTime_not_record`系定理は「指定されたreplay crossingはearlier valueに支配される」
ことをいう。22/28のbirthは最初からnon-recordなので完全に両立し、矛盾を与えない。残り6件だけを
record exclusionで落としてもuniformなupward-terminal処理にはならず、blocker birth timeを
replay crossingへ同定するinterfaceもない。従ってorbit-max方向は停止する。

### 20. target-relative birth recordの半分だけは説明できる

orbit recordは偽だが、2Bの28件では全てorigin predecessor `p`がtargetより上にあった。
この条件は、birth以前に開始したtarget macro intervalを抑えるには十分である。

target macro entry `(s,e)`にはentry cone

```text
e < s + 1 + target
```

がある。`s < f`かつ`target <= p`なら

```text
e < s+1+target <= f+target <= f+p = b.
```

従ってbirth前完了intervalとbirthを跨ぐintervalは全て`b`の左にある。これは2Bの

```text
birth violations = 0
straddle violations = 0
```

を一つの短い算術補題で説明する可能性がある。

しかしbirth後のintervalが`b`を越えないことは出ない。Round 2のseeded反例は
`b=14, f=12, p=2<target 4`なのでこの十分条件から外れるが、条件を満たすactual caseでも
post-birth no-crossingは独立に必要である。従ってtarget-hull recordを全体として追う枝も終了する。

### 21. right-recordを捨てて残す最小provenance補題

gate/debt recursionへ直接戻すため、次のtail splitだけを残す。

```lean
theorem MissingPermanentAboveTail.additionOrigin_predecessor_or_preTail
    (h : MissingPermanentAboveTail target start)
    (hf : 0 < firstTime)
    (hadd : blocker = a (firstTime-1) + firstTime) :
    firstTime <= start ∨ target < a (firstTime-1)
```

証明は`firstTime <= start`で場合分けするだけである。反対側では
`start <= firstTime-1`なので`h.strictly_above`を使う。

この補題はright-recordを経由せず、forced-addition provenanceを二つに振り分ける。

1. `firstTime <= start`: blocker birthを有限pre-tail prefixへ戻す
2. `target < predecessor`: predecessorのfirst occurrenceを取り、
   `EarlierSmaller`かつtarget下界を保つ正規debt childにする

後者は`PositiveTerminalBlockerOrigin.earlierSmaller_or_lift`に不足していたtarget下界を直接補う。
全域性への次の実作業は、right-recordではなく、このsplitを既存gate/debt recursionへ接続し、
pre-tail birthだけをfinite-history budgetへ課金することである。

### 22. 枝Aの最終判定

- orbit running-record birth: **偽、停止**
- target-relative global right-record: 2Bでは28/28だが、局所/seeded反例とpost-birth no-goにより停止
- RLR eventual discharge: main theorem級で、有限certificateなし。停止
- 保存する成果:
  - ungated実軌道反例
  - target-entry cone
  - fixed-target seeded反例
  - exact `target+3` blocked gate
  - addition-originのpre-tail / above-target predecessor split

枝Aとしてはright-recordを主証明路線から外し、標準prefix provenanceを保持するgate/debt recursionへ
戻すのが妥当である。

---

## Round 5: time-only above-target ancestry

### 23. subtraction/addition originの統一

値下降を要求しなければ、tail内のfirst-occurrence provenanceは二originで完全に統一できる。
above-target value `v`がtime `f`にfirst occurrenceを持つとする。

- legal subtraction origin: predecessor `p`は`v+f`なので`target < v < p`
- forced addition origin: `f`がtail後ならpredecessor時刻`f-1`もtail内なので`target < p`
- forced addition originかつ`f <= tailStart`: finite pre-tail root

どちらの非root枝でもpredecessorのfirst time `fp`は

```text
fp < f
```

である。従って次のgeneric lemmaが成り立つ。

```lean
theorem FirstAt.preTail_or_aboveTarget_parent
    (htail : MissingPermanentAboveTail target tailStart)
    (htarget : target < value)
    (hfirst : FirstAt a value firstTime) :
    firstTime <= tailStart ∨
      ∃ parent parentFirstTime,
        target < parent ∧
        FirstAt a parent parentFirstTime ∧
        parentFirstTime < firstTime
```

これはterminal blockerに限らない。任意のabove-target first occurrenceへ反復でき、timeの
well-founded inductionにより

```lean
theorem FirstAt.exists_preTail_aboveTarget_ancestor ... :
  ∃ root rootFirstTime,
    target < root ∧ FirstAt a root rootFirstTime ∧
    rootFirstTime <= tailStart
```

を得る。両定理は独立ファイル
`Recaman/TargetCombTimeAncestry.lean`に実装し、`lake env lean`を通した。

### 24. 既存定理との差

`PositiveTerminalBlockerOrigin.preTail_or_targetEarlierSmaller_or_lift`はterminal combの
originを三分岐し、additionでは`EarlierSmaller`、subtractionではvalue liftを保持する。
新lemmaはentry/terminal情報を捨て、両者から共通部分

```text
target < parentValue
parentFirstTime < childFirstTime
```

だけを抽出する。

`debt_legalSubtraction_earlierPredecessor`は既にdebt-local time dropを与えるが、subtraction parentは
childより大きいため固定`anchorParent`を越えうる。そのため`DebtInvariant.value_lt_anchor`を保存できず、
`debt_legalSubtraction_preservesInvariant`には別途`parent < anchor`が必要だった。

time-only版はanchor上界を捨てた弱いdebt invariant

```text
target < value
FirstAt a value firstTime
firstTime < horizon
```

なら常に保存し、`phaseSearch_debtTimeDrop`を毎回使える。しかしpre-tail rootでnormal phaseへ戻すには
`phaseSearch_exitDebt_of_anchorDrop`が要求するanchor下降がなく、rankのphase成分はdebtからnormalへ
逆向きに増える。従って既存gate/debt recursionへの入口は作れても出口を作れない。

### 25. finite rootはcapacityにならない

target 1355のactual mex epoch開始`tailStart=328002`を使い、2Mまでのabove-target first occurrencesを
time-only parentでpre-tail rootへ畳み込んだ。

| quantity | result |
|---|---:|
| used pre-tail roots | 7,179 |
| largest root | value 657,846, first time 318,832 |
| descendants of largest root by 2M | 421,370 |
| second largest root descendants | 416,140 |

さらに一つのinterior parent value 2,061,814は2Mまでに25個の異なるfirst-occurrence childを
生成した。従ってparent→childはinjectiveでもbounded-branchでもなく、同じroot/edgeへの課金は
大規模に再利用される。

これは論理的にも避けられない。有限個のrootを持つwell-founded treeは、各pathが有限でも
無限に多くのnodeを持てる。time下降はcycleを排除するだけで、root capacityを消費しない。

### 26. Round 5判定

- exact structural statement: 成立しLean化済み
- debt-time rankへの接続: tail内 ancestry中は成立
- pre-tail rootからのrank exit: anchor/budget下降がなく不成立
- capacity/charging: descendant reuseにより増加なし

従ってtime-only ancestryを主証明rankとして延長する枝は停止する。独立Lean lemmaはprovenanceの
整理としては正しいが、全域性への新しい有限資源を与えない。再利用するなら、pre-tail rootで
別のgate certificateまたはstrict history-budget dropを構成できた場合に限る。

---

## Round 6: gate/debt rankへの接続点監査

### 27. pre-tail rootで下がる必要がある量

現行の`phaseSearchRank`は

```text
(missingBelowCount target horizon, anchorParent, phase.rank, localMeasure)
```

である。permanent-tailのhistory horizonでは
`MissingPermanentAboveTail.budget_zero`により第1成分は既に0である。
time ancestryはdebt相内で第4成分を下げるが、debtからnormalへ戻ると
`phase.rank` が `0 -> 1`と逆に上がる。従ってpre-tail rootで退出に使えるのは

```text
rootValue < activeAnchor
```

というstrict anchor dropだけである。root first timeの有限性、tailStartまで時間を
巻き戻すこと、canonical coverage valleyの`1 -> 0` budget edgeのいずれも、
元のtail horizonのbudget 0からの下降にはならない。pre-tail horizonへの巻き戻しは
budgetを増やす向きであり、元のrank edgeと合成できない。

### 28. 最有望なexact lemma候補（Lean化済み）

生き残る候補は三本ではなく一本に絞られた。

```lean
theorem FirstAt.preTail_anchorObstruction_or_normalProgress
    (htail : MissingPermanentAboveTail target tailStart)
    (htarget : target < value)
    (hanchor : anchor <= value)
    (hfirst : FirstAt a value firstTime)
    (hhorizon : firstTime < horizon) :
    (exists root rootFirstTime,
      target < root /\ anchor <= root /\
      FirstAt a root rootFirstTime /\ rootFirstTime <= tailStart) \/
    exists child childFirstTime,
      target < child /\ child < anchor /\
      FirstAt a child childFirstTime /\ childFirstTime < firstTime /\
      DebtInvariant target
        ⟨horizon, anchor, .debt, childFirstTime⟩ child childFirstTime /\
      PhaseSearchProgress target
        ⟨horizon, child, .normal, child⟩
        ⟨horizon, anchor, .debt, firstTime⟩
```

証明はtime ancestryをactive anchorとの閾値で停止する。親値が初めてanchor未満に
落ちたらstrong `DebtInvariant`を作り、`phaseSearch_debtTimeDrop`と
`phaseSearch_exitDebt_of_anchorDrop`を合成する。anchorを割らないままtail前へ
到達した場合だけを左枝として返す。

`Recaman/TargetCombTimeAncestry.lean`に実装し、`lake env lean` を通した。

- 仮定: permanent tail、above-target first occurrence、初期値がactive anchor以上、
  first timeがhistory horizon未満
- 結論: strict anchor crossingがあれば既存rankでnormal退出、なければ
  `pre-tail root >= activeAnchor`だけを残す
- 失敗条件: ancestryがanchorを割らずpre-tailへ到達する
- 有望度: **75/100（正規化補題）、45/100（全域性への直接効果）**

### 29. 追加候補を立てない理由

`pre-tail root >= activeAnchor`枝を「finite prefixだから課金」する候補は、Round 5の
descendant reuse（単一rootに42万以上のdescendant、interior parentに25 children）で
capacityにならない。canonical coverageのbudget dropへつなぐ候補も、tail horizonの
budgetが既に0なのでrankの向きが逆である。これらは過去に停止した
counting/reuse枝の言い換えであり、新候補として再掲しない。

従って次に必要な未知は、generic ancestry定理ではなく、terminal gate固有の
情報から

```text
pre-tail root < activeAnchor
```

を導くことだけである。このgate性質が紙上で出るまでは、time ancestryの
追加強化とpre-tail countingは停止する。

---

## Round 7: terminal gateとfinite pre-tail ceiling

### 30. finite ceilingは成立し、Round 6残余を条件付きで消す

pre-tail rootの値はexact prefix maximumを新定義しなくても、既存軼道上界で

```text
root <= upperTri tailStart
```

と一様に抑えられる。次の二本を
`Recaman/TargetCombTimeAncestry.lean`に追加した。

```lean
theorem FirstAt.value_le_upperTri_of_time_le
    (hfirst : FirstAt a value firstTime)
    (htime : firstTime <= bound) :
    value <= upperTri bound

theorem FirstAt.normalProgress_of_preTailCeiling_lt_anchor
    (htail : MissingPermanentAboveTail target tailStart)
    (hceiling : upperTri tailStart < anchor)
    (htarget : target < value)
    (hanchor : anchor <= value)
    (hfirst : FirstAt a value firstTime)
    (hhorizon : firstTime < horizon) :
    exists child childFirstTime,
      target < child /\ child < anchor /\
      FirstAt a child childFirstTime /\
      childFirstTime < firstTime /\
      DebtInvariant target
        ⟨horizon, anchor, .debt, childFirstTime⟩ child childFirstTime /\
      PhaseSearchProgress target
        ⟨horizon, child, .normal, child⟩
        ⟨horizon, anchor, .debt, firstTime⟩
```

後者はRound 6の左枝`anchor <= root`を前者と`upperTri tailStart < anchor`で
矛盾にするだけである。これにより「blockerがfinite prefix ceilingを越えた後は
anchor=blockerでancestryが必ずanchorを割る」という局所bridgeは証明された。

### 31. natural terminal-gate anchorではより強く、ancestry自体が不要

tail内の`HistoryTerminatedComb s k blocker`では、final fresh landingが
`blocker+1`でありtail上にある。従って`target <= blocker`で、等号は
`blocker_seen`と`target_missing`に矛盾する。combのlow-rail等式は同時に
`blocker < a s`を与える。

そのため次をLean化した。

```lean
theorem HistoryTerminatedComb.tail_blocker_debtNormalProgress
    (htail : MissingPermanentAboveTail target tailStart)
    (htime : tailStart <= s)
    (hcomb : HistoryTerminatedComb s k blocker) :
    exists firstTime,
      target < blocker /\
      FirstAt a blocker firstTime /\ firstTime < s /\
      blocker < a s /\
      DebtInvariant target
        ⟨s, a s, .debt, firstTime⟩ blocker firstTime /\
      PhaseSearchProgress target
        ⟨s, blocker, .normal, blocker⟩ (targetStartNode s)
```

つまりnatural active anchorがcomb entry `a s`なら、terminal blocker自身が
`target < blocker < anchor`を満たすstrong debt値である。blockerのfirst-transitionが
legal subtractionかforced additionかを開く必要すらない。これは既存
coverage/debt bridgeのmacro向けexact adapterである。

### 32. terminal originだけでhigh pre-tail rootを排除する主張は偽

標準軼道に次のexact counterexampleがある。

```text
target-relative H -> L gate: time 733 -> 734, target 19
HistoryTerminatedComb: s=734, k=10, entry=149, blocker=138
blocker first occurrence: 138@120
origin: legal subtraction 258 - 120 = 138
origin parent: 258@119
empirical strict-tail boundary: 132
119 <= 132, yet 149 <= 258
```

`terminalGate_subtractionOrigin_preTailHigh_counterexample`としてLean kernelで認証した。
従ってterminal gate、H→L entry、maximal fresh comb、positive blocker originだけで

```text
pre-tail root < entry anchor
```

を導くことはできない。正しい処理はparent 258を追わず、より小さい
blocker 138自身をstrong debtに載せることである。

### 33. infinite blockersとunboundednessの監査

`HistoryTerminatedComb.same_blocker_finalTime_eq`の対偶により、final timeが異なる
terminal combのblockerは相異なる。従ってchronological terminal combが無限に
存在すれば、blocker集合はNatの有限区間に収まらず、

```text
exists terminal blocker b, upperTri tailStart < b
```

が従う。これと§30のceiling lemmaの接続は数学的に正しい。ただし現行Lean
interfaceには「infinite family of target terminal combs」がなく、その有限鳩の巣部分は
純粋な集合論でありボトルネックではないため未実装とした。

本当の不足は次の二点である。

1. **terminal comb infinitely often**: permanent-above tailからcandidate-low stateが無限回
   出ることは未証明。lowが有限ならeventually high-only candidate tailに入り、
   これは既存監査の「ballot/ledger identityだけではexitなし」枝である。
2. **anchor mounting across episodes**: 各episode内では`blocker < entry`により
   anchor=blockerへのrank dropは可能。しかし後のepisodeのentry/blockerを現在の
   outer parentのchildにするには、zero history budgetの下でlater anchorがcurrent anchorより
   厳密に小さいことが必要。blocker集合のunboundednessはこれを与えず、
   単調増加な相異Nat列ですでにcountermodelになる。

従ってfinite-ceiling + unbounded-blocker bridgeの局所部分は成立するが、
right-recordの代わりに外側反復を閉じるものではない。次のexact研究対象は

```text
eventually-high candidate tailを排除する
or
later terminal combにouter-anchor dropを与える
```

のいずれかである。後者をglobal right-recordと同じ強さまで戻さずに言えるかが
次ラウンドの判定点になる。

### 34. Round 7判定

- finite pre-tail ceiling: **Lean化済み、成立**
- ceilingを越えたanchorでのancestry exit: **Lean化済み、成立**
- natural terminal entry anchor: **blocker自身で直接閉包、ancestry不要**
- terminal gate/originによるhigh root排除: **標準軼道反例により停止**
- infinite terminal blockers: **terminal comb無限を仮定すればunbounded、その仮定が未証明**
- outer anchor mounting: **未解決、unboundedness単独では向きが逆**

---

## Round 8: terminal blockerのsemantic mounting

### 35. historical normalはcurrent nodeではない

Round 7の

```text
C = \<s, blocker, normal, blocker\>
```

は、comb entry horizon `s` に保存されたactual current valueではない。実際、
`HistoryTerminatedComb`から`blocker < a s`なので、次をLean化した。

```lean
theorem HistoryTerminatedComb.blockerNormal_not_orbitReady :
  not (OrbitReadyNormalInvariant target
    \<s, blocker, .normal, blocker\>)

theorem HistoryTerminatedComb.blockerNormal_not_currentOrDebt :
  not (CurrentOrDebtInvariant target
    \<s, blocker, .normal, blocker\>)
```

従って`tail_blocker_debtNormalProgress`のnormal childを、そのまま旧
`CurrentOrDebtInvariant`の再帰入力にするのは不正である。

ただしこれはsemantic holeではない。blockerのrepresentative timeをそのfirst occurrence、
history horizonを`s`とすれば、`C`はexactな
`ExtendedHistoryNormalInvariant`になる。horizon readiness
`target <= s+1`は、permanent tailのcompleted lower historyと
`coveredBelowCount_le_time`から従う。

### 36. ready debt経由で既存refined recursionへ完全に接続

comb entryのactual parentとblocker debtを

```text
P = targetStartNode s
D = \<s, a s, debt, firstTime(blocker)\>
```

とおく。すると既存rankで

```text
D < P    -- phaseSearch_enterDebt
C < D    -- phaseSearch_exitDebt_of_anchorDrop, blocker < a s
C < P    -- transitivity
```

が得られる。`D`は`ReadyDebtInvariant`、従って
`ReadyCurrentOrDebtInvariant`かつ`OrbitReadyRefinedInvariant`である。
`C`は`ExtendedHistoryNormalInvariant`、従って同じく
`OrbitReadyRefinedInvariant`である。

これを`Recaman/TargetCombSemanticMount.lean`で次の三段階にした。

```lean
theorem HistoryTerminatedComb.tail_blocker_semanticMount
-- ready debt, extended-history normal, semantic certificates,
-- P -> D -> C の各rank edgeと合成edgeを同時に返す

theorem HistoryTerminatedComb.tail_blocker_refinedDebtStep
-- 再帰入力として最も直接なready debt child Dを返す

theorem HistoryTerminatedComb.tail_blocker_refinedStepFromEntry
    (htail : MissingPermanentAboveTail target tailStart)
    (htime : tailStart <= s)
    (hcomb : HistoryTerminatedComb s k blocker) :
    (exists witness, a witness = target) or
      exists child,
        OrbitReadyRefinedInvariant target child and
        PhaseSearchProgress target child (targetStartNode s)
```

最後の定理では、`C`に既存
`ExtendedHistoryNormalInvariant.refinedStep`を適用し、その一歩を
`C < P`と合成している。従って一つのterminal episodeについては、targetが出現するか、
既存refined domainのstrict childまで必ず進む。historical-normal closureを新たに仮定する
必要はない。ファイル単体を`lake env lean`でbuild済み。

### 37. 残余はfuture-horizon outer mountingだけ

上のwrapperが起点とする親は、そのterminal comb自身のentry
`targetStartNode s`である。以前の任意のouter parentから未来のentry horizon `s`へ移る
edgeは作っていない。history budgetが既に0なら、未来へclockを進めるだけではrankは下がらず、
通常はfuture entry anchorが現在anchorよりstrictに小さいことが必要になる。

`TargetCombFiniteCeiling.lean`のfinite pigeonhole定理により、`B+2`本の相異なる
final-time completed combから`blocker > B`は得られる。しかしこれは大きいblockerを供給する
向きであり、outer mountingに必要なanchor下降とは逆である。20M監査でも、最初にprefix ceiling
を越えた後に`blocker <= ceiling`へ793回戻っており、「一度越えれば以後monotone」という
envelopeも使えない。finite-ceiling bridgeは各episode内または条件付きancestryには有効だが、
episode間のrank edgeを生成しない。

### 38. low/terminal無限対high-onlyの二分

target-relative candidateはtargetと等しくなれないので、tail上では常にlowまたはstrict highである。

1. lowが有限なら、既存
   `eventually_candidate_strictAbove_of_no_lows`によりeventually high-only candidate tailへ入る。
   現状のhigh-excursion prefix ledgerはstep則の望遠和であり、無限high-onlyを排除しない。
2. lowが無限なら、各lowを含むmaximal episodeからterminal combを切り出すinterfaceが必要である。
   それが得られれば、target omissionの下でtarget landingによる終了はなく、completed terminal combを
   無限に供給する方へ進める。しかし相異blockerのunboundednessまで得ても、§37のfuture-horizon
   mountingは別に残る。

従って正確なglobal残余は次の二点である。

```text
(A) eventual high-only candidate tailを排除する
or
(B) infinitely-many low statesをterminal comb列へ抽出し、
    later episode entryを現在のouter parentより下へmountする
```

Round 8により、(B)の**terminal episode内部のsemantic admissibilityは解決済み**になった。
未解決なのはepisode抽出とepisode間比較だけである。right-recordや単なるblocker
unboundednessへ戻っても後者は解けない。

### 39. Round 8判定

- historical blocker normalの`CurrentOrDebtInvariant`: **偽、Leanで否定済み**
- `ExtendedHistoryNormalInvariant`としてのmount: **成立、Lean化済み**
- parent→debt→normalとrefined next stepの合成: **成立、Lean化済み**
- terminal episode内semantic closure: **完了**
- future episodeを以前のouter parentへmount: **未解決、唯一のsemantic外残余**
- high-only branch: **ledgerだけでは閉じず、独立残余**

---

## Round 9: episode間mountingのexact dichotomy

### 40. zero-budgetではlater horizonを直接比較できる

permanent tail内の全horizonでは`missingBelowCount target horizon = 0`である。
従ってphase rankはraw horizonの増加を見ず、normal node同士ならanchor下降、normalから
debtならphase下降だけでstrict progressになる。次を
`Recaman/TargetCombSemanticMount.lean`に追加した。

```lean
theorem MissingPermanentAboveTail.budget_zero_of_start_le

theorem MissingPermanentAboveTail.laterNormal_progress_of_anchorDrop
-- child horizonがlaterでも childAnchor < parentAnchor ならprogress

theorem MissingPermanentAboveTail.laterDebt_progress_from_normal
-- child horizonがlaterでも同anchorの normal -> debt はprogress
```

特にlater debtへ入るのに、later blockerのfirst occurrenceがearlier episodeより前である
必要はない。必要なのはlater blockerのfirst timeがそのlater entryより前という
`HistoryTerminatedComb`自身の標準性質だけである。

### 41. left-entry枝は次のcomb normalをそのまま再帰childにする

chronological completed comb

```text
h1 = (s1,k1,b1),  h2 = (s2,k2,b2),
s1 + 2*k1 < s2
```

に既存`next_entry_below_or_blocker_lt`を適用すると

```text
a s2 < b1  or  b1 < b2
```

である。左枝では

```text
C1 = \<s1,b1,normal,b1\>
P2 = targetStartNode s2
C2 = \<s2,b2,normal,b2\>
```

に対して

```text
P2 < C1   -- zero budget + a s2 < b1
C2 < P2   -- terminal blocker mount, b2 < a s2
C2 < C1   -- composition
```

となる。`C1`,`C2`はいずれも`ExtendedHistoryNormalInvariant`、
`OrbitReadyRefinedInvariant`、`PhaseSemanticInvariant`を保持する。

これをexactに返す定理をLean化した。

```lean
theorem HistoryTerminatedComb.next_blockerNormalProgress_or_upwardReset
-- left枝: C2の全semantic dataと C2 < P2 < C1
-- right枝: b1 < b2
```

従ってRound 8で曖昧だったfuture-entry mountingのうち、later-entry-left枝は完全に閉じた。
outer residualは厳密にupward blocker resetだけへ戻った。global right-recordは仮定していない。

### 42. historical anchorに対するno-straddleもterminal固有ではない

同じfresh low-rail argumentを一般化して、terminal blocker以外の既出anchorについても

```lean
theorem HistoryTerminatedComb.entry_below_or_anchor_le_blocker
    (hfirst : FirstAt a anchor firstTime)
    (hfirstTime : firstTime < s) :
    a s < anchor or anchor <= blocker
```

をLean化した。fresh comb interval `[blocker+1, a s]`が既出anchorを含めば、その
low-rail first occurrenceに反する。これはancestryから得たhistorical childも、次episodeに
対して少なくとも同じleft/above-anchor二分へ再投入できることを示す。

### 43. ceiling越えupward resetも局所的にはsemantic childへ落ちる

upward reset `b1 < b2`で、さらに

```text
upperTri tailStart < b1
```

とする。`b2`のfirst occurrenceを`f2<s2`とし、later horizonに

```text
D = \<s2,b1,debt,f2\>
```

を作る。§40により`D<C1`である。`b1<=b2`とfinite pre-tail ceilingを
`FirstAt.normalProgress_of_preTailCeiling_lt_anchor`へ渡すと、time ancestryは
必ず`b1`未満へcrossし、extended-history normal child `N`を与える。

```text
N < D < C1
```

をsemantic data込みで合成する次の定理をLean化し、単体buildした。

```lean
theorem HistoryTerminatedComb.next_extendedProgress_of_ceiling
    ...
    (hceiling : upperTri tailStart < blocker1) :
    exists child,
      ExtendedHistoryNormalInvariant target C1 and
      PhaseSemanticInvariant target C1 and
      ExtendedHistoryNormalInvariant target child and
      OrbitReadyRefinedInvariant target child and
      PhaseSemanticInvariant target child and
      PhaseSearchProgress target child C1
```

left枝では`child=C2`、reset枝では上のancestry crossing childである。従ってceilingを
越えたprevious blockerから次episodeへの**一回のsemantic progressは二枝とも閉じた**。

### 44. infinite-low側の抽出は進んだが、無限下降はまだ得ていない

共有`TargetCandidateTransitions.lean`には同時に次が追加された。

1. `candidateBelow_entry_first`: tail内low candidateの次landingはfresh
2. `FirstAt.exists_maximal_freshCombEpisode`: low railの値下降に関するstrong inductionで
   fresh landingから有限maximal comb suffixを得る
3. `FreshCombEpisode.historyTerminated_of_next_not_step`: maximal failureをhistorical
   blockerへ変換
4. `candidateBelow_exists_historyTerminatedComb`: 各tail lowからcompleted terminal combを得る

各terminal final timeの前には有限個のstartしかないため、lowが無限ならfinal timeも無限に
選べる。さらに各combは有限なので、greedyに前comb finalより後のlowを選べば
`s_i+2*k_i<s_(i+1)`を満たすdisjoint chronological subsequenceを紙上では抽出できる。
このinfinite-selection API自体はまだLean化していない。

ただし「terminal combが無限」だけから矛盾はまだ出ない。相異final timeの有限鳩の巣で
ある`b_i > upperTri tailStart`を得て、§43を一回適用することはできる。しかしreset枝の
childは次combのnormal `C_(i+1)`ではなく、blocker ancestryが作る任意のhistorical normal
`N`である。§42により`N`を次episodeと比較することは可能だが、anchorはstrictに下がるため、
有限回後に再び

```text
anchor <= upperTri tailStart
```

へ入り得る。その有限basinではpre-tail root obstructionが再発し、ceiling theoremを
反復できない。従って現時点で得たのは「large-anchor区間の有限下降」であり、infinite
terminal stream全体のcoherent descending chainではない。

### 45. Round 9判定

- later-entry-left mounting: **完全解決、次comb normalをsemantic childとしてLean化**
- episode間residual: **exactにstrict upward resetのみ**
- upward reset above pre-tail ceiling: **一回のsemantic progressをLean化**
- lowからfinite maximal terminal comb抽出: **Lean化済み**
- infinite lowからdisjoint terminal stream抽出: **紙上成立、infinite API未実装**
- infinite terminal streamの全域 contradiction: **未解決**
- 新しい最小残余: **ancestry childのanchorがfinite pre-tail basinへ戻った後の再mounting**
- high-only branch: **従来通り独立に未解決**

---

## Round 10: finite pre-tail basin remountingの最終監査

### 46. fixed historical anchorからのexact conditional remount

tail内のhistorical normal parent

```text
R = \<parentHorizon,r,normal,r\>,
target < r,
FirstAt a r firstTime,
firstTime < parentHorizon <= s
```

とfuture terminal comb `H=(s,k,b)`を固定する。Round 9のno-straddleはexactに

```text
a s < r  or  r <= b
```

を与える。左枝ならzero-budget anchor dropで

```text
targetStartNode s < R
```

となり、terminal blocker mountを合成して

```text
\<s,b,normal,b\> < R
```

を得る。親子双方のextended/refined/semantic dataを保持する次の二定理をLean化した。

```lean
theorem HistoryTerminatedComb.blockerNormalProgress_from_historicalAnchor
-- 仮定 a s < r から future blocker normalをsemantic childとして返す

theorem HistoryTerminatedComb.blockerNormalProgress_or_anchor_le_blocker
-- semantic remount or r <= b のexact routing
```

従ってfinite basinで不足する条件は曖昧な「future horizon compatibility」ではなく、文字通り

```text
exists future terminal H, a H.start < r
```

だけである。また`b<r`を持つfuture terminalがあればno-straddleにより左枝が強制される。

### 47. unbounded terminal streamは左枝を強制しない

反対枝`r<=b`が全future terminalで続くことは、現在証明済みのinterval/freshness/one-use
条件と矛盾しない。任意のfixed anchor `r`に対して

```text
b_j = r + j
e_j = r + j + 1
```

というsingleton fresh-interval ladderを考える。このfamilyは

```text
e_j = b_j + 1
b_(j+1) = e_j
i < j なら e_i <= b_j
blockerはinjectiveかつunbounded
r <= b_j
not (e_j < r)
```

を同時に満たす。`b_(j+1)=e_j`なので、各later blockerは直前episodeのfresh landingとして
すでにhistoricalである。blockerは全て相異なるためone-use terminal blocker条件にも反しない。
fresh intervalsは互いに交差せず、値軸上を一単位ずつ右へ進む。

このcountermodelを次としてLean kernelで認証した。

```lean
theorem finiteBasin_rightLadder_countermodel (anchor : Nat) :
  exists entry blocker : Nat -> Nat,
    (forall j, entry j = blocker j + 1) and
    (forall j, blocker (j+1) = entry j) and
    Function.Injective blocker and
    (forall i j, i < j -> entry i <= blocker j) and
    (forall i j, i < j -> blocker i < blocker j) and
    (forall bound, exists j, bound < blocker j) and
    (forall j, anchor <= blocker j) and
    (forall j, not (entry j < anchor))
```

これは標準Recaman軌道そのもののcounterexampleではなく、現在使っている全macro帰結に対する
合成countermodelである。従って標準軌道の追加性質なしに、interval order、blocker distinctness、
unboundedness、直前fresh値からのhistorical provenanceだけを組み合わせて
`future entry < r`を証明することはできない。

### 48. ceilingとの組合せが停止する正確な場所

`r > upperTri tailStart`なら、全future blockersが`r`以上でもtime ancestryが
pre-tail rootへ到達する前に`r`未満へcrossするためRound 9のceiling theoremが使える。
一方

```text
target < r <= upperTri tailStart
```

では`r<=b`とpre-tail root `root>=r`が同時に成立し得る。right ladderはこの向きの
値配置を無限に維持する。finite prefixにroot候補が有限個あることも、同じroot/parentの
descendant reuseを禁止する定理がないためcapacityにならない。Round 5–7で停止した
pre-tail countingを再び開いても同じreuse obstructionへ戻る。

従ってinfinite-low側を閉じるには、次のいずれかの**新しい標準軌道固有入力**が必要である。

1. fixed historical anchorを跨がず右へ進み続けるterminal ladderを禁止するno-escape定理
2. `r<=b`側でpre-tail rootの再利用を有限課金する新しいprovenance injectivity
3. comb外のhigh-candidate excursionからfuture entryを`r`未満へ戻すglobal balance

現行のpairwise interval order / one-use blocker / finite ceilingの強化だけでは1–3のどれも出ない。

### 49. Round 10判定とactive branch

- fixed-anchor left remount: **exact conditional theoremをLean化、成立**
- `progress or anchor<=future blocker` routing: **Lean化、完全**
- unbounded blockersからfuture-leftを導く主張: **抽象right-ladder countermodelで反証**
- finite pre-tail basinのinterval/one-use攻略: **停止**
- infinite-low branch: **terminal stream抽出までは有望、basin no-escapeという新入力待ち**
- eventual-high branch: **未解決のまま**

したがってmacro/right-record系のactive direct branchは再び0本である。次の探索を続けるなら、
既存interval orderを組み替えるのではなく、標準recurrence固有のclock/legalityを使って
right ladderを壊すか、eventual-high candidate tailを直接排除する必要がある。

---

## Round 11: right ladderに対する標準漸化式のclock監査

### 50. 選んだ固有条件: terminal two-addition launch

Round 10のsingleton ladder

```text
b_j = r+j,
entry_j = b_j+1,
b_(j+1) = entry_j
```

はterminal episode間の実際の軌道を捨てていた。標準Recaman recurrenceでは、
`HistoryTerminatedComb s k b`のfinal low time

```text
F = s + 2*k,
a F = b+1
```

の直後に二回のforced additionが続く。一回目はtarget-low candidate、二回目はhistorical
blocker `b`がrepaymentを止めるためである。従ってexactに

```text
not CanSubtract(F+1)
not CanSubtract(F+2)
a(F+1) = b + F + 2
a(F+2) = b + 2*F + 4
```

となる。これを

```lean
theorem HistoryTerminatedComb.two_forced_launch
```

として`Recaman/TargetLadderClock.lean`にLean化した。

またtail内のlow entryは単にfirst occurrenceであるだけでなく、そのincoming stepが
legal subtractionである。

```lean
theorem MissingPermanentAboveTail.candidateBelow_entry_legal
```

forced addition originなら既存`forcedAddition_candidate_strictAbove`によりcurrent candidateが
highになり、low仮定に反する。このlegal/forced distinctionがinterval countermodelに欠けていた
最小の標準軌道固有条件である。

### 51. singleton unit ladderは少なくとも5 clock離れる

singleton `HistoryTerminatedComb s 0 b`の次に、legal subtractionで

```text
a t = b+2
```

を作るunit-ladder edgeを考える。`t=s+1,s+2`は§50のforced additionと矛盾する。
`t=s+3`なら二回addition後のexact valueから

```text
a(s+3) = b+s+1
```

となり、`b+2`との等式は非初期範囲`1<s`で不可能である。従ってまず`t>=s+4`。
さらに`t=s+4`はadjacent values `b+1,b+2`が4 clock離れて出現することになるが、
triangular parityは4 shiftで不変であり、adjacent valuesに必要なopposite parityに反する。

```lean
theorem HistoryTerminatedComb.singleton_unitLadder_gap_four
theorem HistoryTerminatedComb.singleton_unitLadder_gap_five
```

として

```text
t >= s+5
```

までLean化した。これはRound 10の密な時刻配置を実際に壊す、正しいrecurrence固有の
sparsity theoremである。

### 52. しかしclock sparsityだけではinfinite ladderを壊さない

5-clock gapとadjacent-value parityは無限列と両立する。例えば

```text
s_j = 6*j
```

なら各gapは6で、`upperTri(s_(j+1))-upperTri(s_j)`は奇数なので、隣接entryに必要な
parityが毎回反転する。次をLean化した。

```lean
theorem upperTri_add_six

theorem singleton_unitLadder_clock_constraints_have_infinite_model
    (index : Nat) :
  let s_j := 6*index
  let s_next := 6*(index+1)
  s_j+5 <= s_next and
    (upperTri s_j + upperTri s_next) % 2 = 1
```

従ってtwo-addition launch、incoming legality、parityを組み合わせても得られるのは
uniform density boundだけで、finite basinからのreturnやtarget landingではない。

### 53. exact standard-prefix probe

`experiments/target_ladder_probe.cpp`を追加し、既存maximal target-comb extractorのexact
standard prefixを再利用して、consecutive fixed-target terminal edgesを20Mまで監査した。

```text
history edges                         2,655
upward edges                            20
singleton history episodes             381
next blocker = previous entry             0
exact unit ladder                         0
singleton unit ladder                     0
clock parity failures                     0
```

したがって抽象right ladderはactual 20M prefixには一辺も現れず、singleton terminal自体が
381本あるため単なるvacuityでもない。一方、この0件を説明する一様定理は§51ではない。
actual gapsが5以上であることと「辺が存在しない」ことの間にはまだ大きな差がある。

### 54. 最小の不足仮定とRound 11判定

§50の二回addition後、次entry clock`t`の直前にはlegal subtraction equation

```text
a(t-1) = t + (oldEntry+1)
```

が必要である。従って本当に不足しているのは合同条件ではなく、high launch
`b+2F+4`からこのprecursorへ至る中間区間のvisited-sensitive signed pathを禁止する
no-return statementである。最小形は例えば

```text
oldEntry was a fresh target-low landing
and its terminal episode completed
=> oldEntry cannot later be the blocker of a fresh successor episode
```

である。これは20Mで支持されるが、既存subtraction ledgerはendpointの望遠和に戻り、
visited集合を見ないため証明できない。これを仮定しない限り、6-clock scheduleのような
sparse ladderをclock arithmeticだけで排除できない。

- two-forced launch / low-entry legality: **Lean化済み、成立**
- singleton unit ladderの5-clock gap: **Lean化済み、成立**
- gap + parityによるinfinite ladder排除: **明示的clock modelでno-go**
- actual prefix: **20Mでladder edge 0、経験的には強い**
- direct proof有望度: **20/100**
- visited-sensitive no-return補題の探索価値: **35/100**

Round 11ではright-ladder countermodelの「密なclock配置」は壊せたが、sparse版は残った。
従って新しいactive direct branchには昇格せず、標準visited historyを本質的に使う
no-return theoremが見つかった場合だけ再開する。

---

## Round 12: visited-sensitive fresh-entry no-returnの一般監査

### 55. later blockerが古いfresh intervalに属するならentry equalityまで強制

earlier/later completed combを

```text
H1=(s1,k1,b1), H2=(s2,k2,b2),
s1+2*k1 < s2
```

とする。`b2`がH1のfresh intervalに属する、すなわち

```text
b1 < b2 <= a s1
```

なら、既存`fresh_intervals_ordered`から実は

```text
b2 = a s1
```

まで従う。later intervalが`b1`より左なら`b2<a s2<b1`となって下界に反し、
earlier intervalがlater blockerより左なら`a s1<=b2`となって上界と合成できる。

```lean
theorem HistoryTerminatedComb.later_blocker_on_freshInterval_eq_entry
```

を`Recaman/TargetLadderClock.lean`に追加した。従ってinterior low railの再利用は不可能で、
visited-sensitive問題は**古いfresh entryそのもののreturn**だけに縮約される。

### 56. legal-originから得るexact necessary condition

`b2=a s1`で、entry `a s1`がclock`s1`のlegal subtractionで初出したとする。
later blockerのsubtraction-origin lemmaにより

```text
a s2 < a(s1-1)
```

である。legal landing equationとH2のcomb exit equationは

```text
a(s1-1) = a s1 + s1
a s2 = b2 + k2 + 1 = a s1 + k2 + 1
```

なので

```text
k2 + 1 < s1
```

が必要である。次としてLean化した。

```lean
theorem HistoryTerminatedComb.later_blocker_eq_freshEntry_forces_short
```

これは値・clock・legalityから得られる最強の直接条件だが、later combが十分短ければ満たせる。
従って単独ではno-returnにならない。

### 57. 無条件fresh-entry no-returnは標準prefixで偽

probeを一般化し、全history terminal blockerのfirst occurrenceが過去のmaximal fresh intervalに
属するかを20Mまでexact scanした。

```text
history terminal blockers                  2,660
born on a prior maximal fresh interval       857
of which born exactly at its entry            857
of which born on same-target fresh rail       697
born on immediate previous same-target comb     0
```

全857件がentry equalityであることは§55が説明する。しかし再利用自体は稀どころか多数ある。
最初のstandard-prefix counterexampleはtarget 4で

```text
H1: s=38,  k=13, entry=39, fresh interval=[26,39], blocker=25
M : s=77,  k=11, entry=75, fresh interval=[64,75], blocker=63
H2: s=111, k=0,  entry=40, fresh interval=[40,40], blocker=39
```

である。H1のfresh entry 39が、intervening target-4 terminal comb Mの後、H2のterminal
blockerとしてreturnする。三entryはいずれもtarget-4 low candidateであり、時刻順に非重複である。

このexact orbit dataをprivate certificates

```lean
historyTerminatedComb_38_13_25
historyTerminatedComb_77_11_63
historyTerminatedComb_111_0_39
```

としてkernel検証し、公開定理

```lean
theorem freshLowEntry_later_terminalBlocker_counterexample
```

にまとめた。従って

```text
fresh target-low entry is never a later terminal blocker
```

という無条件no-returnは標準Recaman軌道上で偽であり、停止する。

### 58. 生き残る最小gated形

20Mで0件だったのは一般returnではなく、次の**immediate target-macro successor**版である。

```text
H1,H2 are consecutive history-terminal maximal combs
for the same fixed target epoch,
with no intervening target-terminal comb
-----------------------------------------------------
H2.blocker != H1.entry
```

上のexact counterexampleはH1とH2の間にMがあるため、このgateを満たさない。probeでは
consecutive same-target history edges 2,655本、upward 20本を調べ、equality 0だった。
この形はunconditional theoremに対する最小の観測上の修正である。

ただし`HistoryTerminatedComb`二本だけの型には「間に同target macroがない」という情報がない。
証明には以前から候補だった

```text
TargetMacroSuccessor
```

として、H1のterminal後からH2のmaximal H→L entryまでのhigh-candidate wordとvisited stateを
保持する必要がある。pairwise interval order、first occurrence、subtraction ledgerだけでは
counterexampleのMを認識できず、successor gateを表現できない。

### 59. Round 12最終判定

- interior fresh railのlater blocker再利用: **不可能、Lean化済み**
- entry再利用時のlater length bound `k2+1<s1`: **Lean化済み**
- 無条件fresh-entry no-return: **standard-prefix Lean反例で棄却**
- same-target immediate-successor no-return: **20Mで0/2,655、未証明**
- gated形の探索有望度: **40/100（exploratory）**
- 全域証明への直接有望度: **15/100**

したがってvisited-sensitive枝を続ける場合の唯一の正しい入口は、一般provenanceや
freshnessの追加強化ではなく、`TargetMacroSuccessor`を定義してintervening high-candidate
区間を保持することである。それを実装しないままno-returnを主張する枝は、今回の
`38 -> 77 -> 111` exact counterexampleにより停止する。

## Round 13: consecutive target macro のexact interface

### 60. `TargetMacroSuccessor`の最小構造

新規ファイル`Recaman/TargetMacroSuccessor.lean`に、同じ固定targetに対する連続する
history-terminal maximal combを次の情報だけで表すPropを定義した。

```lean
structure TargetMacroSuccessor
    (target tailStart s₁ k₁ blocker₁ s₂ k₂ blocker₂ : Nat) : Prop where
  tail : MissingPermanentAboveTail target tailStart
  first : HistoryTerminatedComb s₁ k₁ blocker₁
  second : HistoryTerminatedComb s₂ k₂ blocker₂
  first_inside_tail : tailStart < s₁
  chronological : s₁ + 2 * k₁ < s₂
  first_low : nextSubtractionCandidate s₁ < target
  second_low : nextSubtractionCandidate s₂ < target
  candidate_high_between : ∀ time,
    s₁ + 2 * k₁ < time → time < s₂ →
      target < nextSubtractionCandidate time
```

最後のfieldが「間にterminalなし」のexact clock conditionである。これはblockerの順序や
欲しいno-returnを仮定しておらず、H1 terminal後の最初のlater low candidateをH2として
選ぶことから得られる。実際、次を証明した。

```lean
TargetMacroSuccessor.no_intermediate_targetTerminal
```

すなわちopen interval内には同target-lowから開始するhistory-terminal combは存在しない。
さらにtail semanticsとterminal後の二回のforced additionから

```lean
TargetMacroSuccessor.first_entry_legal
TargetMacroSuccessor.second_start_gap
TargetMacroSuccessor.high_excursion
```

を証明した。特に`F=s₁+2*k₁`とすると`s₂≥F+3`であり、区間
`[F+1,s₂-1]`全体が`TargetHighCandidateExcursion target`になる。これはmaximal-low
extraction/successor clock intervalから導ける内容だけである。

### 61. 現行APIで`b₂ ≠ entry₁`はまだ出ない

`b₂=a s₁`を仮定して既存のfirst occurrence、legal subtraction、comb exitをすべて合成した。
得られるexact certificateを次で型に固定した。

```lean
structure TargetMacroEntryReturnResidual (source : TargetMacroSuccessor ...) : Prop where
  blocker_eq_entry : blocker₂ = a s₁
  blocker_first : FirstAt a blocker₂ s₁
  entry_incoming_legal : CanSubtract s₁ (stateAt (s₁-1))
  origin_predecessor_eq : a (s₁-1) = blocker₂+s₁
  later_short : k₂+1 < s₁
  final_successor_first : FirstAt a (blocker₂+1) (s₂+2*k₂)
  high_excursion : TargetHighCandidateExcursion target
    (s₁+2*k₁+1) (s₂-1)
```

そして無条件に

```lean
TargetMacroSuccessor.entry_ne_or_returnResidual
```

を証明した。従って現在のAPIが残すexact gapは
`TargetMacroEntryReturnResidual`の非存在である。これは結論の単なる仮定化ではない。
再訪を仮定したとき、軌道が強制される全endpoint equation、first occurrence、later length
bound、successorの全high intervalを保持した反証対象である。

既存のhigh-excursion ledgerはこのresidualと矛盾しない。欠けているのはhigh interval内の
visited-set evolution、より具体的には各high candidateがいつhistorical blockerとなり得るかを
追跡するinterval-history certificateである。単なるinterval order、triangular parity、endpoint
first occurrenceを追加してもRound 12反例の機構を除去できない。

### 62. Round 13判定

- successor/no-terminal-between interface: **Lean化済み、85/100（再利用性）**
- entry returnのexact residual reduction: **Lean化済み、35/100（探索価値）**
- 現行APIだけによるimmediate-successor no-return: **未証明、15/100**
- 次に必要な新情報: **high excursion全体のvisited-history certificate**
- build: `lake build Recaman.TargetMacroSuccessor`成功（173 jobs）

従って今回の20分ではsuccessor gateを正しく型にし、証明可能部分と不足条件を分離できた。
no-returnを直接仮定する方向は採らず、次ラウンドを行うならresidualを標準prefixで反例探索するか、
high intervalの候補値のfirst occurrenceを追跡する専用ledgerを作るのが最小の次手である。

## Round 14: entry-return residualのcausal-reuse分類

### 63. 旧entryがhigh wordに露出すれば必ずforced use

residualでは`blocker₂=a s₁`かつ`s₁`がそのfirst occurrenceである。従ってsuccessor high
interval内のclock`n`で

```text
nextSubtractionCandidate n = blocker₂
```

となれば、`blocker₂`は既に`valuesThrough n`に属し、step`n+1`は必ずforced additionになる。
さらに`nextCandidate_after_positive_forcedAddition`により次clockのcandidateは
`blocker₂+n`となる。もし`n=s₂-1`ならこれはH2の`second_low`に反するため、旧entryの
high-word露出は最後のhigh clockでは起こらない。

一方、H2 terminalのrepayment pre-state `T=s₂+2*k₂+1`ではcandidateは必ず`blocker₂`で、
historyによりforcedである。従ってhigh word内に一度でも旧entryが露出すれば、
`same_positive_forcedCandidate_reuse_bundle`をその露出と`T`に適用でき、exact balance

```text
2*(subSum T-subSum n) + (T-n) + upperTri n = upperTri T
```

が得られる。この全certificateを

```lean
TargetMacroEntryHighReuseCertificate
```

として定義した。

### 64. 残るexact visited event

次の分類をLean化した。

```lean
theorem TargetMacroEntryReturnResidual.highReuse_or_avoidsHigh
```

任意のentry-return residualは次のどちらかである。

1. 旧entryがhigh word内でpositive candidateとして露出し、forced use二回分の上記exact
   ledger certificateを持つ。
2. successor high word全体が旧entryをcandidateとして避け、H2 terminal repaymentで初めて
   mandatory exposureする。

従って不足情報は一つの明確なvisited event、すなわち

```text
∃ n ∈ [s₁+2*k₁+1, s₂-1], nextCandidate(n)=a s₁
```

の有無まで縮約された。`HighCandidateCausalReuse`は第1枝にexact balanceを与えるが、forced
addition outputがfreshとは限らず、同candidateのreuse intervalも交差し得るため、このbalance
単独では矛盾しない。第2枝ではcandidate equalityが一度もなく、causal-reuse APIを適用する
最初のendpoint自体が存在しない。`TargetMacroSuccessor`のhigh fieldはcandidateのtarget下界だけを
記録し、その値のhistoryを記録しないため、このavoidance枝を排除できない。

### 65. Round 14最終判定

- high露出ならforced + last-high不可能: **Lean化済み**
- high露出からterminal repaymentへのexact reuse balance: **Lean化済み**
- residualの`highReuse ∨ avoidsHigh`分類: **Lean化済み**
- causal-reuseだけによる両枝の排除: **no-go**
- build: `lake build Recaman.TargetMacroSuccessor`成功（176 jobs）
- immediate-successor no-returnの有望度: **20/100**

次に必要なのは一般first occurrence補題ではなく、successor high wordのcandidate値列が旧entryを
必ず再露出する、またはterminalまでavoidした場合に別の有限資源を消費する、という新しい
visited-sensitive coverage theoremである。現行ledgerはそのcoverageを生成しないため、この枝は
ここで停止する。

### 66. parity-incompatible halfの形式的除去

second episodeのexact式`a s₂ = blocker₂ + k₂ + 1`と両endpointの軌道parityを使い、entry returnなら

```text
(upperTri s₁ + upperTri s₂ + (k₂+1)) % 2 = 0
```

でなければならないことを`TargetMacroEntryReturnResidual.parity_compatible`としてLean化した。従って逆の
parity classでは`TargetMacroSuccessor.entry_ne_of_parity_incompatible`が無条件にno-returnを返す。

20Mのupward successor 20辺ではこの定理が16辺を除く。残るcompatible 4辺では経験的に
`k₂+1≤blocker₂-a s₁`だが、比率・clock・deficitに共通機構がなく、現行fieldsは区間分離
`a s₁≤blocker₂`までしか与えない。このmass-gap強化は過適合寄り35/100として停止し、
新しいvisited-sensitive value-space separationが得られた場合だけ再開する。
