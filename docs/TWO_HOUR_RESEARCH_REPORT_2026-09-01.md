# 2時間並列研究レポート — 2026-09-01

## 実施枠

- 開始: 2026-08-31 22:10 JST
- 終了: 2026-09-01 00:10:18 JST
- 方式: Lean形式化、標準prefix exact replay、seeded反例探索を並列化し、各ラウンドで仮説を継続・停止判定

> **結論:** Recamán数列の全射性そのものは未証明である。一方、low-candidate側は
> 「各lowから有限 maximal fresh comb と historical terminal blockerを抽出する」ところまで
> Leanで閉じた。そこから既存semantic rankへ局所的にmountする橋も完成した。残る大域障害は
> finite pre-tail basinで右へ逃げ続けるterminal ladderを、標準Recamán漸化式固有の条件で
> 排除することである。upwardかつparity-compatibleなsuccessorのmass-gap不等式も調べたが、
> 新規実例は4件だけで共通機構がなく、Lean次手には昇格させなかった。eventual-high側のledger・cut-flux・raw candidate課金は反例により停止した。

## 1. 今回証明できたこと

### 1.1 low candidateから有限terminal episodeを必ず抽出できる

`TargetCandidateTransitions`に次を追加した。

- `candidateBelow_entry_first`: tail内のlow candidate landingはfirst occurrence
- `FirstAt.exists_maximal_freshCombEpisode`: 各fresh landingは有限 maximal comb suffixを持つ
- `FreshCombEpisode.historyTerminated_of_next_not_step`: maximal suffixはhistorical blockerで停止する
- `candidateBelow_exists_historyTerminatedComb`: 各tail lowから`HistoryTerminatedComb`を抽出する
- `unbounded_historyTerminatedFinal_of_unbounded_candidateBelow`: lowが任意に遅く現れるならterminal finalも任意に遅く現れる

有限性は、各comb periodでlow railの自然数値が1ずつ厳密に下がることから強帰納法で得た。
これにより、経験的に見えていたmacro episodeは任意の仮想missing-target tail上でも存在する。

### 1.2 terminal blockerを既存semantic rankへmountできる

`TargetCombSemanticMount`で、terminal blockerのhistorical normal nodeが
`ExtendedHistoryNormalInvariant`、`OrbitReadyRefinedInvariant`、`PhaseSemanticInvariant`を満たすことを証明した。
完成episode内部では ready debtからhistorical normalへのstrict progressが得られる。

時間順の二episodeについてはexactに次へ縮約した。

```text
later entry < earlier blocker
または
earlier blocker < later blocker
```

左枝はlater blocker normalへのsemantic progressになる。右枝もearlier blockerが
`upperTri tailStart`を越えていれば、time ancestryがceilingを跨ぐためsemantic childへmountできる。

### 1.3 finite basinの残余をexactにした

任意のhistorical anchor `r`からfuture terminalを比較し、Leanで

```text
future terminalからsemantic progress
または
r ≤ future blocker
```

を得た。しかし後者は、現在のmacro帰結だけでは排除できない。Lean認証した
`finiteBasin_rightLadder_countermodel`は

```text
blocker j = r + j
entry   j = r + j + 1
```

と置き、fresh intervalの全順序、blockerの一回使用、unboundedness、直前fresh値からの
historical provenanceを全て満たしながら、一度も`entry j < r`を起こさない。
これは標準Recamán軌道の反例ではなく、現行macro interfaceだけでは不足することのno-goである。

### 1.4 eventual-high候補のcausal APIと反例

`HighCandidateCausalReuse`で、正のforced-addition candidateには必ず以前の`FirstAt`があり、
同じcandidateを異なるclockで使えばforced output値はstrictに増えることを証明した。
同時に標準prefix上で次をLean認証した。

- target 19が未出の間、candidate 285をclock 173と1325で再利用する
- 二回目のoutput 2935は既にtime 1313で出現済み
- target 4が未出の間、candidate 63と39が別clockで同じoutput 265へ衝突する

従ってcandidate one-use、fresh-output charging、output injectionはいずれも偽である。

### 1.5 time ancestry、finite ceiling、cut flux

- blockerのfirst occurrenceからpre-tail rootまたはtarget-above parentへ戻るtime ancestryをLean化
- pre-tail値を`upperTri tailStart`で一様に抑え、ceilingを越すanchorではnormal progressを得た
- 相異なるterminal final timeが十分あればblockerが任意の有限boundを越える有限鳩の巣定理を証明
- cut clipの1-Lipschitz性とpath signed-flux / positive-negative crossing balanceをLean化

cut balanceはendpointの望遠和であり、両endpointがcut上ならsigned massは0になる。
pre-tail reuseを抑えるcapacityにはならないため、独立攻略としては停止した。

### 1.6 right-ladderに対するclock制約

`TargetLadderClock`で、tail low entryへのincoming transitionがlegal subtractionであること、terminal final
`F=s+2k`の直後二clockがforced additionで

```text
a(F+1)=blocker+F+2
a(F+2)=blocker+2F+4
```

となることを証明した。singleton unit ladderの次fresh entry `blocker+2`は、exact transitionとtriangular parityから
`nextTime≥s+5`を満たす。しかし`s_j=6j`はこのgapとparityを無限に満たすLean countermodelである。
clock/legalityだけが与えるのはsparsityで、no-escapeではない。

20Mではhistory edge 2,655、singleton episode 381に対し、`next blocker=previous entry`は0件だった。
従って次に必要なのはclock密度ではなく、fresh low entryが後のterminal blockerへ戻ることを禁じる
visited-sensitive no-returnである。

ただし無条件のno-returnは標準prefixで偽だった。Lean認証反例はtarget 4の三episode

```text
(s,k,entry,blocker) = (38,13,39,25), (77,11,75,63), (111,0,40,39)
```

で、entry 39が介在episode後にterminal blockerとして戻る。一般に後のblockerが古いfresh interval内に
入るならinterior railには入れず、古いentryと等しいこと、legal originなら後の長さが`k₂+1<s₁`となることは
Leanで証明した。20Mでは過去rail由来blocker 857件が全てentry由来だったが、immediate same-target predecessorの
entry再利用は0/2,655である。従って候補は無条件no-returnでなく、間に別terminalを挟まない
`TargetMacroSuccessor` gated no-returnへ狭まった。

このgateを`TargetMacroSuccessor`としてLean実装した。二本のterminal comb、tail/chronology/両端lowに加え、
open intervalの全candidateがstrict highであることだけを保持する。そこから入口legal、間に同target terminalなし、
次startの3-clock gap、区間全体の`TargetHighCandidateExcursion`を導いた。entry再利用が起きる場合は
`TargetMacroEntryReturnResidual`へ縮約され、blocker equality、first occurrence、生成predecessor式、
後combの短さ、fresh successor final、high excursionを全て保持する。ここから先はhigh区間内の
visited-history evolutionが必要で、現行APIからno-return自体はまだ出ない。

さらにentry-return residualをLeanでexactに二分した。旧entryがsuccessor high word内でcandidateとして
再露出するなら、既訪問性によりforced additionとなり、terminal repaymentでの再露出との間に
`same_positive_forcedCandidate_reuse_bundle`のexact subtraction balanceを持つ。再露出しないならhigh word全体が
旧entryをavoidし、terminal repaymentで初めてmandatory exposureする。前者はoutput freshnessがなく、後者は
causal-reuseの最初のendpoint自体がないため、現行APIだけのimmediate no-returnはここで停止した。

### 1.7 same-candidate reuse balance

`ForcedCandidateReuseBalance`で、同じ正candidateがpre-times `p<q`で再利用されると

```text
2(subSum q-subSum p) + (q-p) + upperTri p = upperTri q
```

となるexact subtraction paymentを証明した。forced版は共有するearlier `FirstAt`も返す。
しかしcandidateごとの全reuseを足すとfirst/lastへ望遠和し、中間の再利用回数は消える。
さらにtarget 19が未出の標準prefixでcandidate 502, 499, 496, 493, 490のreuse intervalsが
5重に重なることをLean認証した。strict high block内のactive overlap depthも200kの21から2Mの427へ増えた。
集約にはunboundedに見えるmultiplicityが残るため、独立なoverlap上界なしでは停止する。
さらにactual reuse intervals `[296,340)`と`[298,342)`のproper crossingをLean認証した。2Mでは
crossing pair 181,987、pairwise-crossing clique最大427で、laminar/stack/small-crossing分解は偽である。
nesting反例もあるためone-queueでもなく、interval-orderによるmultiplicity除去は有望度3/100として完全停止した。

### 1.8 任意長のseeded high corridorという局所no-go

`SeededHighCorridorNoGo`で、任意の有限長`L`に対してtarget 1を欠く有限historyをseedし、実際の
`Basic.step`が`L`回すべてhigh candidateの既訪問によりforced additionを選ぶfamilyを構成した。
値は`L+2+upperTri j`で、偶数`L`なら標準列のmod-2 triangular parityにも両立する。

これはcanonical initial stateからの到達可能性を主張しない。しかし有限符号語、high条件、target omission、
実history membership、interval ledger、parityの任意の組合せだけではuniform corridor boundが出ないことを
Leanで確定する。eventual-high枝の再開にはcanonical prefix固有のgeneration-versus-reuse chronologyが必要である。

## 2. exact computationで分かったこと

### 2.1 low-to-terminal extraction（20,000,000項）

| quantity | result |
|---|---:|
| low candidate states | 5,779,967 |
| history rail mass | 5,776,535 |
| any completed railで被覆 | 5,779,954 |
| true orphan | 13 |
| history orphan | 3,432 |
| 最大rail長 | 159,583 |

history orphan 3,432は、true orphan 13、target episode 1、horizonでcensorされた現episode 3,418に
exactに分解した。最大episodeでのrail重複はなく、low-to-terminal抽出を強く支持する。
一方、全suffixを数えると同一lowのmultiplicityは最大159,583で、uniform fiber boundは偽である。

### 2.2 right-recordとancestry

- 標準prefix 4Bではtarget-gated upward reset 29/29がglobal right record
- ただしarbitrary seeded actual orbitではtarget条件を保ってgap-insertion resetを構成できる
- 20Mでupward reset 20件、ancestry最大60,651 hop、edge最大再利用7
- current blockerがpre-tail maximum以下へ戻る例、ceiling超過後の再侵入を多数確認

right-recordは標準prefixの強い経験則だが、現行local/macro仮定からは導けないため診断指標へ降格した。

### 2.3 eventual-high causal reuse（2,000,000項）

| quantity | result |
|---|---:|
| high forced uses | 430,600 |
| output revisits | 98,593 (22.9%) |
| same-candidate最大reuse | 13 |
| same-output最大multiplicity | 16 |
| first-use age最大 | 1,785,560 |

reuseはhorizonを200kから2Mへ伸ばすと10から13へ増えた。high-only block内でも同一candidate再利用があり、
局所的なinjectivity回復は起きない。

### 2.4 finite-basin remount（20,000,000項）

| quantity | result |
|---|---:|
| terminal ancestry paths | 2,660 |
| target別distinct pre-tail roots | 860 |
| root reuse最大 | 629 |
| remount resolved / unresolved | 2,535 / 125 |
| distinct root resolved / unresolved | 851 / 9 |
| escape待ち最大 | 653 episodes |

未解決9 rootは全てtarget occurrenceまたは20M horizonによる有限censorであり、有限反例は見つからなかった。
distinct unresolved率は200k、2M、20Mで`5.56% → 1.43% → 1.05%`と低下した。一方、最大待ちは
`12 → 156 → 653`へ増えたためuniform waiting boundは棄却する。残る経験的候補は、各fixed rootについて
いつかfuture terminal entryがroot未満へ戻るという非一様no-escapeである。

escape前のfresh intervals `I_i=[blocker_i+1,entry_i]`に対して

```text
Q_k = Σ_i (entry_i - blocker_i)
```

を置くと、20Mの860系列・7,390 waiting episodesで

```text
#waiting ≤ Q_k ≤ maxEntry_k-root
2 Q_k ≤ escapeStart-sourceStart        （resolved時）
```

に違反はなかった。前二式はfresh intervalのdisjointnessとseparator、最後はcombのclock幅から出る
proof-facing候補である。従ってno-escapeが無限ならfresh massとentryは非有界になる。ただし最大待ち653の例でも
hull密度22.75%、clock占有率56.62%で大きなslackが残り、fresh mass単独では矛盾しない。

各episodeについては局所恒等式

```text
entry = blocker + k + 1
2(entry-blocker) = (finalTime-start) + 2
```

を`entry_eq_blocker_add_length`と`twice_entry_gap_eq_duration_add_two`としてLean化した。
さらに二つの時間順episodeについて、両blockerがfixed root以上なら区間幅の和が
`max(entry₁,entry₂)-root`以下となる`two_interval_mass_le_hull`もLean化した。

`Q`とblocker recordを結合すると、20Mの7,390 waiting transitionsでは下降7,348件すべてで
`q_i≤blocker_{i-1}-blocker_i`、上昇42件すべてで`blocker_i≥old maxEntry`だった。しかしrecord gap
`g_i=blocker_i-old maxEntry`が新たな未課金量として残る。個別`g_i/q_i`は最大365.40、系列累積でも
`gap≤Q+root`に9反例、最大`gap/(Q+root)=13.724`だった。この比は200kから20Mへ増えており、
`Q+O(root)`による閉包は停止する。必要なのはrecord gap内の値をcomb外のglobal historyへ課金する別補題である。

そのglobal-history課金も20Mで監査した。20個の相異なるrecord gaps、総mass 17,820,564のうち、
record時点で既訪問なのは3,045,301（17.09%）、未訪問は14,775,263（82.91%）だった。gap同士はdisjointで
既訪問値のfirst witness再利用は最大1なので、この17%にはdistinct chargeがある。しかし最大gapでも84.14%が
未訪問で、pre-tail由来は全massの0.46%、terminal fresh interval由来は0件だった。従ってgap全体をprior historyへ
比例課金する枝は停止する。再開には未訪問gap値のfuture consumptionまたはmassの有限capacityという新しいglobal theoremが要る。

### 2.5 immediate successorのsharp slack（20,000,000項）

same-target consecutive terminal edge 2,655本で`δ=|b₂-e₁|`を測ると、equalityは0、最小slackは1だった。
単独の`δ≥q`、clock幅、low deficit下界はtarget 4の小prefix反例で偽である。一方、

```text
δ is odd  または  q=e₂-b₂ ≤ δ
```

はodd 1,336本、evenかつ`q≤δ` 1,319本、違反0だった。downward 2,635本のmass枝は既存interval orderから
導けるので、新しい内容はupwardかつparity-compatibleな4本だけである。start 2,000より後のholdoutでは
該当1本しかなく、証拠量は弱いが、証明対象としては非常に小さい。equalityなら`δ=0`はevenかつ`q>0`なので、
このhybridを証明できればimmediate successor no-returnが従う。

entry returnを仮定するとparity-compatibleでなければならないこと、およびparity-incompatibleなら
immediate returnしないことを`parity_compatible` / `entry_ne_of_parity_incompatible`としてLean化した。
しかし残る4例では`δ/q`が2〜87、
`q/high clocks`も大小混在し、既存fieldsから得られる`e₁≤b₂`、`q<s₁`、even parityから
`e₁+q≤b₂`へ進む機構はない。これはnonzeroそのものと論理同値ではないが、現状は過適合寄りと判定する。

## 3. 分岐の更新

| branch | 形式的到達点 | 全射性への有望度 | 判定 |
|---|---|---:|---|
| low → maximal terminal extraction | 各lowから有限`HistoryTerminatedComb` | 70/100 | 最有望の基盤として保持 |
| terminal semantic mount | episode内とlater-entry-left、ceiling超resetを接続 | 65/100 | 保持 |
| `TargetMacroSuccessor` no-return | residualをforced reuse balance / avoidanceへ二分 | 20/100 | 現APIでは停止 |
| upward parity-compatible slack | 20Mの新規4件で`q≤b₂-e₁`、違反0 | 35/100 | 過適合寄り、停止 |
| finite-basin no-escape | exact residual、right-ladder no-go、20Mで851/860解決 | 45/100 | successor/gap入力待ち |
| canonical generation-vs-reuse chronology | seeded任意長corridorが局所論を排除 | 30/100 | 唯一のglobal再開点 |
| eventual-high causal history | earlier `FirstAt` mapのみ成立 | 8/100 | 停止 |
| global right-record | 標準prefixで強いがseeded反例あり | 25/100 | 診断用、直接枝停止 |
| cut / gap flux | exact balanceは望遠和 | 10/100 | 独立枝停止 |
| bounded ancestry / finite root capacity | 長鎖・root再利用 | 5/100 | 停止 |

active direct branchは0本である。これは探索が空になったという意味ではなく、現行補題の組替えだけで
全射性へ届く枝を残していない、という停止判断である。

## 4. 次の研究ロードマップ

次の探索は、既存macro定理を増やすより、right-ladder反モデルが満たせない標準recurrence固有条件を探す。

1. **canonical generation-vs-reuse chronology**: terminal intervalの生成clock、
   blocker first-time、visited集合を同時に使い、`target < r ≤ upperTri tailStart`で永久に`r≤blocker`となる
   right ladderを排除できるかを調べる。一様待ち時間は仮定しない。
2. **fresh-mass / record split**: no-escapeなら`Q`とentryが非有界になる。20Mではblocker rise 42件が全て
   系列内new recordだったため、有限descentかunbounded record riseへ二分し、後者に実際の支払があるかを監査する。
3. **provenance injectivity**: pre-tail rootの再利用回数ではなく、各再利用が消費するfresh terminal certificateへ
   単射する輸送補題があるか。raw candidate/outputでは反例があるためterminal単位に限定する。
4. **global balance**: 上の枝が失敗した場合だけ、comb外のhigh excursionとfuture low entryを同じevent族で数える。
   ledger identity、cut telescoping、right-record gap massの再包装は行わない。

再開gateは、(a) actual recurrenceだけでright ladderを壊す補題、(b) terminal利用ごとのdistinct fresh certificate、
(c) eventual-high tailを直接排除するstrict rankのいずれかである。

## 5. 検証

- `./scripts/check.sh`: 229 build jobs、1,075 declarationsの公理監査、禁止proof escape監査を通過
- 許可された依存公理: `{propext, Classical.choice, Quot.sound}`のみ
- `sorry` / `admit` / `native_decide` / user axiom: 0
- 新規・更新した7本のC++ probeをC++20 `-Wall -Wextra -Wpedantic -Werror`で再コンパイル
- 主要probeの200k regressionとsuccessor slack 20Mを再実行し、protocol/parity/order違反0
- manifest: 227 Lean modules、153 human-proof reports
- `status.html`: HTML parser通過、1280pxでhorizontal overflow 0、29 evidence cards、filter操作を確認
- `git diff --check`: 通過

計算結果は仮説選択にのみ用い、Lean定理の仮定にはしていない。
