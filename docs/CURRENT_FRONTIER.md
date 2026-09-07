# Current research frontier

最終更新: 2026-09-07

この文書を、研究状態と次の研究gateに関する唯一の正本とする。個々の主張の証拠は
[`EVIDENCE_REGISTRY.tsv`](EVIDENCE_REGISTRY.tsv)、Lean kernel上の公理依存は
[`Recaman/Audit.lean`](../Recaman/Audit.lean)を正本とする。

## 結論

研究の目標は標準Recamán数列の全射性の真偽を決着させること。全射性・非全射性はともに未証明である。
全射性の命題の証拠レベルは`CONJECTURED`。現在、決着へ直結するactive direct branchは0本である。
#70・#71・#61、および5パターンの並列調査は判定を完了した。

続く[#73第1pass](ISSUE73_PERIODIC_SUPPLY_2026-09-07.md)で、全periodの符号語に対する
**lag≤7の供給容量U7≤Dと、正符号和なら短い供給を持たない加算が存在すること**をLeanで証明した
（E-071）。実過去窓とP2の両方向の一致、lag11の供給と両立する陰性対照もAuditへ登録した。
全lagのE-067/E-070は未解決で、#73はOPEN。E-072・E-073・E-074・E-075のselector・rank・単純予算を停止し、
E-076・E-077・E-078の有限証拠は一般証明と分ける。次は長い供給区間を共通の仕組みへ結び付ける問題が残る。


最新の[並列調査と順位](PARALLEL_APPROACH_TRIAGE_2026-09-07.md)では、次に掘る候補を
**周期符号語の供給不足**へ絞り、[issue #73](https://github.com/hirokidaichi/recaman-lean-research/issues/73)を作成した。有限履歴のeventually periodicな実更新は、各加算phaseに
有限lagの供給恒等式P2を要求する（`E-065`, `PROVED-PAPER`、独立監査済み）。
それを全加算phaseで同時に満たす正符号和の語は存在しない、という命題は`CONJECTURED`（`E-067`）。
period≤18の229,045語と別の90,640評価では反例0だが、一般証明ではない（`E-066`, `COMPUTED`）。
強化した供給phase数の容量不等式も未証明（`E-070`）で、最古Sへの単射案は反証済み（`E-069`）。
これは固定blockによる帰納の可否を判断する構造研究であり、永久欠損へはまだ接続しない。

他の限定候補は停止：同じ集計値から異なる2step到達が生じる履歴対（`E-061`）、SS入口でも
blockerの早い初出を要求できないcanonical反例（`E-063`）、連結supportへ補修できるsurvival反例族
（`E-064`）、全有限穴集合が空になり得るhole-only抽象（`E-068`）。
初出を逆算したold rail輸送と入口分類は`PROVED-PAPER`の部分結果（`E-062`）だが、
canonical生成を分離する新しい不等式ではない。5方式全体の不可能性を示したとは扱わない。

最新の[戦略地図](STRATEGY_MAP_2026-09-07.md)は、#70のLean証明と#71の分類・停止判断、#61の既存証明統合を記録する。
#61では認証済みの19@99734をno-low補題へ接続し、完全なpermanent-tail replayのclock112を
追加仮定なしに排除した。clock下界113・target下界115は`PROVED-LEAN`（`E-060`）。
これは既存の有限残余の解消であり、大域機構の発見や停止済みfloor列挙の再開とは扱わない。
詳細は[#61仮説カード](HYPOTHESIS_CARD_2026-09-07_CLOCK112_CLOSURE.md)。
前回の自由cutoffと固定prefixの監査も維持する。
`∀ B, ∃ N, ∀ n≥N, B<a(n)` は無条件に `PROVED-LEAN`（`E-052`）。
従って自由なeventual landing floorだけでは永久欠損は出ず、canonicalの4の遅い出現が
cutoffを取り違える推論の反例になる（`E-053`）。旧 `E-028` のrouteは `STOPPED`。
同じ検証済みcutoffから先を排除する定量入力は未解決である。

local survival比も追加前史なしには閉じない。density・parity・one-useを全て満たすexact seedに
比を破る59→1のno-wrap continuationがあり（`E-054`, `PROVED-LEAN`）、任意の固定finite prefixを
含めても破れる反例族を得た（`E-056`, `PROVED-LEAN`）。一方、preload-freeな20,001軌道の
2,677,448適用recordではT=1 survival比に違反0（`E-055`, `COMPUTED`）。
canonicalやpreload-freeでのsurvival比の一般命題は未証明。新候補 `7J≤3(v-u)` はcanonical
200億項のholdoutで5件破れた（`E-057`, `REFUTED`）。係数修正は停止し、反例のphase/birth
分類を完了した（`E-058`, `COMPUTED`）。31,058値を二つの隣接producer railへ分類したが、
独立した大域不等式は得られず正のsurvival攻略は`STOPPED`（`E-059`）。
一般seeded countermodel族は#70で全payloadのLean認証を完了した。

形式化済みのresidual kernelは、仮想missing tailをeventual-high corridor（A枝）または
fixed-root target-low stream（B枝）へ送る。A枝は「欠損値非有界」またはrigid burst streamまで
縮約済みだが、burst streamを排除するfixed-seed ancestry/drift枝は停止条件に到達した。
B枝のreset repaymentも、新しいglobal invariantがないため停止中である。

停止は命題の否定を意味しない。fixed-seed infinite supply no-goとreset repaymentのexact命題は
未反証だが、それらを現在のpayloadから導く証明ルートが尽きた、という判定である。

## 現在の分岐

| 分岐 | 現在得られているもの | 証拠 | 判定 |
|---|---|---|---|
| 全射性 | `∀ m, ∃ t, a t = m` | `E-001` | `CONJECTURED`、active direct branch 0 |
| residual kernel | 仮想missing tailのA/B exact二分 | `E-002` | architectureとして保守 |
| A: divergent candidate | candidate発散なら永久欠損値が非有界 | `E-004` | 構造的代償。矛盾ではない |
| A: recurrent burst | 欠損非有界またはrigid burst stream | `E-003` | supply no-goだけが未決 |
| A: demand birth | subtraction/addition birth分類、addition枝のclock contraction | `E-005` | `PROVED-LEAN`の再利用可能部品 |
| A: periodic schedules | balanced有限核とeventually-periodic no-go | `E-006`, `E-007` | 非周期scheduleは未排除 |
| A: supplier ancestry | forced class非閉包、generic parent merge | `E-008` | `REFUTED` |
| A: one fixed seed | 内部供給つき3-use有限例、infinite no-goは未決 | `E-009`, `E-010` | 現proof branch `E-011`は`STOPPED` |
| A: admissible seed density | 既知seedはすべてcanonical density（`valuesThrough_length`, `a_le_upperTri`）に違反 | `E-019` | `COMPUTED`、gate 3の最初の拘束的候補 |
| A: preload-free orbits | 20,001 orbit・1.27M burst useにsame-candidate link 0件（strict-high形・c-floor形とも） | `E-020`, `E-021` | `COMPUTED`、c-floor link no-goは`CONJECTURED` |
| A: cone excursions | burst後のstrict-high excursionは倍化clock前に崩れ、cone-exterior runは2倍へ届かない | `E-022`, `E-023` | `COMPUTED`、excursion boundは独立`CONJECTURED` |
| A: local use gap | `sqrt(6m)`のlocal読み | `E-012` | `REFUTED`、修理も`STOPPED` |
| A: external blocker collision | same-candidate H4/H8 test | `E-015` | 20Mまで評価母集団0、設計を`STOPPED` |
| A: window collision | 異candidate dyadic window集約の`E ∩ S` | `E-016` | 17適用windowすべて交わりなし、`REFUTED` |
| A: demand provenance | 減算初出はnear-diagonalが多数、加算初出はtruncatedが約3割 | `E-017`, `E-018` | `COMPUTED`、最小証人は`PROVED-LEAN`。gate 3の制約条件 |
| B: reset repayment | exact命題は未反証、local bridgeは枯渇 | `E-013` | `STOPPED` |
| 独立部分定理 | `TailHall₃`候補 | `E-014` | `CONJECTURED`、全射性の直接枝ではない |

## 証明frontierの最短形

```text
least missing target
  -> exact residual kernel
     |- A: eventual-high candidate corridor
     |    -> missing values unbounded
     |       or rigid recurrent burst supply
     |          -> fixed-seed infinite supply no-go is open
     |          -> current ancestry/drift proof route is STOPPED
     |
     `- B: fixed-root target-low stream
          -> infinitely many upward resets
          -> reset repayment proof route is STOPPED
```

この図の矢印は証明済みの依存と未証明義務を区別する。最後の二つの`STOPPED`を
同値なcoverage、future return、canonical reachabilityで置き換えてはならない。

## 再開条件

A枝を再開するには、次のいずれかを先にexactな仮説カードへする。

1. external addition blocker集合`E`について、cutoff-independentに`|E|`が非collision量に対して
   strict growthする不等式（`E ∩ S`型のcollisionは同一candidate形・window集約形ともに閉鎖済み）。
2. reuse intervalのcrossingやparent merge後にも保存される非merge質量。
3. arbitrary finite stateと`stateAt start`を、future returnやtarget occurrenceを仮定せず分離する
   canonical-only invariant。
   最初の候補はhistory density（`|seen| ≤ clock+1`、`max seen ≤ upperTri clock`）である。
   `H-20260902-03`により、既知の固定seed反例は全深度でこの拘束に違反する（`E-019`）。次のunitは
   blockerをpreloadせずexact prefixで生成するadmissible synthesizerか、admissible seedのuse数上界の
   紙上証明でなければならない。
   `H-20260902-04`はpreloadなしの単一初期値generalized orbit 20,001本（内部供給burst use 1,272,765件）で
   strict-high same-candidate linkが0件であることを示した（`E-020`）。exact命題「generalized orbitに
   strict-high linkは存在しない」を`CONJECTURED`として登録し（`E-021`）、許可されるformalization routeは
   「最初のlinkがpreloaded blockerを強制する」紙上証明のみとする。
   **意味上の注意**：strict-high（candidate > clock）は2026-09-01のfixed-seed protocolの
   use間条件であり、corridorの実際の条件（least recurring candidate cに対しcandidate ≥ c）より強い。
   そこでprobeにc-floor mode（中間candidateが全て≥c）を追加して再検査したところ、censusは不変で
   link 0件だった。従って`E-021`はc-floor形（corridor-faithful）で登録する。一方`E-023`の
   excursion boundはcone-exterior条件に依存する独立部分命題であり、corridor streamを排除しない
   （`E-022`参照）。同様に、2026-09-01のfixed-seed 3-use記録はstrict-high形の記録であり、
   c-floor形での固定seed探索は未実施である。

2026-09-02の最初のexternal collision unitは、同じcandidateの4回または8回のsupplied useで
`E ∩ S`を要求した。しかしcanonical 20Mでは4,798 useに対し4,797 candidate、最大use数2で、
既知fixed seedも3-useに留まるため評価母集団が空だった。この閾値設計は`STOPPED`とし、上の
再開条件1を満たすには異candidate間または固定clock windowで集約される非空なdebt量を要求する。

2026-09-02の第二unit（`H-20260902-02`）はその要求どおり、異candidate・dyadic window集約の
collision `E(W) ∩ S(W) ≠ ∅`、減算初出需要の半clock縮約`2t < w`、加算初出需要の非truncated性
`2b < w`の3命題を凍結した。3命題ともcanonical discovery 2Mで反証され、holdout 20Mでも
17適用windowすべてで`E ∩ S = ∅`、near-diagonal減算初出1,533件、truncated加算初出732件だった。
従ってcollision型のdebt設計は同一candidate形（空虚）と集約形（反証）の双方で閉じ、再開条件1は
`|E|`のstrict growth形だけを残す。再開条件3のcanonical-only invariantは、canonicalで多数派である
near-diagonal減算sourceを許容しなければならず、birth-clock縮約では固定seedと分離できない。

B枝を再開するには、post-reset blocker birthをfuture repayment、target occurrence、canonical
reachabilityなしに有限化するglobal invariantが必要である。

`TailHall₃`は、全射性ではなく`liminf a_n/n ≤ 3`型の独立部分定理としてのみ再開できる。

いずれも、exact statement、acceptance test、frozen falsifier、stopping conditionを持つ
hypothesis cardが作られるまでactive branchへ昇格しない。

## 2026-09-02 午前の方針転換（真偽を問わない証明計画）

全射性が偽でもよいという方針のもとで、
[`RESEARCH_ROADMAP_2026-09-02_TRUTH_AGNOSTIC.md`](RESEARCH_ROADMAP_2026-09-02_TRUTH_AGNOSTIC.md)
を作成した。要点は次の通り。

- `E-024`（`COMPUTED`, canonical 3e9）: sub-diagonal着地は28.6%で安定し、A枝の無限corridorは
  経験的に全targetで偽である。小さな高さはdescending chain（2時刻で高さ3減、既存のcomb）でしか
  現れず、[1e8,1e9)の47件は1本のchainだった。mex 1355はchainの剰余類（mod 3）が合わず着地できない。
- `E-025`（`PROVED-LEAN`, `MissingDensityDichotomy`）: 二分定理D「無限個のnで`a n ≤ n+2`、または
  全ての窓`[0, m+2]`（`m ≥ 2N+2`）に`m ≤ 4·|missing|`を満たす永久未訪問値のNodupリストがある」。
  系`EventualHighCandidateTail.missing_density`はA枝が密度1/4の欠損を含意することを、
  `not_eventualHigh_of_recurrent_low`は`a n ≤ n+2`の再発が全targetのA枝を否定することを示す。T1完了。
- `E-026`（`PROVED-LEAN`, `DescendingChain`）: chain補題（T2）と遅延着地の特徴づけ`late_landing_iff`（T3）。
  強制加算、帯への着地（高さ`h−3`）、k段の降下`chain_descends`、mod 3剰余類、上方脱出と遅延着地の2出口。
- `E-027`（`COMPUTED`, Chaffin 10^612項）: 下降弧は1 decadeあたり8.45本で一定だが深さ比の裾は急峻で、
  10^41以降10^7未満の着地はない。852655は10^612項まで欠損、1355の初出は第3.25×10^11項。
  真偽の見立ては非全射側に大きく傾いた。
- `E-029`（`COMPUTED`, run-length simulator 10^13）: 1355の初出とmex推移がOEISと一致。2^20未満の遅延着地は
  1 decadeあたり約2.3分の1に減り、10^12台では30件。高さ≤1356のinterior時刻は各decade数百〜二千件で、
  [1e9,3e9)の0件は揺らぎだった。
- `E-030`（`PROVED-LEAN`, `HoleHopping`）: chainは自クラスの最初の未訪問candidateに着地し、小さい値への着地後は
  連続する穴を掃く（comb）。小さい値の領域の力学は「穴の集合の上の剰余類ゲーム」である。
- `E-031`（`COMPUTED`）: 帯の生存を無制限とした閉包はChaffinの穴をほぼ全て（852655を含む）埋めるので、
  852655の保護は剰余類の組合せではなくarcの深さ（帯の生存）に依る。
- `E-032`（`COMPUTED`）: 区間の終端は遅延着地61%・帯の既訪問値39%。帯の未訪問run長は典型的に`n·10^−6`。
- `E-034`（`PROVED-LEAN`, `PopupLock`）: pop-up後に `2c+v+2` が既訪問なら `k=3/4` に固定され、その間 clock 未満の値は
  訪問されず、`k=2` 候補は弧自身の直前の `k=2` 値である。arc trace の終端機構の局所部分は全て Lean 化された。
- `E-035`（`PROVED-LEAN`, `LevelTwoThree`）: pop-up後に `2c+v+2` が未訪問なら `k=2` へ戻り、`k=2/3` ping-pong は
  1対ごとに offset が5減り、K対後の `k=1` への出口では位置エネルギー（値+時刻）が `2m+s−K`、すなわち
  段の直前より `K−1` 低い。Φ を下げる唯一の局所機構が Lean 化された。
- `E-033`（`COMPUTED`, arc trace 10^10）: 弧の底は最後の遅延着地であり、深い弧6本の底はcomb末端で
  `2c+v+2` が既訪問のとき `k=3/4` に固定される（6/6）。その値は同じ弧が少し前に `k=2` 値として
  訪問していた。（旧版の「終端は Φ の落差で記述できる」は `E-036`/`E-037` で撤回。）
- `E-036`（`COMPUTED`, arc potential probe 10^10）: 「固定 ⟺ `Φ=2·時刻+高さ` の落差 ≥ 3」は偽。blocked かつ
  落差 < 3 が 318 件（test 値は前の弧の `k=4` 値）、fresh かつ落差 ≥ 3 が 2,745 件。底 = 最初の落差 ≥ 3 の
  comb 末端は 0/39。Φ の減少は `k ≥ 3` を経由する区間でのみ起こる（45,859 件、`maxk ≤ 2` は 0）。
- `E-037`（`COMPUTED`, arc death-rule probe 10^10）: 固定は通常破れる（break 15,926 / wrap 8 / `k=5` へ 3,452）。
  break 添字は `i_gen=(T−1)+⌊(J_eff+2)/3⌋`（12,777/15,926）、固定のまま剰余が尽きる条件は `v<13+7·i_pred`
  （7/1/0/15,926）。36 弧の底は全て comb 末端で、弧の終わりは wrap 8・break 後に穴なし 11・fresh 後に
  穴なし 15・`k=5` 後 2。landing floor は「剰余の残量と帯の run で費用が決まる hole-hopping の降下が
  852656 に届かない」命題に更新（カード受入条件 3）。
- `E-038`（`PROVED-LEAN`, `LockResidue`）: 剰余則 `(q,r)→(q±1,r−q)`（`q≤r`）と剰余の跳ね上がり（`r<q`、ステップ種に
  よらず弧が終わる）、固定の 1 対で剰余が 7 減ること、予算 `t<m+7`（comb 末端座標で `v<13+7K`）で対の内部に
  剰余増加が起きること、着地前 run が J 対なら固定が `⌊(J+2)/3⌋` 対以上続くことを Lean 化。`E-037` の wrap 条件と
  T=1 の break 下界（10^10 で 2,658/2,658）の局所部分が定理になった。
- `E-039`（`PROVED-LEAN`, `PingPongRuns`）: 任意 level `p+2/p+1` の ping-pong の 1 対で剰余は `2p+3` 減り、K 対の run の
  上側値は `a m + k`、下側値は `a m − (m+k+1)` の連続 run（候補の既訪問/未訪問だけで記述）。既訪問候補は加算を、
  未訪問候補は減算を強制する。chain(p=0)・k=2/3 段(p=1)・固定(p=2) の共通形で、blocker provenance
  （`H-20260903-01`、[card](HYPOTHESIS_CARD_2026-09-03_BLOCKER_PROVENANCE.md)）の仮説 (B) の裏付け。
- `E-040`（`PROVED-LEAN`, `CombExit`）: T 本の歯の comb の加算値 `i+v+2−s` が、test 値未訪問後の k=2/3 段の出口候補
  `i+v−2−3k`（`3k+5 ≤ T`）を塞ぐ。段は `⌊(T−2)/3⌋` 対以上続く（`popup_lock_persists` の fresh 側対応物）。
  provenance census（10^9）で entry23 blocker の 85% が同じ弧の level-1 値、その主成分が gap=7 の comb 加算値
  だったことの exact な説明。
- `E-041`（`COMPUTED`, blocker provenance 10^10、`H-20260903-01` は `REFUTED`）: 降下を塞ぐ値 52,228 件の初訪問を
  全数調査。lock 側（test/lockcand/l3）は全て level ≥ 2 で 96% が**同じ弧自身**の run（k=2/3 段の下側 run、chain の
  上側 run、以前の固定の k=3 run）、残りは前の弧の k=4 固定 run（`n/c ∈ [0.44,0.62]`）。fresh 側（entry23/bandexit）は
  同じ弧の level-1 値が 87%（comb の歯 4 の加算値 = gap 7、`CombExit`）、前の弧の k=2 値（`n ≈ c/2`）が 12%。
  99.78% が ping-pong run に属し、例外は梯子・スパイク・谷のみ。**帯の履歴は「同じ弧の直近の run」と「前の弧の
  時刻 ≈ c/2 の run」で決まる**（スケール半減の自己相似）。[epoch report](BLOCKER_PROVENANCE_EPOCH_2026-09-03.md)。
- `E-042`（`PROVED-LEAN`, `H-20260905-01`）: no-wrap 予算 `13+7k≤v` と comb 末端より早い clock
  `n<c=i+1` だけで、lock candidate `w=2c+v−1−3k` は sharp な `2n+14+4k≤w` を満たす。
  positive `n` では `2≤w/n`。従って `E-041` 後続候補 (A') の `lockcand` level 下界も
  provenance を使わない算術的帰結であり、この枝は landing floor の causal input として `STOPPED`。
  再開条件だった具体的run帰属は `E-043` で調べ、`E-044` のno-goまで進んだ。
- `E-043`（`COMPUTED`, `H-20260905-02`）: `lockcand` 初訪問を same-arc `q=2` の upper/lower/both
  ping-pong rail、run外の `SSSS` ladder / `SSAA` valley、または直前arc `q=4` の `SSSS` ladderの
  6型へ凍結分類した。`c<10^10` の609件と未使用holdout `10^10≤c<2·10^10` の274件は無修復で
  全て分類され、time/budget/formula/flag/gap-cost違反も0。一般定理ではなく200億までの有限証拠。
- `E-044`（`PROVED-LEAN`, `LockResidue`）: same-arc型の `q=2` 分解 `w=2n+r` は
  `2(c−n)+12+4k≤r` と `2(c−n)+13+4k≤n` を課す。一方、任意の `M` に対して一つのlocal
  `(n,r,w)` が `M` 個の異なる後続event式・no-wrap予算と両立する弱化history countermodelもLean化。
  実測でもevent arc当たりのquery最大数は129から196へ増えた。local producer分類だけからuniform
  bounded charge / landing-bottom descentは出ないため枝は `STOPPED`。再開にはactual arc survivalを使う
  strict descentまたはfinite-to-one chargeが必要。[epoch report](LOCKCAND_PRODUCER_EPOCH_2026-09-05.md)。
- `E-045`（`COMPUTED`, `H-20260905-03`）: actual arc survivalへ戻り、同じcompleted arcに後続late
  landingを持つblocked comb endの必要条件候補 `7·hPrev≤16·v`（run identityにより
  `7T+21J≤9v`）を凍結した。既存discovery 19,365件、10^10時点でopenだった第40弧のpre-cutoff
  352件、未使用holdout `10^10≤c<2·10^10` 6,391件で違反0・identity違反0。第40弧は
  `a(13808214835)=1814`を底として完了し、この新terminal recordもthreshold未満に入った。
- `E-046`（`PROVED-LEAN`, `LockResidue`）: `T=1`ではthresholdの逆向き
  `16v<7(v+1+3J)`がpre-landing runを最初のresidue-budget failure pairまで持続させる。
  level-3側freshnessの下で`popup_lock_wrap_of_long_prelanding_run`がpair内residue increaseを強制し、
  threshold未満terminal 9件中T=1 wrap 7件の機構を説明する。
- `E-047`（`PROVED-LEAN`, `H-20260905-04`, `LockResidue`）: multi-toothではfinal lockの
  `k<T-1`候補がearlier-tooth test値そのものであることを使い、その値がfinal landing時までに既訪問という
  actual-history仮定とshiftしたpre-landing runを合成する
  `popup_lock_wrap_of_multitooth_history`を証明。唯一のthreshold未満`T=2` terminalはこの条件と数値的に
  整合する。一方、同membershipは全`T≥2` recordの21,563/45,889件にしかなくcomb形だけでは導けない。
  一般survival比は`CONJECTURED`のままで、残余はmembershipをarc survivalから強制するedgeと
  `l3blocked` survival。
- `E-048`（`PROVED-LEAN`, `H-20260905-05`, `PingPongRuns`）: 一般levelの
  `pingpong_pair_wrap`はresidueがpair費用`2p+3`未満なら二歩内のincreaseを返す。`p=3`を反復runへ
  適用した`level45_run_wrap`は`9K≤r<9(K+1)`でpair `K`のwrapを強制し、threshold未満terminal
  `c=99734,v=19`の`5A 4S 5A 3S`（初期residue 9）を説明する。
  `popup_l3blocked_level45_entry/wrap`がpopup座標からこのkernelへのbridgeも与える。通常の
  `l3blocked`後に必要なfresh/blocked historyが何pair続くかは未証明。
- `E-049`（`REFUTED`, `H-20260905-06`）: completed-arc l3blocked 4,844件のinitial level-5/4 runを
  exact追跡。discovery 3,478件はwrap 1 / upperBlocked 628 / lowerFresh 2,849、holdout 1,366件は
  0 / 223 / 1,143で、wrap index違反0。しかしterminal `c=588583`はbudget 532 pairに対し43 pairで
  `lowerFresh`へ離脱し、offset 1350で後からwrapするため「terminal iff initial budget wrap」は反証。
  個別traceでは後続がupper residue `4393-7j`のlevel-4/3 phase 628点であることをexact確認した。
  first-exit classifier枝は`STOPPED`。再開にはlevel下降を跨ぐphase間のglobal descentが必要。
- `E-050`（`PROVED-PAPER`, `H-20260906-01`）: phase capacity
  `B(q,r)=floor(r/(2q-1))`と`alpha·n+beta·x+psi(q)`の和は、exact seeded lowerFresh族と
  upperBlocked族により全係数が排除され、連続positive-length phase間のstrict descentもnonincreaseも
  与えない。seedはhistory cardinality、triangular range、canonical parityを満たすが、全seed memberの
  initial-0 first-birth provenanceは要求しない。従ってこの限定classは`STOPPED`であり、全canonical
  invariantのno-goとは扱わない。
- `E-051`（`COMPUTED`, `H-20260906-02`）: completed canonical arcの`l3blocked` event後、最初のwrap
  またはlate landingまでの同一positive blocker多重度`<=2`を凍結検査。discovery `s<=600000`は
  17 excursion・6,305 use・最大2、holdout `600000<s<=2000000`は22 excursion・12,802 use・最大1、
  違反0。一回使用は`c=97896,w=395922`の二回使用で偽。all-scale boundは`CONJECTURED`で、
  survival ratioへ接続するweight inequalityなしにはLean化しない。
- `E-028`（`STOPPED`, `H-20260902-05`）: 自由cutoffのlanding floorから非全射を導くrouteを停止。
  floor自体は`E-052`の無条件な帰結で、prefixと同じcutoffを供給しない。rising floorだけによる
  欠損無限個の推論も`E-053`で撤回。固定した検証済みHから先の排除には新しい定量入力が必要。
- 両方向の証明はchainの侵入率・生存の定量定理（T4）に帰着する。Chaffinのデータで「侵入（弧）の
  発生率は`c/n`で減衰しないが、弧の深さが固定値へ届かなくなる」と判明したため、T4は非全射方向
  （chainの生存長が帯の未訪問run長で決まる自己相似構造）の証明を目標にする。
- 上の分岐表と再開条件は歴史的記録として残し、優先順位は2026-09-06の戦略地図に従う。

## 文書の役割

| 文書 | 役割 | 更新規則 |
|---|---|---|
| `CURRENT_FRONTIER.md` | 現在の研究状態と再開gateの正本 | status変更時に必ず更新 |
| `EVIDENCE_REGISTRY.tsv` | frontier-changing claimと証拠の機械可読正本 | claim追加・label変更時に更新 |
| `Recaman/Audit.lean` | `PROVED-LEAN`定理のkernel監査正本 | major theorem追加時に更新 |
| `PROOF_MAP.md` | theorem dependencyと過去の到達経路 | 現在の優先順位を主張しない |
| `ROADMAP.md` | 判断とgateの時系列 | 過去記述を上書きせず追記 |
| `STATUS_REPORT_2026-08-30.md` | 2026-09-01までの説明的snapshot | current statusの正本にしない |
| `RESEARCH_PORTFOLIO.md` | 過去枝のscore・停止理由・再開条件 | historical portfolioとして保存 |
| `DEVELOPMENT_LOG.md` | append-onlyな実装・研究ログ | 過去記録を書き換えない |
| `HYPOTHESIS_CARD_*.md` | 一つのbounded research unit | quantifier・acceptance・stopを凍結 |
| round/audit report | 一回の研究handoff | 後日のstatus正本にしない |

## 同期規則

1. evidence labelには`PROVED-LEAN`, `PROVED-PAPER`, `COMPUTED`, `OBSERVED`,
   `CONJECTURED`, `REFUTED`, `STOPPED`だけを使う。
2. `PROVED-LEAN` registry rowは一つ以上の`#print axioms`対象を持たなければならない。
3. computationのhorizon延長だけではlabelを上げない。
4. exact命題が`CONJECTURED`でも、証明ルートが尽きれば別rowで`STOPPED`にする。
5. current branchの変更は、この文書とregistryを同じchange setで更新する。
6. `bash scripts/check_research_registry.sh`と`./scripts/check.sh`を通してからhandoffする。

## 現在の検証基準

- Lean 4.33.1、標準ライブラリのみ。
- Lean source 268 files（root・auditを含む）、71,906 lines。
- `./scripts/check.sh`: 269 jobs、1,225 audited declarations。証拠台帳78件。
- 許可された公理依存は`{propext, Classical.choice, Quot.sound}`。
- `sorry`, `admit`, `native_decide`, user-defined `axiom`は禁止。
