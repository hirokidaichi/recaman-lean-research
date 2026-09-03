# Current research frontier

最終更新: 2026-09-02

この文書を、研究状態と次の研究gateに関する唯一の正本とする。個々の主張の証拠は
[`EVIDENCE_REGISTRY.tsv`](EVIDENCE_REGISTRY.tsv)、Lean kernel上の公理依存は
[`Recaman/Audit.lean`](../Recaman/Audit.lean)を正本とする。

## 結論

標準Recamán数列の全射性は未証明であり、証拠レベルは`CONJECTURED`である。
現在、全射性へ向かうactive direct branchは0本、実行中のbounded research unitも0件である。

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
- `E-028`（`CONJECTURED`, `H-20260902-05`）: landing floor「ある時刻以降の弧の底は852655を超える」。
  これが全射性の否定の唯一の証明義務であり、深さ`D = log n − log v`の定常性（中央値7.4 decade、
  指数裾、半減期18.7 decade）がその機構の手掛かりである。
- 両方向の証明はchainの侵入率・生存の定量定理（T4）に帰着する。Chaffinのデータで「侵入（弧）の
  発生率は`c/n`で減衰しないが、弧の深さが固定値へ届かなくなる」と判明したため、T4は非全射方向
  （chainの生存長が帯の未訪問run長で決まる自己相似構造）の証明を目標にする。
- 上の分岐表と再開条件は歴史的記録として残し、優先順位はロードマップのT1〜T5に従う。

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
- Lean source 255 modules、69,106 lines。
- `./scripts/check.sh`: 257 jobs、1,186 audited declarations。
- 許可された公理依存は`{propext, Classical.choice, Quot.sound}`。
- `sorry`, `admit`, `native_decide`, user-defined `axiom`は禁止。
