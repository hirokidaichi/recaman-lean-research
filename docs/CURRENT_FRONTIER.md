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
- `E-025`（`PROVED-PAPER`）: 二分定理D「無限個のnで`a n ≤ n+2`、または未訪問整数の下密度≥1/4」。
  A枝は密度1/4の欠損を含意する。Lean化がT1。
- 両方向の証明はchainの侵入率・生存の定量定理（T4）に帰着する。侵入率が`c/n`なら全射、
  `n^{-1-ε}`なら非全射が見立てで、3e9では区別できない。run-length simulatorで1e12以上を見る。
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
- Lean source 247 modules、67,763 lines。
- `./scripts/check.sh`: 249 jobs、1,138 audited declarations。
- 許可された公理依存は`{propext, Classical.choice, Quot.sound}`。
- `sorry`, `admit`, `native_decide`, user-defined `axiom`は禁止。
