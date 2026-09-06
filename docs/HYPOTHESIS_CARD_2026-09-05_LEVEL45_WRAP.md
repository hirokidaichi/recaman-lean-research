# Hypothesis card: l3blocked 後の level-5/4 residue 予算

- ID: `H-20260905-05`
- Owner: Codex
- Created: 2026-09-05
- Status: `PROVED-LEAN`
- Research branch: `H-20260905-03` の `l3blocked` 残余

## Exact statement

clock `m` で `a m = 5m+r`, `r<m` とする。level-5/4 ping-pong が `K` pair 続き、
各upperからのlevel-4候補がfresh、各completed pairのreturn候補が既訪問で、

```text
9K <= r < 9(K+1)
```

なら、pair `K` の一歩目か二歩目でresidueが増加する。

提案Lean declarationは`level45_run_wrap`。`pingpong_run`の`p=3` instanceと、一般の一対に対する
`pingpong_pair_wrap`を合成する。さらにpopup lockのupper stateとlevel-three candidate既訪問から
level-five entryを出す`popup_l3blocked_level45_entry`、両者を結ぶ
`popup_l3blocked_level45_wrap`までを同じunitに含める。

## Why it would matter

- Frontier obligation discharged: blocked comb lockが`l3blocked`でlevel 5へ上がった後のarc終了を、
  1 pairあたり9のresidue費用へ還元する。
- Stronger than an existing identity or equivalent reformulation because: 有限runの最後にactual residue increaseを返す。
- Smallest useful consequence: threshold未満terminal `c=99734,v=19` の `5A 4S 5A 3S` を説明する局所kernel。

## Provenance and dependencies

- Definitions used: `a`, `valuesThrough`。
- Lean theorems used: `pingpong_run`, `residue_wrap`, `landing_of_fresh`。
- Unverified mathematical assumptions: canonical `l3blocked`後に必要なfresh/blocked historyが何pair続くか。
- Literature source or analogy: Chaffin arcのresidue非増加区間。

## Falsification plan

- Small and boundary cases: `K=0`, remainder `0..4`（一歩目wrap）、`5..8`（二歩目wrap）、
  `r=9K` と `r=9(K+1)-1`。
- Adversarial or weakened-history model: final fresh条件を外すとforced additionでwrap位置が変わり得るため外さない。
- Discovery range: 既存trace `c=99734` と `c=588583` のみ。
- Frozen holdout range: 新規経験定数ではなくrecurrenceの条件付き帰結なのでなし。
- Maximum one permitted repair: pair-start clock下界を明示する修正のみ。
- Stop condition: `pingpong_run`からpair `K` のexact residue `r-9K`が出ない場合、または
  結論がresidue increaseでなくstep wordだけに弱まる場合は`STOPPED`。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-05 | `OBSERVED` | `other_lock_windows.txt`, `c=99734` | l3blocked後はlevel-5 residue 9から1 pairで0へ下がり、次のsubtractionでresidue increase。 |
| 2026-09-05 | `COMPUTED` | `awk '$13=="l3blocked" && $12==1 && $21==1 {...}' comb_ends.txt` | completed-arc l3blocked 4,844件中continued 4,842、terminal 2。threshold未満は`c=99734`のterminal 1件だけ。compact結果は`docs/data/deathrule/h2e10_blocked_comb_survival_ratio.txt`。 |
| 2026-09-05 | `PROVED-LEAN` | `lake env lean Recaman/PingPongRuns.lean` | `pingpong_pair_wrap`、`level45_run_wrap`に加え、l3blocked座標からlevel-five residueへ入るbridgeと合成wrap定理を証明。 |

## Semantic audit

- Informal statement implies formal statement: `p=3` ping-pongは1 pairあたり`2p+3=9`を払い、残余9未満のpairでwrapする。
- Formal statement implies intended consequence: 条件を満たすactual runは同じChaffin arcをpair `K`より先へ継続できない。
- Counterfactual examples that should make the statement false: final lower candidateが既訪問ならfresh subtractionは起きない。
- Could the theorem be proved from weaker or vacuous assumptions?: step recurrenceと明示historyだけを使う非空の条件付きkernel。
- Are reachability, freshness, time order, or actual-orbit provenance accidentally omitted?: 全候補を`valuesThrough`でactual presentation時に課す。

## Decision

- Continue / formalize / refute / stop: 条件付き局所kernelは`PROVED-LEAN`。一般run survivalは未着手のまま閉じる。
- Reason: 一般survival長を主張せず、残余9の局所終了機構だけを分離した。
- Reopen only if: `l3blocked`後の5/4 run長をactual arc historyから下界づける不変量が得られた場合。
