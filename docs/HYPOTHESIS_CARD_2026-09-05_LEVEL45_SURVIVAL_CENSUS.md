# Hypothesis card: l3blocked 後の level-5/4 survival census

- ID: `H-20260905-06`
- Owner: Codex
- Created: 2026-09-05
- Status: `REFUTED`
- Research branch: `E-048` 後の actual-history edge

## Exact statement

completed canonical arc内のblocked comb endでlock outcomeが`l3blocked`となる全recordを対象にする。
entry clock `m=c+5+2*iObs`、entry residue `r5=v-10-7*iObs` とし、直後から続く最大の
level-5/4 word

```text
5 --fresh subtraction--> 4 --blocked candidate/addition--> 5
```

のcompleted pair数 `L45` と最初の終了理由（residue wrap、upper candidate blockedでlevel 6、
lower return candidate freshでlevel 3、late landing）をexact simulatorで記録する。

検査する仮説は「`l3blocked` recordが同じarcの次のlate landingまで継続しないことと、initial
level-5/4 runがbudget index `K=floor(r5/9)`まで達してwrapすることが同値」。

## Why it would matter

- Frontier obligation discharged: `E-048`の条件付きwrap theoremに必要なactual run長が、arc terminalを
  直接分類するか判定する。
- Stronger than an existing identity or equivalent reformulation because: `l3blocked`後の未計測historyを
  pair単位で追い、局所budgetとarc survivalを接続する。
- Smallest useful consequence: cleanな同値が偽でも、first exit reasonとterminal/continuedのexact表を得る。

## Provenance and dependencies

- Definitions used: `arc_death_rule_probe`のcanonical recurrence、Chaffin residue increase、comb/lock record。
- Lean theorems used: `popup_l3blocked_level45_wrap`（比較対象）。
- Unverified mathematical assumptions: なし。検査する同値は経験仮説。
- Literature source or analogy: Chaffin arc partition。

## Falsification plan

- Small and boundary cases: `c=99734`（`r5=9`, 1 pair後wrap）と`c=588583`（terminalだがgap 1350）を必ず個別監査。
- Adversarial or weakened-history model: initial runがfirst exit後に別phaseでwrapするterminalを反例として数える。
- Discovery range: completed arcsの`c<10^10`。
- Frozen holdout range: card作成後に再計算する`10^10<=c<2*10^10`。
- Maximum one permitted repair: first exit reasonの分類名修正のみ。仮説の定数やterminal定義は修理しない。
- Stop condition: discovery反例1件、またはholdout反例1件で同値を`REFUTED`。分類表は`COMPUTED`として保存し、
  first exitだけでterminalを分離できなければ枝を`STOPPED`。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-05 | `OBSERVED` | existing windows | `c=99734`は1 pair後wrap、`c=588583`はterminal gap 1350で単純budget時刻とずれる可能性。 |
| 2026-09-05 | `REFUTED` | `/tmp/recaman_arc_death_rule_probe_l45 1000000 OUTDIR` | discovery反例`c=588583`: terminalだがinitial 5/4 runは43 pairでlowerFresh、budget index 532より大幅に早く離脱。 |
| 2026-09-05 | `COMPUTED` | `/tmp/recaman_arc_death_rule_probe_l45 20000000000 OUTDIR` | discovery 3,478件はwrap 1 / upperBlocked 628 / lowerFresh 2,849、holdout 1,366件は0 / 223 / 1,143。wrap index違反0、holdout terminal 0。exact結果は`docs/data/deathrule/h2e10_level45_survival.txt`。 |
| 2026-09-05 | `COMPUTED` | `/tmp/recaman_arc_death_rule_probe_trace 589933 OUTDIR 588588 589933` | `c=588583`を個別監査。43 completed 5/4 pair後のlowerFreshはresidue 4,396のlevel 3へ入り、続く4/3 phaseは628回のupper stateで`4393-7j`（違反0）、最後にwrap。一般化せず二段phaseの反例構造だけを確定。 |

## Semantic audit

- Informal statement implies formal statement: simulatorのpair stateは各clockのquotient、step種、residue increaseを同時監査する。
- Formal statement implies intended consequence: 同値が通れば`l3blocked` terminalは`E-048`のrun survivalだけへ還元できる。
- Counterfactual examples that should make the statement false: initial 5/4 runがfirst exitした後、later phaseでlandingなしにwrapするarc。
- Could the theorem be proved from weaker or vacuous assumptions?: finite censusであり定理とは呼ばない。
- Are reachability, freshness, time order, or actual-orbit provenance accidentally omitted?: canonical simulator自身のactual prefixだけを使う。

## Decision

- Continue / formalize / refute / stop: 仮説は`REFUTED`、initial-run classifier枝は`STOPPED`。
- Reason: `c=588583`がlowerFresh後の別phaseを経てterminalになるため、first exitだけではarc survivalを分類できない。holdoutにterminalはなく修理根拠もない。
- Reopen only if: lowerFresh後に観測した`5/4 -> 4/3`のようなlevel下降を一般化し、phaseごとの
  survivalを結ぶstrict landing-bottom descentまたはfinite-to-one chargeが定式化できる場合。
