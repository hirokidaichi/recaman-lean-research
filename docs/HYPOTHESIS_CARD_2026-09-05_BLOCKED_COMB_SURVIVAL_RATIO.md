# Hypothesis card: blocked comb の生存比

- ID: `H-20260905-03`
- Owner: AI research epoch 2026-09-05（1時間 bounded unit）
- Created: 2026-09-05
- Status: `CONJECTURED`
- Research branch: 非全射方向。`E-028` landing floor の arc survival/depth

## Exact statement

canonical Recamán orbit を `experiments/arc_death_rule_probe.cpp` の exact arc detector で分解する。
完了した弧に属する comb end record を取り、着地 clock/value を `(c,v)`、歯数を `T`、comb の
直前で終わる maximal level-1/2 run の pair 数を `J`、その run の入口高さを `hPrev` とする。
さらに test 値 `2c+v+2` が時刻 `c` までに既訪問（`blocked`）で、同じ弧の中に `c` より後の
遅延着地がある（`continued`）と仮定する。このとき

```text
7 * hPrev <= 16 * v.
```

probe が全 record で確認する exact identity

```text
hPrev = v + T + 3 * J
```

の下では、これは次の survival cost と同値である。

```text
7 * T + 21 * J <= 9 * v.
```

このunitは canonical有限計算による反証可能性を先に判定する。一般のLean定理とは主張しない。

## Why it would matter

- Frontier obligation discharged: `E-044` 後に残った「actual arc survivalからlanding bottomへの
  strict descent」の最小候補。producerの局所分類ではなく、同じ弧で次の遅延着地が存在するための
  必要条件を与える。
- Stronger than an existing identity or equivalent reformulation because: `hPrev=v+T+3J` は局所runの
  恒等式にすぎないが、上の不等式は future continuation を仮定して初めて `T,J` の総費用を `v` で抑える。
- Smallest useful consequence: `7T+21J>9v` の blocked comb end はその弧の最後の遅延着地である。
  これが一様なら、深い弧を終わらせる sufficient criterion を与える。

## Provenance and dependencies

- Definitions used: canonical `a`、Chaffin arc、late landing、comb end、`blocked`、`continued`、
  pre-landing run `(J,hPrev)`（すべて `arc_death_rule_probe.cpp` 冒頭にexact定義）。
- Lean theorems used: `chain_descends`、`late_landing_popup`、`popup_lock_wrap`、
  `level23_exit`。ただし仮説自体はまだ有限計算だけで評価する。
- Unverified mathematical assumptions: `continued -> 7*hPrev<=16*v` の一般性、定数 `7/16` の機構、
  completed arcでのfinite detectorとChaffinの弧の一致（先頭19弧はcheckpoint済み）。
- Literature source or analogy: Chaffinのping-pong区間。`E-037` の10^10 death-rule censusに未凍結の
  ratio tableとして現れた候補。

## Falsification plan

- Small and boundary cases: `T=1`、`J=0`、最小のblocked record、等号近傍、wrap/break/l3blockedの
  各 outcome、`hPrev=v+T+3J` のidentityを検査する。
- Adversarial or weakened-history model: future `continued` を外すと反例が多数あることを確認し、
  純算術やlocal producer分類だけからは出ないことを監査する。fresh comb endは対象外だが、条件の
  必要性を調べる対照群として違反を数える。
- Discovery range: source revision `904ab56` 以前の保存済み exact run、全 completed-arc record with
  `c<10^10`。blocked・continued 19,365件で違反0（カード作成前の観測）。
- Frozen holdout range: このカード作成後に初めて計算する全 completed-arc record with
  `10^10<=c<2*10^10`。
- Maximum one permitted repair: strict境界だけが破れた場合に限り、`<=` を `<` に変更してよい。
  定数、blocked条件、continued条件、rangeは変更しない。
- Stop condition: holdoutに違反が1件でもあれば `REFUTED`。holdoutが通っても、actual arc survivalを
  使う紙上dependency chainが書けなければ `COMPUTED` に留め、Lean wrapperは作らず `STOPPED` とする。

## Acceptance test

1. `arc_death_rule_probe 20000000000 OUTDIR` が先頭19 landing checkpointと既存exact checksを通す。
2. `comb_ends.txt` を discovery/holdout に分け、`arcCompleted && hasRun && blocked && continued` の
   全recordで `7*hPrev<=16*v` と `hPrev=v+T+3J` を監査する。
3. outcome別件数、最小slack `16v-7hPrev`、対照群の違反数、最小反例（あれば）を保存する。
4. 正の結果の場合でも、`continued` を供給するactual-history edgeを一つ特定できなければ形式化しない。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-05 | `OBSERVED` | `docs/data/deathrule/h1e10_summary.txt` | `c<10^10` のcompleted arcsで blocked・continued 19,365件、`16v<7hPrev` は0件。全combではfresh・continuedの反例2件があり、blocked条件は実質的。 |
| 2026-09-05 | `COMPUTED` | revision `904ab56`; `arc_death_rule_probe 20000000000 OUTDIR`; frozen holdout `10^10<=c<2*10^10` | holdout eligible 6,391件、ratio違反0、run identity違反0。break 5,025 / l3blocked 1,366。最小slack 475,297。第40弧の底1814はthreshold未満のterminal wrap。 |
| 2026-09-05 | `PROVED-LEAN` | `lake env lean Recaman/LockResidue.lean` | `popup_lock_wrap_of_long_prelanding_run`: `T=1`のlong runとlevel-3側freshnessから最初のbudget failure pair内のresidue increaseを証明。threshold未満terminal 9件中、T=1 wrap 7件の機構。 |

## Semantic audit

- Informal statement implies formal statement: `continued` は同じcompleted arc内の後続late landingの存在、
  `blocked` はtest値の時刻`c`での既訪問性であり、予測ラベルではなくexact trajectory eventである。
- Formal statement implies intended consequence: 反対命題により `7T+21J>9v` ならそのcomb end以後、
  同じ弧にlate landingはなく、現在の`v`が弧の底である。
- Counterfactual examples that should make the statement false: blockedで、長いpre-landing runにより
  `hPrev`が大きいにもかかわらず、lock/break後に同じ弧が再びlate landingするrecord。
- Could the theorem be proved from weaker or vacuous assumptions?: `continued`を外すと10^10までに
  `16v<7hPrev` のblocked recordが8件ある。`blocked`を外すとcontinued反例が2件あるため、両条件は必要。
- Are reachability, freshness, time order, or actual-orbit provenance accidentally omitted?: canonical orbit、
  completed arc、strictly later landingを明記した。finite computationを一般定理と呼ばない。

## Decision

- Continue / formalize / refute / stop: 一般のsurvival必要条件は`CONJECTURED`のまま。bounded unitは
  holdoutの`COMPUTED`とT=1 wrap枝の`PROVED-LEAN`で閉じた。
- Reason: holdout反例はなく、係数7をresidue budgetへ結ぶactual-history dependency chainが得られた。
  ただし`T>=2`と`l3blocked`を含む一般証明はない。
- Reopen only if: `T>=2`のearlier-tooth candidate history、または`l3blocked`後のsurvivalを扱う
  exact statementを別カードにし、どちらか一方だけを凍結した場合。
