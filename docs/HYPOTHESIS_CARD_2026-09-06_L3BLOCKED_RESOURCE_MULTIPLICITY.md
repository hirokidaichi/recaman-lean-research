# Hypothesis card: l3blocked 後 excursion の positive blocker 多重度

- ID: `H-20260906-02`
- Owner: Codex
- Created: 2026-09-06
- Status: `COMPUTED`
- Research branch: `E-049` 後の actual-history finite-to-one charge 候補

## Exact statement

標準初期値 `a(0)=0` から生成した canonical Recamán 軌道を対象にする。completed Chaffin arc 内の
blocked comb end `c` から生じる `l3blocked` event の clock を `s` とする。`e>s` を、residue が
直前 clock より増加するか `a(e)<e` となる最小 clock とする。このとき任意の `w>0` について、

```text
{t | s<t<e, a(t-1)-t=w, w は clock t より前に既訪問}
```

の要素数は高々 2 である。

今回の有限検査は event clock `s<=600000` を discovery、`600000<s<=2000000` を凍結holdoutとする。
arc completion と `e` の存在を horizon 内で確認できないrecordは標本へ含めない。

## Why it would matter

- Frontier obligation discharged: `E-049` が要求した phase 間 finite-to-one charge の最小候補を検査する。
- Stronger than an existing identity or equivalent reformulation because: residue telescopingではなく、actual
  history の同一既訪問候補が excursion 内で再利用される回数を直接制限する。
- Smallest useful consequence: blocker resourceを `(w, firstBirth(w))` へ課金する際の局所入次数を2で抑える。

## Provenance and dependencies

- Definitions used: `arc_death_rule_probe` の canonical recurrence、Chaffin arc、comb end、`l3blocked`。
- Lean theorems used: なし。有限計算の後も無条件定理とは扱わない。
- Unverified mathematical assumptions: 全scaleで多重度2が保たれること、およびこの局所制限からsurvival比の
  重み付き不等式が導けること。
- Literature source or analogy: blocker finite-to-one charging。

## Falsification plan

- Small and boundary cases: discovery `s<=600000` を独立replayし、既知の二重使用
  `(c,s,e,w)=(97896,97983,98664,395922)` と一回使用上界の反例を再現する。
- Adversarial or weakened-history model: 今回はcanonical軌道だけを検査する。seeded historyへ一般化しない。
- Discovery range: completed-arc event clock `s<=600000`。
- Frozen holdout range: completed-arc event clock `600000<s<=2000000`。
- Maximum one permitted repair: なし。多重度2を3へ変更せず、endpointやevent domainも変更しない。
- Stop condition: 同一excursion・同一positive blockerの3回目のuseを1件でも見つければ`REFUTED`。
  holdout完走時は`COMPUTED`で閉じ、Lean wrapperは追加しない。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-06 | `OBSERVED` | advisory audit supplied context, `N=600000` | completed excursion 17件、positive blocked use 6,305件、最大多重度2。一回使用は`c=97896`で反証と報告。現作業ツリーでは未検証。 |
| 2026-09-06 | `COMPUTED` | `arc_death_rule_probe 600001 OUTDIR 1 600001` + `l3blocked_resource_multiplicity.py` | discoveryを独立replay。17 excursion、6,305 use、最大2、違反0。`w=395922`のbirth/use clocksを一致再現。 |
| 2026-09-06 | `COMPUTED` | `arc_death_rule_probe 2000000 OUTDIR 1 2000000` + frozen holdout | holdout 22 excursion、12,802 use、最大1、`>2`違反0。2,000,000 clockのrecurrence再検査も違反0。compact outputは[`h2e6_l3blocked_resource_multiplicity.txt`](data/deathrule/h2e6_l3blocked_resource_multiplicity.txt)。 |

## Semantic audit

- Informal statement implies formal statement: candidateをclock直前値から再計算し、出力stepと既訪問性も独立照合する。
- Formal statement implies intended consequence: 一excursion内の同一具体資源への局所課金だけを高々2にする。
- Counterfactual examples that should make the statement false: 同じ`w`が`e`より前の3個の異なるclockでforced
  additionを起こすcanonical excursion。
- Could the theorem be proved from weaker or vacuous assumptions?: 有限censusであり定理とは呼ばない。completed
  arcを要求するのは`e`の存在を未来仮定せず確定するためである。
- Are reachability, freshness, time order, or actual-orbit provenance accidentally omitted?: initial-0 prefixをclock 1から
  replayし、全candidate membershipをその時点以前の出力だけで再構成する。

## Decision

- Continue / formalize / refute / stop: finite unitは`COMPUTED`で閉じる。all-scale statementは`CONJECTURED`、Lean化しない。
- Reason: discoveryを再現し、凍結holdoutにも反例はなかったが、39 excursionの有限evidenceに留まる。
- Reopen only if: holdout後に多重度2とsurvival ratioを結ぶcutoff-independentな重み付き不等式が紙上で得られる場合。
