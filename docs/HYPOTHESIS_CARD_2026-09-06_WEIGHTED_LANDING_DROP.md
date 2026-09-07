# Hypothesis card: 一歯combのweighted landing drop

- ID: `H-20260906-08`
- Owner: Codex
- Created: 2026-09-06
- Status: `REFUTED`
- Research branch: survival比へ接続する最小の重み付き不等式候補

## Exact statement

canonical completed arcの、hasRunかつT=1のblocked comb end `(c,v)`を取る。
同じarcで最初の後続late landingを `(e,u)` とし、prelanding AS run長をJとする。

```text
7J ≤ 3(v-u).
```

係数はlevel-3/4 lockの1 pairあたりのdrop 7と、J本のprelanding railが約J/3 pairのlockを
強制することから選んだ。`l3blocked`によるphase変更も含むstatementである。
`u≥1`から `21J+7≤9v`、従ってT=1のsurvival比が従う。この候補はsurvival比そのものより強い。

## Why it would matter

- phaseを跨いでも成立すれば、既存conditional lock定理とgeneral survival比の間を埋める。
- no-wrap時の `G=r-q(q+1)/2` はSで不変、Aで `2q+1` 減るため、v-uは実際のaddition weightの和。
  この恒等式は既知であり、研究入力はJからその和への下界である。
- H-07のseeded familyはこの不等式も破るので、canonical historyを実質的に使う必要がある。

## Falsification plan

- Discovery: source revision `8a4314d7` のcanonical `c<10^9`。
  まず既存probeを再実行した2M recordで予備反証し、違反があれば直ちに停止する。
- Frozen holdout: `10^9≤c<2·10^10`。予備反証がなかった場合だけ生成する。
- Boundary: J=0、最小positive J、break/l3blocked、next landingのclock/valueを全recordで確認。
- 対象は次のcomb末端でなく、直後のcombの最初のlate landing（c0,v0）。
- Repair: なし。係数・domain・next landing選択を変えない。
- Stop: 一つのcanonical違反、またはholdout完走。未反証だけでLean化しない。

## Informal chain / semantic audit

1. actual next late landingを既存detectorのcontinued/gapと次combのc0/v0の両方から同定する。
2. run identityとtime orderを再検査する。
3. 符号付き整数 `3(v-u)-7J` の最小値と違反を列挙する。
4. local arithmeticだけのseeded反例を除外するのはcanonical initial-0 provenanceである。
5. 証明する場合、未知edgeは「prelanding runからactual addition weightへの下界」の一つ。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-06 | `CONJECTURED` | 予備2M tableを見る前に凍結 | Jからlanding dropへの係数7/3を固定。 |
| 2026-09-06 | `COMPUTED` | [exact outputs](data/strategy_2026-09-06/README.md) / [監査と論証](STRATEGY_AUDIT_2026-09-06.md) | COMPUTED: 20B table 56,580行。discovery適用1,221行は違反0、holdout適用3,228行に5反例。最初はc=11685598221,v=4318940415,J=276986,e=11685741477,u=4318376915でslack=-248402。 |

## Decision

- Continue / formalize / refute / stop: REFUTED、係数調整なしでSTOPPED。l3blockedのphase変更をまたぐ一律7J/3下界を再利用しない。最初の反例のphase・費用・7境界birth診断を完了。全blocker集合の共同生成分類をissue #71の独立unitとする。
- Reopen only if: 異なる独立history入力があり、同じ比の係数調整ではない場合。
