# Hypothesis card: phase capacity affine potential

- ID: `H-20260906-01`
- Owner: Codex
- Created: 2026-09-06
- Status: `REFUTED`
- Research branch: `E-049` 後の phase-to-phase descent

## Exact statement

`q>=2`、residue `r` のpositive-length `q/(q-1)` phaseに

```text
B(q,r) = floor(r / (2q-1))
Phi(n,q,r,x) = B(q,r) + alpha*n + beta*x + psi(q)
```

を割り当てる。ここで`alpha,beta`は固定実数、`psi : {2,3,...}->R`も固定関数である。
検査した仮説は、標準Recamán ruleを正確に実行する全seeded segmentについて、次のresidue wrapまでに
現れる連続する全positive-length phaseの間で`Phi`をstrictに減少させる係数が存在すること。

seedはboundary `b`で`0`とcurrent valueを含み、`|seen|<=b+1`、`max(seen)<=b(b+1)/2`、current valueの
parityがcanonical clock parityと一致するものまでに制限してもよい。標準initial-0 orbitだけに量化した
仮説ではない。

## Why it would matter

- Frontier obligation discharged: `E-049`後のlevel下降を跨ぐ単一potential候補を判定する。
- Stronger than an existing identity or equivalent reformulation because: phaseのarithmetical capacityにclock/value
  correctionを加え、phase間でuniformな降下を要求する。
- Smallest useful consequence: この形のpotential探索を再開しないための明示的no-go。

## Provenance and dependencies

- Definitions used: exact seeded greedy Recamán step、residue wrap、positive-length ping-pong phase、`B(q,r)`。
- Lean theorems used: `E-038`のresidue lawはraw-residue repairの意味監査にのみ使用。
- Unverified mathematical assumptions: seeded familyを排除する未知のfull initial-0 provenance条件がcanonical
  orbit上でも同じno-goを与えることは仮定しない。
- Literature source or analogy: potential / amortized capacity。

## Falsification plan

- Small and boundary cases: `q=2,3,4,5`のpair費用とwrap境界を確認する。
- Adversarial or weakened-history model: density・range・parityを満たすexact seedを明示し、historyを各step後に更新する。
- Discovery range: symbolic familyと`M=1`のlowerFresh sample。
- Frozen holdout range: 有限holdoutではなく、`M`と`n`を独立に非有界化する二反例族。
- Maximum one permitted repair: level正規化を外したraw residueだけを確認する。
- Stop condition: 全係数を排除する反例族、またはrepairが既存residue telescopingへ退化した時点で`STOPPED`。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-06 | `PROVED-PAPER` | [`PHASE_HISTORY_ADVISORY_AUDIT_2026-09-06.md`](PHASE_HISTORY_ADVISORY_AUDIT_2026-09-06.md) | lowerFresh族が`beta<0`と`beta=0`、upperBlocked族が`beta>0`を排除し、全係数を排除。 |
| 2026-09-06 | `COMPUTED` | `python3 experiments/phase_capacity_countermodels.py` | lowerFresh `M=1,2,10,100` と upperBlocked sample のexact seeded replay、seed bounds、wrap clock、capacity差が全てPASS。 |

## Semantic audit

- Informal statement implies formal statement: phase start、clock、value、quotient、residueを反例族で明示する。
- Formal statement implies intended consequence: affine capacity classのstrict descentとnonincreaseをともに排除する。
- Counterfactual examples that should make the statement false: lowerFresh族ではcapacity gainが`4M-1`、
  upperBlocked族ではvalueが`2n+4`増えてcapacityが4減る。
- Could the theorem be proved from weaker or vacuous assumptions?: exact greedy transitionsと実際のwrapをseedから導出し、
  future persistenceを仮定しない。
- Are reachability, freshness, time order, or actual-orbit provenance accidentally omitted?: boundary後のreachability・freshness・
  history更新は保持する。boundary以前の全seed memberのcanonical first-birth pathだけは意図的に要求しない。

## Decision

- Continue / formalize / refute / stop: affine capacity仮説は`REFUTED`、枝は`STOPPED`。
- Reason: 二つのexact seeded familyが`beta<0`、`beta>0`、`beta=0`を順に全て排除し、raw residue repairは
  `E-038`の望遠和に退化する。
- Reopen only if: full initial-0 provenanceから供給され、seeded familyを実質的に排除する新しい定量history入力が
  phase survival ratioへ接続された場合。
