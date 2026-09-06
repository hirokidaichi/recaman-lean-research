# Hypothesis card: 多歯 comb の lock-wrap 分解

- ID: `H-20260905-04`
- Owner: Codex
- Created: 2026-09-05
- Status: `PROVED-LEAN`
- Research branch: `E-028` landing floor / `H-20260905-03` の `T >= 2` 残余

## Exact statement

comb end の landing を `(c,v)=(i+1,v)`、歯数を `T>=1` とし、最初の歯の直前 clock を
`i0=i-2(T-1)`、その landing 値を `v0=v+T-1` とする。`i0` より前に `J` pair の
pre-landing run

```text
a(i0-2j)=(i0-2j)+(v0+1+3j),
v0+3j in valuesThrough(i0-2j)       (0<=j<=J)
```

があるとする。final comb end の popup lock pair `k<T-1` の level-two candidate が実履歴で
既訪問であり、pair `K` まで level-three candidate が fresh、かつ

```text
6+7K <= v < 13+7K,
16v < 7(v+T+3J)
```

なら、pair `K` の二歩のどちらかで residue が増加する。

Lean declaration は `popup_lock_wrap_of_multitooth_history` とし、上の actual-history
membership、run、index non-underflow、popup entry を明示仮定に持ち、結論は
`popup_lock_wrap` と同じ residue-increase disjunction とする。

## Why it would matter

- Frontier obligation discharged: `H-20260905-03` の threshold 未満 terminal 9件のうち、
  `T=1` 以外で唯一の `T=2` wrap を同じ係数7の機構へ含める。
- Stronger than an existing identity or equivalent reformulation because: comb の歯と
  pre-landing run が、final lock の異なる candidate index 区間を実際に供給することを示す。
- Smallest useful consequence: 一般 survival 比に必要な未証明部分を「earlier-tooth test値が
  final landing時までに既訪問」という有限の actual-history 条件へ分離する。

## Provenance and dependencies

- Definitions used: `a`, `valuesThrough`, comb tooth count `T`, pre-landing run length `J`。
- Lean theorems used: `prelanding_upper_values`, `popup_lock_candidate_blocked_by_run`,
  `valuesThrough_mono_of_le`, `popup_lock_wrap`。
- Unverified mathematical assumptions: earlier-tooth candidate membership を comb 形だけからは
  導かない。一般 survival 必要条件がこの membership を強制するかは未検証。
- Literature source or analogy: Chaffin arc の residue 非増加定義。

## Falsification plan

- Small and boundary cases: `T=1` で既存定理へ縮退すること、`T=2` では `k=0` のみを
  earlier-tooth側が負担すること、`K<T-1` と `K>=T-1` の境界を確認する。
- Adversarial or weakened-history model: earlier-tooth test値の既訪問性を削除した版を調べる。
  2×10^10 census では `T>=2` の全 earlier-tooth候補が既訪問なのは
  21,563 / 45,889件だけなので、無条件版は採用しない。
- Discovery range: 既存 `arc_death_rule_probe` の `c<2*10^10` 診断だけを semantic audit に使う。
- Frozen holdout range: 新しい定数候補ではないため追加 holdout は設けない。
- Maximum one permitted repair: Nat index の non-underflow 仮定を明示化する修正のみ。
- Stop condition: ratio から run が負担すべき index 長を算術的に導けない、または
  earlier-tooth membership が結論そのものを仮定するだけなら `STOPPED`。

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-05 | `OBSERVED` | `/tmp/recaman_arc_death_rule_probe 20000000000 /tmp/recaman-survival.axRzpR` | `T>=2` の全 earlier-tooth candidate が landing時に既訪問なのは21,563/45,889件。comb形だけからの無条件化を棄却。 |
| 2026-09-05 | `OBSERVED` | `awk` audit of `comb_ends.txt`, record `c=32144188` | 唯一のthreshold未満`T=2` terminalは`K=2301`, `6+7K=16113<=v=16114<16120=13+7K`, run必要長6901<=J=10644、earlier-tooth `k=0` candidate既訪問。 |
| 2026-09-05 | `PROVED-LEAN` | `lake env lean Recaman/LockResidue.lean` | `popup_lock_wrap_of_multitooth_history` がtooth-history区間 `k<T-1` とshiftしたpre-landing run区間を合成し、pair `K` のresidue increaseを証明。 |

## Semantic audit

- Informal statement implies formal statement: tooth側とrun側が `k<K` を分割して全 lock candidateを
  既訪問にし、fresh側とresidue budget failureを `popup_lock_wrap` へ渡す。
- Formal statement implies intended consequence: threshold未満で、明示した実履歴があるmulti-tooth
  blocked combはそのpairで同一arcを継続できない。
- Counterfactual examples that should make the statement false: earlier-tooth candidateがfreshなら
  lockはそのpairでlevel 2へbreakでき、wrapは強制されない。
- Could the theorem be proved from weaker or vacuous assumptions?: ratioは `K>=T-1` 部分で run長を
  支払うために必要。`K<T-1` では ratio/run は使われず、全pairをtooth historyが支払う境界枝となる。
- Are reachability, freshness, time order, or actual-orbit provenance accidentally omitted?:
  reachabilityは `a` と `valuesThrough` でactual orbitに固定し、freshnessとpresentation時刻を明示する。

## Decision

- Continue / formalize / refute / stop: 条件付きhistory分解は`PROVED-LEAN`。無条件版と一般survival命題は継続しない。
- Reason: `T=2` wrapを同じ係数7の機構へ含めつつ、一般 survival 命題との未証明edgeを隠さない最小形になった。
- Reopen only if: actual arc survivalから earlier-tooth membership を強制する独立不変量が得られた場合。
