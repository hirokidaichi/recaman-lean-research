# Hypothesis card: quadratic gap between nested supplies in an A run

- ID: `H-20260909-05`
- Owner: Codex, four roles sequentially
- Created: 2026-09-09, within the one-hour research run
- Status: `PROVED-LEAN`
- Base revision: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`

## One bounded question

Let w and v be arbitrary newest-first binary words, d=|w|, and k≥1.
Assume both w and A^k w v satisfy P2. Is the following uniform gap necessary?

```text
Δ(Δ−4k) ≥ 4k(d−1),    where Δ=k+|v|.
```

Here the second supply is k A steps later and its window contains the entire
first window; its lag is d+Δ. This containment is essential. A later short
lag wholly inside the earlier window is not covered.

Since P2 implies d≥3, the inequality implies **Δ>4k**. Consequently two
sharp supplies d=4m−1 cannot occur in one uninterrupted A run: a later sharp
supply at m+k would have Δ=4k. This is a uniform overlap obstruction, not
another fixed-lag table or a full capacity theorem.

## Dependency chain and weakest lemma

P2(w) gives mass 1 and moment 0. Thus A^k w has mass k+1 and twice-moment
k(k+3). The tail v must have mass −k and moment
`k(d+k)−k(k+3)/2`. For a length-ℓ tail of mass −k, putting all its A signs
last maximizes its moment and gives

```text
4 moment(v) ≤ ℓ²−2ℓk−k²−2k.
```

Substitution yields `(ℓ−3k)(ℓ+k)≥4k(d−1)`, the claimed inequality.
The weakest new lemma is this extremal moment bound applied to the nested
window, not a return, reachability, or supplied-history assumption.

## Frozen falsifier

- Boundary k=0 is excluded from the strict conclusion; an unchanged supply is allowed.
- Drop old moment: w=ASA, k=1, v=SSA makes A^k w v a P2 word although Δ=4.
- Drop new moment: w=AAS, k=1, v=SSA keeps the right signed mass but violates the gap.
- Weakened model: all sign words, no freshness and no actual orbit.
- Discovery: d=3,7,11; k=1,2,3; all tails of length 0..15 with mass −k.
- Conditional holdout: d=15,19; k=1,2,3; all tails of length 0..19 with mass −k.
  A fixed representative P2 w per d suffices because the nested equations use
  only d and its two exact P2 moments. Every accepted concatenation is replayed.
- No repair. Stop on any failing concatenation or a lost containment assumption.
- Acceptance: full paper argument and semantic Lean theorem over actual windows,
  or an exact counterexample. Finite absence of counterexamples alone is insufficient.

## Evidence and decision

`PROVED-LEAN`: `nested_supply_gap` proves the full quadratic inequality over
arbitrary words. `stream_nested_supply_strict_gap` proves its strict
consequence for actual stream windows, preserving `d+k≤d₂` as an explicit
containment assumption. `sharp_supply_no_second` excludes two sharp supplies
within an A run, and `sharp_charge_injective` proves equality of their
penultimate-S charges forces equality of times.

`COMPUTED`: all declared tail ranges pass. Some discovery and holdout cells
with k=3 contain **zero** nested P2 contacts; these are not positive support.
For example d=7,k=2 has an equality witness tail SSSSSSAAAA, giving Δ=12
and Δ(Δ−8)=48=8(d−1). Both dropped-moment controls fail as predicted.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/nested_supply_gap.py
./scripts/check.sh
```

Exact output: [nested_supply_gap.txt](data/issue73_20260909/nested_supply_gap.txt).
Repository audit: 1,265 declarations, all permitted dependencies.
**Decision: retain the quadratic gap with containment.** The subsequent
[H-07](HYPOTHESIS_CARD_2026-09-09_NONNESTED_LAG_DROP.md) refutes removal of
containment even for minimal supplies after arbitrarily long A runs.
