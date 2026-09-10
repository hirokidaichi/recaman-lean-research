# Hypothesis card: all sharp leading-run P2 windows are integer partitions

- ID: `H-20260909-04`
- Owner: Codex, four roles sequentially
- Created: 2026-09-09, within the one-hour research run
- Status: `PROVED-PAPER` (full bijection); forced S-block consequence `PROVED-LEAN`
- Base revision: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`

## Exact bounded question

For each m≥1, are the P2 words of length 4m−1 with their first m signs A
in bijection with integer partitions of m?

Write a partition as m nonnegative integers λ_0≥...≥λ_(m−1) with sum m,
padding by zeros. Construct the A-position set (one-based offsets)

```text
{1,...,m} ∪ {3m+i−λ_i : 0≤i<m}.
```

All other positions are S. For m≥3 the resulting words are minimal P2
windows by H-20260909-03. The all-m bijection is the acceptance target;
counting a new fixed lag is not acceptance. It does not supply a periodic
injection or prove E-070.

## Paper chain to audit

The m late A offsets x_i are strictly increasing and lie after the first m
positions. Their coordinatewise maximum is 3m+i. Set λ_i=3m+i−x_i.
These differences are nonnegative and nonincreasing. P2 fixes the total A
position sum at m(4m−1), so the differences sum to exactly m.

Conversely, a partition of m has λ_i≤m, so x_i≥2m>m; the offsets are strictly
increasing and at most 4m−1. There are exactly 2m A signs. Their position sum
is m(4m−1), giving signed sum 1 and moment 0. The constructions are inverse.
This is a complete proof to be checked against the independently generated
finite sets; no finite set supplies the universal quantifier.

## Frozen falsifier

- Boundary m=1,2: the bijection is tested, but minimality is not asserted.
- Discovery m=3..8; holdout m=9..24.
- Generate partitions recursively on their decreasing parts.
- Independently generate all increasing late-A position tuples with the exact
  target sum using only subset endpoint bounds; do not use partition deficits
  to generate this second set.
- Compare the full sets, not just counts. Recheck signed sums and moments.
- No repair. Stop on any missing word, duplicate, or wrong moment.
- No actual-orbit reachability assumption; positive drift and periodicity are absent.

## Evidence and decision

`PROVED-PAPER`: the two explicit inverse constructions above prove the
arbitrary-m classification. The proof uses no finite enumeration as a premise.
The full word/partition bijection is not implemented in Lean.

`PROVED-LEAN`: `sharp_middle_S_block` and `stream_sharp_S_block` independently
prove its important consequence: for m≥3, offsets m+1,...,2m−1 are S.
They use the same extremal deficit inequality directly, with no partition
interface or unverified classification assumption.

`COMPUTED`: every independently generated set agrees at m=1..24, including
all 1,575 words at m=24. Counts begin 1,2,3,5,7 for m=1..5. Both minimality
and the m≥3 bound intentionally exclude the boundary cases m=1,2.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/sharp_partitions.py
./scripts/check.sh
```

Exact output: [sharp_partitions.txt](data/issue73_20260909/sharp_partitions.txt).
Source hashes and the 1,265-declaration audit are in the same bundle.
**Decision: retain the bijection as paper mathematics and use the audited
S-block consequence for capacity. Do not treat counting more partitions as
new research progress.**
