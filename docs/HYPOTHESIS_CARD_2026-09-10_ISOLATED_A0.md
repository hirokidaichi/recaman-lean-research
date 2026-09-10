# Hypothesis card: isolated a=0 previous-S joint with E-128

- ID: `H-20260910-31`
- Created: 2026-09-10 19:46 JST, timed session until 24:00
- Status: previous-S joint `REFUTED` (E-136); dual sibling `PROVED-LEAN` (E-135); singleton repair stopped on holdout p=17; nonsingleton 5-tuple is E-135 (E-148)
- Research branch: issue #73, SS=2 allocation after E-133 stopped named charges

## Exact statement

Let t be a current-A time whose minimum P2 window has ssCount=2 and
leading A-run 0, i.e. e(t-1)=S. Proposed charge: φ(t)=t-1.

1. φ is injective among isolated a=0 min SS=2 sources (true: they all
   use distinct times t-1).
2. φ(t) is never the E-128 S-ended prefix endpoint of a current-A
   source whose some P2 window has ssCount≤1.

One permitted repair: restrict to singleton A, i.e. e(t+1)=S.

## Why it would matter

52,198 / 52,357 of canonical SS=2 min sources are isolated a=0.
An injective S map disjoint from E-128 would be a separate capacity
piece. It is not E-070.

## Falsification

- Discovery: binary periods 1..16. Collision at period 13.
- Canonical 10^7: 3950 joints with E-128 endpoints.
- Cause: E-135, the dual of E-132. If e(t-1)=S and t,t+1,t+2 are A,
  then t+2 has clean AAS. That lag-3 source uses t-1 as its E-128
  endpoint.
- Repair: singleton A. Discovery periods 1..16 clean. Holdout period 17
  has 51 collisions. Stop.

## Evidence log

| Date | Label | Result |
|---|---|---|
| 2026-09-10 19:52 | `REFUTED` | period 13 previous-S × E-128 |
| 2026-09-10 19:58 | `PROVED-LEAN` | E-135 dual AAS sibling |
| 2026-09-10 19:58 | `COMPUTED` | 3950 canonical joints |
| 2026-09-10 20:04 | `STOPPED` | singleton repair holdout p=17, 51 collisions |
| 2026-09-10 21:00 | `COMPUTED` | 5 nonsingleton isolated sources are E-135 triples (E-148) |

## Decision

Do not reopen previous-S or singleton repair. The 5 nonsingletons are
not a new class. Remaining isolated mass is singletons without a
surviving S-charge.
