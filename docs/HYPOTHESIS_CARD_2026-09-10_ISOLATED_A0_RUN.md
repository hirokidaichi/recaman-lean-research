# Hypothesis card: isolated a=0 nonsingleton runs

- ID: `H-20260910-35`
- Created: 2026-09-10 21:00 JST
- Status: `COMPUTED` (E-148). Dual sibling already `PROVED-LEAN` (E-135)
- Research branch: issue #73, after E-136 stopped previous-S

## Exact statement

On the canonical prefix of length 10^7, every isolated a=0 min SS=2 source
is one of:

1. singleton A, i.e. e(t+1)=S (52,193 cases), or
2. the first of an A-run of length exactly 3: e(t)=e(t+1)=e(t+2)=A,
   e(t+3)=S, with t+1 carrying no P2 and t+2 carrying clean lag-3 AAS
   (5 cases: 196641, 2866284, 7906786, 8642654, 8775876).

There is no isolated a=0 min SS=2 at the start of an A-run of length ≥4.

This is a finite census. E-135 already proves that any isolated start of
a length-≥3 A-run forces the lag-3 clean sibling at t+2.

## Why it would matter

The 5 “nonsingleton” isolated sources are not a new allocation class.
They are E-135 companions viewed from the isolated end. Remaining
isolated a=0 mass is singletons, still without a surviving S-charge
after E-136.

## Falsification

Holdout: none. Do not raise 10^7 to a theorem. Do not map t-1 to an S
budget.

## Evidence log

| Date | Label | Command | Result |
|---|---|---|---|
| 2026-09-10 21:00 | `COMPUTED` | `orbit_iso_next.cpp` | 5/5 are length-3 runs, t+1 no P2, t+2 clean lag-3, t+3 S |

## Decision

Record E-148. Stop new named charges on isolated a=0. Continue only with
a new local inequality that is not an endpoint map.
