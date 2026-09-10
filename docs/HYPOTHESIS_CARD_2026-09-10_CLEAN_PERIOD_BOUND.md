# Hypothesis card: sharp period bound for a clean P2 witness

- ID: `H-20260910-14`
- Created: 2026-09-10 JST
- Owner: Codex, four roles sequentially
- Status: `PROVED-LEAN`
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`

## Exact bounded question

For arbitrary p>0 periodic e and a clean P2 witness d=8k+3:

- if p is even, p≥6k+4;
- if p is odd, d≤p, strengthened to d+2≤p when e(t)=A;
- consequently d<2p always, and 3d+7≤4p for supplied A phases.

The supplied-A bound should be sharp for every k≥0: use p=6k+4,
all odd times A, and among even times only multiples of p equal A.
At t=2k+1 this should have the unique P2 lag8k+3 and equality3d+7=4p.
The stronger bound without e(t)=A is false at p3,d3, current S.

## Why it matters / dependency chain

This closes the completeness bound used by the local-clean falsifier,
including windows longer than a period and the distinction between all
supplied phases and supplied A phases. It is a sharp structural bound,
not a period-limited capacity claim.

For even p=2N, repeat the unique odd-offset A at index k+N. It would lie
in the forced-S part if N≤3k+1, giving p≥6k+4. For odd p, repeating the
newest S at offset1 into the even offsets rules out p<d when k≥1. The
k0 case is checked separately. If current A and p=d, the oldest forced S
would equal the current sign, impossible. The explicit family realizes
the even lower bound because the compressed window contains exactly one
multiple of N=3k+2.

## Falsifier / acceptance / stop

- Check all binary periods1..10 discovery,11..16 holdout, all current signs,
  all clean P2 windows through2p. This is a new bound property on previously
  used word ranges, not a fresh sample of the original capacity conjecture.
- Check the sharp family k0..32 discovery,k33..512 holdout, including the
  minimum/unique lag from the exact local classification.
- Negative control: p3 word SAA, with a clean P2 at current S, violates
  3d+7≤4p if the current-A premise is removed.
- Acceptance: all-period Lean bounds and the all-k equality family; stop
  or keep only the correctly qualified bounds if a boundary case fails.

## Evidence and audit

`PROVED-LEAN`: `CleanPeriodBound.even_period_bound`, `odd_period_bound`,
`clean_lag_lt_twice_period`, `odd_current_A_bound`, and
`sharp_current_A_bound` prove all claimed inequalities with their exact
premises. `sharpFamily_certificate` proves the all-k periodic equality
family, current A, cleanliness, and uniqueness among ALL P2 lags.
`current_A_premise_counterexample` and its period lemma certify p3,d3 at
current S, showing why the strongest inequality needs that premise.

`COMPUTED`: `python3 experiments/issue73_20260910/clean_period_bound.py`
passes all binary periods1..16 at both current signs and all513 family
parametersk0..512. Exact output and source hash:
`docs/data/issue73_20260910/clean_period_bound.txt`.

`./scripts/check.sh`: PASS,1,445 declarations; log
`docs/data/issue73_20260910/check14_counterexample_period_bound.txt`.
The d<2p bound closes H-09's finite-search cutoff argument without changing
its all-lag capacity statement. The sharp stronger bound is specifically
about supplied A phases. No uniform period bound is asserted for dirty
P2 windows; stopped examples with lag much larger than p still apply.

