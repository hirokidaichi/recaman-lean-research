# Frozen holdout protocol — H-20260920-01 / original Q

Frozen before first holdout execution, 2026-09-20 daytime session. Source revision:
`08c08565c743f39350c9b959e1df7d30aa1cae5d`. Uncommitted source hashes are in
`PRE_HOLDOUT_SHA256SUMS`, written before execution.

The sample is the previously declared, still unused p=32/33 sample: seed 2026091801,
2000 distinct positive-mass bit words at each period. One Python `random.Random`
instance, periods 32 then 33, `getrandbits(p)`, bit u=1 means A at phase u. Reject
nonpositive mass and exact duplicates within each period; rotations remain distinct.
The accepted strings in order, each with a trailing newline, determine the sample hash.

For each word, compute the full supplied set U by exact integer running mass and
moment for each A phase, checking all d=1..p(p+1), stopping at the first P2.
Hall is checked on full U by augmenting-path matching. This matcher has separately
been compared with exhaustive subset Hall on all positive bit words of p=1..10.
Enumerate all subsets B of supplied phases with minimal lag 3/7/11, and test tightness.
Check Q for every lag-11 SS=2 donor outside B; check W for every w1 member in tight B.

Required completion: exactly 2000 words per period; at least 20 donor-bearing Hall
words per period; positive Q nonempty and W counts; no violation. A timeout, insufficient
population, or counterexample has nonzero exit status. Time budget is 1800 seconds.
Any unexpected failure is retained, not repaired by changing this sample after inspection.

Command:

```sh
python3 -u experiments/issue73_20260920/short_owner_holdout.py --mode holdout --seconds 1800
```

This is finite computational evidence only. The source proof candidate already compiles;
the sample does not justify universal quantifiers. Independent audit remains separate.
