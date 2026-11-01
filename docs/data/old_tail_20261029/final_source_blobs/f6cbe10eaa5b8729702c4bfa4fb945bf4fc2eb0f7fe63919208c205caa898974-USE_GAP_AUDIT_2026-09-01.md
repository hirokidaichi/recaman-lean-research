# Burst-stream use-gap audit — 2026-09-01

## Conclusion

The proposed local bound

```text
next low clock n - use clock m >= sqrt(6m) (1 - o(1))
```

does **not** follow from the candidate floor, exact greedy steps, and the
three-addition burst.  A parametric seeded family has gap squared divided by
`m` tending to `4`, not `6`.  The missing assumption was an implicit cap of
three on an addition run; `RecurringCandidateBurst` proves only a lower bound
of three.  The local use-gap branch is therefore `STOPPED`.

This does not refute the main finite-seed supply conjecture.  The family uses
a seed depending on the chosen interval.  A surviving statement must make
the single finite seed and global self-supply requirement explicit.

## Bounded research question

Can two consecutive low-candidate use clocks in the recurrence branch be
forced, from the current Lean payload alone, to obey a cutoff-independent
square-root-six gap?

- Acceptance: an exact quantified inequality, boundary checks, a frozen
  holdout, and a paper dependency chain before Lean implementation.
- Stopping condition: one exact `Basic.step` seed satisfying the local floor
  and burst payload but violating the inequality.

The stopping condition was met.

## Exact counterfamily

Fix `c = 10` and an integer `q >= 3`.  Put

```text
m = q^2 + 2q
g = 2q + 1
n = m + g.
```

At candidate clock `m`, enter candidate `c` by a legal subtraction.  Between
the two use clocks prescribe the step word

```text
A^(q+1) S^q.
```

Let `x` be candidate excess above `c`.  Before the `j`-th addition,

```text
A_j = j*m + j(j-1)/2                 (0 <= j <= q).
```

After all `q+1` additions, before the `s`-th subtraction,

```text
B_s = (q+1-s)m + q(q+1)/2 - s(q+3) - s(s-1)/2
                                             (0 <= s < q).
```

The endpoint calculation is

```text
B_q = m + q(q+1)/2 - q(q+3) - q(q-1)/2 = 0,
```

so the candidate returns exactly to `c` at time `n`.  For `s < q`, the
`B_s` are positive and strictly decrease to

```text
B_(q-1) = n + 1.
```

Thus all intermediate candidates are strictly above their absolute clocks;
the two endpoints are consecutive low-candidate clocks and the candidate
floor `c` is preserved.

Preload the finite history with the addition candidates `c + A_j`, the
second use's successor demand `c+n`, zero, and the pre-entry value.  Every
addition is then genuinely forced.  The subtraction candidates are fresh:
for `1 <= s < q`, writing `r=q-s`,

```text
A_r < B_s < A_(r+1),
B_s - A_r       = (q-s)(q+s+3) > 0,
B_s - A_(r+1)   = -s(s+2) < 0.
```

The first subtraction candidate is `B_0=A_(q+1)`, beyond the seeded range;
the later `B_s` are strictly decreasing and hence do not repeat a prior
subtraction landing.  The output after addition `j` is
`c+A_(j+2)+1`; the strict interleaving and the fact that adjacent `A` values
differ by more than one show that it is not a `B_s`.  Therefore the
prescribed word follows the exact
greedy rule from this finite seed.  Preloading `c+n` gives the second use its
second forced addition; the loop-return law gives the third.

Finally,

```text
g^2 / m = (2q+1)^2 / (q^2+2q) -> 4,
g^2 < 6m  for every q >= 3.
```

Hence the local square-root-six asymptotic is false at arbitrarily large
clocks.  Longer addition runs are the mechanism.

## Evidence

- `PROVED-LEAN`: `Recaman.seededUseGap_local_counterexample` checks the
  concrete instance `q=10`, `m=120`, `n=141`.  It verifies the legal entry,
  equal endpoint candidates, strict-high interior, eleven additions, ten
  legal subtractions, the next three-addition burst, and `21^2 < 6*120`.
- `PROVED-PAPER`: the parametric calculation and freshness separation above.
- `COMPUTED`: exact greedy discovery and holdout:

```text
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/use_gap_counterexample.cpp -o /tmp/use_gap_counterexample
/tmp/use_gap_counterexample 3 100
/tmp/use_gap_counterexample 101 10000
```

Exact output:

```text
use-gap-counterexample checked=98 qRange=[3,100]
first q=3 m=15 n=22 gap=7 gapSquaredOverM=3.266666667 seedSize=6
last q=100 m=10200 n=10401 gap=201 gapSquaredOverM=3.960882353 seedSize=103
all exact greedy continuations passed; every row has gap^2 < 6m
use-gap-counterexample checked=9900 qRange=[101,10000]
first q=101 m=10403 n=10606 gap=203 gapSquaredOverM=3.961261175 seedSize=104
last q=10000 m=100020000 n=100040001 gap=20001 gapSquaredOverM=3.999600090 seedSize=10003
all exact greedy continuations passed; every row has gap^2 < 6m
```

The computation is not the proof; it freezes and stress-tests the same
formula on disjoint ranges.

## Semantic audit

The previous transfer silently read “at least three additions” as “exactly
three additions.”  This is not available:

- `RecurringCandidateBurst` gives a three-addition prefix only.
- `SeededHighCorridorNoGo` already supplies arbitrarily long exact
  forced-addition corridors from finite seeds.
- The new counterexample preserves the local floor and both endpoint bursts,
  so adding those fields to a local theorem does not repair it.

The parametric seed changes with `q`; consequently it does not decide whether
one fixed finite seed can sustain infinitely many demands.  That global
question remains `CONJECTURED` and is the only repair compatible with the
original hypothesis card.

## Decision

- Local `sqrt(6m)` use-gap: `REFUTED`; do not formalize or repair with an
  unproved addition-run cap.
- Eventually-periodic no-go: retain only as `OBSERVED` until its exact
  schedule type, quantifiers, paper proof, and missing checker are restored;
  only then can it be promoted to `CONJECTURED` or stronger.
- Main burst-supply conjecture: continue only with an explicit single-finite-
  seed global self-supply statement.
