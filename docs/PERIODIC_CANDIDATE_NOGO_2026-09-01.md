# Periodic candidate-schedule no-go — reconstruction, 2026-09-01

## Conclusion

An eventually periodic addition/subtraction schedule cannot keep the
non-truncated subtraction-candidate walk above a fixed floor while returning
to a bounded band infinitely often.  More sharply, a periodic schedule which
preserves a candidate floor must have positive sign sum and therefore makes
the candidate diverge to infinity along every phase.

The full eventually-periodic statement is `PROVED-PAPER`.  Its finite
balanced-period core is `PROVED-LEAN` in `PeriodicCandidateNoGo`: the drift
sum over the actual cyclic rotations is `-p²`, hence a nonempty balanced
period has a negative-drift phase.  It restores the exact mathematical
content behind the previously missing `periodic_nogo_check.py`, but it does
not decide the main burst-supply conjecture: a nonperiodic drift-and-reset
schedule remains possible.

## Bounded research question

Can an eventually periodic step word support a candidate floor and finite
liminf using only the exact candidate transition law, without an upper bound
on addition-run length?

- Acceptance: an exact quantified sign recurrence, a complete three-case
  proof by the period sign sum, and an independent exhaustive checker.
- Stopping condition: any need for a three-addition run cap, a history
  preload assumption, or an unrecorded schedule convention.

The acceptance condition was met; none of the stopping conditions was used.

## Exact statement

Let `p > 0`.  Let `epsilon : Nat -> Int` be eventually periodic with period
`p`, take only the values `-1` and `1`, and let an integer walk `x` satisfy,
from some clock `N` onward,

```text
x_(n+1) - x_n = epsilon_n * (n+1) - 1.                 (1)
```

Here `epsilon_n=1` denotes addition and `epsilon_n=-1` subtraction.  Equation
(1) is exactly the Recaman candidate transition

```text
d_(n+1) = d_n + n       on addition,
d_(n+1) = d_n - (n+2)   on subtraction,
```

in a corridor where the candidate stays positive and Nat subtraction does
not truncate.

If `x` is bounded below from `N` onward, then

```text
for every K, all sufficiently late n satisfy K < x_n.
```

Consequently an eventually periodic candidate schedule with finite liminf
cannot occur in an `EventualHighCandidateTail`.

## Proof

Write one period as signs `epsilon_0,...,epsilon_(p-1)` and set

```text
S = sum_r epsilon_r.
```

For every fixed phase, its displacement from one cycle to the next is affine
in the cycle number, with leading coefficient `p*S`.

1. If `S < 0`, every fixed phase eventually has arbitrarily large negative
   cycle displacement.  Summing the affine displacements sends that phase to
   `-infinity`, contradicting the lower floor.
2. If `S > 0`, summing the positive-leading affine displacements sends every
   phase to `+infinity`.  Since there are only `p` phases, the whole walk
   diverges.
3. Suppose `S = 0`.  The one-period displacement is then independent of the
   cycle number.  At phase `r` write it as

   ```text
   C_r = sum_(i=0)^(p-1) epsilon_(r+i) * (i+1) - p,
   ```

   with the signs read cyclically.  Rotating the phase gives

   ```text
   C_(r+1) - C_r = p * epsilon_r.
   ```

   More importantly, over all rotations every sign receives every weight
   `1,...,p` once.  Therefore

   ```text
   sum_r C_r
     = (1+...+p) * S - p*p
     = -p^2 < 0.                                      (2)
   ```

   Some phase has `C_r < 0`; repeated periods send that phase to
   `-infinity`, again contradicting the floor.

Only `S > 0` survives, and that case diverges.  This proves the statement.

## Lean finite core

`Recaman/PeriodicCandidateNoGo.lean` formalizes the indexing-sensitive part
without adding an infinite-sequence interface:

```text
balanced_periodPhaseDrifts_eq_rotations
balanced_periodRotations_drift_sum
balanced_periodRotations_has_negative
```

The first theorem identifies recurrence-generated phase drifts with the
drifts of actual cyclic rotations.  The second proves their sum is `-p²` for
every balanced integer sign list.  The third excludes the empty-list
boundary and extracts a negative actual phase.  The transfer from the three
sign-sum cases to eventual divergence remains the paper argument above.

## Reproducible finite check

The checker exhausts all step words in two disjoint period ranges and checks
the exact zero-sum identities, including (2):

```text
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/periodic_candidate_nogo_check.cpp \
  -o /tmp/periodic_candidate_nogo_check
/tmp/periodic_candidate_nogo_check 1 16
/tmp/periodic_candidate_nogo_check 17 22
```

The first range is discovery and the second is the frozen holdout.  This
computation is `COMPUTED`, not the proof.

Base revision: `b0cde86`, with the checker in the current research working
tree.  Exact output:

```text
periodic-candidate-nogo periods=[1,16] checkedWords=131070
negativeSignSum=56747 positiveSignSum=56747 balanced=17576
balancedIdentityFailures=0 balancedWithoutNegativePhase=0
all balanced words satisfy sum(C_r)=-p^2 and have a negative-drift phase
periodic-candidate-nogo periods=[17,22] checkedWords=8257536
negativeSignSum=3659364 positiveSignSum=3659364 balanced=938808
balancedIdentityFailures=0 balancedWithoutNegativePhase=0
all balanced words satisfy sum(C_r)=-p^2 and have a negative-drift phase
```

## Semantic audit

- No addition-run upper bound is present.  Arbitrarily long addition runs
  are allowed.
- The argument uses no candidate freshness, seed, reachability, or future
  coverage assumption; it is a pure consequence of the non-truncated step
  law and a lower floor.
- Positive sign sum is not contradictory: it is precisely the divergent
  candidate branch already isolated by
  `EventualHighCandidateTail.candidate_diverges_or_recurrence`.
- The result rules out only eventual periodicity in the recurrence branch.
  It gives no obstruction to nonperiodic self-supply, so it must not be
  described as a proof of the burst-supply conjecture.

## Decision

- Eventually-periodic finite-liminf candidate schedule: `REFUTED`.
- Periodic no-go: full asymptotic statement `PROVED-PAPER`; balanced finite
  arithmetic core `PROVED-LEAN`.
- Main fixed-finite-seed self-supply question: remains `CONJECTURED`.
- Next decision: use the result only as a regression condition on proposed
  abstract schedules.  Do not build the infinite-walk interface until a
  concrete consumer needs more than the paper-level transfer.
