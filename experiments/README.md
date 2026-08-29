# Empirical probes

These programs are exploratory companions to the Lean development. Their output is
evidence for choosing conjectures; it is not imported into any Lean proof.

Build with a C++20 compiler:

```bash
c++ -O3 -std=c++20 experiments/recaman_empirical.cpp -o /tmp/recaman_empirical
c++ -O3 -std=c++20 experiments/recaman_b1_history.cpp -o /tmp/recaman_b1_history
c++ -O3 -std=c++20 experiments/recaman_debt_history.cpp -o /tmp/recaman_debt_history
c++ -O3 -std=c++20 experiments/replay_prefix_successor_coverage.cpp -o /tmp/replay_prefix_successor_coverage
```

Example runs:

```bash
/tmp/recaman_empirical 1000000
/tmp/recaman_b1_history 1000000
/tmp/recaman_debt_history 1000000
/tmp/replay_prefix_successor_coverage 1000000 1000 99734 112
```

The reported billion-step run used `1000000000` as the final argument. It requires
substantial time and memory because exact history membership is stored as a bitset.
`recaman_empirical.cpp` checks the borrow-coordinate transition equations while it
runs; a mismatch exits nonzero. `recaman_b1_history.cpp` performs the focused
one-borrow and first-occurrence audit described in the main README.

`recaman_debt_history.cpp` finds positive diagonal states whose final two or
more transitions form a maximal subtraction tail.  For each such state it
reports the tail's starting value, the history blocker exposed by the forced
addition immediately before the tail, the blocker's first-occurrence time and
branch, and the earlier forced-addition candidates obtained by following that
first-occurrence history.  The optional second argument limits the number of
full replay passes used to recover successively earlier first occurrences:

```bash
/tmp/recaman_debt_history 10000000 64 > /tmp/recaman_debt.csv
```

The CSV data goes to standard output and aggregate diagnostics go to standard
error.  A terminal classification of `legal_subtraction`, `target_candidate`,
or `candidate_below_target` records where the empirical debt chain stopped.
These observations select candidate lemmas; they are not proof assumptions.
The summary also counts every positive diagonal state, including the small
base case that has no two-step subtraction tail.  Thus a run with no
debt-eligible row still records how far the stronger diagonal-uniqueness
conjecture was checked.

`replay_prefix_successor_coverage.cpp` audits the finite predicate formalized
as `ReplayPrefixSuccessorCoverage`.  For every numerically eligible replay
clock it finds the latest first occurrence of a successor of a larger prefix
value.  With cutoff 99734, the first uncovered eligible clock below 1000 is
777: predecessor value 878 has successor 879 first occurring at time 328002.
This is empirical guidance only.  The Lean theorem additionally needs a
kernel-checked low witness at the cutoff; the experiment never supplies one
as a proof.

An exact-history run through one billion steps found four positive diagonal
states, at times `1`, `1520`, `9317`, and `31221`.  The three nontrivial states
had subtraction-tail length one and their successor values had already
occurred.  No debt-eligible diagonal event with a subtraction tail of length
at least two was observed.  This is empirical evidence only; the Lean
development continues to handle the debt branch without assuming it is
absent.
