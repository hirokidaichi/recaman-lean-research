# Empirical probes

These programs are exploratory companions to the Lean development. Their output is
evidence for choosing conjectures; it is not imported into any Lean proof.

Build with a C++20 compiler:

```bash
c++ -O3 -std=c++20 experiments/recaman_empirical.cpp -o /tmp/recaman_empirical
c++ -O3 -std=c++20 experiments/recaman_b1_history.cpp -o /tmp/recaman_b1_history
c++ -O3 -std=c++20 experiments/recaman_debt_history.cpp -o /tmp/recaman_debt_history
c++ -O3 -std=c++20 experiments/replay_prefix_successor_coverage.cpp -o /tmp/replay_prefix_successor_coverage
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic \
  experiments/prefix_successor_certificate_generator.cpp \
  -o /tmp/prefix_successor_certificate_generator
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic \
  experiments/prefix_successor_certificate_test.cpp \
  -o /tmp/prefix_successor_certificate_test
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/lean_trace_witness_generator.cpp \
  -o /tmp/lean_trace_witness_generator
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/lean_trace_witness_test.cpp \
  -o /tmp/lean_trace_witness_test
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/balanced_trace_source_generator.cpp \
  -o /tmp/balanced_trace_source_generator
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/balanced_trace_source_test.cpp \
  -o /tmp/balanced_trace_source_test
```

Example runs:

```bash
/tmp/recaman_empirical 1000000
/tmp/recaman_b1_history 1000000
/tmp/recaman_debt_history 1000000
/tmp/replay_prefix_successor_coverage 1000000 1000 99734 112
/tmp/prefix_successor_certificate_test
/tmp/prefix_successor_certificate_generator 400000 1000 99734 112
/tmp/lean_trace_witness_test
/tmp/lean_trace_witness_generator 2622 64
/tmp/balanced_trace_source_test
/tmp/balanced_trace_source_generator 4825 64
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

`prefix_successor_certificate_generator.cpp` turns the same exact-history
audit into deterministic TSV rows. Every row is explicitly marked
`evidence_kind=empirical`; it is candidate data for a future Lean certificate,
not a proof imported by the kernel. The companion regression test fixes the
known clock-112 exception and checks that cutoff 99734 covers every eligible
clock through 776 before exposing clock 777 / successor 879 as the next wall.
The generator arguments are `steps`, `clockMax`, `cutoff`, and `clockMin` in
that order.

`lean_trace_witness_generator.cpp` emits the exact-history branch reasons and
the 108 occurrence witnesses in the clock-112 target band as Lean source
input. The output is deterministic and marked `EMPIRICAL INPUT ONLY`; its
claims become proofs only after a sound Lean checker accepts them. The
arguments are `traceSteps` and `chunkSize`. The flat generated term is useful
as an interchange format but is intentionally not imported: at 2622 steps it
exceeds practical kernel reduction time. `BalancedTraceCertificate` instead
checks 64-step leaves through a balanced tree and reaches time 4825 in a few
seconds.

`balanced_trace_source_generator.cpp` is the reproducible source path for
that balanced certificate. It emits compact branch codes, fixed-size leaves,
and a deterministic midpoint-balanced tree, together with empirical metrics
on standard error. The 4825-step source has 76 leaves and a fixed FNV-1a
fingerprint `7e016593e1de83eb`. A measurement-only 99734-step generation has
1,559 leaves and 486,466 source bytes; it is not imported or compiled by the
Lean development.

An exact-history run through one billion steps found four positive diagonal
states, at times `1`, `1520`, `9317`, and `31221`.  The three nontrivial states
had subtraction-tail length one and their successor values had already
occurred.  No debt-eligible diagonal event with a subtraction tail of length
at least two was observed.  This is empirical evidence only; the Lean
development continues to handle the debt branch without assuming it is
absent.
