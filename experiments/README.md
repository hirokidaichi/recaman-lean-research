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
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/blocker_interval_hall.cpp \
  -o /tmp/blocker_interval_hall
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/blocker_interval_tail.cpp \
  -o /tmp/blocker_interval_tail
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/causal_blocker_probe.cpp \
  -o /tmp/causal_blocker_probe
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/target_transition_probe.cpp \
  -o /tmp/target_transition_probe
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
/tmp/blocker_interval_hall 1000 10000 100000 1000000
/tmp/blocker_interval_tail 1000 10000 100000 1000000
/tmp/causal_blocker_probe 20000000 7
/tmp/causal_blocker_probe --run-only 1000000000
/tmp/causal_blocker_probe --saturation 20000000
/tmp/causal_blocker_probe --saturation-lite 1000000000
/tmp/target_transition_probe 5000000
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
fingerprint `600675d8573dbe4a`. The checker now emits an explicit high
recursion-depth scope around the balanced tree, so the same source path also
supports authenticated deep endpoints. `DeepNineteenTraceCertificate`
kernel-checks 99,734 steps (`a 99734 = 19`, 1,559 leaves, 486,570 bytes,
FNV-1a `d122a1781c70f149`), and
`DeepSixtyoneTraceCertificate` kernel-checks 181,653 steps
(`a 181653 = 61`, 2,839 leaves, 894,439 bytes,
FNV-1a `f7c9baff6b448cdd`). These modules are intentionally expensive to
rebuild, but they are imported proofs rather than measurement-only evidence.

`BalancedTraceSuffix` reuses a successful deep run instead of checking an
almost-identical prefix again. `DeepSeventysixFromSixtyone` extracts the
authenticated input of the rightmost leaf, splits it after eleven steps, and
reverses the remaining ten value updates to prove `a 181643 = 76` from the
existing 181,653-step certificate. No second deep trace source is needed.

`DeepSixtyoneMexCertificate` rechecks the same authenticated endpoint with a
generic mex predicate. It proves that every value below 879 belongs to
`valuesThrough 181653`, while 879 does not. This raises every hypothetical
globally missing target to at least 879; it does not assume the empirical
later occurrence `a 328002 = 879`.

The next proposed endpoint has a reproducible generator regression but is
not yet a Lean theorem: 328,002 steps, 5,126 leaves, final leaf length 2,
expected value 879, 1,634,667 source bytes, and FNV-1a
`538690d9af3ec36d`. At that empirical endpoint the next mex is 1,355.

An exact-history run through one billion steps found four positive diagonal
states, at times `1`, `1520`, `9317`, and `31221`.  The three nontrivial states
had subtraction-tail length one and their successor values had already
occurred.  No debt-eligible diagonal event with a subtraction tail of length
at least two was observed.  This is empirical evidence only; the Lean
development continues to handle the debt branch without assuming it is
absent.

`blocker_interval_hall.cpp` generates every positive forced-addition blocker
job `(lastOccurrence + 1, clock - 1, clock)` and checks all interval Hall
inequalities exactly with a lazy range-add/range-max tree. It reports the
least integral capacity offset `C_H*`, a worst interval, and the corresponding
demand, subtraction mass/count, residual, and slack. It also analyzes the
relaxed family that keeps only the first job for each exact last-occurrence
release. The built-in regression fixes the sharp initial obstruction:
`C=8` fails on `[2,6]`, while `C=9` is tight. Exact runs through 20,000,000
steps kept `C_H*=9` and the same worst interval for both families. This is
empirical evidence for a causal first-window congestion inequality, not a
proof; removed annulus jobs in the first-family run do not reserve capacity.

`blocker_interval_tail.cpp` reuses the same exact generator and scans tail
restrictions. Its lazy scan is regression-checked against an `O(H^2)` all-
interval implementation through `H=100` for `C=0..12`. Once the interval
left endpoint is restricted to `p>=7`, exact runs through 5,000,000 steps
give the sharp constant `C*=3` for the all-job family as well as the relaxed
first-job family. Worst cases are single-job three-step `-++` windows such as
`[16,18]`, `[111,113]`, and `[1227,1229]`. A deliberately noncausal seed—
several preloaded values with synthetic last-occurrence labels—violates the
same `C=3` inequality on `[7,15]`; this regression records why static history
plus local transitions is insufficient. The aggregate tail Hall inequality
remains a conjecture. Even if true, its current derived consequence is the
partial growth result `liminf a_n/n <= 3`, not surjectivity.

`causal_blocker_probe.cpp` tests deliberately simpler explanations of the
tail Hall capacity before they are promoted to mathematical conjectures.
Assigning each job wholly to its first or last subtraction fails by large
margins, so those local ownership rules are rejected. Its `--run-only` mode
uses a dense exact-history bitset to scan consecutive additions. Through one
billion steps the longest run has length six, first occurring on
`[5026070,5026075]`; no seven-addition run was observed. During an addition
run, the subtraction candidate at each clock from the second onward is
exactly one below the orbit value two clocks earlier. Thus the scan measures
a causal predecessor-saturation pattern that arbitrary seeded histories can
fake for any prescribed finite length. The run bound is empirical and, even
if true, is not currently strong enough to imply surjectivity. The detailed
`--saturation` mode records source freshness, last-predecessor times, edge
reuse, and total value multiplicity. The lower-memory `--saturation-lite`
mode omits occurrence-time maps for distant holdout scans. Through one
billion steps a value is used as the source of a consecutive-addition pair at
most twice, even though the 20-million detailed scan sees one value occur 48
times in total. Predecessor ages are unbounded on the tested horizons, and a
single long run can use distinct sources, so neither age nor fixed source
multiplicity is yet an amortizing potential.

The run-only regression also rejects any completed addition run of length
exactly two. This is backed by a direct recurrence argument: after a
subtraction at `s` and additions at `s+1,s+2`, the subtraction candidate at
`s+3` is exactly `a(s-1)`, hence is positive and already seen. A maximal run
therefore has length one or at least three. When a maximal addition run does
end, its following subtraction lands at one below the value from two clocks
earlier, filling the first missing predecessor gap along the run.

`target_transition_probe.cpp` classifies subtraction candidates relative to
the running mex and compresses alternating low landings into maximal combs.
It also connects consecutive history-terminated combs into macro edges and
audits the exact Lean-side interval-order and origin claims. At 20,000,000
steps it finds 2,655 macro edges: 2,635 blocker decreases, 20 upward resets,
and no equal or separator-violating edge. All 1,260 subtraction-origin
terminal blockers have their generating predecessor strictly above the comb
entry; all 20 upward resets are addition-origin. The high-to-low exit window
has no violations, but its minimum integer slack is one and its maximum
utilization is 999,999 ppm, so the probe rejects any uniform-margin
strengthening.
