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
/tmp/fixed_seed_supply_falsifier 2000000 4096      # arbitrary seeds (2026-09-01 record)
/tmp/fixed_seed_supply_falsifier 2000000 4096 1    # canonically admissible seeds only
/tmp/window_demand_provenance_probe 20000000
/tmp/generalized_orbit_supply_probe 0 1000 100000     # preload-free orbits, discovery
/tmp/generalized_orbit_supply_probe 0 1000 100000 1   # same, corridor-faithful c-floor links
/tmp/cone_excursion_probe 0 1000 100000              # breaker and cone-exterior run census
/tmp/near_diagonal_rate_probe 3000000000            # per-decade near-diagonal census, 25 s
python3 experiments/chaffin_landing_analysis.py rec-landings-1e612.txt rec-holes-2_32.txt  # Chaffin's tables
/tmp/landing_depth_probe 0 1000000000                # arc minima (A393814/A393815) and depth quantiles
/tmp/rlsim 10000000000000 accel                    # run-length orbit to 1e13 in about 8 minutes
/tmp/rlsim 10000000000 plain                        # step-by-step cross-check, 4 minutes
python3 experiments/hole_hopping_closure.py docs/data/chaffin_rec-holes-2_32.txt  # residue-class game closure
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
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/target_right_record_probe.cpp -o /tmp/target_right_record_probe
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/seeded_right_record_search.cpp -o /tmp/seeded_right_record_search
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/target_ancestry_capacity_probe.cpp -o /tmp/target_ancestry_capacity_probe
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/target_high_candidate_probe.cpp -o /tmp/target_high_candidate_probe
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/target_comb_extraction_probe.cpp -o /tmp/target_comb_extraction_probe
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/target_ladder_probe.cpp -o /tmp/target_ladder_probe
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/target_successor_slack_probe.cpp -o /tmp/target_successor_slack_probe
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/target_upward_provenance_probe.cpp -o /tmp/target_upward_provenance_probe
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/use_gap_counterexample.cpp -o /tmp/use_gap_counterexample
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/periodic_candidate_nogo_check.cpp \
  -o /tmp/periodic_candidate_nogo_check
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/supply_ancestry_probe.cpp -o /tmp/supply_ancestry_probe
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/fixed_seed_supply_falsifier.cpp \
  -o /tmp/fixed_seed_supply_falsifier
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/window_demand_provenance_probe.cpp \
  -o /tmp/window_demand_provenance_probe
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/generalized_orbit_supply_probe.cpp \
  -o /tmp/generalized_orbit_supply_probe
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/cone_excursion_probe.cpp -o /tmp/cone_excursion_probe
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/near_diagonal_rate_probe.cpp -o /tmp/near_diagonal_rate_probe
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/landing_depth_probe.cpp -o /tmp/landing_depth_probe
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/run_length_recaman_simulator.cpp -o /tmp/rlsim
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
/tmp/target_right_record_probe 20000000
/tmp/target_ancestry_capacity_probe 20000000
/tmp/target_high_candidate_probe 2000000
/tmp/target_comb_extraction_probe 20000000
/tmp/target_ladder_probe 20000000
/tmp/target_successor_slack_probe 20000000 2000
/tmp/target_upward_provenance_probe 20000000
/tmp/target_upward_provenance_probe 2000000000
/tmp/seeded_right_record_search --walk-record-sub 12 250
/tmp/use_gap_counterexample 3 100
/tmp/use_gap_counterexample 101 10000
/tmp/periodic_candidate_nogo_check 1 16
/tmp/periodic_candidate_nogo_check 17 22
/tmp/supply_ancestry_probe 10000001 0 10000000
/tmp/supply_ancestry_probe 20000001 10000001 20000000
/tmp/fixed_seed_supply_falsifier 2000000 4096
```

`use_gap_counterexample.cpp` is the frozen falsifier for the local reading
of the burst-stream use-gap claim.  For every checked `q`, it follows the
exact greedy rule from a finite seed, realizes the word `A^(q+1) S^q`
between consecutive low-candidate clocks, checks the candidate floor and a
three-addition burst at the second use, and verifies `gap^2 < 6m`.  The
discovery range is `q=3..100`; the frozen holdout is `q=101..10000`.  The
seed is not claimed canonically reachable and varies with `q`, so this
refutes only a local floor/burst derivation.  Any surviving theorem must
state a genuinely global finite-seed self-supply condition.

`periodic_candidate_nogo_check.cpp` exhausts periodic addition/subtraction
words and verifies the zero-sign-sum phase-drift identities behind the
periodic candidate no-go.  Periods `1..16` are the discovery range and
`17..22` the frozen holdout.  The proof is the signed-sum argument recorded
in `docs/PERIODIC_CANDIDATE_NOGO_2026-09-01.md`; enumeration is only a
regression check.

`supply_ancestry_probe.cpp` classifies positive forced candidates by their
first birth and follows subtraction-born values to their predecessor orbit
value.  The frozen discovery and holdout windows expose both failures needed
by the ancestry audit: a forced reuse maps back to a legal birth, and
distinct subtraction-born children can share one predecessor value.  The
smallest two examples are separately kernel-checked in
`Recaman/SupplyAncestryCounterexample.lean`; the large-window census remains
`COMPUTED` evidence only.

`fixed_seed_supply_falsifier.cpp` replays one byte-identical finite state
across all horizons and synthesizes candidate-return words on the three
burst supply lattices.  With RNG seed `20260901`, it finds a fixed seed with
fingerprint `14161494152507716643` supporting internally supplied uses of
candidate 20 at clocks `94,286,862`.  The unchanged seed has no fourth use
through clock one million.  This refutes only finite raw-demand deficits;
it neither constructs nor excludes an infinite fixed-seed supply stream.

`external_blocker_collision_probe.cpp` is the exact falsifier for
`H-20260902-01`.  For each positive forced candidate `c`, it classifies the
already-visited successor demands `c+m` by first birth: subtraction-born
demands enter `S_c`, while a positive candidate forcing an addition birth
enters `E_c`.  It tests whether the first four or eight supplied uses force
`E_c ∩ S_c`.  The frozen 20M run has no candidate with four supplied uses,
so both threshold hypotheses are vacuous and the branch is `STOPPED`; this
absence is not a uniform bound.

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

`target_upward_provenance_probe.cpp` reuses the exact macro extractor and
dense first-occurrence ancestry metadata to audit every upward same-target
terminal reset. It records whether the new blocker is a terminal right
record, its first branch, the forced birth candidate, pre-epoch ancestry,
and whether that candidate belongs to any earlier terminal fresh interval.
It also audits nonuniform return below each terminal blocker and, separately,
below each upward-reset blocker. At 2B, 21,495 of 21,510 terminal anchors had
a later entry strictly below the anchor; 26 of 28 upward resets were repaid by
the immediately next terminal episode. The remaining two belong to the early
target-4 epoch, which ends when target 4 occurs.

`target_ancestry_capacity_probe.cpp` additionally reports fixed record-gap
cohorts at 200k and 2M. This separates values already visited when a record is
created, values first visited later, and values still unvisited at the audit
horizon. The result is a diagnostic future-consumption curve, not a proof of
eventual coverage.

`target_reset_repayment_probe.rb` is the frozen seeded falsification harness
for Round 17. It starts from reproducible nonnegative signed-clock histories,
then follows the exact greedy rule and classifies upward same-target terminal
resets as later repaid, ended by target occurrence, or horizon-censored. The
discovery and independent holdout commands are:

```bash
ruby experiments/target_reset_repayment_probe.rb 5000 200 10000 20260901
ruby experiments/target_reset_repayment_probe.rb 1000 200 50000 20260902
```

`target_reset_preload_counterexample.rb` freezes the audited seed used to
refute the local fixed-history-preload proof route:

```bash
ruby experiments/target_reset_preload_counterexample.rb 1200
```

The continuation obeys the exact greedy step rule, but the finite seed is not
claimed reachable from the canonical initial state. These scripts falsify
local causal generalizations; they cannot instantiate a permanent-missing
tail and therefore do not refute the exact repayment conjecture.

The `--walk-record-sub` seeded search is a no-go check: it finds a finite
history whose subsequent real `Basic.step` orbit has an upward terminal
record born by legal subtraction. Therefore the standard-prefix addition-
origin law cannot be inferred from local step legality or the macro fields.
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

The broadened macro mode also follows first-occurrence ancestry and the
value-axis order of all prior fresh intervals. At 20,000,000 steps, upward
ancestry has maximum length 60,651 and edge reuse seven, rejecting bounded or
injective genealogy charging. All 20 upward intervals are global right
records, but 17 jump across prior intervals (maximum 2,237), while 1,142
downward moves also cross intervening intervals. The interval sequence is not
a local stack traversal. Upward record gaps have total mass 17,820,564;
14,775,263 values are unseen at reset time and 9,518,181 remain unseen at the
horizon, so fresh intervals alone are not a closed conservation system.

The focused target probes split the later audit into reproducible units.
`target_comb_extraction_probe` measures how maximal history-terminal combs
cover all target-low states. `target_ancestry_capacity_probe` follows blocker
first-time roots, fixed-root remounts, fresh-mass hulls, descent payments, and
record gaps. `target_high_candidate_probe` audits the complementary high-only
corridor. `target_ladder_probe` checks immediate and non-immediate reuse of
fresh entries as later terminal blockers. `target_right_record_probe` and the
seeded search separate standard-prefix evidence from claims that fail once an
arbitrary reachable-looking history is allowed. All outputs are empirical;
the corresponding exact finite examples are separately certified in Lean.
