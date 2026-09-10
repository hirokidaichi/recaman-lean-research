# Hypothesis card: relevance census on the standard finite orbit

- ID: `H-20260910-07`
- Owner: Codex, four roles sequentially
- Created: 2026-09-10 JST
- Status: `COMPUTED` (E-103)
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`

## Bounded question

How many supplied A decisions in the first10,000,000 standard Recamán
steps are already covered by lag≤11, old sharp windows, and the new
bounded-excess conditions? How many remain outside, and what preceding
A-run lengths do they have? This evaluates usefulness and blind spots,
not the truth of global surjectivity or E-070.

## Exact computation and acceptance

At zero-based sign time t, prefix sums P(n)=sum signs[0:n] and
W(n)=sum i*signs[i] give P2(t,d) iff
`(P(t-d),W(t-d))=(P(t)-1,W(t)-t)`.
Store the latest prior index for each pair to recover the minimum P2
lag in all available finite history, without a lag cutoff. Verify this
algorithm against a separate direct sum/moment scan on all binary words
of lengths1..8 discovery,9..13 holdout, plus a standard prefix.

Then generate Basic.step exactly: a0=0, subtract at clock n iff a>n
and a−n is unvisited, otherwise add. Discovery steps1..100,000;
holdout100,001..1,000,000 and1,000,001..10,000,000. These are contiguous
parts of one deterministic trajectory, not independent statistical samples.
Record standard known prefix checks, maximum value/run, histogram of
minimum P2 lag and run index, source hash, compiler, command, revision.

Count each fixed R=0,1,2,3,4,8,16 separately. Also report the diagnostic
pointwise union over R; it is NOT one proved simultaneous capacity bound.
The old sharp threshold at L11 is m≥12; the current rank theorem's R0
threshold is m≥13, so neither is silently substituted for the other.

Acceptance is a reproducible exact census with independently checked
lookup semantics. Stop on a lookup mismatch, recurrence mismatch, integer
overflow or a declared memory/value cap; report the reached range only.
No Lean changes are required solely to bless a large computation.

## Evidence

`COMPUTED`: `verify_prefix_lookup.py` exhaustively compares the independent
prefix-key and direct moment scans for all binary words of lengths1..13,
plus the first5,000 standard signs. All pass; the standard value at5,000
is5,106. Exact output: `docs/data/issue73_20260910/verify_prefix_lookup.txt`.

`orbit_coverage_census.cpp` was compiled with Apple clang17,
`-O3 -std=c++20 -Wall -Wextra -pedantic`. Source hash, compiler, command,
all range counts and checkpoint states are in
`docs/data/issue73_20260910/orbit_coverage_census.txt`.
The declared value cap2,000,000,000 was never reached. Actual maximum
value61,998,984. The independent Lean reference first occurrence19@99,734
agrees. At10,000,000 the value is20,438,710, signed prefix sum28, and
weighted prefix sum20,438,682. The weighted invariant is also exactly
`a(n)-P(n)`, since signs are indexed from0 and recurrence clocks from1.

Across the complete range: A5,000,014; S4,999,986; finite-history
P2-supplied A1,315,896; lag≤11 supplied A3,898. Of supplied As,
1,312,147 have preceding A-run length0 (the previous sign is S).
Maximum preceding A-run length5, meaning the current A can complete a
run of length6. Every new bounded-excess class and the old sharp m≥12
class has count0. The largest observed minimum P2 lag is9,317,727.

These are finite descriptive counts. A missing finite-history P2 witness
does not imply an actual addition lacked a historical blocker: P2 is the
fixed-lag identity relevant to an eventually periodic tail, not a necessary
identity for every finite actual blocker. Likewise, periodic capacity does
not automatically yield a theorem about an arbitrary finite standard prefix.

Decision: stop further optimization of the long-A-run subclass in this
session. The accepted structural theorems remain valid, but their empirical
coverage is zero on this range. Shift the bounded research question to
all-lag supplies in an alternating/parity-restricted model, while keeping
its restrictions explicit. No claim of a uniform maximum run6 is made.

## Frozen follow-up H-07b: local-parity coverage

After H-09's finite falsifier passed, extend the same exact10^7-step
census to locally parity-clean witnesses. A minimum P2 window is clean
iff it contains S signs of only one time parity; a larger window cannot
remove a parity defect, so this detects existence of any clean witness.
Record all-clean and long-clean (d≥19) counts, their run and lag histograms,
and the union with lag≤11. Check the explicit old short plus half-lag
charges for S membership and injectivity throughout the finite prefix.
Use the same three ranges, recurrence and source checks. This is an exact
new statistic on reused data, not a new blind trajectory holdout. The
original census source/output remain unchanged.
