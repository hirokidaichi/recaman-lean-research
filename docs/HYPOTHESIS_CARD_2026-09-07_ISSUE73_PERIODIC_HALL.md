# Hypothesis card: issue 73, periodic supply Hall gate

- ID: `H-20260907-09`
- Owner: root; independent combinatorial and geometric proof passes by the continuing workers
- Created: 2026-09-07 01:30 UTC
- Status: short-lag capacity `PROVED-LEAN`; full Hall H and E-067/E-070 `CONJECTURED`; refuted selector/budget classes `STOPPED`
- Base revision: `b4b5afaaac126acaa0c4fc0042bdaa4fafd289a1`
- Issue: https://github.com/hirokidaichi/recaman-lean-research/issues/73
- Time boundary: initial research pass ends by 02:30 UTC; finish a decisive result earlier if available

## One bounded question

For every integer p>=1 and periodic word epsilon: Z->{-1,+1} of period p with
positive sum S, define A and D as its addition and subtraction phase sets.
For t in A, a supplier lag d satisfies

```text
1 <= d <= p(p+1),
sum(i=1..d) epsilon(t-i) = 1,
sum(i=1..d) i*epsilon(t-i) = 0.                 P2
```

Let U be the phases admitting a supplier lag. For t in U let d_t be the least
such lag and N_t = {(t-i) mod p : 1<=i<=d_t, epsilon(t-i)=-1}.
The first gate is the precise Hall assertion

```text
for every T subset U, |union(t in T) N_t| >= |T|.       H
```

H implies |U|<=|D| (E-070), which implies U!=A (E-067) since |A|>|D|.
These implications do not reverse automatically. A failure of H stops only this
matching proof class. A counterword for U=A is required to refute E-067.

## Why this changes the next decision

The independently audited paper reduction E-065 shows that an eventually
periodic exact finite-history continuation must have positive S and U=A.
Thus E-067 would exclude such continuations. It would not prove surjectivity
or non-surjectivity, and variable-length or aperiodic block schemes remain open.
H is a concrete sufficient route to E-067, rather than an assumed injection.

## Known inputs and exclusions

- H-20260907-07: exact bounded-lag reduction and sign convention, PROVED-PAPER.
- E-066: finite positive-word census through p=18, not an all-period proof.
- E-069: oldest-S map fails on SSSSAAAASAAA; the whole domains still have a matching.
- Minimum-kappa, longest run, backward lex and maximal moment selectors already failed.
- Existing LoopClosingSubtraction treats the same local return mechanism; do not
  present arithmetic restatements of loop closure as a new global obstruction.
- No canonical reachability, subtraction freshness or seed-size assumption is
  allowed inside H. It is a pure finite-word conjecture.

## Frozen falsifier protocol

- Positive/boundary controls: p=1 all A (U empty); SAAA (one supplied phase,
  one S); E-069's collision with a valid alternative matching.
- Negative control: dropping the weighted-moment equation falsely supplies all
  phases of AA, despite D empty. The checker must distinguish this weaker model.
- Discovery: all positive-sum words with p=1..12; compute minimum-lag domains,
  maximum bipartite matching, and an explicit Hall-deficient subset if one exists.
- Frozen holdout: p=13..18, run only if discovery passes without a repair.
  These word ranges were used for a different property in the preceding unit;
  they are a split for the new H property, not a new canonical trajectory holdout.
- Independently compare supplier calculations with direct summation on all
  positive-sum words through p=8, and matching with all subset inequalities on
  those words. Verify every counterword's sums directly.
- Stop immediately on the first H counterexample. Record its exact N_t, deficient
  subset, U/A/D counts, and whether the weaker claims survive. No ad hoc map repair.
- If H survives finite tests, only an all-period proof or a precise failure of a
  proof class changes its status; increasing the horizon is not completion.

## Four roles and file boundaries

Root proposes and freezes H, then performs the exact falsifier. The macro worker
separately attempts a combinatorial all-period argument, and the joint-generation
worker attempts a geometry/height-area argument. Any successful paper proof or
counterexample receives an independent auditor before Lean implementation.
All new experiments and outputs go in issue73_20260907 directories. The earlier
hashed bundle and the user's recaman-visualizer directory are not edited.

## Acceptance and formalization gate

Accept either a complete all-period proof, or an explicit finite falsifier for H,
E-070 or E-067 with the exact logical scope. If the main word lemma is proved,
write its minimal consuming Lean statement and dependency chain before coding;
add major declarations to Recaman/Audit.lean and run ./scripts/check.sh.
At the time boundary, record failed attempts and the weakest unresolved edge;
do not turn absence of a counterexample into a theorem.

## Evidence and decision

First Hall gate completed: discovery 3,458 words and frozen holdout 225,587 words,
zero counterexamples. Direct-lag and all-subset checks agree on all 206
positive-sum words through p=8. This is COMPUTED, not a proof of H.

### Second falsifier gate, frozen before execution

Instead of extending the period census, search a finite automaton for a capacity
counterexample of unrestricted period. State = the last L signs. An S transition
has weight -1; an A transition has weight +1 if its preceding state has any P2
lag <=L, and weight 0 otherwise. A positive-weight directed cycle gives an
explicit periodic word with more supplied A than S, refuting E-070 (but not
necessarily E-067). The state graph is the full binary shift graph, so the cycle
word must be independently replayed and its exact P2 sums checked.

Frozen L values: discovery 3,7,11,15; conditional holdout 19 if no earlier positive
cycle is found. Stop immediately on a positive cycle. If none is found, save
the finite integer potential and check every edge inequality. Such a computed
finite certificate is not an all-L proof; a human-readable potential formula or
a Lean-checked certificate would be needed to promote an infinite-period claim.
No repaired weights or supply definitions are permitted after looking at output.

### Formalization decision after independent audit

The macro worker proved U7<=D by three disjoint local charging patterns; the
independent auditor checked short periods and multiple wraps. The root will
formalize this intended **all-period, lag<=7** count and its positive-sum
obstruction, not the still-unproved all-lag conjecture. Dependency chain:

```text
exact seven-bit history <-> P2 at some lag 1..7
-> verified finite potential inequality on every append-A/append-S transition
-> telescoping on any periodic word
-> number of supplied A (lag<=7) <= number of S
-> positive-sum word has an A with no supply lag<=7.
```

The finite potential is independent of the word period. The semantic bridge
must construct the state from the actual seven preceding signs of an arbitrary
periodic sign function; an assumed opaque closing path alone is insufficient.
The new result is consumed by the existing all-lag question: any counterword
must use a longer minimal lag. The moment parity further forces that lag >=11
on paper; do not conflate the formal lag<=7 theorem with all-lag capacity.

### Final evidence and decision

- `PROVED-LEAN`: `ShortPeriodicSupply.periodic_capacity` and
  `exists_phase_without_short_supply`, with the exact P2 semantic bridge and a
  lag11 negative control. Major declarations are in Recaman/Audit.lean.
- `PROVED-PAPER`: the explicit U7 injection gives Hall for all subsets of U7.
  The Lean proof establishes the capacity by a different finite potential,
  rather than formalizing this particular injection.
- `COMPUTED`: Hall through period18, finite automaton potentials through lag19,
  and the fixed-U7 matching extension to lag11. None proves the full H.
- `REFUTED`: oldest endpoint S, uniformly negative second moment, one-unit
  all-A future debt, and the escape-phase selector (including its one repair).
- `STOPPED`: those specific proof classes. H and E-067/E-070 remain open.
- No all-lag proof or all-A-supplied counterword was obtained. The next gate is
  whether long-lag classification yields a common all-lag charge, not merely
  another larger finite certificate.

See [the conclusion-first handoff](ISSUE73_PERIODIC_SUPPLY_2026-09-07.md) and
[reproducibility bundle](data/issue73_20260907/README.md) for commands, changed
files, failed attempts, exact source hashes and final validation.
