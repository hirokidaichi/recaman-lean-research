# Global fixed-seed supply parallel round — 2026-09-01

## Conclusion

The recurrent burst-supply statement is still `CONJECTURED`, but the present
proof branch is `STOPPED`.  The exact demand-birth split is useful and is now
`PROVED-LEAN`; its subtraction branch does not preserve forced supplier
nodes, and the weakest generic ancestry can merge.  The available interval
payment is only the old endpoint ledger, while the use stream is merely
cofinal and may be arbitrarily sparse.  There is therefore no strict
demand-versus-supply deficit in the current payload.

An exact arbitrary-state falsifier found one byte-identical finite seed that
internally supplies candidate `20` at counted use clocks `94`, `286`, and
`862`.  This is `COMPUTED` and refutes any proposed bound of two supplied
returns, but the same seed has no fourth qualifying use through clock
`1,000,000`; it is not an infinite countermodel.

The periodic side question is closed at the appropriate evidence levels.
The balanced finite identity is `PROVED-LEAN`; the full statement that an
eventually periodic non-truncated candidate walk cannot have both a lower
floor and finite liminf is `PROVED-PAPER`.  Nonperiodic drift-and-reset
schedules remain possible.

## Hypothesis-card status

- `H-20260901-01`: `STOPPED`; the exact infinite supply claim remains
  `CONJECTURED`.
- `H-20260901-02`: `STOPPED`; its predeclared ancestry-closure and strict-
  drift stopping conditions were met.
- local `sqrt(6m)` use-gap: `REFUTED` and `STOPPED` from the preceding round.
- periodic balanced finite core: `PROVED-LEAN`.
- eventually-periodic floor plus recurrence schedule: `REFUTED` by a
  `PROVED-PAPER` argument.

## Bounded questions and acceptance tests

Four independent work units were run.

1. **Demand birth.**  Classify the first occurrence of `c+m` at a rigid use
   into a taken subtraction or an addition, retaining enough inequalities
   to show a strict clock contraction in the late addition branch.  Accept
   only after root import, axiom audit, and the repository check.
2. **Fixed-seed falsification.**  Replay the exact greedy rule from one
   unchanged finite state.  Count a use only when its demand is born after
   the seed, its entry is a legal subtraction, the next three steps add, and
   every intervening candidate is strict high.  Four counted uses were the
   predeclared useful-falsification threshold.
3. **Ancestry audit.**  Test whether subtraction births return another node
   of the same forced-supplier class with a decreasing rank.  Stop if branch
   polarity breaks closure or the broadened relation reduces to noninjective
   ledger accounting.
4. **Periodic no-go.**  Reconstruct the exact integer recurrence, prove the
   three sign-sum cases on paper, exhaust disjoint period ranges, and
   formalize only the indexing-sensitive finite identity.

## Role separation

- Proposer: source decomposition, candidate-return lattices, and cyclic
  drift identity.
- Falsifier: fixed-seed exact replay, canonical and holdout windows,
  branch-polarity checks, shared-parent search, and empty-period boundaries.
- Formalizer: demand-birth classification, finite ancestry counterexamples,
  and cyclic drift sum.
- Auditor: compare all formal conclusions with the canonical corridor and
  arbitrary-state claims; reject horizon-dependent preloads, future-return
  assumptions, and claims that a finite search proves an infinite no-go.

## Strongest evidence

### Demand birth — `PROVED-LEAN`

`RecurringCandidateDemandBirth` proves:

```text
corridor_recurringCandidate_demand_birth_classified
corridor_recurringCandidate_late_demand_birth
```

Every sufficiently late rigid demand has a first birth before its use.  A
subtraction birth is legal, not forced.  A late addition birth satisfies

```text
target + 2*(t+1) < c+m.
```

### Ancestry failures — `PROVED-LEAN` and `COMPUTED`

`SupplyAncestryCounterexample` kernel-checks the smallest local failures:

```text
42 is born legally at clock 20 and forced at clock 36;
151 and 135 are born from the same predecessor value 261.
```

The exact discovery window through state `10,000,000` and frozen holdout
`[10,000,001,20,000,000]` found no ancestry-clock violation and found a
second shared parent `605746`.  These large-window claims are `COMPUTED`;
they do not assert an eventual corridor.

### One fixed seed — `COMPUTED`

The best frozen seed has boundary `45`, current value `113`, candidate
`c=20`, 489 seen values, and fingerprint `14161494152507716643`.  After an
uncounted bootstrap use at `46`, it has:

```text
use 94  with demand 114 born at clock 47;
use 286 with demand 306 born at clock 96;
use 862 with demand 882 born at clock 288.
```

The first post-plan non-high candidate is at clock `868`.  Replays through
the frozen holdout `8,650` and diagnostic horizon `1,000,000` keep the seed
unchanged and find only those three uses.  The canonical discovery through
clock `2,000,000` found 119 internally supplied burst events, all with
different candidates and hence no strict-high same-candidate link.

### Periodic no-go — `PROVED-LEAN`, `PROVED-PAPER`, `COMPUTED`

For a balanced period of length `p`, `PeriodicCandidateNoGo` proves that the
sum of the actual cyclic phase drifts is `-p²`, so some phase has negative
drift.  The paper proof adds the negative, positive, and zero sign-sum cases
to show: a lower-bounded eventually periodic walk with the exact candidate
increment law must diverge.  The checker exhaustively verified 8,388,606
words over periods `1..22` in discovery and holdout ranges.

## Failed attempts and counterexamples

- Closed forced-supplier ancestry is `REFUTED`: the subtraction birth branch
  supplies `CanSubtract`, exactly opposite to the premise for another forced
  supplier node.
- Generic predecessor injection is `REFUTED`: children `151` and `135` merge
  at parent `261` in the standard prefix.
- Addition contraction plus subtraction accounting is `STOPPED`: the latter
  is exactly the reusable/crossing endpoint ledger, and cofinal uses have no
  density lower bound.
- The four-use fixed-seed threshold was not met.  Depth-four frozen samples
  that generated return words failed through seed/subtraction collision,
  history/subtraction collision, or preloaded demand.  `no_return_word` is a
  sampler outcome, not an UNSAT certificate.
- The full periodic conclusion was not promoted to `PROVED-LEAN`; an
  infinite-sequence/asymptotic interface would exceed the finite theorem and
  has no current consumer.

## Remaining uncertainty and next decision

No proof or infinite countermodel for one fixed finite seed was found.  The
next admissible research input is not another ancestry wrapper.  It must be
an independently falsifiable inequality for

```text
E = addition candidates not internally produced before their required use,
S = candidates reserved for future fresh legal subtractions,
```

showing cutoff-independent positive growth of `|E|` or an unavoidable
collision `E ∩ S`.  The fingerprinted three-use seed is a mandatory
regression case.  Reopen the supply branch only after such an inequality, a
non-merging mass, or a canonical-only invariant survives a frozen holdout
without assuming target occurrence, future return, or canonical reachability.

## Reproduction commands

```text
lake env lean Recaman/RecurringCandidateDemandBirth.lean
lake env lean Recaman/PeriodicCandidateNoGo.lean
lake env lean Recaman/SupplyAncestryCounterexample.lean

c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/periodic_candidate_nogo_check.cpp \
  -o /tmp/periodic_candidate_nogo_check
/tmp/periodic_candidate_nogo_check 1 16
/tmp/periodic_candidate_nogo_check 17 22

c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/supply_ancestry_probe.cpp -o /tmp/supply_ancestry_probe
/tmp/supply_ancestry_probe 10000001 0 10000000
/tmp/supply_ancestry_probe 20000001 10000001 20000000

c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/fixed_seed_supply_falsifier.cpp \
  -o /tmp/fixed_seed_supply_falsifier
/tmp/fixed_seed_supply_falsifier 2000000 4096

./scripts/check.sh
```

## Changed research artifacts

- Lean: `RecurringCandidateDemandBirth`, `PeriodicCandidateNoGo`,
  `SupplyAncestryCounterexample`, plus root and audit integration.
- Exact probes: `periodic_candidate_nogo_check.cpp`,
  `supply_ancestry_probe.cpp`, `fixed_seed_supply_falsifier.cpp`.
- Research notes: the two hypothesis cards, periodic no-go reconstruction,
  supply ancestry audit, and fixed-seed falsification report.

The pre-existing untracked `recaman-visualizer/` directory was not used or
modified by this round.
