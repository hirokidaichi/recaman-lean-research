# Supply ancestry audit — 2026-09-01

## Conclusion

The subtraction-born branch of
`corridor_forcedAddition_birth_classified` is not closed on forced supplier
nodes.  It returns

```text
CanSubtract (t + 1) (stateAt t),
```

whereas another application of the supplier theorem at `t` requires the
opposite premise.  Retaining the hidden `FirstAt` witness makes the failure
stronger: at the birth exposure the candidate is fresh, so it cannot be a
history-blocked forced use.

Broadening the node to the predecessor value gives a genuine
clock-decreasing first-occurrence ancestry, but loses the recurring-demand
shape and is not injective.  Its subtraction interval contributes exactly
the already-known endpoint ledger identity, whose intervals can cross and
overlap.  Addition-born demands have a half-clock contraction, but the
recurrence stream is only cofinal and may be arbitrarily sparse.  The two
branches therefore give no strict demand-versus-supply drift from the
current payload.

Status of the closed subtraction-ancestry proposal: `REFUTED`.
Status of this ancestry/drift research branch: `STOPPED`.

The main single-finite-seed self-supply question remains `CONJECTURED`; this
audit removes one proposed way of proving it.

## Bounded research question

For a sufficiently late rigid use clock `m`, put

```text
x_m = c + m.
```

The second forced addition exposes `x_m` as its failed subtraction
candidate.  If the first occurrence of `x_m` is a taken subtraction, does
the birth classification produce another node of the same supplier class,
with a strictly decreasing rank, so that iteration gives a finite-seed
global deficit?

Acceptance required one of the following.

1. An exact relation with preserved corridor, forcedness, demand provenance,
   and a strictly decreasing rank, together with a paper dependency chain.
2. A concrete failure identifying the first premise lost, followed by an
   audit of the weakest broadened relation.

The stopping condition was reduction to endpoint ledger/injective counting,
or supply and demand remaining of the same order.  Both stopping conditions
were met.

## Four-role audit

- Proposer: specialize the birth theorem to the rigid demand `x_m`, then
  recurse through subtraction births.
- Falsifier: check the branch polarities, small standard-orbit examples,
  shared-parent examples, and a disjoint frozen range.
- Formalizer: identify the exact existing Lean statements that would be the
  recursion step and its subtraction payment.
- Auditor: verify that the relation preserves the informal supplier node and
  produces more than a repackaged ledger identity.

No recursive ancestry wrapper was formalized because the falsifier and
auditor reached the predeclared stop.  The useful positive classification
and the two finite counterexamples were nevertheless formalized separately
in `RecurringCandidateDemandBirth` and `SupplyAncestryCounterexample`.

## Exact specialization to a rigid demand

At a rigid use clock `m`, the event and burst theorems give

```text
a (m + 1) = c + 2m + 2,
nextSubtractionCandidate (m + 1) = c + m = x_m,
not CanSubtract (m + 2) (stateAt (m + 1)).
```

For large `m`, `x_m` clears any fixed cutoff hull.  Applying
`corridor_forcedAddition_birth_classified` with `n=m+1` yields a clock `t`
with `t+1 <= m+1` and one of two branches:

```text
S: CanSubtract (t + 1) (stateAt t)
   and nextSubtractionCandidate t = x_m;

A: not CanSubtract (t + 1) (stateAt t)
   and x_m = a t + (t + 1).
```

The underlying theorem `corridor_forcedAddition_birth` additionally says
that `t+1` is the first occurrence clock of `x_m`.  The public conclusion of
`corridor_forcedAddition_birth_classified` drops this `FirstAt` field even
though its proof selects that witness.  A combined lemma could retain it,
but doing so does not repair the argument below.

### Addition branch

After enlarging the fixed cutoff by one, the witness lies strictly inside
the old corridor and `corridor_value_law` gives

```text
target + (t + 1) < a t.
```

Consequently

```text
target + 2(t + 1) < x_m = c + m.
```

This is a real half-clock contraction:

```text
t + 1 <= floor((m + c - target - 1) / 2)
```

with the subtraction and floor interpreted in the integers; the preceding
strict inequality is the exact natural-number form.  This part is
`PROVED-LEAN` as `corridor_recurringCandidate_late_demand_birth`; it is not
the failed step.

### Subtraction branch: the first lost premise

The desired recursive node at clock `t` would need

```text
not CanSubtract (t + 1) (stateAt t),
```

because supplier classification applies to a forced addition.  The branch
provides its negation.  With the retained first-occurrence proof, `x_m` is
fresh before clock `t+1`; the legal subtraction is precisely the step that
creates it.  Thus this exposure is a birth, not another blocked use.

Mapping a forced use of `x_m` to another forced use of the same value does
not help.  No such intermediate use is supplied by the theorem.  Mapping it
back to its unique birth terminates at the legal node; mapping it to the
original forced use is circular.

This closed-node proposal is `REFUTED` directly by the theorem's exact
premise polarity.

## The weakest broadened ancestry

Suppose a value `v` is first born by subtraction at clock `b=t+1`.  Define

```text
parent(v) = a t = v + b.
```

Take the first occurrence of `parent(v)`.  Its clock is strictly less than
`b`; if that birth is another subtraction, repeat, and if it is an addition,
stop.  The first-occurrence clock is a well-founded rank, so this generic
ancestry always terminates.

However, the following supplier premises are lost at the first edge.

1. `parent(v)` need not be exposed at a forced addition.
2. It need not equal `c+m'` for any rigid use clock `m'`.
3. It inherits neither the recurring-candidate floor event nor an unbounded
   stream of nodes of its own type.
4. Different children may share the same predecessor value, because that
   value may recur at several clocks and make different fresh subtractions.

Only “a large corridor-internal orbit value with an earlier first clock” is
preserved.  That property holds for generic provenance and is not a supply
deficit.

## Small exact standard-orbit failures

The new exact probe scans forced positive candidates in chronological order.
The first subtraction-born forced candidate is

```text
a 19 = 62,
a 20 = 42 = 62 - 20             (first birth, legal subtraction),
a 35 = 78,
78 - 36 = 42                    (state 35, forced use at clock 36).
```

Thus the natural back edge from the forced use of `42` lands immediately on
a legal, not forced, exposure.

The first failure of injectivity for the broadened predecessor map is
already contained in the prefix through state `133`:

```text
a 109 = 261,
a 110 = 151 = 261 - 110,
a 113 = 265 and 265 - 114 = 151 is blocked;

a 125 = 261,
a 126 = 135 = 261 - 126,
a 133 = 269 and 269 - 134 = 135 is blocked.
```

The distinct subtraction-born forced candidates `151` and `135` share the
same predecessor value `261`.  Its own first-occurrence ancestry is

```text
261 --S at clock 109 from 370,
370 --A at clock 108.
```

This is an exact standard-orbit counterexample, stronger than a free-history
or arbitrary-seed countermodel for any claim based only on local
`Basic.step`, first occurrence, and predecessor identity.  The seeded
use-gap family remains a separate warning: finite local demands can be
preloaded, but it does not address a single fixed global seed.

The shared-parent claim was frozen after the discovery pass.  A disjoint
state-window pass `[10,000,001,20,000,000]` found another exact pair:

```text
parent 605746
child 359133: birth clock 246613, forced use state 10039825
child 359097: birth clock 246649, forced use state 10039849.
```

The general-window observations are `COMPUTED`; they are not corridor
theorems.  The two smallest standard-prefix examples are independently
`PROVED-LEAN` in `SupplyAncestryCounterexample`.  Neither claim says that the
displayed states lie in an eventual corridor.

## Why the subtraction resource is only the old ledger

In the subtraction branch, `x_m` is exposed at the earlier state `t` and
again at the later forced state `n=m+1`.  Applying
`same_positive_candidate_reuse_subtraction_balance` gives exactly

```text
2 * (subSum n - subSum t) + (n - t) + upperTri t = upperTri n.
```

This is the endpoint subtraction ledger specialized to equal candidate
values.  It contains no strict surplus.  `PROVED-LEAN` counterexamples
`five_high_candidate_reuse_intervals_overlap_counterexample` and
`high_candidate_reuse_intervals_cross_counterexample` show that such
payments cannot be summed using disjointness, laminarity, or a one-stack
claim.

Tracing predecessor first occurrences does not restore additivity: the
standard-prefix pair above shows that paths can merge at a reused parent.
Charging only the distinct birth clocks is valid, but it is precisely the
one-birth-per-clock injection already present in the hypothesis card.

## Drift audit

Partition rigid demands through a horizon into addition-born and
subtraction-born values.

- Addition-born demands inject into early birth clocks and satisfy the
  half-clock contraction above.
- Subtraction-born demands inject into legal subtraction birth clocks, but
  their reuse intervals have only the exact endpoint ledger and can overlap.
- All demand values are distinct, so the total birth map uses at most one
  clock per demand.  This gives linear capacity, not a shortage.
- The recurrence conclusion is only `for every M, there exists m >= M`.
  It gives no positive lower density for use clocks; an arbitrarily sparse
  cofinal sequence is compatible with every linear clock-capacity bound.
- Burst outputs can themselves be addition births of later demands on the
  affine self-supply lattices already listed in the hypothesis card, so they
  cannot be counted as automatically disjoint extra cost.

Therefore addition contraction plus subtraction birth accounting does not
produce a cutoff-independent strict drift.  Any repair would need a new
global input such as a uniform overlap bound, a non-merging mass attached to
reused parents, or a lower density for rigid uses.  None follows from the
current corridor/burst payload, and assuming future occurrence or canonical
reachability would be circular.

## Evidence

- `PROVED-LEAN`: `corridor_forcedAddition_birth_classified` returns legal
  subtraction in its subtraction-born branch, the opposite of the recursive
  forcedness premise.
- `PROVED-LEAN`: `same_positive_candidate_reuse_subtraction_balance` is the
  exact available interval payment.
- `PROVED-LEAN`: the five-overlap and crossing counterexamples rule out
  direct aggregation of those payments.
- `PROVED-LEAN`: `corridor_recurringCandidate_demand_birth_classified` and
  `corridor_recurringCandidate_late_demand_birth` retain the rigid demand's
  exact birth branches and prove `target + 2(t+1) < c+m` in the late
  addition branch.
- `PROVED-LEAN`: `subtractionBorn_42_forcedReuse_counterexample` certifies the
  forced-to-legal polarity reversal, and
  `subtractionBorn_sharedParent_counterexample` certifies parent merging.
- `REFUTED`: closure on forced supplier nodes and injectivity of the generic
  predecessor ancestry.
- `COMPUTED`: exact discovery and frozen-window commands at revision
  `b0cde869612789d1351441168dced4ec6f24167c`:

```text
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/supply_ancestry_probe.cpp -o /tmp/supply_ancestry_probe
/tmp/supply_ancestry_probe 10000001 0 10000000
/tmp/supply_ancestry_probe 20000001 10000001 20000000
```

Exact output:

```text
window states=[0,10000000] forcedPositive=2121439 additionBorn=835048 subtractionBorn=1286391
ancestryClockViolations=0
firstSubtractionBornForced candidate=42 birthClock=20 parent=62 useState=35
firstSharedParent parent=261 child1=151 birth1=110 use1=113 child2=135 birth2=126 use2=133
prefix a109=261 a110=151 a113=265 a125=261 a126=135 a133=269
sharedParentBirth clock=109 kind=S predecessor=370 predecessorBirth=108 predecessorKind=A
windowSharedParent parent=261 child1=151 birth1=110 use1=113 child2=135 birth2=126 use2=133
window states=[10000001,20000000] forcedPositive=2099959 additionBorn=904028 subtractionBorn=1195931
ancestryClockViolations=0
firstSubtractionBornForced candidate=42 birthClock=20 parent=62 useState=35
firstSharedParent parent=261 child1=151 birth1=110 use1=113 child2=135 birth2=126 use2=133
prefix a109=261 a110=151 a113=265 a125=261 a126=135 a133=269
sharedParentBirth clock=109 kind=S predecessor=370 predecessorBirth=108 predecessorKind=A
windowSharedParent parent=605746 child1=359133 birth1=246613 use1=10039825 child2=359097 birth2=246649 use2=10039849
```

## Decision

- Closed subtraction-born supplier ancestry: `REFUTED`.
- Addition-contraction plus subtraction-ledger drift: `STOPPED`.
- Lean implementation: keep the positive demand-birth lemmas and finite
  counterexamples; do not add a recursive ancestry relation or wrapper,
  because no frontier-changing consumer survives the audit.
- Main finite-seed global self-supply conjecture: remains `CONJECTURED`.
- Reopen only after an independently falsifiable global constraint controls
  reuse-interval overlap or parent-path merging, or supplies a nonzero lower
  density of rigid use clocks without assuming target occurrence, future
  return, or canonical reachability.
