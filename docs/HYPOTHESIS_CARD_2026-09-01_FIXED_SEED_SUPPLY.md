# Hypothesis card: fixed-seed global supply no-go

- ID: `H-20260901-02`
- Owner: global-supply parallel round
- Created: 2026-09-01
- Status: `STOPPED`（exact no-go命題自体は`CONJECTURED`）
- Research branch: A枝、`H-20260901-01`のsingle-finite-seed強化

## Exact statement

Fix an absolute start clock `start` and one finite `State seed`.  Define the
deterministic continuation

```text
S 0       = seed
S (r + 1) = Basic.step (start + r + 1) (S r),
x r       = (S r).value - (start + r + 1).
```

The same `seed.value` and `seed.seen` are used for every horizon.  The seed
may be arbitrary apart from the harmless consistency condition
`seed.value in seed.seen`; allowing an arbitrary finite history makes the
question stronger and cleanly separates it from canonical reachability.

For fixed `target < c`, call this a fixed-seed recurrent supply corridor if

```text
(floor)       there is R0 such that target < x r for every r >= R0;
(least floor) there is R1 such that c <= x r for every r >= R1;
(uses)        for every R there is r >= R with x r = c;
(supply)      at every sufficiently late such use r,
              c + (start+r) belongs to (S (r+1)).seen.
```

The last field is the exact successor demand from the rigid use event.  In
the canonical corridor it is supplied by
`corridor_recurringCandidate_successor_seen`; in the arbitrary-state model
it is retained explicitly so that the question concerns supply rather than
unproved generic transport of the canonical theorem.

## Conjecture

No fixed-seed recurrent supply corridor exists.

Equivalently, for one deterministic continuation from one finite state,
the distinct demands `c + (start+r)` at arbitrarily late use clocks cannot
all have birth witnesses inside the finite seed or the continuation itself.
This is not a claim of a uniform finite maximum length: the existing seeded
countermodels choose a different history for each requested horizon.

## Why it would matter

- A proof discharges the recurrent right disjunct of
  `EventualHighCandidateTail.missingUnbounded_or_burstStream`, because the
  canonical orbit is the special seed `stateAt start`.
- A fixed-seed countermodel refutes every argument using only the exact
  local step law and finiteness of the initial history.  The remaining
  canonical problem would then require an independently testable invariant
  of histories generated from `initial`.
- The statement is stronger than finite preload exhaustion and weaker than
  Recaman surjectivity.  It mentions neither future target occurrence nor
  coverage of any interval.

## Required source decomposition

Let `seedMax` be the maximum of the finite list `seed.seen`.  For a
sufficiently late use clock `m=start+r` with `seedMax < c+m`, the demand is
not preloaded.  Let `j=s+1` be its least positive local occurrence:

```text
(S j).value = c+m,
and (S i).value != c+m for every 1 <= i < j.
```

The intended arbitrary-seed decomposition is

```text
0 <= s < r,
relative FirstAt of demand at local time s+1,
and either
  subtraction birth:
    local candidate(s) = c+m and absolute step(start+s+1) subtracts,
or
  addition birth:
    (S s).value+(start+s+1) = c+m and that absolute step adds.
```

In the addition branch the corridor cone should further give

```text
2*(start+s+1) + target < c+m,
```

after the cutoff boundary is excluded.  This is a genuine clock contraction.
The subtraction branch is the only possible carrier of a near-diagonal
source and therefore the exact ancestry/interval gate.  For the canonical
specialization `seed=stateAt start`, the relative witness agrees with the
global `FirstAt a`; `RecurringCandidateDemandBirth` formalizes that
canonical version.  It must not be silently reused for an arbitrary seed.

## Provenance and dependencies

- Definitions used: `State`, `step`, `CanSubtract`,
  `nextSubtractionCandidate`, `EventualHighCandidateTail`.
- Lean theorems used in the canonical specialization:
  `missingUnbounded_or_burstStream`,
  `corridor_recurringCandidate_successor_seen`,
  `corridor_forcedAddition_birth`, and
  `firstAt_succ_birth_dichotomy`.
- Unverified mathematical assumptions: the fixed-seed no-go itself and a
  strict resource deficit for the subtraction-birth channel.
- Literature source or analogy: none; this is an internal exact-state
  strengthening selected by the falsification protocol.

## Falsification plan

1. Search exact deterministic continuations from one fixed state.  The seed
   must be byte-for-byte identical when the tested horizon is extended.
2. Record every recurrent use, demand value, first occurrence, birth type,
   and whether the demand came from the seed or was generated internally.
3. Freeze a discovery range before running a disjoint holdout.
4. Test every proposed ancestry rank or deficit against:
   - `SeededHighCorridorNoGo`;
   - `SeededUseGapCounterexample` and its `A^(q+1)S^q` family;
   - same-candidate reuse with nonfresh output;
   - overlapping and crossing reuse intervals;
   - nonperiodic drift-and-reset schedules.

Computation may produce `COMPUTED` evidence or a candidate counterexample;
absence of a long continuation is never a proof.

- Discovery range: canonical prefix through clock `2,000,000`; synthesized
  bootstrap clocks `4..256`, candidates `1..32`, 4,096 frozen random plans
  at depths `2..4`, RNG seed `20260901`.
- Frozen holdout range: the selected byte-identical seed through ten times
  its planned end clock `865` (`8,650`), followed by a diagnostic
  replay through `1,000,000`; neither replay changes its 489-value history.
- Maximum one permitted repair: split internally generated demand births
  into subtraction and addition channels once.  No second repair.

## Acceptance test

Accept the conjecture only after all of the following hold:

1. An exact finite-window inequality, monotone resource, or well-founded
   ancestry relation has a strict deficit independent of the seed size once
   the finite seed is passed.
2. Every premise is supplied by the floor/use/supply fields above; no
   canonical reachability or future coverage assumption is inserted.
3. The statement survives the frozen exact countermodel holdout.
4. A complete paper dependency chain proves nonexistence before Lean work.
5. The minimal Lean theorem consumes the existing burst-stream payload and
   passes `Recaman/Audit.lean` and `./scripts/check.sh`.

## Stopping condition

Set this card to `REFUTED` or `STOPPED` if any one occurs:

- one explicit fixed finite state has a paper-proved infinite recurrent
  supply continuation;
- the ancestry relation is not closed under its own predecessor step;
- supply and demand remain of the same asymptotic order with no strict drift;
- the only repair invokes canonical reachability, target occurrence, or a
  future return;
- one evidence-based repair of the subtraction-source class is refuted.

Horizon-dependent preloads do not refute the card, but they do stop any
attempt to infer a uniform finite corridor bound from local data.

## Evidence log

| Date | Label | Artifact | Result |
|---|---|---|---|
| 2026-09-01 | `PROVED-LEAN` | `RecurringCandidateBurst` | Canonical recurrent uses create one distinct demand `c+m` and at least three additions. |
| 2026-09-01 | `REFUTED` | `SeededUseGapCounterexample` | Local floor/burst data allow arbitrarily small `sqrt(6m)` gaps when the seed changes with the interval. |
| 2026-09-01 | `PROVED-PAPER` | `PERIODIC_CANDIDATE_NOGO_2026-09-01.md` | A periodic non-truncated candidate schedule preserving a floor must diverge; a recurrent fixed-seed countermodel must be nonperiodic. |
| 2026-09-01 | `COMPUTED` | `periodic_candidate_nogo_check 1 16`; `17 22` | 8,388,606 periodic words checked; every balanced word has a negative-drift phase. |
| 2026-09-01 | `PROVED-LEAN` | `RecurringCandidateDemandBirth` | Canonical demand births split into legal subtraction and addition; the late addition branch has an exact half-clock contraction. |
| 2026-09-01 | `PROVED-LEAN` | `PeriodicCandidateNoGo` | The balanced finite core is kernel-checked: phase-drift sum `-p²` and existence of a negative cyclic phase. |
| 2026-09-01 | `PROVED-LEAN` | `SupplyAncestryCounterexample` | Forced subtraction-born reuse is not closed at birth, and distinct children can merge at one parent. |
| 2026-09-01 | `REFUTED` | `SUPPLY_ANCESTRY_AUDIT_2026-09-01.md` | The one permitted subtraction-source repair gives neither closed ancestry nor an injective/additive resource. |
| 2026-09-01 | `COMPUTED` | `fixed_seed_supply_falsifier 2000000 4096` | One fixed seed supports internally supplied counted uses at `94,286,862`; demands `114,306,882` are born at clocks `47,96,288`. No fourth use through clock `1,000,000`. |

## Semantic audit

- Informal statement implies formal statement: one seed and one deterministic
  continuation are quantified before all horizons and use clocks.
- Formal statement implies intended consequence: the canonical recurrence
  branch is obtained by choosing an actual `stateAt start` seed.
- Counterfactual example that should make the statement false: one finite
  arbitrary state whose exact continuation maintains the floor and supplies
  infinitely many recurrent uses.
- The arbitrary finite seed is deliberate.  A proof here transfers to the
  canonical orbit; a counterexample does not by itself refute the canonical
  branch.
- The demand values are distinct because the use clocks are distinct, but
  their FirstAt injection into clocks is only linear counting and is not a
  strict deficit.
- Previously visited values are reusable; no token is consumed merely by a
  forced addition.
- Eventually periodicity is now excluded only in the nondivergent case.
  Nonperiodic exponential or drift-and-reset supply remains admissible.
- No upper bound on addition-run length may be used.
- Reachability audit: canonical `FirstAt a` is unavailable in the arbitrary
  seed model.  The relative least local occurrence above `seedMax` must be
  used instead.

## Decision

- Continue / formalize / refute / stop: `STOPPED`.  The exact no-go remains
  `CONJECTURED`; neither an infinite countermodel nor a proof was obtained.
- Reason: the predeclared stop condition “ancestry is not closed under its
  own predecessor step” is met, and the broadened relation has same-order
  supply/demand with no strict drift.  The finite search also shows that one
  fixed seed can internally supply three uses, so raw demand counting is too
  weak.
- Reopen only if: an independently falsifiable external-blocker-debt
  inequality separates required additions from future legal subtractions,
  or a canonical-only invariant separates `stateAt start` histories from the
  fingerprinted arbitrary seed without assuming the desired return.
- Do not begin the final Lean no-go theorem until a strict paper deficit is
  present.
