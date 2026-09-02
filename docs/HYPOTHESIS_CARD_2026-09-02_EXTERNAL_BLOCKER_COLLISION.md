# Hypothesis card: external blocker / subtraction collision

- ID: `H-20260902-01`
- Owner: AI research epoch 2026-09-02
- Created: 2026-09-02
- Status: `STOPPED`
- Research branch: A, recurrent rigid supply

## Exact statement

Fix a candidate value `c`.  A **supplied use** is a clock `m` such that

```text
nextSubtractionCandidate m = c,
the step m+1 is a forced addition,
w_m := c + m is already in valuesThrough (m+1).
```

For a finite set `U` of supplied use clocks for `c`, let `w_m = c+m` and classify the first
occurrence of every `w_m`:

- `S(U)` contains `w_m` when its first occurrence is a legal subtraction landing;
- if the first occurrence of `w_m` is an addition at clock `b`, define its birth candidate
  `e_m = w_m - 2b`; `E(U)` contains `e_m` when `0 < e_m` (the addition was externally blocked).

Frozen hypothesis H4:

```text
For every c and every prefix U consisting of the first four supplied uses of c,
E(U) ∩ S(U) ≠ ∅.
```

The only permitted repair is to replace four by eight, without changing `E`, `S`, or the prefix
quantifier.

## Why it would matter

- Frontier obligation discharged: it would provide the first independently testable collision
  between external addition blockers and fresh subtraction supply requested by
  `CURRENT_FRONTIER.md`.
- It is stronger than birth-clock injection: it requires equality of resource values, not merely
  one birth clock per demand.
- If a uniform threshold survived, the next paper step would test whether each collision consumes
  a non-reusable subtraction-born value strongly enough to rule out an infinite rigid stream.

## Provenance and dependencies

- Definitions: `nextSubtractionCandidate`, `valuesThrough`, `FirstAt`, `CanSubtract`.
- Lean theorems: `EventualHighCandidateTail.diverges_or_rigidEventStream`,
  `corridor_recurringCandidate_demand_birth_classified`.
- Unverified assumption: the collision threshold H4.
- No canonical reachability or target occurrence is used in the statement.

## Falsification plan

- Boundary cases: candidate `c=0`, nonpositive addition birth candidate, repeated `E` values.
- Mandatory countermodel: the fingerprinted three-use seed is below the threshold and therefore
  neither confirms nor refutes H4.
- Discovery range: canonical prefix clocks `[0, 2,000,000]`.
- Frozen holdout: canonical prefix clocks `(2,000,000, 20,000,000]` after freezing H8 if H4 fails.
- Maximum one permitted repair: H4 to H8.
- Stop condition: an exact canonical prefix supplies four uses with no collision, followed after
  repair by eight uses with no collision; or the only surviving statement depends on a seed-size
  constant or future occurrence.

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-02 | `COMPUTED` | `b0cde869`; `external_blocker_collision_probe 2000000` | 1,568 supplied uses, 1,567 candidates, no candidate with four uses; H4 has an empty evaluation population. |
| 2026-09-02 | `COMPUTED` | frozen `external_blocker_collision_probe 20000000` | 4,798 supplied uses, 4,797 candidates, maximum two uses. Candidate 723 is used at clocks 984 and 4596 with `E={643}`, `S=∅`. H4 and H8 remain vacuous. |
| 2026-09-02 | `STOPPED` | [epoch report](EXTERNAL_BLOCKER_COLLISION_EPOCH_2026-09-02.md) | The same-candidate threshold cannot independently test the reopening gate: it requires the unproved recurrence stream before its collision conclusion has a nonempty domain. |

## Semantic audit

- Informal statement implies formal statement: sets are made only from exact first-occurrence and
  actual-step data.
- Formal statement implies intended consequence: a collision identifies a value that served both
  as an external forced-addition blocker and as a fresh subtraction landing.
- Counterfactual falsifier: four/eight supplied uses whose addition-birth blockers avoid every
  subtraction-born demand value.
- Reachability is not smuggled into the statement; the canonical probe is only the first
  falsifier. A surviving H8 would still require arbitrary-seed testing before Lean work.
- A collision alone is not yet a contradiction and must not be reported as a proof of the supply
  no-go.

## Decision

- Continue / formalize / refute / stop: `STOPPED`. H4 was not refuted; it was not meaningfully
  exercised. The only permitted H8 repair has the same empty-domain failure.
- Reason: the canonical discovery and frozen holdout contain no four-use candidate, and the known
  fixed seed contains only three uses. Therefore the proposed evaluator depends on first obtaining
  the very infinite same-candidate recurrence whose supply it was intended to constrain.
- Reopen only if: a debt/collision quantity aggregates across different candidate values or across
  a clock window, has a nonempty canonical and arbitrary-seed falsifier, and does not use another
  same-candidate use-count threshold.

