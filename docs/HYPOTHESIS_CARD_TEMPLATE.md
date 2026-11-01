# Hypothesis card: `<short name>`

- ID: `H-YYYYMMDD-NN`
- Owner:
- Created:
- Status: `CONJECTURED`
- Research branch:
- Work state (separate from evidence label; e.g. unstarted / active / waiting / method stopped):
- Parent card / allocation cycle:

## Exact statement

Write all quantifiers, domains, constants, cutoff dependence, and history assumptions. If there is
a proposed Lean declaration, include its signature here before implementation.

## Why it would matter

- Frontier obligation discharged:
- Stronger than an existing identity or equivalent reformulation because:
- Smallest useful consequence:

## Allocation and decision value

- Mode: exploitation / local exploration / global exploration (split mixed work into units):
- Competing units and shared bottlenecks:
- Why this unit now (evidence, not an invented success probability):
- If successful, which dependency edge changes?:
- If unsuccessful, which candidate family is excluded and how does the next choice change?:

| Budget dimension | Cycle total | This unit planned | This unit actual | Cap / accounting rule |
|---|---|---|---|---|
| Agent work minutes (elapsed time recorded separately if parallel) | | | unstarted | |
| Compute / tokens / money, each in its own unit if used | | | unstarted | |

- Cycle allocation: exploitation / local exploration / global exploration / audit:
- Audit reservation and who performs the separate audit pass:
- First checkpoint (time or artifact):

Do not add unlike units or count the same work in both parent and child budgets. A starting
60/30/10 exploitation/exploration/audit split is a revisable policy, not an optimality claim.
Audit overruns reduce other allocations; never omit required validation to meet a time cap.

## Provenance and dependencies

- Definitions used:
- Lean theorems used:
- Unverified mathematical assumptions:
- Literature source or analogy:

## Falsification plan

- Small and boundary cases:
- Adversarial or weakened-history model:
- Discovery range:
- Frozen holdout range:
- Maximum one permitted repair:
- Stop condition:

Previously inspected ranges belong to discovery. For paper-only units, mark ranges not applicable
and retain boundary/countermodel checks. Freeze a fresh holdout after any permitted repair.

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| | `OBSERVED` | | |

## Semantic audit

- Informal statement implies formal statement:
- Formal statement implies intended consequence:
- Counterfactual examples that should make the statement false:
- Could the theorem be proved from weaker or vacuous assumptions?:
- Are reachability, freshness, time order, or actual-orbit provenance accidentally omitted?:

## Decision

- Continue / formalize / refute / stop:
- Continue only if (new evidence or a smaller non-equivalent obligation):
- Switch if / destination (including cost cap and repeated obstacle):
- Stop this method if (distinguish method failure from refuting the exact statement):
- Reason:
- Reopen only if:

## Allocation update log

| Checkpoint / date | Evidence and decision-changing information | Planned → actual cost | Old → new allocation and destination | Next acceptance / stop test |
|---|---|---|---|---|
| Unstarted | No execution evidence yet | — | — | |

Record counterexamples against the exact version they refute; a failed stronger auxiliary does
not refute the parent claim. Two consecutive cycles with the same obstacle and no new edge or
candidate elimination trigger the protocol's review of another mechanism. Record a method as
`STOPPED` without promoting or refuting an unresolved parent merely to close a work session.
