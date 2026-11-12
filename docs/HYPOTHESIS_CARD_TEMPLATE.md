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

## Connection to arbitrary depth

- Assessment axis: `local_progress` / `depth_general_progress` (not evidence labels):
- Quantifiers and dependence on depth D, length, height and run count:
- Original actual-supply/free assumptions and their producers:
- Repeated use of the same free position, maximum load and boundary correction:
- Depth-dependent cost and its proved payment/cancellation:
- Concrete next inequality or history-preserving induction step consuming this result:
- Existing generic input and the genuinely new edge beyond it:
- Countermodel/no-go test for this mechanism, with reachability scope:

A fixed-depth improvement or paper-to-Lean connection is not by itself depth-general progress.
Freeze the exact candidate before falsification/implementation. Selecting a candidate is preparation,
not new evidence. A parameterized wrapper or assumed conversion to ordinary counts fails this assessment.

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

Do not add unlike units or count the same work in both parent and child budgets. From the
2026-11-12 user instruction use local completion 30 / general-principle exploration and
falsification 60 / independent audit 10. Reserve at least 25 minutes for a distinct mechanism.
This is a revisable policy, not an optimality claim.
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
- Local assessment, evidence, and whether the local cap has been reached:
- Depth-general assessment and the protocol 1.8 criterion actually met:
- Consecutive completed parent cycles without depth-general progress and prior tracker link:
- Switch if / destination (including cost cap and repeated obstacle):
- Stop this method if (distinguish method failure from refuting the exact statement):
- Reason:
- Reopen only if:

## Allocation update log

| Checkpoint / date | Evidence and decision-changing information | Planned → actual cost | Old → new allocation and destination | Next acceptance / stop test |
|---|---|---|---|---|
| Unstarted | No execution evidence yet | — | — | |

Record counterexamples against the exact version they refute; a failed stronger auxiliary does
not refute the parent claim. Keep local stagnation separate from depth-general stagnation.
Two completed parent cycles without depth-general progress trigger 20/70/10 even if local
lemmas succeeded. Never reset the counter merely at a date change. Record a method as
`STOPPED` without promoting or refuting an unresolved parent merely to close a work session.
