# Hypothesis card: terminal A-run SS bound

- ID: `H-20261001-03`
- Owner: Codex, separate proposer / falsifier / formalizer / auditor passes
- Created: 2026-10-01
- Status: `PROVED-LEAN` (E-363); independent semantic review PASS. See [E-363-independent](statement_audits/E-363-independent.md). Issue #75 remains OPEN awaiting PR incorporation.
- Base: `07d75dfdb733dfa5196f608e63bd23dd754940bf`, isolated worktree.
- Research question: issue #75, sections 2 and 4 of E-361.

## Exact statement

For all finite newest-first Bool words W, A=true, S=false, overlapping
`q=OneSSMultiplicity.ssCount W`, and all natural t and X:

```text
W = (X ++ [false]) ++ replicate t true, P2 W -> t <= q.
The same hypotheses plus
  forall j, 0<j<length W -> not P2(W.take j)
give t>0 -> t<q, hence t<=q-1 (Nat subtraction truncates at zero).
In particular q=2 -> t<=1.
Every P2 word has such an X,t decomposition.
For each decomposition, length(W.reverse.takeWhile id)=t,
so t is the maximal terminal A-run length, not an arbitrary A suffix.
```

No length cutoff, assumed prefix ceiling, moment sign assumption, NoSAAS,
periodicity, current-A, owner family, orbit, or initial-history condition.

## Why it matters

Discharges the SS budget component of E-361 and makes every SS=2 minimal
donor's terminal A-run t belong to {0,1}, independently of its length.
It constrains t=L-r, not owner delta=r-kx or tight-set avoidance. The
all-q witnesses and general #73 are separate research units.

## Dependencies and pre-implementation chain

- Existing definitions: LeadingRunSupply mass/moment/P2, overlapping ssCount.
- Existing Lean: LowSSEndpoint.mass_ending_A, ssCount_post_A, ssCount_tail_le;
  mass_append, moment_append, mass_replicate_A;
  E-362 FirstP2EndingS.minimal_p2_ends_S.
- Repository search checked LowSSEndpoint, OnePerRun append count,
  SSFreeSupply, SSGapBudget, LeadingRunSupply and E-361/E-362.
- No uncommitted primary-checkout helper is used.
- Weakest new useful inequality: for every terminal-S/A decomposition,
  every suffix has mass at least min(0,t-q-1).
  Derive general mass >= -ssCount-1 by appending A to the existing
  mass_ending_A theorem. Appending A changes no SS count. Drop prefixes
  one sign at a time and use ssCount tail monotonicity; once inside the
  final A run suffix mass is nonnegative.
- If t>q, all suffix masses are nonnegative. Induction from
  moment(b::w)=mass(b::w)+moment w makes total moment positive at mass 1,
  contradicting P2. If t>=q all suffix masses are >=-1; total mass=1
  then gives every prefix mass<=2 by take/drop mass additivity.
  E-362 forces S termination, contradicting t>0. The ceiling is derived.
- P2 excludes all-A words; last-sign recursion constructs the terminal
  decomposition. Reverse/takeWhile verifies maximality for every decomposition.

## Falsification plan

- Boundary controls: AAS (q=t=0), AASASSA (P2, q=t=1, nonminimal),
  ASSA (moment zero, mass zero), A (mass one, nonzero moment),
  AAASSSASASA (minimal, q=2,t=1). Removing t>0 from strictness is false.
- Weakened history: all abstract words, no orbit restriction to weaken.
- Reproduce unchanged E-361 script: discovery lengths 3,7,11,15,19;
  existing holdout length 23. These are reproducibility runs, not new holdout.
- Preserve exact commands, script digest, base revision and output files.
- No repairs to the fixed issue statement permitted.
- Stop on counterexample, necessary new unproved assumption, or failure
  to find the complete suffix-to-prefix route within 90 minutes of formalization.

## Evidence log

| Date | Label | Command / revision | Result |
|---|---|---|---|
| 2026-10-01 | `PROVED-LEAN` | E-362, base revision | Exact ceiling-two first-P2 lemma is available; independent review was pending at that base revision and is now PASS. |

- Frozen before reruns: `docs/data/terminal_a_ss_bound_20261001/protocol.frozen.md`
  and `PRE_RUN_SHA256SUMS`.
- Reproduction of E-361 protocol on base `07d75df`:
  `python3 experiments/terminal_a_budget.py discovery` -> 3,021 P2 words,
  zero weak/strict-bound violations; `holdout` -> 30,554 P2 words,
  zero violations. These repeat existing holdout, not new independent data.
- `controls.json` records all five predeclared controls, including
  nonminimal q=t=1 and minimal q=2,t=1. Computation is `COMPUTED`.
- Formalization began 2026-10-01 08:43:30 UTC. The complete route passed
  `lake env lean Recaman/TerminalASSBound.lean` by 08:47 UTC, well
  within the 90-minute gate. No mathematical counterexample or repair.
  Initial failures concerned list rewrite recursion and inequality reflexivity.

## Semantic audit

- Informal/formal: same original P2 predicate and overlapping SS count;
  exact decomposition includes S and gives the maximum A suffix.
- Every P2 word must admit the decomposition; no hidden subset of P2 words.
- q=0/1 and t=0 must satisfy the truncated non-strict formulation.
- Counterfactuals above must still falsify strengthened/weak-hypothesis variants.
- E-362 is a proven theorem, not a new unproved hypothesis. The prefix
  ceiling must be derived from the suffix inequality inside this proof.
- Separate-session review is not claimed by a same-session auditor pass.

## Decision

The exact issue statement is formalized; no added ceiling, cutoff, or
defined hypothesis. Independent review is PASS in E-363-independent on the
unchanged source hash. Its R/W/C/T=9/7/0/0 counts terminal_run_length as a
run induction; the earlier conservative same-session count was 8/8/0/0.
End this unit at the SS bound. E-364 separately proves the sharp construction
without this upper bound. Issue #75 remains OPEN awaiting PR #78 incorporation.
