# Hypothesis card: window-aggregated demand provenance

- ID: `H-20260902-02`
- Owner: AI research epoch 2026-09-02
- Created: 2026-09-02
- Status: `REFUTED`
- Research branch: A, recurrent rigid supply (reopening gates 1 and 3 of `CURRENT_FRONTIER.md`)

## Exact statement

A **low supplied use** is a state clock `m` such that

```text
m + 1 < a m,
c := a m - (m + 1) ∈ valuesThrough m        (the step m+1 is a forced addition),
c ≤ m                                       (the candidate is low),
w := a m - 1 ∈ valuesThrough m               (the successor demand is already supplied).
```

Here `w = c + m` is exactly the rigid successor demand of `RecurringCandidateBurst`, written
without reference to any candidate recurrence.  Let `FirstAt a w j` be the canonical first
occurrence of `w`.

- The demand is **subtraction-born** at `t = j` when the step into clock `j` is a legal
  subtraction.
- The demand is **addition-born** at `b = j` when that step adds; its birth blocker is
  `e = w - 2b` whenever `2b < w`, and the birth is **truncated** when `2b ≥ w`.

For `k ≥ 0` let the dyadic window `W_k = {m : 2^k ≤ m < 2^(k+1)}`, and over the low supplied
uses with `m ∈ W_k` define

```text
E(W_k) = { w - 2b : addition-born demand with 2b < w },
S(W_k) = { w      : subtraction-born demand }.
```

Frozen statements, all quantified over the canonical orbit only:

```text
H-W  for every k with E(W_k) ≠ ∅ and S(W_k) ≠ ∅,  E(W_k) ∩ S(W_k) ≠ ∅;
H-S  for every subtraction-born low supplied demand w born at t,  2t < w;
H-A  for every addition-born low supplied demand w born at b,     2b < w.
```

`H-W` is the cross-candidate, fixed-window form of the collision test that
`H-20260902-01` could not evaluate.  `H-S` asks whether the subtraction channel is
half-clock contracted like the corridor addition channel.  `H-A` asks whether the corridor-only
contraction `target + 2(t+1) < c + m` already holds on the canonical prefix without the corridor
premise.

## Why it would matter

- Frontier obligation discharged: gate 1 asks for an unavoidable collision `E ∩ S` or strict
  growth of `|E|` aggregated across candidates or a clock window; `H-W` is that statement with a
  nonempty evaluation population.
- Stronger than an existing identity because: none of the three statements follows from the
  step law, the burst theorem, or the corridor contraction; each has a concrete canonical
  countermodel shape.
- Smallest useful consequence: a surviving `H-S` would be a canonical-only invariant candidate
  (gate 3) excluding the near-diagonal subtraction source that the fixed-seed cards identified
  as the only carrier of an infinite stream.

## Provenance and dependencies

- Definitions used: `nextSubtractionCandidate`, `valuesThrough`, `FirstAt`, `CanSubtract`.
- Lean theorems used: `recurringCandidate_addition_burst` (identifies `w = c + m` as the sole new
  demand), `corridor_recurringCandidate_late_demand_birth` (corridor-only contraction that
  `H-A` tests canonically).
- Unverified mathematical assumptions: the three frozen statements.
- Literature source or analogy: none; internal exact-state falsification.

## Falsification plan

- Small and boundary cases: `m ≤ 8`, truncated births with `w = 2b`, candidate `c = m`.
- Adversarial or weakened-history model: the fingerprinted fixed seed
  (`14161494152507716643`) has three addition-born demands with births `47, 96, 288` for
  `w = 114, 306, 882`; it satisfies `H-A`, has no subtraction-born demand, and is therefore
  not a test of `H-W` or `H-S`.
- Discovery range: canonical clocks `[0, 2,000,000]`.
- Frozen holdout range: canonical clocks `(2,000,000, 20,000,000]`, run once as census even
  if discovery already refutes.
- Maximum one permitted repair: replace dyadic windows by windows `[T, 4T)`; no change to
  `E`, `S`, or the contraction constants.
- Stop condition: any statement refuted in discovery is `REFUTED` without repair; a statement
  surviving both ranges is at most `COMPUTED` and requires a paper proof before Lean work.

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-02 | `COMPUTED` | `11fae7f` + working tree; `window_demand_provenance_probe 2000000` | 971 low and 597 high supplied uses in 21 windows. 13 windows have both `E` and `S` nonempty; all 13 have `E ∩ S = ∅`. 444 near-diagonal subtraction births, 259 truncated addition births. |
| 2026-09-02 | `REFUTED` | same command | `H-W`, `H-S`, `H-A` all fail inside the discovery range. First witnesses: `H-S` at `m=112, c=39, w=151, t=110` and `m=132, c=3, w=135, t=126`; `H-A` at `m=5, c=1, w=6, b=3`. |
| 2026-09-02 | `COMPUTED` | frozen `window_demand_provenance_probe 20000000` | 2,987 low and 1,811 high supplied uses in 25 windows. 17 applicable windows, all collision-free. 1,533 near-diagonal subtraction births, 732 truncated addition births. Window `[2^23, 2^24)`: 733 low uses, 449 subtraction-born of which 401 near-diagonal, 75 blocked and 209 truncated addition-born. |
| 2026-09-02 | `PROVED-LEAN` (cross-check) | `SupplyAncestryCounterexample` | The first two `H-S` witnesses are the kernel-certified first occurrences `FirstAt a 151 110` and `FirstAt a 135 126`. |

The discovery output is deterministic; its SHA-256 is
`4e9e46539e16e258682974ac719c9475f9ac118b46d7f5a896c7a3aaee80a57f`.

## Semantic audit

- Informal statement implies formal statement: a low supplied use is defined by exact history
  membership at clock `m`; no candidate recurrence, target, or cutoff appears.
- Formal statement implies intended consequence: `H-W` would be the aggregated collision that
  gate 1 requests; `H-S` would forbid the near-diagonal subtraction channel canonically.
- Counterfactual examples that should make the statements false: a window whose blockers all
  differ from its subtraction-born demands; a value landed legally just below its later use
  clock; a demand born by an addition whose candidate was zero.
- Could the theorem be proved from weaker or vacuous assumptions?: not applicable, all three
  are refuted; the refutations use only exact canonical steps.
- Reachability, freshness, time order, or actual-orbit provenance omitted?: none; every witness
  is a canonical clock with a canonical first occurrence.

## Decision

- Continue / formalize / refute / stop: `REFUTED` for all three statements, in the discovery
  range, with no repair exercised.
- Reason: cross-candidate window collisions never occur in 17 applicable windows through 20M,
  so the collision phrasing of gate 1 is dead in both its same-candidate and its aggregated
  form.  Near-diagonal subtraction births are the canonical majority (401 of 449 in the
  largest complete window), so gate 3 cannot use a birth-clock contraction.  Truncated
  addition births are canonical and common, so the corridor contraction is a corridor-only
  fact and is not a canonical separator.
- Reopen only if: gate 1 is restated as strict cutoff-independent growth of `|E|` against a
  quantity that is not a collision, or gate 3 proposes an invariant that admits near-diagonal
  subtraction sources.  Do not run another `E ∩ S` collision design.
