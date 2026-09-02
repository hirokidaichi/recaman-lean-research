# Hypothesis card: same-candidate supply chains in preload-free orbits

- ID: `H-20260902-04`
- Owner: AI research epoch 2026-09-02
- Created: 2026-09-02
- Status: `COMPUTED`（凍結命題H-G3は未反証。派生するexact命題は`CONJECTURED`）
- Research branch: A, fixed-seed supply (gate 3, follow-up of `H-20260902-03`)

## Exact statement

A **generalized orbit** with start `v0` is the exact greedy continuation of the state
`⟨v0, [v0]⟩` from clock `1`:

```text
a 0 = v0,   a (n+1) = if n+1 < a n ∧ a n - (n+1) ∉ history then a n - (n+1) else a n + (n+1).
```

Its history at clock `n` has exactly `n + 1` entries, so it satisfies the canonical
cardinality invariant `valuesThrough_length` and never preloads a blocker.  The canonical orbit
is the case `v0 = 0`.

Counted-use semantics are those of the canonical scan in `fixed_seed_supply_falsifier`:

- a **low entry** at clock `m` is a legal subtraction into candidate `c` with `0 < c ≤ m`;
- a **burst use** also has additions at `m+1, m+2, m+3`;
- an **internal demand use** also has `c + m` first born at a clock in `[1, m+1]`;
- a **strict-high link** joins two internal demand uses `m < m'` of the same `c` such that
  every clock `t` with `m < t < m'` has candidate `a t - (t+1) > t`;
- the **chain** of `c` is the number of consecutive strict-high linked uses.

Frozen hypothesis:

```text
H-G3  no generalized orbit with start v0 in the discovery or holdout range has a
      same-candidate chain of length ≥ 3 within horizon 100,000.
```

`H-G3` is the preload-free counterpart of the three-use arbitrary-seed record of
`H-20260901-02`.

## Why it would matter

- Frontier obligation discharged: gate 3 asks whether a canonical-only invariant separates
  `stateAt start` from the known countermodels.  `H-20260902-03` showed that every known
  countermodel violates history density; this unit asks whether density-respecting histories
  can produce the same chains at all.
- Stronger than an existing identity because: the population is 20,001 exact orbits with more
  than a million internal demand uses, all satisfying the cardinality invariant by construction.
- Smallest useful consequence: a refutation would give a density-admissible three-use
  countermodel and kill density as a gate-3 invariant; survival with zero links makes the
  strict-high link itself a falsifiable exact conjecture for preload-free histories.

## Provenance and dependencies

- Definitions used: `State`, `step`, `CanSubtract`, `nextSubtractionCandidate`.
- Lean theorems used: `valuesThrough_length` (cardinality invariant of the population);
  `recurringCandidate_addition_burst` (why three additions and the demand `c + m` are the
  rigid use shape).
- Unverified mathematical assumptions: none in the probe; the horizon is finite.
- Literature source or analogy: none.

## Falsification plan

- Small and boundary cases: `v0 = 0` must reproduce the canonical scan of the falsifier
  (`119` internal demand uses, `0` links, chain `1` through clock `2,000,000`).
- Adversarial model: the arbitrary-seed record of `H-20260901-02` is the positive control for
  the link semantics; it is excluded from this population by construction because its seed has
  489 values at boundary 45.
- Discovery range: starts `[0, 1000]`, horizon `100,000`.
- Frozen holdout range: starts `[1001, 2000]`, horizon `100,000`.
- Diagnostics (not label-raising): starts `[0, 200]` at horizon `1,000,000`; starts
  `[2001, 20000]` at horizon `100,000`.
- Maximum one permitted repair: none.
- Stop condition: any start with chain `≥ 3` refutes; otherwise report the link census.

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-02 | `COMPUTED` | `2424e49` + working tree; `generalized_orbit_supply_probe 0 0 2000000` | Start `0` reproduces the falsifier's canonical scan: 119 internal demand uses, 0 strict-high links, chain 1. |
| 2026-09-02 | `COMPUTED` | `generalized_orbit_supply_probe 0 1000 100000` (SHA-256 `d0bfd13f…`) | 1,001 orbits, 47,175 internal demand uses, 0 strict-high links; every orbit has chain 1. `H-G3` not refuted. |
| 2026-09-02 | `COMPUTED` | frozen `generalized_orbit_supply_probe 1001 2000 100000` (SHA-256 `7bc29ea1…`) | 1,000 orbits, 58,663 internal demand uses, 0 links, all chains 1. `H-G3` not refuted. |
| 2026-09-02 | `COMPUTED` (diagnostic) | `generalized_orbit_supply_probe 0 200 1000000`; `2001 20000 100000` | 20,048 and 1,146,879 internal demand uses respectively, 0 links in both. |
| 2026-09-02 | `COMPUTED` (diagnostic) | `cone_excursion_probe` on the same ranges | Every strict-high excursion after a burst use ends before clock `2m+2` (`t/m ≤ 1.098` for `m ≥ 100`), and no cone-exterior run reaches its doubling clock; see `E-022`. |

## Semantic audit

- Informal statement implies formal statement: the population is defined by one exact state
  and the exact step rule; no cutoff, target, or reachability from `initial` is assumed.
- Formal statement implies intended consequence: a chain of length `k` in a preload-free
  orbit would be a density-admissible `k`-use supply example.
- Counterfactual examples that should make the statement false: any start whose orbit reuses
  one low candidate three times with strict-high excursions between the uses.
- Could the conclusion be proved from weaker or vacuous assumptions?: the link detector is
  the same logic that reports two links on the seeded record, so links are detectable; the
  absence of a positive control inside the population is itself the finding.
- Reachability, freshness, time order, or actual-orbit provenance omitted?: none; births are
  exact first occurrences inside each orbit.
- Strength of the between-use condition: strict-high (`candidate > clock`) is the 2026-09-01
  protocol's condition and is stronger than the corridor's fixed-target floor; the link
  conjecture therefore constrains cone-exterior self-supply only, not the corridor stream
  (see `CONE_EXCURSION_CENSUS_2026-09-02.md`).

## Decision

- Continue / formalize / refute / stop: `COMPUTED`; `H-G3` is not refuted, and the census is
  stronger than the frozen statement: no strict-high link at all in 20,001 orbits.
- Reason: with blockers generated only by the orbit itself, no candidate is ever reused in the
  rigid burst shape across a strict-high excursion, whereas 489 preloaded values gave three
  such reuses.  Density is therefore binding on the mechanism, not only on the record.
- Reopen only if: a preload-free orbit exhibits a strict-high link, or a paper argument shows
  that the first strict-high link forces a preloaded blocker.  The derived exact statement
  “no generalized orbit has a strict-high same-candidate link” is registered as
  `CONJECTURED` and is the next admissible falsification target, with the paper attempt as the
  only permitted formalization route.
