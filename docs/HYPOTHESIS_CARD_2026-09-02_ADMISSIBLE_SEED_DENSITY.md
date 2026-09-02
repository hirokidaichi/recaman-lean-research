# Hypothesis card: canonically admissible seed density

- ID: `H-20260902-03`
- Owner: AI research epoch 2026-09-02
- Created: 2026-09-02
- Status: `COMPUTED`（exact命題は`CONJECTURED`のまま）
- Research branch: A, fixed-seed supply (reopening gate 3 of `CURRENT_FRONTIER.md`)

## Exact statement

Two invariants of every canonical state `stateAt n` are `PROVED-LEAN`:

```text
(valuesThrough_length)  (valuesThrough n).length = n + 1
(a_le_upperTri)         ∀ t ≤ n, a t ≤ upperTri t ≤ upperTri n
```

Call a finite `State` placed immediately before absolute clock `boundary + 1`
**canonically admissible** when

```text
|distinct seen values| ≤ boundary + 1   and   max seen value ≤ upperTri boundary.
```

Every seed produced by the frozen synthesis protocol of `H-20260901-02`
(`fixed_seed_supply_falsifier`: canonical horizon `2,000,000`, bootstrap clocks `4..256`,
candidates `1..32`, three burst lattices, RNG seed `20260901`, 4,096 plans per depth `2..4`,
32 return-word samples per interval) is now filtered by this predicate before any exact
replay.  Frozen question:

```text
H-D  Under the unchanged protocol, does any canonically admissible seed realise
     at least one counted use with the five checks of the 2026-09-01 falsification?
```

The comparison target is the arbitrary-seed record of three counted uses
(fingerprint `14161494152507716643`, 489 seen values at boundary `45`).

## Why it would matter

- Frontier obligation discharged: gate 3 asks for a canonical-only invariant that separates
  `stateAt start` from an arbitrary finite state without assuming future return or target
  occurrence.  History density is such an invariant, already kernel-checked, and this unit
  tests whether it is *binding* on the known countermodels.
- Stronger than an existing identity because: the earlier cards allowed arbitrary seeds, so
  their countermodels said nothing about canonical histories; the filter measures exactly how
  far they are from canonical.
- Smallest useful consequence: if no admissible seed exists in the protocol, the three-use
  record is an artefact of inadmissible blocker density, and density becomes the first concrete
  gate-3 candidate.

## Provenance and dependencies

- Definitions used: `State`, `step`, `CanSubtract`, `valuesThrough`, `upperTri`.
- Lean theorems used: `valuesThrough_length` (`EventualHighCorridorSecondMissing`),
  `a_le_upperTri` (`OrbitBounds`).
- Unverified mathematical assumptions: none in the filter; the sampler is not exhaustive.
- Literature source or analogy: none.

## Falsification plan

- Small and boundary cases: boundary `3..8` where `upperTri boundary` is small enough that the
  height bound alone rejects a seed.
- Adversarial model: the arbitrary-seed mode is rerun unchanged and must reproduce the
  2026-09-01 output byte for byte (SHA-256 `209f96a0…`).
- Discovery range: identical to `H-20260901-02` (same ranges and RNG seed).
- Frozen holdout range: identical to `H-20260901-02` (ten times the planned end clock).
- Maximum one permitted repair: none; the filter is a fixed predicate.
- Stop condition: report the census and the minimum density excess; do not tune the protocol.

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-02 | `COMPUTED` | `5108b17` + working tree; `fixed_seed_supply_falsifier 2000000 4096` | Arbitrary mode is byte-identical to the 2026-09-01 record (SHA-256 `209f96a0ce2f9df65aed7713aaa8cac0ba695712a8231f974cae23d38b876b5c`). |
| 2026-09-02 | `COMPUTED` | `fixed_seed_supply_falsifier 2000000 4096 1` | Canonical-density mode: deterministic depth 1 has 3,563 plans reaching synthesis, 2,608 rejected by size and 955 by height; random depths 2/3/4 have 357/104/15 plans reaching synthesis, all rejected by size. No admissible seed at any depth. Minimum size excess is 4 (10 seen values needed at boundary 5, candidate 5, two intervals). |

## Semantic audit

- Informal statement implies formal statement: the filter is applied to the exact seed set the
  synthesiser would replay, before the replay, so it cannot reject a seed for a reason other
  than density.
- Formal statement implies intended consequence: an admissible seed would be a countermodel
  candidate that canonical density does not exclude; its absence in the protocol means that
  every exact seed of `H-20260901-02` used canonically impossible blocker preloading.
- Counterfactual examples that should make the statement false: an admissible seed with one or
  more counted uses; the arbitrary-mode record failing to reproduce.
- Could the conclusion be proved from weaker or vacuous assumptions?: no theorem is claimed;
  `no_return_word` remains a sampler outcome, and the protocol never generates blockers inside
  the seed's own history, which an admissible construction would have to do.
- Reachability, freshness, time order, or actual-orbit provenance omitted?: the filter uses
  only two canonical invariants; it does not assume the seed is reachable.

## Decision

- Continue / formalize / refute / stop: `COMPUTED`; the exact fixed-seed no-go stays
  `CONJECTURED`.
- Reason: the frozen protocol has no canonically admissible seed at any depth, and even the
  best plan needs four more seen values than a canonical history can hold at its boundary.
  Density is therefore the first gate-3 invariant that is both kernel-checked and binding on
  every known countermodel.
- Reopen only if: a synthesiser that generates blockers by an exact prefix (rather than
  preloading them) finds an admissible multi-use seed, or a paper argument bounds the counted
  uses of every admissible seed.  Do not weaken the density predicate to fit the sampler.
