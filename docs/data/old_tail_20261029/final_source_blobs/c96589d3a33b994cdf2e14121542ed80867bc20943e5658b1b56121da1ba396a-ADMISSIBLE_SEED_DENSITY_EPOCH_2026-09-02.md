# Admissible seed density epoch

Date: 2026-09-02  
Hypothesis: `H-20260902-03`  
Decision: `COMPUTED`

## Conclusion

Every exact fixed seed found by the frozen 2026-09-01 synthesis protocol violates a canonical
history invariant.  With the two kernel-checked bounds

```text
|distinct seen values at clock n| ≤ n + 1        (valuesThrough_length)
every seen value at clock n       ≤ upperTri n    (a_le_upperTri)
```

imposed on the synthesised seed before replay, the protocol produces no seed at any depth.
The three-use record (489 seen values at boundary 45, where a canonical history holds at most
46) is therefore an artefact of blocker preloading that no `stateAt start` can provide.  The
minimum size excess over all synthesised plans is four values.

This does not prove the fixed-seed no-go: the sampler is not exhaustive, and the protocol never
tries to *generate* blockers inside the seed's own history.  It does identify history density
as the first reopening-gate-3 invariant that is both `PROVED-LEAN` for canonical states and
binding on every known countermodel.

## Frozen definitions

The synthesiser, ranges, lattices, return-word sampler, RNG seed, five counted-use checks, and
holdout rule are exactly those of `FIXED_SEED_SUPPLY_FALSIFICATION_2026-09-01.md`.  The only
change is an optional third argument.  When it is `1`, a synthesised seed with `initial` values
at boundary `B` is rejected before replay as

- `inadmissible_history_density` when `|initial| > B + 1`, or otherwise
- `inadmissible_history_height` when `max initial > B (B + 1) / 2`.

With the argument absent the program is unchanged.

## Reproduction

Base revision (working tree contains the patched falsifier):

```text
5108b17  theorem: certify the supplied-demand provenance witnesses
```

Commands:

```bash
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/fixed_seed_supply_falsifier.cpp \
  -o /tmp/fixed_seed_supply_falsifier

/tmp/fixed_seed_supply_falsifier 2000000 4096      # arbitrary seeds, 2026-09-01 record
/tmp/fixed_seed_supply_falsifier 2000000 4096 1    # canonically admissible seeds only
```

Arbitrary mode reproduces the 2026-09-01 output byte for byte
(SHA-256 `209f96a0ce2f9df65aed7713aaa8cac0ba695712a8231f974cae23d38b876b5c`).

Canonical-density mode:

```text
seed admissibility=canonical_density (|seen| <= boundary+1, max seen <= upperTri boundary)
canonical discovery horizon=2000000 lowEntryUses=161315 threeAdditionBursts=119 internalDemandUses=119 distinctCandidates=119 strictHighLinks=0 maxChain=1
synthesis deterministic depth=1 cases=no_return_word:19507 inadmissible_history_density:2608 inadmissible_history_height:955 total:23070
synthesis random depth=2 rngSeed=20260901 trials=4096 no_return_word:3739 inadmissible_history_density:357 
synthesis random depth=3 rngSeed=20260901 trials=4096 no_return_word:3992 inadmissible_history_density:104 
synthesis random depth=4 rngSeed=20260901 trials=4096 no_return_word:4081 inadmissible_history_density:15 
density excess min=4 seedSize=10 boundary=5 c=5 intervals=2
best fixedSeed none
```

## Strongest evidence

- `COMPUTED`: at depth 1 all 3,563 plans that reach synthesis are inadmissible (2,608 by size,
  955 by height); at depths 2, 3, 4 all 357, 104, 15 plans are inadmissible by size.  In the
  arbitrary mode the same plans yielded 1,414, 31, 1, and 0 exact seeds.
- `COMPUTED`: the smallest size excess is 4, attained by a two-interval plan at boundary 5 with
  candidate 5 that needs 10 seen values.
- `PROVED-LEAN` (existing): `valuesThrough_length` and `a_le_upperTri` are the only inputs to
  the filter.

## Failed approach and semantic audit

The filter cannot be satisfied by reordering or trimming the seed: the synthesiser already
stores only the blockers the plan requires plus `0` and the start value, so `|initial|` is a
lower bound on any preloaded history that realises the plan.  What the protocol does not try is
a seed whose blockers are themselves produced by an exact canonical-like prefix, which is the
only way a real history reaches boundary `B` with `B + 1` values.

A tempting overclaim is that "no admissible seed supports three uses".  The evidence supports
only "no seed of this protocol is admissible", which is a statement about the protocol's
preloading, not a bound on admissible seeds.

## Next decision

- Register history density as the gate-3 candidate.  Any future fixed-seed countermodel must
  be canonically admissible, or it says nothing about branch A.
- The next admissible unit needs a different generator: extend an exact prefix (canonical or
  otherwise admissible) rather than preloading blockers, and count uses under the same five
  checks.  Alternatively, attempt a paper bound on counted uses for admissible seeds.
- Branch-A status is unchanged: the fixed-seed infinite supply no-go is `CONJECTURED`, the
  collision routes are closed, and the density route is open but has no active card.
