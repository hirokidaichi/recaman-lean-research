# Fixed-seed burst-supply falsification — 2026-09-01

## Pre-registered bounded question

Can one *identical* finite seeded `Recaman.State` generate, under the exact
greedy `Basic.step` rule, a nontrivial chain of repeated uses of one positive
candidate `c` in which every counted successor demand was born during the
continuation rather than preloaded?

For a seed placed immediately before absolute clock `startClock`, write
`d(t) = value(t) - (t+1)` whenever the subtraction clock is positive.  A
counted use at time `m` must satisfy all of the following exact checks:

1. the step into time `m` is a legal subtraction and `d(m)=c`, with `0<c<=m`;
2. the next three steps are forced additions;
3. `c+m` occurs in the history by time `m+1`, and its first occurrence is at
   a clock strictly after the seed boundary;
4. between consecutive counted uses `m<n`, every `d(t)` for `m<t<n` is
   defined and satisfies `t<d(t)`;
5. the seed's value and seen set are byte-for-byte identical for every replay
   horizon.  In particular, extending the holdout may not add blockers.

The search may use one uncounted bootstrap use whose demand is preloaded.
Its burst output may supply the first counted demand.  A later counted demand
may be supplied by any earlier continuation output, but never by the seed.

## Frozen acceptance test

- **Strong success:** an infinite fixed-seed construction with a complete
  paper proof of exact step legality and internal demand provenance.
- **Useful falsification:** one frozen fixed seed with at least four counted
  uses satisfying the five checks.  This only kills any proposed deficit
  lemma that already forbids that finite configuration.
- **Useful negative:** if that threshold is not met, report the best exact
  prefix and a frozen obstruction census distinguishing demand absence,
  candidate-floor failure, seed/subtraction collision, and an externally
  blocked addition.

Discovery is frozen to:

- the canonical seed through absolute clock `2,000,000`; and
- synthesized bootstrap clocks `m0=4..256`, candidates `c=1..32`, with
  candidate-return clocks selected from the three burst supply lattices
  `2m+2`, `3m+4`, and `4m+7`.  Within each interval, candidate-step words are
  selected before exact-state replay and must begin with three additions.

After choosing a seed using discovery only, holdout is one exact replay of
that unchanged seed through ten times its planned final clock (capped at
`10,000,000`).  The holdout records all additional qualifying uses; it does
not repair the seed or schedule.

## Frozen stopping condition

Stop this branch if every apparent longer success either changes the seed
with the requested horizon, places a counted value `c+m` in the seed, or
needs a blocker not produced by the frozen continuation.  A finite failure
does not prove that no fixed seed exists.  It instead identifies the next
candidate inequality or provenance condition.  No Lean theorem will be
created from a finite search.

## Role separation

- Proposer: burst-lattice return schedules and a fixed-seed synthesis rule.
- Falsifier: exact step replay, first-occurrence provenance, boundary cases,
  and the untouched holdout.
- Formalizer: none unless a parametric paper argument survives falsification.
- Auditor: compare every counted event with the five checks above and reject
  horizon-dependent preload as a semantic failure.

## Results

### Conclusion

`COMPUTED`: one identical finite seed supports **three** counted uses with
fully internal successor-demand provenance, but it does not self-extend to a
fourth use.  The frozen seed has boundary time `45`, current value `113`,
candidate `c=20`, and 489 distinct seen values.  Its reproducible fingerprint
is `14161494152507716643`.  There is one uncounted bootstrap use at `46`; the
counted uses and demand births are

```text
use 94  : demand 114 first occurs at clock 47
use 286 : demand 306 first occurs at clock 96
use 862 : demand 882 first occurs at clock 288
```

These are genuine burst supplies:

```text
94  = 2*46  + 2,  and 114 = c + 2*46  + 2
286 = 3*94  + 4,  and 306 = c + 3*94  + 4
862 = 3*286 + 4,  and 882 = c + 3*286 + 4.
```

Exact replay checks the legal entry subtraction, candidate `20`, three
forced additions, and the strict-high interior on all three planned return
intervals (including the bootstrap interval).  None of `114`, `306`, or
`882` belongs to the seed.  Thus the weak
claim “a fixed finite seed cannot support three such internally supplied
uses” is `REFUTED`.  The pre-registered useful-falsification threshold of
four counted uses was **not** met.

The unchanged seed was then replayed through the frozen holdout clock `8650`
and the extended diagnostic clock `1,000,000`.  Both runs found exactly the
same three qualifying uses and no fourth.  Consequently this is not an
infinite construction and does not refute the main burst-supply conjecture.

### Reproducible command

```text
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/fixed_seed_supply_falsifier.cpp \
  -o /tmp/fixed_seed_supply_falsifier
/tmp/fixed_seed_supply_falsifier 2000000 4096
```

The implementation freezes `mt19937_64` seed `20260901`, 4096 random plans
at each requested depth 2--4, and 32 return-word samples per interval.  The
depth-1 parameter pass is deterministic.  Repeating the entire command
twice produced byte-identical output; its SHA-256 is
`209f96a0ce2f9df65aed7713aaa8cac0ba695712a8231f974cae23d38b876b5c`.

Exact output:

```text
canonical discovery horizon=2000000 lowEntryUses=161315 threeAdditionBursts=119 internalDemandUses=119 distinctCandidates=119 strictHighLinks=0 maxChain=1
synthesis deterministic depth=1 cases=exact:1414 no_return_word:19507 seed_subtraction_collision:1175 history_subtraction_collision:974 total:23070
synthesis random depth=2 rngSeed=20260901 trials=4096 exact:31 no_return_word:3739 seed_subtraction_collision:98 history_subtraction_collision:209 preloaded_counted_demand:19
synthesis random depth=3 rngSeed=20260901 trials=4096 exact:1 no_return_word:3992 seed_subtraction_collision:24 history_subtraction_collision:60 preloaded_counted_demand:19
synthesis random depth=4 rngSeed=20260901 trials=4096 no_return_word:4081 seed_subtraction_collision:3 history_subtraction_collision:7 preloaded_counted_demand:5
best fixedSeed boundary=45 value=113 c=20 seedSize=489 fingerprint=14161494152507716643 bootstrapUse=46 seenFirst=0,20,66,106,113,161,205,210,257,260,310,406 seenLast=156847,157479,158112,158746,159381,160017,160654,161292,161931,162563,162571,163212 plannedCountedUses=94,286,862
best demandBirths=94<-47,286<-96,862<-288
frozen holdout horizon=8650 qualifyingUses=3 strictHighLinks=2 maxChain=3 firstNonHighAfterPlan=868 events=94@birth47,286@birth96,862@birth288
extended diagnostic horizon=1000000 qualifyingUses=3 strictHighLinks=2 maxChain=3 firstNonHighAfterPlan=868 events=94@birth47,286@birth96,862@birth288
interpretation finite computation only; no infinite fixed-seed claim proved or refuted
```

Here `no_return_word` is a sampler result, not an UNSAT certificate: it also
includes parity failures and cases in which the 32 frozen samples found no
strict-high return.  The depth-2--4 rows are not exhaustive.

### Strongest negative evidence

For the canonical seed through clock two million, 161,315 positive low
entries were found.  Only 119 had the three-addition burst and an internally
born successor demand.  Their 119 candidates were all different.  Hence
there was no same-candidate strict-high link and the maximum chain length was
one.  This is finite canonical evidence only.

The synthesized search exposes a sharper local obstruction.  For a proposed
word, let

```text
E = addition candidates not produced before their required addition,
S = candidates at planned legal subtractions.
```

Every member of `E` must be put in the fixed seed.  Exact realizability
therefore requires `E` to avoid every not-yet-taken member of `S`; otherwise
the seed turns that subtraction into an addition.  A second failure mode is
that an earlier continuation output hits a later member of `S`.  These are
the reported `seed_subtraction_collision` and
`history_subtraction_collision` classes.  Among depth-4 samples whose return
words were generated, every plan failed by one of those two collisions or
by preloading a counted demand.

### Failed attempts and uncertainty

- The standard initial state supplied isolated events but no repeated
  candidate within the discovery horizon.
- Depths one, two, and three had exact synthesized examples; their seeds are
  not the same seed.  Increasing the requested planned horizon generally
  adds external blockers, which is the forbidden horizon-dependent repair.
- The selected depth-3 seed remained unchanged in both later replays, but
  the candidate floor broke outside the planned third use and no fourth
  qualifying use appeared.
- The search did not enumerate all step words or all finite states.  It
  neither proves a depth-4 no-go nor excludes a different infinite seed.
- The seed is a legal finite `State` for `Basic.step`, but canonical
  reachability from `initial` is not claimed.

### Decision and next proof obligation

The finite synthesized-search branch is `STOPPED`: the four-use acceptance
threshold failed, the unchanged best seed did not self-extend, and longer
planned examples require a different external-blocker preload.  The main
single-finite-seed supply conjecture remains `CONJECTURED`.

The next inequality should measure **external blocker debt**, not successor
demands alone.  A useful exact target is a cutoff-independent statement that
for a chain of `k` strict-high returns, either

```text
|E| grows by a positive amount with k,
```

or some external/internal blocker collides with a required fresh
subtraction.  The three-use seed shows why counting only the distinct values
`c+m` is insufficient: all three are supplied internally while 489 other
seen values support the planned corridor.  Before Lean formalization, the
proposer must specify the weakest `E`-versus-`S` inequality that survives
candidate reuse and test it against this fingerprinted seed.
