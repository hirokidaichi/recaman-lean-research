# Generalized orbit supply epoch

Date: 2026-09-02  
Hypothesis: `H-20260902-04`  
Decision: `COMPUTED`

## Conclusion

No preload-free orbit produces even one strict-high same-candidate link.  Across 20,001
generalized Recamán orbits (single initial value `v0 ∈ [0, 20000]`, exact greedy rule, history
of exactly `n + 1` values at clock `n`) and 1,272,765 internally supplied burst uses, every
candidate's chain length is one.  The frozen `H-G3` (no chain of length three) is not refuted,
and the observed census is stronger than the statement that was frozen.

Together with `H-20260902-03`, this isolates the mechanism of the only known multi-use
countermodel: three strict-high reuses of candidate 20 required 489 preloaded values at boundary
45, and no history that generates its own blockers has shown a single reuse of that shape.

## Frozen definitions

```text
generalized orbit:  a 0 = v0, history {v0}, exact Basic.step rule from clock 1
low entry:          legal subtraction into candidate c, 0 < c ≤ m
burst use:          low entry followed by additions at m+1, m+2, m+3
internal demand:    c + m first born at a clock in [1, m+1]
strict-high link:   two internal demand uses m < m' of one c with every
                    intermediate candidate strictly above its clock
```

The detector is the canonical-scan logic of `fixed_seed_supply_falsifier`; on the seeded
record it reports the two links of the three-use chain, and on `v0 = 0` it reproduces the
canonical census exactly.

## Reproduction

Base revision (working tree contains the probe):

```text
2424e49  docs: test the fixed-seed record against canonical history density
```

```bash
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/generalized_orbit_supply_probe.cpp \
  -o /tmp/generalized_orbit_supply_probe

/tmp/generalized_orbit_supply_probe 0 0 2000000        # canonical control
/tmp/generalized_orbit_supply_probe 0 1000 100000      # discovery
/tmp/generalized_orbit_supply_probe 1001 2000 100000   # frozen holdout
/tmp/generalized_orbit_supply_probe 0 200 1000000      # diagnostic
/tmp/generalized_orbit_supply_probe 2001 20000 100000  # diagnostic
```

Outputs:

```text
generalized-orbit-supply starts=[0,0] horizon=2000000 overflow=0 internalDemandUses=119 strictHighLinks=0
maxChain census: 1:1
best start=0 maxChain=1 links=0 c=78 uses=187
H-G3=not-refuted startsWithChain3=0

generalized-orbit-supply starts=[0,1000] horizon=100000 overflow=0 internalDemandUses=47175 strictHighLinks=0
maxChain census: 1:1001
best start=0 maxChain=1 links=0 c=78 uses=187
H-G3=not-refuted startsWithChain3=0

generalized-orbit-supply starts=[1001,2000] horizon=100000 overflow=0 internalDemandUses=58663 strictHighLinks=0
maxChain census: 1:1000
best start=1001 maxChain=1 links=0 c=3 uses=295
H-G3=not-refuted startsWithChain3=0

generalized-orbit-supply starts=[0,200] horizon=1000000 overflow=0 internalDemandUses=20048 strictHighLinks=0
maxChain census: 1:201
best start=0 maxChain=1 links=0 c=78 uses=187
H-G3=not-refuted startsWithChain3=0

generalized-orbit-supply starts=[2001,20000] horizon=100000 overflow=0 internalDemandUses=1146879 strictHighLinks=0
maxChain census: 1:18000
best start=2001 maxChain=1 links=0 c=130 uses=493
H-G3=not-refuted startsWithChain3=0
```

Discovery and holdout outputs have SHA-256
`d0bfd13f0818f291a8dc8891c43482120382034a9e6340c04521ed4f41bb33e8` and
`7bc29ea1c1407ea468f81900f3045e184b3fd49e5d205be35986811121e0a071`.

## Strongest evidence

- `COMPUTED`: 0 strict-high links in 1,272,765 internal demand uses over 20,001 starts, with
  every orbit's maximal chain equal to 1.
- `COMPUTED`: the canonical control `v0 = 0` matches the falsifier's canonical scan
  (119 uses, 0 links) exactly, so the two implementations agree on the semantics.
- `COMPUTED` (from `H-20260902-03`): the only known chains of length 2 and 3 come from seeds
  that violate the cardinality invariant by at least four values.

## Failed approach and semantic audit

The population deliberately keeps the full rigid use shape (legal entry, three additions,
internal demand) so that the result is about the mechanism the corridor needs, not about a
weaker statistic.  Absence over a finite horizon and a finite start range is not a proof; a
strict-high link could appear at a larger start or later clock.  The detector cannot be vacuous:
it reports links on the seeded record.

An overclaim to avoid is that "density proves the no-go".  What the two units show is that
density is *binding* on the known countermodels and that density-respecting histories have not
produced the mechanism at all.  The proof obligation is unchanged.

## Next decision

- Register the exact statement "no generalized orbit has a strict-high same-candidate link"
  as `CONJECTURED`.  It has a nonempty population, no cutoff, no target, and no reachability
  premise; a single refuting start closes it.
- The only permitted formalization route is a paper argument that the first strict-high link
  of a preload-free orbit forces a blocker that the orbit cannot have produced.  Do not start
  Lean work before that argument exists.
- Branch-A status is unchanged: the fixed-seed infinite supply no-go remains `CONJECTURED`,
  with density and the link conjecture as the open gate-3 candidates.
