# Cone excursion census

Date: 2026-09-02  
Parent unit: `H-20260902-04` (diagnostic)  
Labels: `COMPUTED` census, one derived `CONJECTURED` statement

## Conclusion

The strict-high excursion that follows a burst use always collapses long before the doubling
clock, and no cone-exterior excursion of any preload-free orbit lasts from a clock `s` to `2s`.
Across the canonical orbit through clock 2,000,000 and 20,000 generalized orbits through clock
100,000:

- every one of 1,252,246 burst uses with candidate `c ≥ 2` has its first low candidate
  (`a t - (t+1) ≤ t`) at a clock `t < 2m + 2`; the largest ratio `t / m` is `1.44` at `m = 25`,
  `1.098` for `m ≥ 100`, and `1.033` on the canonical orbit;
- none of about 85 million maximal cone-exterior runs (`a t > 2t + 1`) starting at clock
  `s ≥ max(16, 4 v0)` reaches clock `2s`; the largest ratio `(last + 1) / first` is `1.222`
  (canonical, `first = 18`) and at most `1.073` for runs starting after clock 9,000.

The first fact explains the zero strict-high links of `H-20260902-04`: a same-candidate reuse
needs the walk to stay above its clock from the burst to the next use, and the walk never does
so for more than about a tenth of the use clock once `m ≥ 100`.

## Semantic caveat

The strict-high condition `a t - (t+1) > t` is the between-use condition of the 2026-09-01
fixed-seed protocol.  It is **stronger** than the eventual-high corridor of branch A, which only
requires the candidate to stay above the fixed `target`.  A corridor stream may pass through
cone-interior clocks (`target + t + 1 < a t ≤ 2t + 1`) between uses.  Therefore neither the link
conjecture `E-021` nor the excursion bound below excludes the corridor; they constrain the
seeded protocol's model and the shape of self-supply through cone-exterior excursions only.
Any future fixed-seed or preload-free unit must state which between-use condition it uses.

## Frozen questions and definitions

```text
burst use:        legal subtraction into candidate c with 2 ≤ c ≤ m, additions at
                  m+1, m+2, m+3, and c + m first born at a clock in [1, m+1]
breaker:          least t > m with a t - (t+1) ≤ t
cone-exterior run: maximal interval of clocks t with a t > 2t + 1, counted only
                  when it starts at t ≥ max(16, 4 v0)
Q1  every breaker satisfies t < 2m + 2
Q2  every counted run [first, last] satisfies last + 1 < 2 first + 1
```

A breaker is always a subtraction step: after an addition at clock `t` the candidate is
`a (t-1) - 1 ≥ 2t - 2 ≥ t`, so additions cannot end a strict-high excursion.  The probe
confirms `intoAddition = 0` everywhere; this part is arithmetic, not evidence.

## Reproduction

```bash
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/cone_excursion_probe.cpp -o /tmp/cone_excursion_probe

/tmp/cone_excursion_probe 0 0 2000000        # canonical
/tmp/cone_excursion_probe 0 1000 100000      # discovery
/tmp/cone_excursion_probe 1001 2000 100000   # holdout
/tmp/cone_excursion_probe 2001 20000 100000  # diagnostic
```

```text
cone-excursion starts=[0,0] horizon=2000000 overflow=0 burstUses=119 noBreakerInHorizon=0
breaker t/m bins [1,1.25)=119 [1.25,1.5)=0 [1.5,2)=0 [2,inf)=0 intoSubtraction=119 intoAddition=0
Q1 breakersAtOrAfterDoubling=0 maxRatio=1.03333 (start=0,c=8,m=450,t=465)
Q2 runFloor=4 coneExteriorRuns=161323 runsReachingDoubling=0 maxRatio=1.22222 (start=0,first=18,last=21)

cone-excursion starts=[0,1000] horizon=100000 overflow=0 burstUses=47111 noBreakerInHorizon=22
breaker t/m bins [1,1.25)=47085 [1.25,1.5)=4 [1.5,2)=0 [2,inf)=0 intoSubtraction=47089 intoAddition=0
Q1 breakersAtOrAfterDoubling=0 maxRatio=1.44 (start=72,c=19,m=25,t=36)
Q2 runFloor=4 coneExteriorRuns=7727372 runsReachingDoubling=0 maxRatio=1.22222 (start=0,first=18,last=21)

cone-excursion starts=[1001,2000] horizon=100000 overflow=0 burstUses=58609 noBreakerInHorizon=11
breaker t/m bins [1,1.25)=58598 [1.25,1.5)=0 [1.5,2)=0 [2,inf)=0 intoSubtraction=58598 intoAddition=0
Q1 breakersAtOrAfterDoubling=0 maxRatio=1.11321 (start=1731,c=85,m=106,t=118)
Q2 runFloor=4 coneExteriorRuns=7193819 runsReachingDoubling=0 maxRatio=1.07256 (start=1127,first=9992,last=10716)

cone-excursion starts=[2001,20000] horizon=100000 overflow=0 burstUses=1146417 noBreakerInHorizon=308
breaker t/m bins [1,1.25)=1146109 [1.25,1.5)=0 [1.5,2)=0 [2,inf)=0 intoSubtraction=1146109 intoAddition=0
Q1 breakersAtOrAfterDoubling=0 maxRatio=1.09836 (start=2234,c=96,m=122,t=134)
Q2 runFloor=4 coneExteriorRuns=69944107 runsReachingDoubling=0 maxRatio=1.07044 (start=5862,first=48622,last=52046)
```

`noBreakerInHorizon` counts burst uses whose excursion was still open at the horizon; they are
excluded from the ratio census rather than counted as evidence either way.

## Derived exact statement

```text
Cone-exterior excursion bound (CONJECTURED, E-023):
for the canonical orbit and every clock s ≥ 16, if a t > 2t + 1 for all t in [s, e],
then e + 1 < 2s + 1.
```

The generalized-orbit form replaces `16` by `max(16, 4 v0)`.  The statement uses no target,
cutoff, or reachability premise, and a single run reaching its doubling clock refutes it.  It is
an independent partial statement about how long the orbit stays above the line `2t + 1`; by the
caveat above it does not bear on the branch-A corridor, whose floor is the fixed target line.

## Next decision

- Record `E-022` (census) and `E-023` (excursion bound) and attach the semantic caveat to
  `E-021`.
- The preload-free and fixed-seed units should be re-specified with the corridor's actual
  between-use condition (candidates above a fixed floor, not above the clock) before any
  further countermodel search; the strict-high form is now known to be far more restrictive
  than the corridor.
- No Lean work follows from this census.
