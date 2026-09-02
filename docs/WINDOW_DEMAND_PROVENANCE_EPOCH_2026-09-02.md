# Window-aggregated demand provenance epoch

Date: 2026-09-02  
Hypothesis: `H-20260902-02`  
Decision: `REFUTED`

## Conclusion

The three frozen statements of the window-aggregated unit are all refuted inside the canonical
discovery range and remain refuted in the frozen holdout.  This closes the collision family of
branch-A reopening designs: the same-candidate threshold of `H-20260902-01` was vacuous, and the
cross-candidate dyadic-window form `H-W` has a nonempty population (17 applicable windows
through clock 20,000,000) in which the blocker set and the subtraction-born demand set never
meet.

Two further canonical facts are now `COMPUTED` and constrain future cards:

1. Subtraction-born successor demands are usually near-diagonal.  In the largest complete
   window `[2^23, 2^24)`, 401 of 449 subtraction-born demands are born at a clock `t` with
   `2t ≥ w`.  Any canonical-only invariant proposed for gate 3 must admit this channel.
2. Addition-born successor demands are frequently truncated births (`2b ≥ w`, zero candidate).
   The corridor contraction `target + 2(t+1) < c+m` is therefore a corridor-only fact and does
   not distinguish the canonical prefix from a seeded state.

## Frozen definitions

A low supplied use is a state clock `m` with `m+1 < a m`, candidate `c = a m - (m+1) ≤ m`
already visited (the step `m+1` is a forced addition), and successor demand `w = a m - 1 = c+m`
already visited by clock `m`.  The canonical first occurrence of `w` is classified as a legal
subtraction landing at `t` or an addition at `b`.  Blocked addition births with `2b < w`
contribute `e = w - 2b` to `E(W)`; subtraction births contribute `w` to `S(W)`, where `W` is the
dyadic window `[2^k, 2^(k+1))` containing `m`.

```text
H-W  E(W) ≠ ∅ ∧ S(W) ≠ ∅  →  E(W) ∩ S(W) ≠ ∅   for every window W
H-S  2t < w                                    for every subtraction-born demand
H-A  2b < w                                    for every addition-born demand
```

No target, cutoff, candidate recurrence, future return, or reachability premise is used.

## Reproduction

Base revision (working tree adds the probe):

```text
11fae7f2  docs: centralize the research frontier and stop the collision threshold
```

Commands:

```bash
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/window_demand_provenance_probe.cpp \
  -o /tmp/window_demand_provenance_probe

/tmp/window_demand_provenance_probe 2000000
/tmp/window_demand_provenance_probe 20000000
```

Discovery output (SHA-256 `4e9e46539e16e258682974ac719c9475f9ac118b46d7f5a896c7a3aaee80a57f`):

```text
window-demand-provenance horizon=2000000 lowSuppliedUses=971 highSuppliedUses=597 windows=21
window k:[2^k,2^(k+1)) low high candidates sBorn aBlocked aTruncated nearDiagonal |E| |S| |E&S|
window 0 0 0 0 0 0 0 0 0 0 0
window 1 0 0 0 0 0 0 0 0 0 0
window 2 1 0 1 0 0 1 0 0 0 0
window 3 0 0 0 0 0 0 0 0 0 0
window 4 1 0 1 0 0 1 0 0 0 0
window 5 1 0 1 0 0 1 0 0 0 0
window 6 3 1 3 1 0 2 1 0 1 0
window 7 4 1 4 1 2 1 1 2 1 0
window 8 5 1 5 0 2 3 0 2 0 0
window 9 5 0 5 1 1 3 1 1 1 0
window 10 6 2 6 1 1 4 1 1 1 0
window 11 11 3 11 6 1 4 4 1 6 0
window 12 14 5 14 6 5 3 3 5 6 0
window 13 29 6 29 13 7 9 10 7 13 0
window 14 43 24 43 24 9 10 20 9 24 0
window 15 53 20 53 18 17 18 17 17 18 0
window 16 62 37 62 33 13 16 27 13 33 0
window 17 115 66 115 57 30 28 51 30 56 0
window 18 138 76 138 70 24 44 58 24 70 0
window 19 260 173 260 158 50 52 149 50 158 0
window 20 220 182 220 114 47 59 101 46 114 0
H-W=REFUTED applicableWindows=13 collisionFreeWindows=13 7 9 10 11 12 13 14 15 16 17 18 19 20
H-S=REFUTED violations=444 (m=112,c=39,w=151,birth=110) (m=132,c=3,w=135,birth=126) (m=771,c=110,w=881,birth=765) (m=1346,c=254,w=1600,birth=1344) (m=2337,c=643,w=2980,birth=2051)
H-A=REFUTED violations=259 (m=5,c=1,w=6,birth=3) (m=17,c=7,w=24,birth=15) (m=32,c=13,w=45,birth=30) (m=65,c=25,w=90,birth=63) (m=100,c=63,w=163,birth=98)
```

Frozen holdout output, summary and the four largest windows:

```text
window-demand-provenance horizon=20000000 lowSuppliedUses=2987 highSuppliedUses=1811 windows=25
window 21 323 166 323 188 56 79 167 56 187 0
window 22 641 359 641 367 160 114 332 160 367 0
window 23 733 475 733 449 75 209 401 75 449 0
window 24 316 214 316 204 43 69 189 43 204 0
H-W=REFUTED applicableWindows=17 collisionFreeWindows=17 7 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24
H-S=REFUTED violations=1533 (m=112,c=39,w=151,birth=110) (m=132,c=3,w=135,birth=126) ...
H-A=REFUTED violations=732 (m=5,c=1,w=6,birth=3) (m=17,c=7,w=24,birth=15) ...
```

Window 24 is incomplete because the horizon `20,000,000` lies inside `[2^24, 2^25)`.

## Strongest evidence

- `REFUTED` `H-W`: every one of the 17 windows containing both a blocked addition-born demand
  and a subtraction-born demand has `E ∩ S = ∅`.  The collision is not merely rare; it never
  occurs, and within every window the blockers are pairwise distinct (`|E|` equals the blocked
  count except once, in window 20).
- `REFUTED` `H-S`: `1,533` subtraction-born demands through 20M are born at `2t ≥ w`.  The first
  two witnesses, `151` born at clock `110` and `135` born at clock `126`, are the values whose
  first occurrences `SupplyAncestryCounterexample` certifies in the Lean kernel; the probe and
  the kernel agree on both clocks.
- `REFUTED` `H-A`: `732` addition-born demands are truncated births.  The first is
  `a 3 = 6 = 3 + 3` with candidate `0`, later demanded at `m = 5` by candidate `1`.
- `COMPUTED`: per window, subtraction-born demands are roughly 55–65% of low supplied uses,
  and near-diagonal births are roughly 85–90% of those.

The near-diagonal witnesses are exact greedy events; they are not seeded.  They show that the
"only carrier of a near-diagonal source" identified by `H-20260901-02` is the canonical norm,
not an artefact of arbitrary seeds.

## Failed approach and semantic audit

The unit was designed so that discovery could refute before any data-dependent choice.  All
three statements failed at the smallest scales (`m = 5` for `H-A`, `m = 112` for `H-S`,
window 7 for `H-W`), so no repair was exercised and no threshold was tuned.

A tempting misreading is that `E ∩ S = ∅` is itself a law worth proving.  It is not: an empty
intersection has no consequence for the stream, and a one-window collision would not have
contradicted anything either.  The correct reading is that collision-shaped debt quantities have
no exact content on the canonical orbit, in either aggregation.

## Next decision

- Retire `E ∩ S` collision designs.  Gate 1 of `CURRENT_FRONTIER.md` keeps only the strict
  growth phrasing for `|E|`, and any future `|E|` quantity must be measured against a
  non-collision counterpart.
- Gate 3 invariants must admit near-diagonal subtraction births; birth-clock contractions
  cannot separate `stateAt start` from the fingerprinted seed, whose three demands are all
  blocked addition births satisfying `H-A`.
- Branch-A status is unchanged: the fixed-seed infinite supply no-go remains `CONJECTURED`;
  the ancestry/drift, same-candidate collision, and window collision routes are closed.
