# Hypothesis card: one-per-run for min SS=2

- ID: `H-20260910-32`
- Created: 2026-09-10 20:04 JST, timed session until 24:00
- Status: nested k=1 and k≥2 `PROVED-LEAN` (E-137); short remainder `PROVED-LEAN` (E-140); unrestricted consecutive one-per-run `REFUTED` on free histories (E-142); canonical 10^7 SS=2 still 0 (E-134)
- Research branch: issue #73, SS=2 allocation after E-136 stopped previous-S

## Exact statement

If t < u are current-A times in the same A-run (e(s)=A for all s∈[t,u])
and both have a minimum P2 window with ssCount=2, then false.

Split:
1. Nested: the later tail contains the earlier window as a prefix.
   `PROVED-LEAN`: an A-started P2 SS=2 word cannot have an SS=2 P2 prefix
   in its tail, because the remaining suffix would be SS-free of mass -1,
   hence (SA)^n S, whose moment forces a negative length.
2. Distance 2: later min SS=2 forces e(t-1)=A, so the run continues
   strictly before t. `PROVED-LEAN`.
3. Long-earlier: earlier lag exceeds the later tail. The remainder extra
   is necessarily SS-free of mass 1 (join-SS would overcount). If
   `|extra|+1 ≤ 2|v|`, this is `PROVED-LEAN` impossible (E-140). The
   remaining hole is extra longer than about `2|v|`. That hole is inhabited
   on free histories: glue `minWord (|v|-1)` to a mass-0 moment-(-1) SS=2
   tail. Smallest Lean-certified pair is `v=SSAAASAASS`, extra=`minWord 9`,
   old length 31, new=`ASSAAASAASS` (E-142). Canonical 10^7 still has 0
   SS=2 run violations (E-134). SS=3 on the same orbit has 6 long extras,
   all NoSS mass-1 with the E-140 moment, all SA-started not minWord (E-143).

## Why it would matter

At most one min SS=2 source per A-run would give |SS=2| ≤ |A-runs| ≤ |S|,
a separate capacity like E-127, not joint with E-128. Companions already
share a run with a clean source, so joint still needs a different S.

## Falsification

- Word search: later = A ++ tail, tail's min P2 never has SS=2 through
  length 23.
- Extension search: later = A ++ proper prefix of an earlier min SS=2
  word: 0 hits, lengths 11..23.
- Periodic 1..18 and canonical 10^7: 0 run violations (E-134).

## Decision

Unrestricted consecutive one-per-run is `REFUTED` on free histories.
Nested, distance-2, and short remainder remain theorems. Do not claim
orbit-level SS=2 one-per-run. The next bounded question is why the
minWord extra is absent from canonical 10^7 while SA-started long extras
appear for SS=3. Do not reopen named S-charges.
