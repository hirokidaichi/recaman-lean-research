# Hypothesis card: SS=3 reverse-nested extras

- ID: `H-20260910-33`
- Created: 2026-09-10 20:37 JST, timed session until 24:00
- Status: 6/6 orbit violators `COMPUTED` (E-143); unrestricted SS=2 one-per-run `REFUTED` separately (E-142)
- Research branch: issue #73, after E-142 killed free-history one-per-run

## Exact statement

On the canonical Recamán prefix of length 10^7, every pair of consecutive
current-A times that both carry a minimum P2 window of ssCount=3 has
gap 1, later lag f < earlier lag d, and extra := oldest `d-(f-1)` signs
of the earlier window satisfies:

- `NoSS extra` (ssCount extra = 0, join SS = 0)
- `mass extra = 1`
- `moment extra = 1 - (f-1)`
- extra starts with SA, not with AA, hence is not `minWord (f-2)`
- extra = `(SA)^k ++ minWord r` for an explicit `(k,r)`
- the later window starts with at least four A

This is the E-140 moment identity with a long non-sharp remainder.
It is a finite census, not a theorem about all SS=3 windows.

## Why it would matter

The free-history SS=2 counterexample uses the sharp extra `minWord`
starting AA. The only actual-orbit consecutive SS≥2 sources found so
far use a different extra, starting SA and strictly longer than minWord.
A surviving orbit obstruction might be “extra cannot start AA”, or
“SS=2 forbids the SA-started long extra that SS=3 permits”.

## Provenance and dependencies

- Definitions: newest-first past, P2, ssCount, minWord, E-140
- Unverified: nothing beyond the 10^7 prefix
- Not claimed: capacity, E-070, a new S-charge

## Falsification plan

- Recompute the 6 extras from signs; check mass/moment/ss independently
- Holdout: none yet; do not raise 10^7 to a theorem
- Stop if any of the 6 fails the E-140 identities, or if an SS=2
  orbit pair appears
- Do not reopen named S maps

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-10 20:37 | `COMPUTED` | `orbit_ss3_extra.cpp` then `orbit_ss3_extra_shape.py` | 6/6 E-140 identities, 0/6 minWord, 6/6 SA-start, 6/6 later lead≥4 |
| 2026-09-10 20:53 | `COMPUTED` | `orbit_ss3_extra.cpp` sa_pairs | extra=`(SA)^k ++ minWord r` for (25,96),(2,267),(249,832),(4,361),(590,2583),(335,1674); moment 3k−r matches |
| 2026-09-10 20:53 | `PROVED-LEAN` | `sa_prefixed_minWord` | the family is MassOneNoSS with moment 3k−r (E-146) |

## Semantic audit

- Informal “SS=3 one-per-run fails like SS=2 equality family” is false:
  extras are not minWord
- Formal census does not imply a general SS=3 remainder theorem
- Reachability is actual canonical orbit, not free history

## Decision

Record E-143 and E-146. minWord extra (k=0) is absent from canonical
SS=2 (E-144, E-147). Next: do not reopen named S-charges. Isolated a=0
nonsingletons are E-135 triples (E-148), not a new charge.
