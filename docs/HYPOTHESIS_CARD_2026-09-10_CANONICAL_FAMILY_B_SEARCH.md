# Hypothesis card: canonical family B holdout search

- ID: `H-20260910-25`
- Status: `COMPUTED`: canonical B witness found; universal B absence `REFUTED` (E-125)
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`
- Roles sequential.

## Bounded question

Does a canonical family-B minimum P2 window occur by step10^9?
Replay the standard exact recurrence;10^7 is the existing discovery range,
and10^7+1..10^9 is the frozen extended holdout. Stop on the first B witness,
at10^9, at900 seconds, or when the declared value-bitset cap16*10^9 would
be exceeded. Any resource stop is reported as incomplete, not absence.

Use H22's complete B parameterization to avoid a billion-entry P2 hash map.
At a current A preceded by exactly one A, a B window must contain the latest
SS pair and latest completed A-run of length3. Let j,z be cumulative-S ranks
of these two events. Then n=4j−2z+1 and d=2n+1. Check d>0, old endpoint S,
that both event boundaries are inside, and that the preceding SS and enlarged
A gap are outside. These conditions describe every B window by H22. Any hit
is independently checked by scanning all prefix moments in its exact word.
The initial value0 and seen{0} remain fixed. At10^7, cross-check the known
value20,438,710 and A/S counts5,000,014/4,999,986. Record A3-run counts too.

Acceptance: an explicit canonical witness with all moments recomputed, or
COMPUTED absence through the completed cap. Neither outcome alone proves
an asymptotic result. H24's seeded witness prevents promotion to a generic
finite-history impossibility theorem. Do not extend the cap after a miss.

## Evidence

- The search stopped at its first candidate, step96,911,838 (sign time96,911,837), rather than continuing toward10^9. The exact window is `ASASASAAASS`, minimum lag11, n5,j3,z4; SS times96,911,826/96,911,827. `canonical_family_b_search.txt` contains the source revision/hash, checkpoint and witness.
- Independent fixed-witness verification used Python with a dense byte membership array instead of the C++ bitset, replaying from a0 through all96,911,838 steps. The value before the A is299,100,441, its candidate is202,188,603=a(96,911,826), and the new value is396,012,279. All smaller P2 lags fail. The full final20-step trace is in `verify_canonical_family_b.txt`.
- `python3 experiments/issue73_20260910/verify_canonical_family_b.py > docs/data/issue73_20260910/verify_canonical_family_b.txt`: PASS (about37 seconds in this run).
- This canonical witness is COMPUTED, not kernel-certified. The small finite-state B control is separately PROVED-LEAN. No claim of absence through10^9 or of an all-parameter canonical family is made.
- Stop the B-exclusion direction. Both H22 families must remain in any canonical capacity argument.
