# Hypothesis card: actual eventual-positive-periodic supply bridge

- ID: `H-20260910-17`
- Status: `PROVED-LEAN` (E-116; canonical positive-drift specialization)
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`
- Roles: proposer / falsifier / formalizer / auditor, sequential.

## Exact bounded question

For every global periodic Boolean e, period p>0, and N≥0, assume
canonicalSign(n)=e(n) for all natural n≥N, and positive sign sum of one
period. Prove that every A phase of e has a finite positive P2 lag, WITHOUT
assuming bounded supplier lags, positive subtraction candidates, or that
suppliers occur after N. This is the positive-drift part of E-065 for the
canonical trajectory. Arbitrary externally seeded recurrences are outside
this exact theorem unless separately derived.

Acceptance: derive candidate growth, exclusion of finite preperiod history,
existence of a actual late historical blocker, and transport its resulting
P2 to every periodic A phase. Add an explicit current-clock threshold if
convenient. Stop if an initial-history term or nonpositive-candidate case
is silently assumed away. Do not promote the full E-065 statement about
all finite seeds from a theorem about the canonical sequence alone.

## Informal dependency chain before implementation

Strengthen the H16 block arithmetic: for b length p≥1,mass≥1; arbitrary
old v length r; R≥max(p,r), q≥4R+4 and n≥qp+r+1,
`n*(mass(b^q v)−1)−moment(b^q v)≥q`.
In the whole actual prefix this equals a(t)−(t+1). A long periodic suffix
therefore makes the subtraction candidate exceed every a(u),u<N, and
also makes it positive. An A step must then be blocked by u≥N.
Its complete supplier window agrees with e. H16 bounds its lag and H15
forces P2 at a sufficiently late clock. Periodicity transports it to the
original phase. No pigeonhole argument or guessed lag is needed.

## Frozen falsifier

Check all positive-mass binary b of p1..5, all independent v of r0..7,
and q=4max(p,r)+4 plus the next two values; n=qp+r+1 and this plus17.
Discovery p≤4,r≤5; remaining pairs are holdout. Independently expand the
words and compute the candidate quantity. Check zero-mass AAASSS breaks
growth. For actual initial history, compare whole-prefix value identities
and the reason-for-A dichotomy through2,000. This is finite arithmetic
validation, not evidence for actual eventual periodicity.

## Evidence

The first harness used n=6q+1 for the zero-mass control, where the candidate is 3q−1 and the lower bound happens to hold. Corrected the control to its declared collision clock n=9q, giving candidate0. Positive-mass checks had all passed; the failed control output is retained. No claim or discovery/holdout ranges were changed.


## Result and semantic audit

- `COMPUTED`: the frozen independent expanded-word tests and canonical prefix checks pass; `eventual_periodic_bridge.txt`. The zero-mass control correction is recorded above.
- `PROVED-LEAN`: `Recaman/EventualPeriodicSupply.lean` proves candidate growth despite arbitrary old words, period-mass invariance, exact tail-window agreement, exclusion of all u<N, late A ⇒ genuine historical supplier ⇒ P2, and transport to every integer A phase.
- No assumption of short suppliers or already supplied A phases occurs in `every_A_phase_has_P2`. The preperiod N is arbitrary. No real-valued asymptotics or pigeonhole principle is needed.
- `./scripts/check.sh > docs/data/issue73_20260910/check17_eventual_periodic_bridge.txt 2>&1`: PASS,1,473 audited declarations.
- Scope: this certifies the canonical positive-drift part of E-065. The global periodic representative is supplied as an explicit representation of the tail. Arbitrary externally seeded orbits and the zero/negative sign-sum cases of E-065 are still paper-only. The finite-word E-067/E-070 and surjectivity remain unresolved.
- Next decision: close the natural eventual-periodicity representation and the sharper p(p+1) P2 lag bound, then address nonpositive drift separately.
