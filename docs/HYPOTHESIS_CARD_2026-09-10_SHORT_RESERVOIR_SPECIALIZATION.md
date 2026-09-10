# Hypothesis card: concrete lag≤11 plus bounded-excess capacity

- ID: `H-20260910-06`
- Owner: Codex, four roles sequentially
- Created: 2026-09-10 JST
- Status: `PROVED-LEAN` (E-102)
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`

## Exact bounded question and acceptance

For every p-periodic stream and R≥0, let U be ALL A phases with a P2
lag≤11. Let Q contain A phases with exact preceding run length m≥4R+13
and a P2 lag≤4m−1+4R. Does |U|+|Q|≤D follow in Lean with no injection
premise left in the public theorem? The expected answer specializes E-101
to the existing phi7/phi11 map, not a new table or higher lag classification.

Acceptance: exact P2 definition of U, existing short-map injectivity
discharged, all-period theorem audited; plus a concrete nonsharp Q witness
whose minimum lag exceeds11 and4m−1. Stop on any semantic mismatch or
counterexample; do not weaken U to a convenient subset.

## Dependencies and falsifier

E-080 gives the short images and their disjointness. P2 parity ensures
all lags≤11 are3,7,11. E-101 then applies with L11. The main new work is
the exact union/count glue and a concrete extension witness.

Before Lean implementation, test the actual phi7/phi11 offsets and the
explicit free-S rank construction on structured periodic words. Include
all eligible Q phases, not merely the inserted witness. Check finite P2
lags only through each phase's declared band; this is sufficient to define
Q and is not advertised as all-lag enumeration. R0..4 discovery,5..12
holdout; exact script parameters are frozen before execution. No numerical
pass can replace the universal short-map glue.

## Evidence

`PROVED-LEAN`: `Recaman/ShortReservoirCapacity.lean` defines the complete
short phase list and proves `mem_shortPhases` iff current A and some P2
lag≤11. Its public `short_plus_bounded_excess_capacity` theorem has no
old-injection premise: phi7, phi11, their separate injectivity and their
cross-image exclusion are discharged using E-080. The conclusion is
`suppliedCount + u11Count + Q.length ≤ subtractionCount` for every p>0.
The Q run threshold is4R+13, uniformly in R.

The finite word certificate at m17 has exact first-S boundary, P2 at71,
no shorter P2 prefix, and excess4. It therefore proves a genuinely nonsharp
local supply word. Its periodic embedding and complete concrete rank map
are verified by the Python structured test, not by this finite-word
certificate alone.

`COMPUTED`: command
`python3 -u experiments/issue73_20260910/short_reservoir_specialization.py`,
output `docs/data/issue73_20260910/short_reservoir_specialization.txt`.
All52 near-sharp cases and12 extremal-density cases pass. At R1,m17,
period72 has A37,S35,U11=1,Q=1 with minimum lag71, giving capacity slack33.
At R12 the extremal-density period3504 has A1753,S1751,U11=2,Q=1,
minimum lag3503 and slack1748. These examples show a strict enlargement
of the covered supply class, but also a large remaining unused capacity;
they do not come close to settling the full E-070 inequality.

Audit: `./scripts/check.sh` passed; exact log
`docs/data/issue73_20260910/check06_short_reservoir_capacity.txt`.
The count and all new declarations are recorded in that log.

Decision: accept the concrete specialization. Next assess the coverage
and blind spots of the new structural class, rather than equating a
larger theorem family with progress toward a global contradiction.
