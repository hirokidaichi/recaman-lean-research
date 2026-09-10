# Hypothesis card: complete one-SS minimal P2 classification

- ID: `H-20260910-22`
- Status: `PROVED-PAPER` complete classification; all-parameter family algebra `PROVED-LEAN` (E-121)
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`
- Four roles performed sequentially.

## Exact bounded question

A nonempty newest-first word has P2, contains no SAAS, and exactly one
adjacent SS pair. Write its unique S-gap encoding
`A^g0 S A^g1 S ... S A^gn`, with n S signs. Does it have no shorter P2
prefix exactly when it belongs to one of the following two families?

A: g0=gn=0; one internal gap z is0; one different gap j is4;
all remaining internal gaps1; `n=6j−2z+1`.
B: g0=1,gn=0; one internal gap z is0; one different gap j is3;
all remaining internal gaps1; `n=4j−2z+1`.
Here 1≤j,z≤n−1, j≠z. These conditions imply n odd and lag2n+1≥7.

Acceptance: exact finite falsification, a complete paper proof of both
classification directions and minimality, and Lean certification of the
all-parameter moment/length equations if feasible. Do not label the full
classification PROVED-LEAN unless the arbitrary-word parser and both
minimality directions are checked. Stop on any additional family; no
charge rule, injection, or capacity theorem is conjectured in this card.

## Informal dependency chain before Lean

Mass1 gives n+1 As. A unique SS makes exactly one internal gap0; all
other internal gaps are positive. No SAAS forbids internal gap2.
Thus there are only3 extra As beyond the n−2 mandatory internal As:
(1) all3 at endpoints; (2) one gap3 and one endpoint A; (3) one gap4.
For g0=a, a unique enlarged gap j of excess h (h0,2,3), and SS gap z,
the S position sum is `n²+n(a−1+h)+z−hj`. Moment0 becomes
`n(2a+2h−5)=2hj−2z+1`.
The endpoint-only case that survives has a2 and already starts with
P2 prefix AAS. The h2,a0 case has n=2z−4j−1 and z≥4j+2,
so an earlier SS-free clean prefix at lag8j+3 exists. The remaining cases
are exactly A/B. For the reverse direction, any shorter P2 prefix must
fit this same exhaustive gap list; before the exceptional gap it cannot
have zero moment, and after it the linear equation fixes the total n.
The prefix-minimality step is the main semantic audit obligation.

## Frozen falsifier

Enumerate all seven possible extra-A gap shapes with n3..63 discovery,
n64..257 holdout. Solve/check the exact moment condition, explicitly build
every resulting P2 word, and independently scan ALL shorter prefix lags.
Verify classification both ways. Separately enumerate all binary words of
length1..17 and compare the raw NoSAAS/SS1/P2/minimum predicates with the
gap generator. Controls: the centered charge collision word from E-112
must be familyA; the endpoint-only and h2,a0 families must have earlier
P2 prefixes. There is no lag-by-lag selector table or κ repair.

## Evidence

- Complete two-direction paper proof: `docs/ONE_SS_CLASSIFICATION_2026-09-10.md`. It includes the unique gap parser, all seven allocations, exclusion by earlier prefixes, and reverse minimality.
- `COMPUTED`: frozen generator and raw binary cross-check passed;17,771 P2 words through n257,13,611 minimal words. Exact output `one_ss_classification.txt`.
- `PROVED-LEAN`: `OneSSGapAlgebra` proves the actual encoded word's length/mass/moment, the complete arithmetic split, explicit familyGaps via list updates, and P2 for all legal parameters of A/B. The arbitrary-word exhaustion and general A/B minimality are explicitly paper-only.
- Full `./scripts/check.sh`: PASS,1,530 audited declarations; `check22_one_ss_gap_algebra.txt`.
- E-112's centered counterexample remains family A, so classification does not repair its charge. No injection or capacity result is claimed.
