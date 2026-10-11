# Hypothesis card: an internal SSS gives two excluded phases

- ID: H-20261006-03
- Base: 65c25ab742ab4aa749bfd5f48438dbcb7b774d1d
- Created: 2026-10-06, after H-02 diagnostic and before the controls below
- Roles: parent proposer/falsifier; Sol6.1 independent paper derivation;
  issue81_auditor independent semantic audit
- Initial status: CONJECTURED, paper argument proposed for audit

## Exact statement and smallest new edge

For any p>0 and p-periodic actual binary stream e (positive period mass
is NOT needed), take a minimal P2 donor W of SS=2. Let s be the integer
clock of its oldest S. Suppose W contains a chronological SSS at q,q+1,q+2,
with s<q. Then phase(s) and phase(q) are distinct actual S phases in W,
and neither is the S-ended endpoint of ANY current-A P2 window with SS≤1.

The new local edge is simpler than Hall: the first S of SSS cannot be a
lowSS current-A endpoint. A current in either next S position is not A;
any later current window ending there contains both SS edges. Periodic
translation of a supposed phase collision q=s mod p creates a third
SS edge in W, contradicting SS=2. E-368 supplies the exclusion of s.

Consequently any lowSS phase set L plus two distinct minimal SS2 donors
satisfies the local Hall inequality whenever one donor has this internal
SSS configuration: its two excluded phases augment the E-368 injection.
This is sufficient; it is not asserted necessary.

## NoSAAS pure-alternating corollary

For a same-oldest pair under global NoSAAS, use the audited integer lift
W_A=C A and W_S=X C. Suppose X=(AS)^(d_A−1) A and C contains SSS.
Then its SSS cannot start at the common oldest s:

If C=T SSS, T is SS-free, ends A, and has mass3. Since T is followed by
SSS, every noninitial A run is bracketed by S, including its last run.
NoSAAS therefore permits only
T=(AS)^a AAA (SA)^b (start A) or
T=(SA)^j AAA (SA)^b, j≥1 (start S).
The mass surplus over the alternating runs is respectively2 and3.
P2(C A) forces a=3b+2 in the former and 3j−3b−2=0 in the latter.
The latter is impossible modulo3. The former starts AS, so actual
signs at t_A−2,t_A−1,t_A are SAA. NoSAAS forces the next sign A,
whereas X's last SA gives that next sign S. Contradiction.

Thus the corollary supplies the two excluded phases and proves local
Hall for NoSAAS, pure-alternating collision prefix, and a single SSS run.
Two separated SS edges and the other collision-prefix family are not
automatically covered.

## Dependencies and semantic scope

Existing H-01 geometry, E-368 lowSS endpoint image/oldest exclusion,
mass/moment append identities and actual periodicity. No assumed Hall,
owner, reachability, extra-S hypothesis or finite lag bound.
The argument is paper-only; do not report it as PROVED-LEAN.
A canonical NoSAAS invariant motivates this restricted branch but does
not turn an abstract periodic sign construction into an actual orbit.

## Frozen falsifier / controls

These are explicit constructed and reused boundary models, not an
expanded exhaustive periodic census. Discovery controls:
1. Previously checked p33 pure-alternating collision, C=AAASSSASAS:
   NoSAAS, internal SSS, two excluded phases should be present.
2. Change C to ASASAAASSS in the same construction:
   preserve minimal SS2 pair but violate NoSAAS; SSS now starts at s.
   This must defeat the proof's q>s conclusion without NoSAAS.
3. Reused p22 word ASAAAAASASASASASASASSS, mass2, the H-02 holdout
   NoSAAS collision: it uses the second prefix family and has internal SSS.
4. Construct the remaining oldest-SSS/second-prefix shape for r=0:
   C=(AS)^(9r+5) AAA (SA)^(3r+1) SSS,
   X=(SA)^(8r+6) A, period word reverse(X C) A.
   Test all premises directly before treating this as a surviving example.

Held-out constructed controls: the same fixed algebraic family r=1,2.
No repaired formulas or search-range extension after seeing them.
Every model checks true current signs, all positive proper prefixes,
actual window compatibility, circular NoSAAS, SS edges and endpoint
witnesses by direct scan. Only positive-mass models use the finite
p(p+1) bound for all endpoint witnesses. That computational device does
not introduce a mass premise into the paper theorem.

## Acceptance / stop

Accept the fully audited all-lag paper subcase, or a concrete refutation.
If any required inference fails, stop this proposed proof and retain
H-01/H-02 as CONJECTURED. Do not add the unknown second phase as a premise.
No Lean module in this short pass; the next decision is whether this
subcase merits formalization or the explicit remaining family is sharper.

## Evidence / decision

Frozen before controls. Record results and final audit below.

