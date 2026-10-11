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


## Follow-on result after controls (2026-10-06)

**PROVED-PAPER, independent final audit PASS.** The standalone internal-SSS
lemma and the frozen pure-alternating corollary passed. A subsequent,
separate endpoint calculation also closed the other NoSAAS/oldest-SSS
case; the original frozen protocol is retained unchanged.

In that case X=(SA)^j A and C=T SSS. The run/moment classification gives
C=(AS)^a AAA(SA)^b SSS, a=3b+2, b=3r+1, j=8r+6.
With s=0, the actual signs from endpoint1 through t_A−1 are
SS(AS)^b AAA(SA)^a. Their mass-one current-A candidate is only t_A,
where lag=d_A−2 and moment=−1. Through reverse(X)=A(AS)^j the mass is
2/3, ending at2 with last sign S. Any further lowSS extension has already
spent its one SS edge at clocks1,2, so its extra word is A-started and
SS-free, with nonnegative mass. Therefore ALL future endpoint1 windows
fail P2. Periodic lifting gives phase(s+1) exclusion, distinct from
phase(s); p=1 would contradict the simultaneous actual S and current A.

Together: under global NoSAAS, if the common SS2 core contains SSS,
either its first S is internal and supplies the second excluded phase,
or it is oldest and the pure-X branch is impossible while the second
branch supplies s+1. Thus the whole NoSAAS/single-SSS collision class
satisfies the strong endpoint inequality and local Hall, without positive
period mass. The no-NoSAAS and separated-SS cases are still unproved.

[Complete final independent proof](data/ss2_pair_endpoints_20261006/audit/oldest-sss-endpoint-addendum.md).
The six fixed controls and every eligible endpoint set were independently
replayed: all passed. The negative NoSAAS control refutes removing NoSAAS
from the pure-X conclusion q>s, not the strong endpoint inequality.
The r=1,2 controls were already seen when the final s+1 lemma was proposed;
they are regression evidence, NOT fresh holdout for that lemma.
Its unbounded evidence is the complete paper proof.

This short pass stops after saving the result. Next: formalize the exact
SSS capacity theorem, and separately test whether the separated-SS
collision class is nonempty before proposing its endpoint mechanism.
Do not mark H-01/H-02 or any central claim solved. No Lean source changed.
