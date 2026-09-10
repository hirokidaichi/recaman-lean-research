# Hypothesis card: natural periodic-tail representation and complete lag cutoff

- ID: `H-20260910-18`
- Status: `PROVED-LEAN` (E-117)
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`
- Four roles performed sequentially.

## Bounded question

For any p>0,N and natural sign stream f with f(n+p)=f(n) for n≥N,
construct e(t)=f(N+((t−N) mod p).toNat) for every integer t and prove both
global p-periodicity and agreement at every natural n≥N. Independently,
for EVERY positive-mass periodic e and any P2(t,d), prove
`0<d<p(p+1)` (no current-A premise). Combine this with E-116 using only
the natural eventual-periodicity and the actual first full-period mass.

Acceptance: complete representation and final canonical theorem in Lean,
plus a balanced-period counterfamily showing the positive-mass cutoff
cannot simply be omitted. Stop if negative integer residues, period1,
N0, or the clock into/out-of-transition indexing fails.

## Dependency chain before implementation

Natural periodicity iterates by q periods. For n≥N, Euclidean division
of n−N yields the extension equality. The chosen integer residue is
nonnegative and below p, including when t<N. For the lag cutoff, write
d=qp+r with r<p. Repeated-block mass gives 1=qS+s_r≥q−r, so q≤r+1≤p.
Then d≤p²+p−1. E-116 supplies P2; no hidden fixed-lag premise remains.

## Frozen falsifier

All binary positive-mass period words p1..8 discovery,p9..12 holdout,
all phases, all lags1..p(p+1)+p. Compute mass/moment incrementally.
Negative control: newest period AASS and residual AAS give P2 at every
lag4q+3 despite balanced mass; q0..8 discovery,9..64 holdout.
Extension boundary check: p1..8,N0..6, all p-bit words, arbitrary fixed
preperiod signs, integer t from−2p through N+4p. Compare modulo extension
with the explicitly repeated tail on its valid natural domain.

## Evidence

- `COMPUTED`: frozen `periodic_representation.py` passed all positive words/phases, balanced q0..64, and integer/natural boundary checks; exact output in `periodic_representation.txt`.
- `PROVED-LEAN`: `PeriodicTailRepresentation` constructs the representative, proves agreement/periodicity, the complete strict cutoff, and `canonical_natural_eventual_supply` without a supplied extension or P2 premise. Balanced period AASS has P2 at every lag4q+3, all q, with current phase S; the cutoff theorem makes no current-A assumption.
- Full `./scripts/check.sh`: PASS,1,480 audited declarations; `check18_periodic_representation.txt`.
- Auditor: p>0 is enforced at the final theorem and cutoff. The extension agreement happens to hold even at p0 under the trivial periodicity assumption; that stronger helper does not weaken the final claim. N0 and negative integer phases are covered.
- E-065's canonical positive-drift statement is now fully Lean, with the original strict finite cutoff. General finite seeds and nonpositive drift remain separate.
