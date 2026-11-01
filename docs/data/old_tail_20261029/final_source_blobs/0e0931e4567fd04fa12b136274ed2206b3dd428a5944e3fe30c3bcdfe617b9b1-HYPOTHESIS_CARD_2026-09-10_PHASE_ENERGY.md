# Hypothesis card: phase-energy obstruction before lag matching

- ID: `H-20260910-19`
- Status: `STOPPED` (E-118; raw value-support conjecture remains unproved)
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`
- Four roles sequential; this is a new algebraic necessary condition, not a selector repair.

## Bounded question

For a periodic sign word s_t of period p and positive sum S, define
P(t)=sum_{i<t}s_i, W(t)=sum_{i<t}i*s_i, C=W(p), A=2C−pS,
H(t)=2S W(t)−p P(t)^2−A P(t),
D(t)=2[S t−p P(t)]+p−A.
Both H,D are p-periodic. P2 at (t,d),u=t−d implies
`H(u)=H(t)−D(t)`. Is there ALWAYS an A phase t for which H(t)−D(t)
is absent from the finite set of p phase H values?

This deliberately drops the P(t)−P(u)=1 congruence and positive-lag
requirement. It is a weaker necessary condition, NOT equivalent to P2.
If the obstruction is universal it would imply E-067, but neither finite
verification nor the necessary identity is a proof of universality.

## Search and stopping condition fixed in advance

Enumerate all binary positive-mass words p1..14 discovery,p15..18 holdout.
Stop at the first word whose every A has an H-value supplier. Independently
compute all P2 lags up to p(p+1) for that word and explain which missing
conditions prevent a genuine E-067 counterexample. Do not silently add a
congruence filter to rescue the failed conjecture.
If all pass, record only COMPUTED and attempt a separate algebraic proof;
stop this cycle without a proof if no monotone inequality emerges.
Boundary checks: p1, balanced words as excluded controls, repeated periods,
and direct P2⇒energy identity on every tested positive word up to p8.

## Informal identities before any Lean

Periodicity: W(t+p)=W(t)+pP(t)+C, P(t+p)=P(t)+S.
An A step has H(t+1)−H(t)=D(t)−2p; an S step has change −D(t).
Also D(t+1)−D(t)=2S−2p*s_t. A P2 supplier therefore must hit the
specified phase energy value, but matching energy alone may be too weak.
Initial search did not identify the old invariant in this normalization. The deeper audit below corrects that provenance claim.

## Evidence

- `COMPUTED`: the frozen all-positive-word search through period18 passed; exact output `phase_energy.txt`. No universal theorem follows from this.
- **Provenance audit corrected the proposed novelty.** In the existing `docs/data/issue73_20260907/geometry_attempt.md`, write b0=C+S−pS/2 and κ(t)=W(t)+P(t)−(b0+pP(t))²/(2pS). Direct expansion gives `H(t)=2S*κ(t)+b0²/p`. Thus H is exactly the already studied κ, up to a positive factor and constant. The two-child equation is the existing κ equation in integer scaling.
- `STOPPED`: no new monotone inequality or payment for incoming S demands was found. The raw energy-value-support statement is not refuted, but the proposed new-invariant route failed the continuation gate. No congruence-filter repair, λ retuning, or lower-κ S inventory is authorized by these finite results.
- No Lean module or new mathematical frontier claim was added for this rediscovery. E-082/E-083 stops remain in force. The search log is retained as finite evidence, not marketed as a new mechanism.
