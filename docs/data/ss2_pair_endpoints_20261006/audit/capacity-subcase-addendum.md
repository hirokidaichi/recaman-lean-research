# Independent paper audit: pure-alternating / single-SSS capacity subcase

**PASS for the complete paper proof below.** In the explicitly restricted branch (global NoSAAS; the collision prefix X is pure alternating; C's two overlapping SS edges occur in one SSS run), two distinct actual donor S phases are excluded from every current-A S-ended lowSS P2 endpoint. Hence H-02 and the original local Hall inequality hold in this subcase. Positive period mass is not used. This is not a proof for the other X branch or for two separated SS runs.

This addendum reconstructs the argument independently from the proposed route; no repository files or Lean source were changed. New frozen finite controls, when supplied, are supplementary falsification and do not replace the following unbounded argument.

## Exact premises and coordinates

Let p>0 and e:Int->Bool be p-periodic with no SAAS anywhere in the full integer stream. Take two phase-distinct current-A minimal P2 windows, each with exactly two overlapping SS pairs, sharing their true-oldest S phase. Apply the previously audited terminal-tail/full-endpoint and chronology arguments, shifting one entire window by an integer multiple of p, to get actual integer clocks t_A<t_S and common oldest S time s, with

- W_A=C A, length d=d_A, and W_S=X C;
- C=past e t_A (d-1), covering every clock from s=t_A-d+1 through t_A-1;
- C ends S, mass(C)=0, moment(C)=-d, ss(C)=2;
- X=(AS)^(d-1) A in the selected pure-alternating branch.

SS2 P2 windows have length at least11 (existing TwoSSEndpoint.ss2_length_ge_eleven), so d-1>=1 and X really ends SA. In particular e(t_A+1)=S, while e(t_A)=A. No period-mass hypothesis enters this geometry.

Assume C has a run SSS, at chronological clocks q,q+1,q+2. These are in C, so s<=q and q+2<=t_A-1. Since ss(C)=2, those are its only two SS edges. The choice of q is the chronologically first/oldest S in that run, not the newest S.

## 1. A triple's oldest S is excluded from all lowSS endpoints

For any positive lag l with full endpoint exactly q, its current time is u=q+l. If l=1 or2, e(u)=S because u is inside the triple, contradicting current-A. If l>=3, the actual window contains q,q+1,q+2 and hence two overlapping SS edges, contradicting ss<=1. This does not need P2, minimality, NoSAAS or positivity.

For a modular endpoint equal to phase(q), periodicity shifts the alleged entire window so its full endpoint is exactly q, preserving current-A, P2, SS and lag. Therefore phase(q) is outside E_low, where E_low includes ALL eligible positive-lag S-ended lowSS witnesses, minimal or not. It is an actual donor S phase because q lies in C.

## 2. q=s is impossible in the pure-alternating branch

Suppose q=s. Then C=T SSS. T cannot be empty because mass(C)=0. T ends A, since a final S would join the triple into SSSS and create at least3 SS edges. It is SS-free, since the triple already consumes the entire SS2 budget. Mass gives mass(T)=3.

Set L=|T|. From P2(W_A)=P2(T SSS A), the moment equation is

M(T) -(L+1)-(L+2)-(L+3)+(L+4)=0,

so M(T)=2L+2. We classify T using the actual following S of the triple, not merely NoSAAS of T in isolation. Every A run other than a possible initial run is bounded on both sides by S, including T's final A run, so such runs cannot have length2.

If T starts A, there are #S(T)+1 A runs and two extra A letters beyond one per run. A run of length2 away from the first is forbidden. A first run of length2 would leave one extra A to another run, forcing that forbidden length2; thus the only possibility is one run of length3 and all others of length1. This includes the S-free T=AAA boundary. Hence

T=(AS)^a AAA (SA)^b,  a,b>=0.

Here L=2a+3+2b and M(T)=5a+b+6. The moment equation gives a=3b+2>=2. Thus C and W_A start AS. Together with actual current A at t_A and e(t_A+1)=S from X's final SA, clocks t_A-2,t_A-1,t_A,t_A+1 form S,A,A,S, contradicting global NoSAAS.

If T starts S, each S is followed by an A run and the A surplus is3. All A runs, including the final one, are bounded by S. Therefore no run has length2; three surplus letters can only form one length4 run, all others having length1. Thus

T=(SA)^j AAA (SA)^b,  j>=1,b>=0.

The prior final A of (SA)^j combines with AAA to form that length4 run. Now L=2j+3+2b and M(T)=7j+b+6. M(T)=2L+2 gives 3j-3b-2=0, impossible modulo3. Both starts are impossible; therefore q>s.

## 3. q and s are distinct phases, even when windows wrap

Suppose q=s modulo p. Periodicity transports e(q+1)=S to e(s+1)=S; e(s)=S already holds. All these clocks are inside C: s+1<=q and q+2<=t_A-1. Consequently C has the three SS edges

(s,s+1), (q,q+1), (q+1,q+2).

Their starting clocks are s<q<q+1, so they are distinct even if q=s+1 and the triples overlap. This contradicts ss(C)=2. Thus phase(q) != phase(s). This argument does not assume lag<p, a primitive period, or positive period mass.

## 4. Two excluded phases give the requested subcase capacity

E368 oldest_phase_ne_lowSS_endpoint excludes phase(s) from every element of E_low. The triple argument excludes phase(q). Both are actual S phases in C, hence in N_pair, and they are distinct modulo p. Therefore

|N_pair minus E_low| >= 2.

For any finite nodup current-A lowSS set L with arbitrary specified P2 lags, E368 lowSS_endpoint_image supplies |L| distinct endpoints F subset N(L) and F subset E_low. Adjoining phase(s) and phase(q) produces |L|+2 distinct elements of N(L union {v,w}). Hence the original local Hall inequality follows for this same restricted donor configuration. Member minimality and S-ending are still not assumed; normalization occurs inside each original window.

## Dependency and limitation audit

The proof uses actual common history, current-A signs, exact overlapping SS count, the explicit pure-alternating prefix, and global NoSAAS. Minimality is used by the existing collision geometry/tail bounds and E368's oldest exclusion. The q endpoint obstruction itself is stronger and needs none of those latter assumptions. There is no assumed Hall, owner map, unproved capacity or fixed second-offset conjecture.

The period mass can be omitted from this subcase theorem: all periodic transport and E368 inputs only need p>0. Keep positivity in the general H-02 conjecture if that remains the frozen original target, while labeling this subcase's stronger scope explicitly.

Do not generalize the q=s contradiction to X=(SA)^j A: in that branch e(t_A+1)=A, so the start-AS contradiction used here disappears. Do not generalize the triple endpoint obstruction to two separated SS pairs: then there need not be any S followed by two further S signs. The p33 and all-p>=33 padding collision family is a nonvacuous instance of this subcase (C=AAASSSASAS, s=0, triple starts q=4, distinct phases0 and4). This partial capacity proof coexists with oldest-map noninjectivity.

Label recommendation: this complete restricted proof is PROVED-PAPER after its exact statement is recorded; it is not PROVED-LEAN. General H-01 and H-02 remain CONJECTURED. The prior stopped geometry-only route is now advanced for this subcase by an actual second-phase mechanism, not by a wrapper. Formalization should preserve all extra branch premises explicitly and include actual examples plus controls removing the pure-prefix or triple-run conditions.
