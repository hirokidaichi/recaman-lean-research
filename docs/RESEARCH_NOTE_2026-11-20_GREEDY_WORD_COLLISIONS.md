# A finite greedy sign word is determined by two chronological collision tests

**PROVED-PAPER**, human review pending, NOT Lean-checked. Every finite sign word, with arbitrary length/depth, is realizable by an actual greedy continuation from a COHERENT finite State if and only if the two explicit height/area collision tests below hold. The state is not asserted to have a canonical prehistory. An explicit constructor preserves the complete initial visited stock and all future S novelty. This generalizes a hand-built old-stock argument to an arbitrary finite word; it does not turn a raw-word free count into the complete-orbit free ledger.

## Exact v1 statement and the v0 falsification

Let w have length Q; H(0)=B(0)=0, H(i+1)=H(i)+sign(w_i), B(i+1)=B(i)+H(i+1). A clock q<Q is ORIGINAL supplied iff w_q=A and some u<q has H(q)=H(u)+1 and B(q)-B(u)=(q-u)H(u); otherwise an A is original free.

For EVERY landing v in1..Q with w_(v-1)=S, require:

(I) for EVERY0<=u<v, NOT [H(u)=H(v) AND B(v)-B(u)=(v-u)H(v)].
(II) for EVERY earlier A clock0<=q<v, NOT [H(q)-1=H(v) AND B(v)-B(q)=(v-q)H(v)].

Then (I)/(II) hold IFF there exist b:Nat and State s with s.value IN s.seen such that SeededReplay.run b s follows exactly w. The current-in-seen condition is essential. The initial v0 omitted it and is REFUTED by b10/value100/seen{77,88}, which greedily executes SAAS with values100,89,101,114,100. Its final S returns to an initial value not present in seen; (I) forbids that loop. This is the ONE explicit hypothesis repair to v1, retained in the card. It is a real coherence condition satisfied by canonical histories and the constructor, not a restatement of the conclusion.

## Exact affine state and candidate equations

At step-clock b+i+1 the unique values following w from x are

    X_i=x+(b+i+1)H(i)-B(i),
    C_q=X_q-(b+q+1)=x+(b+q+1)(H(q)-1)-B(q).

Direct subtraction gives X_(i+1)-X_i=(b+i+1)sign(w_i). These are integer identities before any positivity/greedy assumption. If an original Win(u,q) exists, C_q=X_u identically for EVERY b,x, not just at a measured clock.

## Necessity: no old visits or forced-A blockers may disappear

If (I) fails, X_v=X_u for ALL b,x. Coherent initial current and every subsequent output remain visited. Thus the S at v would land at a prior visited value, contradicting its legal novelty.

If (II) fails, X_v=C_q for ALL b,x. Since the later S lands positively, C_q>0. The earlier A at q therefore could not be justified by a nonpositive candidate: it required C_q already in seen. That blocker remains visited until v, again contradicting S novelty. This handles every possible reason for the earlier addition and does not assume each A was internally supplied.

## Sufficiency: a quantitative, complete seed constructor

Let n=Q+1, b=100n^2 and x=100(b+Q+1)n. Let V={0,x} union C_q for every ORIGINAL FREE A q<Q. All elements are integers; positivity proved below makes them natural numbers. Use State(value=x,seen=any finite list of V). In particular x belongs to seen.

Every X_i and C_q has the form x+b*h+c, with |h|<=n and |c|<=2n^2. Indeed |H|<=Q and |B_i|<=Q(Q+1)/2, directly from unit steps. Since b>4n^2, two such expressions with DISTINCT integer h cannot be equal. For equal h, equality is precisely equality of their constants, which is exhausted by the following cases.

Every X/C is positive because

    x-b*n-2n^2=99bn+98n^2>0.

For a S landing v:

* Earlier X_u, including u0, cannot equal X_v: same-coefficient equality is exactly forbidden(I); distinct coefficients are separated by b.
* Seed0 is different by positivity. Seed x is the preceding case u0.
* Consider a seeded C_q at an original free A. For q<v, same-coefficient equality with X_v is exactly forbidden(II). For q=v the coefficient differs by1. For q>v, same-coefficient equality would give H(q)=H(v)+1 and B(q)-B(v)=(q-v)H(v), a literal original Win(v,q) at that A, contradicting that q was ORIGINAL FREE. This explicitly checks FUTURE seed items already present from the start. Distinct coefficients are again separated by b.

Thus every S landing is positive and absent from the FULL initial seed and ALL previous outputs. For an A q: if original free, its positive C_q is in V; if original supplied, its unchanged original Win source gives C_q=X_u for u<q, already visited. Hence each prescribed greedy sign is forced. Induction over q yields the exact SeededReplay word with all stock retained. No future is assumed legal and then used as a hypothesis.

The size bound is |V|<=F_word(Q)+2, NOT equality and NOT injectivity from raw free to numerical blockers. Equal blocked candidates may share an old value. This entire argument is independent of any source depth, height ceiling, number of runs, or sign-deficit condition.

## The explicit generic seed is nevertheless noncanonical

This rejects the displayed constructor's initial stock, not every possible realization of its sign word. If that stock covered the complete canonical visited values at time b with current x, E755 would require upperTri(b)<=x+2b(|V|-1). Since F_word<=Q, |V|-1<=Q+1=n, the RHS is at most

    100(b+n)n+2bn=b(102n+1),

where b=100n^2. But upperTri(b)=b(100n^2+1)/2>b(102n+1) for n>=3 (Q>=2). The strict polynomial is50n^2-102n-1/2>0, immediate at n3 and increasing thereafter. For n1/2 (Q0/1), x=b(100n+1)>upperTri(b), violating the canonical triangular range instead. This argument concerns membership/full visited cover, so padding the seen list with duplicates or reordering it cannot fix the obstruction.

For Q>=2 the elementary cardinality and current triangular range are compatible (the latter is x<=upperTri(b)); even all seed values lie within that range from |h|<=n/|c|<=2n^2 and (101n+1.02)b<upperTri(b) for n>=3. Current parity is canonical because b is a multiple of100 and x even. These elementary filters do not supply the global clock/novelty cost. None of this is standard-orbit reachability or C1.

## Boundary and semantic audit

Q0 is a coherent empty replay; Q1 allows either sign by the constructor. S freshness always refers to the whole stock, including candidates for later A. A candidate<=0 in a hypothetical necessary-direction replay cannot evade(II), because a later S at that value would be nonpositive. Initial current-in-seen was checked explicitly and v0's counter is retained. An actual raw Win supplies an older NUMERICAL value within the segment, but extra seed entries have no constructed sign prehistory: raw EndN/free is never asserted to be the full canonical-orbit ledger.

The finite H04 replays for root18 and affine m1/m3 passed; they are COMPUTED special applications, not evidence that all finite words satisfy(I)/(II). The arbitrary-word theorem is the proof above. No new Lean adoption or extra CPU job is used to relabel it PROVED-LEAN.

## Finite integer-mean square filter (PAPER corollary)

For EVERY nonempty balanced finite word v of length L, if areaW(v)=L*c with c an integer, v++v is impossible in ANY greedy continuation, even an incoherent initial State. The mean c is strictly between min/max of its unit-step closed walk: both extrema occur among H1..HL and not all heights agree. Hence some downward crossing is an actual S landing at height c, at a phase t in1..L. (If c<0, descend from initial0 to a lower minimum; if c>=0, descend from a higher maximum to terminal0.) In the doubled word, the same S landing phase t+L has the same height and B(t+L)-B(t)=L*c. Its numerical value therefore equals the earlier S output at t for EVERY b,x. That earlier output is recorded regardless of initial coherence; the second S cannot be fresh. Empty L0 must be excluded.

This rejects a balanced zero-area-loop amplification mechanism without a cutoff or free-count assumption. It does not reject all balanced motifs: W has mean-5/8, not an integer, and W^N is a proved greedy finite-state replay. Noninteger mean is necessary for an arbitrarily repeated greedy balanced block, not sufficient; its other chronological collision tests remain. The old infinite eventual-periodic positive-mass theorems are separate and are not claimed as new.

In particular Z=ASSSSAAA has length8/mass0/area-8, integer mean-1. Thus Z++Z cannot occur as an actual greedy sign segment. Its phase3 S landing equals phase11 for every b,x; for example starting b100/current1000 gives prescribed values at those phases both896. This DOES NOT refute or make vacuous E743's abstract EndN/free theorem: its domain is a raw sign history with original Win suppliers, not an actual numerical trajectory with fresh S arrivals. Pure sign-positive/source-consistent PC5 histories and actual orbit reachability have always been distinct evidence levels. The all-R raw-sign floor conjecture is NOT solved by adding the unproved claim that every such history is greedily realizable.

For two A clocks p<q sharing one literal original source u, their bridge is balanced with area (q-p)H(u), because both original Win equations have that source. Its relative mean is-1. Hence two IDENTICAL consecutive bridges between three such hits are impossible in actual greedy history. More generally every S landing v at height H(u) has numeric value X_u+P(u)-P(v), P(v)=B(v)-(v+1)H(u). Fresh S forces these P(v) values to be distinct. This is a genuinely numerical/provenance restriction, NOT an injection into original free; converting that distinct area inventory into C1's low-free wallet remains unpaid.
