# At most three LOW classes cannot hide repeated original free clocks

PROVED-PAPER, not Lean checked; human review pending. This is a LOCAL small-class-budget result, not the arbitrary-K/depth theorem and not another depth-general reset. It is a new conversion from distinct original candidate classes to actual original free clocks, not an application of a free-count bound with the missing conversion assumed.

## Exact statement and essential maximality

For EVERY finite original unit-sign word f[0,T), let1<=h<T, f(i)=S for i<h and f(h)=A (MAXIMAL initial S run). Let H/B start at Nat0 and H(T)=2-h. Count original LOWfree A at q<T with H(q)<=1-h using ALL literal original Win sources; F is their number, K their DISTINCT pairs

    C_q=(H(q)-1,(q+1)(H(q)-1)-B(q)).

H_t is the sum of the first t unit signs (A+1/S-1), and B_t=sum_(i=1..t)H_i, with H0=B0=0. Every supplier uses the original `Win`/`EndN f 0 q` convention: the area sums states u+1 through q, ending immediately before the target A at q.

If K<=3, then

    F=K<=3,                     D=max(0,-h-min H)<=1.          (1)

No positive-deficit, S-novelty, actual State, depth cap, run-count or high-prefix bound is assumed. All old sources and source-before prefixes remain. Maximality is ESSENTIAL: the exact raw word S3 A4 with nominated h1 has return1=2-h, F3/K3/D2. It satisfies the weaker initial-S^h condition but violates the depth conclusion. This is not a counter to the main H01 inequality D<=K. Do not narrow H01's broader quantifiers silently.

## Two internally supplied floor lemmas

Write ell=min H over the WHOLE finite word. Every A with preheight ell is original free, because its source would have height ell-1. Every A with preheight ell+1 is also free: a source at ell would have a nonnegative relative area, including the final+1, so could not have area0. This includes sources before every proposed cut.

If two A p<q have the SAME candidate pair at preheight k, then

    H(p)=H(q)=k,   B(q)-B(p)=(q-p)(k-1).

The bridge's relative area above k-1 is0 but its first A contributes+2. Hence it must visit height<=k-2. In particular candidate pairs of A at ell or ell+1 NEVER repeat anywhere in the original word. This is a height/area producer, not an assumed injection. It applies to these A because they were just proved free.

At the first global minimum v, recovery to final2-h supplies A at ell and ell+1. For D>=2 the first head A at p=h has preheight-h=ell+D, giving a THIRD class different in slope from these two. Under K<=3 these exhaust the complete class support: exactly one class at each bottom level, and the original head class. Consequently the bottom A each occur ONCE in the whole word; after the recovery AA from v the walk cannot revisit either bottom level and still end at2-h. There was no A at ell+1 before v, since that would have a distinct pair from the later recovery A and force a fourth class. Thus the only pre-v state at ell+1 is v-1.

## D>=4 gives an immediate fourth class

For D>=3, an A at ell+2 before v would be free: ell+1 has never been visited yet. Its preheight is different from the head height, so it is forbidden by the three-class support. Therefore the first visit to ell+2 is v-2, followed immediately by SS to v. After v's AA recovery, an A at ell+2 is supplied by the descending state v-1 via SAA.

After its first supplied A at ell+2, any later A at ell+2 is free: its only candidate-height ell+1 outputs remain v-1 and v+1, and the first source's area starts at0 and then strictly increases because every future state is at least ell+2; the second source's area is always positive. Thus this extra free class is forbidden for D>=3. Before the first A at ell+3, the walk cannot return below ell+2. The only possible delay is an AS loop at ell+2. Its next A at ell+2 has candidate-height ell+1, whose ONLY original output positions are v-1 and v+1. The corresponding relative areas are3 and4, so it is free, a forbidden fourth class. Hence the next A at ell+3 is immediate. Its complete source set at height ell+2 consists of v-2 and v+2; their areas are-3 and+1, respectively. It is free. For D>=4 its height is different from the head, so this is the fourth class. Thus D>=4 is impossible.

The old descending source and the recovered source are BOTH included in each calculation. Counting only the local source would miss the SAA exception and invalidate the argument.

## D3: one supplied head-AS loop must be retained

Now the A at ell+3 is at the original head height k=-h. It is free, so its pair must equal the first head A's pair. Before v there was only one A at that head height: any earlier extra A there would be free (no state at ell+2 yet), and a repeated class would need to visit ell+1 and therefore the global minimum already. Thus the prefix from p to its final return w at height k before the descent is an irreducible positive Dyck loop: length L>=2, every interior height strictly above k, relative area A>=1. It is followed by S3 to v and A3 to this recovered head state q.

The S3 A3 bridge has length6/relative area-9. Equality of the head candidate pairs gives

    A-9=-(L+6),                   A=3-L.

Since L>=2 and A>=1, L2/A1 are forced. The high loop is exactly AS. Thus the ENTIRE segment p..q is the literal Z1=AS4A3, with q=p+8. This bounds the previously unbounded high prefix without assuming it.

Before the first A at height k+1 (the LOW boundary A needed to reach k+2), the only possible delay is (AS)^j at height k followed by an A there. A drop to ell+2 would cause the forbidden extra free A established above. For the A at q+2j, its candidate-height ell+2 has exactly two original sources, p+3 and p+7. Their areas are

    -3+3j,                        1+3j.

Therefore j1 is ACTUAL, j0 free, and j>=2 free. Do NOT discard the j1 supplied exception. Every AS decreases this fixed-height candidate pair's intercept by3; for j>=2 the free pair differs from the original head class. So j can only be0 or1 under the three-class budget.

Finally check EVERY old source at head height k for that first boundary A. In any formal weighted walk write X_p=z. The old AS return at p+2 has value z-1; the recovered head state q has z+8; each AS after q decreases current by1. The boundary A's rejected candidate is z+7-j, while ALL original head-height outputs are

    z, z-1, and z+8-i for0<=i<=j.

For j0/1 none equals z+7-j. A literal P2 source would give such a numerical equality for EVERY base/current, so no original source exists. The boundary A is free at a new slope, a fourth class. D3 is impossible. These formal value differences use only the signed window identity; actual greedy realizability is not assumed.

For an explicit indexing check, let N be the formal step at p. The forced Z1 prefix's states p,p+2,p+3,p+7,p+8 have values z,z-1,z-N-3,z-N+1,z+8. After j AS delays the head current is z+8-j and the step is N+8+2j; its rejected candidate is z-N-3j. Subtracting it from the two complete source values at p+3/p+7 gives exactly -3+3j and1+3j above. Executing that head A makes the boundary candidate z+7-j. Thus the j1 actual exception and both j0/1 boundary exclusions use the same original clock convention. These are formal signed sums, not extra State assumptions.

## D2: the high-prefix area cannot be3

Here the original head is k=ell+2. Before v, any extra A at k is free, since ell+1 has not been visited. A repeated head pair would force ell already before the first minimum. Thus the prefix p..w is again an irreducible positive loop of length L>=2 and area A>=1, followed by S2 to v and AA back to k at q0.

Until the first boundary A at k+1 the path can only be (AS)^j A at k. Its two candidate-height ell+1 sources have areas3j and1+3j, hence the A at k is actual exactly for j0. For j>=1 it is free. It cannot reuse the head pair: equality would give

    A-4+j=-(L+4+2j),              A=-L-3j,

contradicting A>=1. Thus j0 only. For the boundary A, ALL sources at height k are p,w,q0; their areas are A-3,-3,+1. An irreducible loop cannot have area3: for L2 its area1, while for L>=4 every interior height>=1 and the second height>=2, giving area>=L>=4. Hence no source supplies the boundary A, a fourth class. D2 is impossible.

Indeed, if the formal value at p is z and its step is N, the high return w has value z-A. The S2A2 segment returns to q0 with value z-A+4; after the immediately following head A the boundary candidate is z-A+3. Subtracting this from the complete head-height output bank z,z-A,z-A+4 yields A-3,-3,+1. This verifies the use of the old head output p as well as w and the recovered output; none is discarded because it predates the minimum.

This proves D<=1 without an upper bound on the high-loop length or run count. The high-prefix restrictions were DERIVED from the assumed three classes and global floor, not supplied as a new history hypothesis.

## D0/1 give the singleton conclusion

For D0 every LOW A is at ell or ell+1, so the floor lemmas say it is free and its pair never repeats: F=K.

For D1 the initial head A is at ell+1. Recovery from the later global minimum gives a second A at ell+1 with a DISTINCT pair, plus the A at ell. These are already three classes. Under K<=3 no other LOWfree class can occur. None of these bottom pairs can repeat, so there are exactly three LOWfree clocks, F=K=3. This completes(1).

## Falsifier / scope / continuation

The newly frozen RAW proof-grammar worker checked192 discovery and3128 separate parameter controls, with4 nonvacuous K<=3 examples in EACH set. All bottom-level free/singleton, irreducible-area and new implication predicates passed. Positive-deficit/I/II were NOT used to filter this broader raw domain. The negative S3 A4/h1 control gave F3/K3/D2 and confirms why maximality is required. These finite outputs are COMPUTED, not an all-word proof. The small admissible population is explicit; no range extension is made to manufacture support. Simple monotone/Z1 profiles are OLD controls for NEW class predicates, not rerun old C1 cutoffs or fresh orbit data. See THREE_CLASS_PROTOCOL.json/three-class.log.

OLD E767's N1/Z1 family already has D3/F5/K4. It shows the singleton conclusion cannot be extended from three to four classes; it is used as an old boundary control, not today's new counter. The main next unknown is the exact first four-class case with repetition and interleaved recovery. The general K_LOW>=D claim, the broader nonmaximal-head version, C1/Q/H/SL/surjectivity remain unproved. No new Lean job is started after H04's512MB STOPPED finite certificate.
