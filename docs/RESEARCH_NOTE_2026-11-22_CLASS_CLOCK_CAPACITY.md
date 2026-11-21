# Original candidate classes pay unweighted clock capacity in every lower strip

PROVED-PAPER, not Lean checked; human review pending. A new all-depth recurrence bounds ORIGINAL LOWfree CLOCKS, all original LOW A and strip visits from DISTINCT original free candidate classes and an explicit height width. The depth cost, repeated charges and boundary terms are paid below. This does NOT supply D<=K, a bound on high excursions/time, class finiteness for a canonical history, or C1.

## Original objects and exact per-level inequality

Let f[0,T) be ANY finite unit-sign word, H0=B0=0. For all original state positions and A clocks put

    O_u=(H_u,(u+1)H_u-B_u), 0<=u<=T,
    C_q=(H_q-1,(q+1)(H_q-1)-B_q), f(q)=A.

Here A has sign+1, S has sign-1, H_t is the sum of the first t signs and B_t=sum_(i=1..t) H_i. Thus B_q-B_u-(q-u)H_u is EXACTLY `Ar f u (q-u)` in `Recaman/SingleWindowEquality.lean`, with its final H_q included and H_u excluded. Equality C_q=O_u says H_q=H_u+1 and this area is0; u<q supplies the positive window length. This is precisely `EndN f 0 q` for the original A clock q. No off-by-one source/target change or numerical-blocker substitution is involved.

A is actual iff SOME u<q has C_q=O_u: this is exactly its original height rise1/zero relative area Win. A is free otherwise. No P2 source is reset, selected independently or discarded. Co-suppliers remain. Numerical equality at an exceptional base is NOT substituted for equality of these pairs.

At integer level r let a_r count ALL original A at preheight r, f_r count the free ones, k_r count DISTINCT pairs of those free A, and m_r count DISTINCT pairs of ALL A at that level. Let N_v count ALL original state positions0..T at height v, including initial and final positions. All these are finite literal counts, not new hypothesis Props.

### Same-pair load and the exact charge multiplicity

If A p<q have one pair C and preheight r, then

    B_q-B_p=(q-p)(r-1).

The bridge area above r-1 is0; its first A contributes+2. Thus some intermediate state is at most r-2. Returning to H_q=r requires an A at preheight r-2 STRICTLY between p and q. Choose the last such A. Consecutive bridges for ONE pair are disjoint, so their chosen A clocks are distinct. Therefore every pair has load at most

    1+a_(r-2).                                                   (1)

The1 pays its first occurrence. Across different free pairs, a lower A can be reused at most k_r times; across all A-pairs at this level at most m_r times. These multiplicities are retained, not assumed disjoint or replaced by a depth-independent constant. Different recipient levels r use different lower levels r-2.

In particular

    f_r<=k_r(1+a_(r-2)),       a_r<=m_r(1+a_(r-2)).                (2)

This is not a constant per-seed load claim: the lower ORIGINAL A-clock inventory (supplied PLUS free) is a real cost, paid recursively below. It is also not a count of numerical seed values.

### Every old supplier is paid by a crossing inventory

Every actual A pair comes from an ORIGINAL output at level r-1. Every other pair belongs to the k_r free classes. Counting the FULL original output bank, even future positions as a harmless upper bound, gives

    m_r<=k_r+N_(r-1).                                            (3)

An output shared by many suppliers/classes is never silently deleted; using positions rather than distinct outputs only increases the upper bound. Every old/source-before prefix output and both endpoints are included.

For EVERY integer v, edge conservation gives the exact boundary identity

    N_v=a_v+a_(v-1)+1_{H_T<=v}-1_{v>0}.                          (4)

Proof: downcrossings v+1->v equal a_v+1_{H_T<=v}-1_{H_0<=v}; arrivals from below equal a_(v-1), and add the initial-state indicator1_{H_0=v}. With H0=0 the last two initial indicators combine to-1_{v>0}. This handles a positive cut, starting at the cut, ending at a lower state, and the empty word. In particular N_v<=a_v+a_(v-1)+1 for ALL v. One may not omit the end correction or call the simplified exact equality valid above0. AA at v1 has N1=1, while a1+a0=2; the initial-side correction is-1.

Combining(2)-(4) supplies, for EVERY r,

    a_r <= (k_r+a_(r-1)+a_(r-2)+1)(1+a_(r-2)),
    f_r <= k_r(1+a_(r-2)).                                      (5)

The recurrence itself is proved, not supplied as an assumption. Lower A is NOT replaced by free. OLD E660's failure of A<=2free is compatible with this nonlinear paid inventory.

## All-prefix, arbitrary-cut theorem

Assume the full finite word stays above an integer floor ell; let ell<=R be ANY integer upper cut (R need not be nonpositive), W=R-ell. Let K=sum_(ell<=r<=R) k_r, the distinct original free classes below R. Distinct preheights have distinct pair slopes, so this sum counts classes exactly. It is never a sum of possibly coincident numerical values.

At ell all A are free because their source height ell-1 is absent. At ell+1 all A are free because every putative source at ell has nonnegative relative area, including the target's+1. Neither level's pairs repeat: (1)'s bridge would need a state below ell. Thus

    a_ell=f_ell=k_ell,        a_(ell+1)=f_(ell+1)=k_(ell+1).     (6)

These statements hold even if the supplied floor is below the actual minimum (the unused counts are0). Define the explicit NONNEGATIVE integer sequence

    b0=b1=K,
    b_(j+2)=(K+1+b_(j+1)+b_j)(1+b_j), j>=0.                    (7)

Then for EVERY0<=j<=W,

    a_(ell+j)<=b_j.                                             (8)

Proof is induction: (6) supplies the two bases, (5) and k_r<=K supply the next step using nonnegative products. b is nondecreasing, since its next factor product is at least the previous term; b0=b1. This is also valid for K0. No height-width change is packaged as a new binder around an assumed unweighted inequality.

Summing(2) and paying the MAXIMUM shared lower-A inventory gives

    F_R=K                         if W<=1,
    F_R<=K(1+b_(W-2))             if W>=2,                     (9)
    A_R:=sum_(ell<=r<=R) a_r <=sum_(j=0..W) b_j.               (10)

The depth-dependent growth in(7) is explicit; it has not vanished. The sharper weighted form is F_R<=K+sum k_r*a_(r-2), with first-class boundary K and maximum per-lower-A duplication k_r. Induction(8) then pays this entirely in K and W. This is an upper capacity, not the missing lower bound of classes on W.

Finally sum(4) over ell..R. Since a_(ell-1)=0 and the negative initial corrections can be discarded upwards,

    V_R:=#{0<=t<=T:H_t<=R} <=2*sum_(j=0..W)b_j+W+1.           (11)

The W+1 is the finite terminal tail's boundary inventory. All initial/final visits are counted. This bounds how MANY strip visits occur, not when their last clock occurs. HIGH parts between them can be arbitrarily long.

## Sharper original minimum/return consumer

For the main original finite domain, initial S^h/h>=1 (NOT assumed maximal), H_T=2-h, put ell=min H=-h-D and R=1-h. Then W=D+1. For all r<=R the terminal correction in(4) is0 and v=r-1<0, so the initial correction is also0. Replace(7) by the smaller

    c0=c1=K, c_(j+2)=(K+c_(j+1)+c_j)(1+c_j).                 (12)

It is internally supplied by the same full-output argument, with no boundary term needed. Consequently

    D0: F_LOW=K_LOW;
    D>=1: F_LOW<=K_LOW(1+c_(D-1)).                            (13)

Every actual/free count still refers to the ORIGINAL Nat0 history. No head maximality, positivity, source radius, S freshness or fixed number of runs is smuggled into this consumer. H05's local maximal-head K<=3 singleton theorem is much sharper in that corner; it is not falsely presented as following from this loose general bound. The main D<=K theorem remains open.

## One infinite word: finite classes/floor force lower-strip escape

For ONE infinite original unit-sign word, suppose a COMMON lower floor ell holds at every time, and there are only finitely many DISTINCT original free classes at preheights<=R. Let their total be K. Every finite prefix uses the SAME original source ledger and class budget, so(7)-(11) apply with the SAME ell,R,K. There are uniformly finitely many A/visits below R; hence only finitely many such positions in the infinite word, and eventually H>R. If this finite-class condition holds for every R, H tends to+infinity.

This is a conditional raw combinatorial consumer. It does not assert that C1/canonical hypotheses supply class finiteness, does not use a different State for each prefix, and does not replace numerical stock by original classes. OLD E764's numerical-positive escape theorem has different supplied premises. No recurrence/desired escape is assumed as a new Prop here.

## Falsifier, contrasts and scope

The first frozen NEW-predicate worker checked4095 raw words (511 discovery lengths0..8,3584 separate parameter controls9..11),20464 same-pair loads,7416 source-visit/capacity positions,8190 bottom checks, and490 actual main-domain words. All predicates passed. These words may have appeared in previous work; they are regression/parameter controls for NEW predicates, not fresh orbit data or a new C1 cutoff.

The separate direct-literal-window auditor checked1023 raw words (127 discovery0..6,896 parameter controls7..9),6789 FULL initial/end boundary identities and12555 arbitrary-endpoint/floor-margin/negative-and-positive-cut capacities. The AA/v1 negative control shows why the simplified equality needs its initial-side correction. It does not refute the upper capacity. Both workers finished inside their fixed current-day CPU/wall contract. Finite tests are COMPUTED support; the all-prefix and infinite statements rest on the full proof above and remain PAPER/human review pending.

The new H03 family has h10/D3/K6/F7 while numerical source age and HIGH prelude grow. It is consistent with(9)-(13): this theorem bounds LOWER activity and class duplication, not time spent above the strip or the numeric source's last clock. Therefore no hidden conversion from a strip-visit count to a last-clock bound is permitted. Initial numerical State/current/high stock still cost something, and no C1/coverage/surjectivity conclusion is obtained.

All old STOPPED jobs and protected labels remain unchanged; no Lean implementation of this recurrence was started. Next useful question is whether the FIRST new lower class at width W can force a better (ideally linear) height payment than this very loose recurrence, while retaining all original sources and the true overlap multiplicities.
