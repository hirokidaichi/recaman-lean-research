# Numerical non-P2 blockers have a sharp minimum source age

NOVELTY CORRECTION: the age inequality/recent-source theorem below are OLD E114 PROVED-LEAN in `Recaman/ShortBlockerRigidity.lean`, discovered during current source audit. They are INPUT, not today's progress. The all-m actual coherent sharp family and its full-head lift are new PAPER scope checks pending human review; no new Lean was launched. This is a source-to-target AGE bound, not the STOPPED E012 spacing claim between repeated target USES. It pays explicitly with clock and age, not original LOWfree. No original source, co-supplier, old stock or source-before prefix is removed.

## OLD E114 all-word theorem and its existing consumer

For EVERY finite signed weighted walk with unit signs, integer initial current x and nonnegative base b, let H/B be its full original cumulative sign height/area and X_t=x+(b+t+1)H_t-B_t. Suppose 0<=u<q and the INTEGER candidate X_q-(b+q+1) equals X_u. Set L=q-u, n=b+q+1, s=H_q-H_u and Ar=B_q-B_u-L*H_u. Then

    Ar=n(s-1).                                                   (1)

If s=1, (1) gives Ar0, exactly the literal original Win/P2 source. If s!=1, then

    4n<=L^2+4L.                                                 (2)

No positivity, greedy, seed-size, sign-deficit, depth, run count or length ceiling is assumed for this implication. In a canonical actual history the equation uses a(q)=a(u)+q+1, so it does not confuse Nat subtraction truncated to0 with an integer candidate. For a positive original-free A, EVERY numerical historical source has s!=1 and satisfies(2), not just one selected source.

Consequently for EVERY R>=0, at n>(R^2+4R)/4 ALL numerical sources of age<=R are exact original P2 sources; conversely any such original P2 source remains a numerical source. This supplies equality of recent source sets at a paid clock threshold. It does not eliminate older sources, external initial blockers or nonpositive candidates. A distinct original LOW candidate-class/free charge is still missing.

## Complete endpoint-envelope proof

For ANY length-L unit-sign word of final mass s, let A denote its prefix area. Put a=(L+s)/2 and z=(L-s)/2. Adjacent swapping SA to AS preserves mass and raises area by2. Sorting gives the maximum at A^a S^z and minimum at S^z A^a. Direct summation gives

    -L^2+s^2+2(L+1)s <=4A<=L^2-s^2+2(L+1)s.                    (3)

The same bound follows from the existing `mass_eq`, `twice_moment` and `positions_upper`, together with the elementary lower bound 2*positions>=a(a+1). This is an alternative algebraic verification, not a second result. It holds for L0 as well. In(1), L>=1.

If s>=2, let Q=L^2+4L. The exact factorization

    (s-1)Q-[L^2-s^2+2(L+1)s]=(s-2)(L^2+2L+s)>=0

and(3)/(1) give 4n(s-1)<=(s-1)Q. Divide by the POSITIVE s-1 to obtain(2).

If s<=0, the lower envelope gives 4n(1-s)<=L^2-s^2-2(L+1)s. The difference from (1-s)Q is

    4L+s^2-s(L^2+2L-2)>=0,

since L>=1 and L^2+2L-2>=1. Divide by POSITIVE 1-s. These two cases exhaust integer s!=1. No unproved area bound or desired charge is input. The L1 possibilities cannot satisfy a positive integer-clock blocker equation, but the proof does not silently use that exclusion.

Equality in(2) forces the positive case s2 and the maximum-area word A^(L/2+1) S^(L/2-1). The negative case is strict because its displayed difference includes4L>0. In the positive factorization s>2 is strict. Thus L is even and n=L^2/4+L. The all-parameter greedy construction below shows this algebraic boundary is actually realizable with a coherent finite stock.

## Actual coherent sharp family, for EVERY m>=1

Put b=m^2-1,x=m^2+1,L=2m,n=m^2+2m and prescribe

    v=A^(m+1) S^(m-1), then one final A.

Let U_j=x+b*j+j(j+1)/2, the value after j initial A. Supply the COMPLETE initial stock

    V={0,x} union {C_j:0<=j<=m},
    C_j=x+(j-1)b+(j^2-j-2)/2.

All members are natural: C0=1, C1=m^2, and C_(j+1)-C_j=b+j>=0. The current x belongs to V. Every initial A is forced by its positive candidate C_j already in V. Duplicates are harmless, including m1's C0=C1. No unreachable initial stock is called canonical.

For the k-th S, 1<=k<=m-1, put r=m+1-k. Its prescribed output is

    Y_k=U_r-k^2,                 2<=r<=m.

Because k^2< b+r=U_r-U_(r-1), one has U_(r-1)<Y_k<U_r. Thus it avoids EVERY earlier ascent output, initial current and0. The S outputs strictly decrease, so they avoid each other. For the initial blockers, C_j=U_(j-1)-1 for j>=1. If k1 then r=m and C_(r+1) is NOT in the seed (its index is m+1, an actual S clock). If k>=2, then Y_k<=U_r-4<C_(r+1) while Y_k>U_(r-1)>C_r. Hence all seed candidates are avoided as well. C0 lies below x. Every S landing is strictly positive and fresh against the FULL stock/outputs. The m1 empty-S boundary is included.

At time L the value is x+n, so the final candidate is the INITIAL current x and forces A. The word mass at that time is2. Any literal original P2 source would have height1; the only prior such state is u1 on the initial ascent. Its relative area is n-L=m^2, never0. Therefore the final A is genuinely original free, yet numerically blocked by u0 at mass difference2. Finally 4n=L^2+4L exactly.

Thus the quadratic coefficient and the linear correction in(2) are sharp in the arbitrary coherent-State domain, including with an additive fixed correction when varying m. This is not canonical sharpness, an original-positive/initial-S/return counter, or a C1 counterexample. The family starts with A and its initial stock has no canonical prehistory supplied.

## Falsifier and formalization chain

The frozen finite check covered8191 sign words of lengths0..12, including924 positive integer-clock non-P2 equations satisfying source-base>=0. Both endpoint envelopes and(2) passed. Actual full-stock replays for discovery m1/2/3 and untouched parameter controls m5/11/17 passed; each final A had zero original P2 suppliers and attained equality. These finite checks are COMPUTED support, not proof of the all-parameter statements. Source/argv/hash/CPU are in `data/depth_general_20261122/BLOCKER_AGE_PROTOCOL.json` and exact receipts. No stopped job was resumed.

Aborted formalization plan, retained for the novelty audit (DO NOT execute as new work): (a) prove both endpoint envelopes on the existing literal word mass/moment; (b) use the exact canonical value/window identity already in `FiniteP2Semantics`; (c) prove source-age or P2 alternative without assuming an area envelope/charge as a new Prop; (d) recent-source exclusion is the consumer. SOURCE AUDIT OVERRIDES THIS PROPOSED PLAN: the optimized age inequality and canonical consumer already exist verbatim in E114, so this formalization is NOT executed and is not progress. No new module is created. If formalized, PAPER-to-Lean is local progress only and not a second depth-general reset. All human review remains pending.

## Remaining uncertainty

K_LOW depth payment for arbitrary interleaved recovery remains CONJECTURED. The new clock/age threshold has no unpaid conversion into original LOWfree count. A blocker can be older than the threshold, or an arbitrary initial stock value can be a blocker without a source in the word. E766 generic class counting is not imported at exceptional canonical base0. E388 COMPUTED/E404 CONJECTURED/E384 existence-unLean, protected central claims and all old resource/one-repair STOPPED restrictions are unchanged.
