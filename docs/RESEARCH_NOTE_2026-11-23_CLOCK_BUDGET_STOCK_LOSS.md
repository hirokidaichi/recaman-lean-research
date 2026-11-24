# Linear stock-loss payment fails even after four explicit clock-budget filters

REFUTED: a fixed linear payment of old-to-next numerical stock loss by ALL original free/classes, even after the FOUR specified necessary canonical filters below. The all-parameter proof is PAPER, not Lean checked/human review pending. This is the strongest H06-H09 no-go; the earlier coherent-only H08 failed cardinality and is preserved with that limitation. Passing these necessary filters is NOT actual canonical reachability or C1 refutation.

## Exact theorem with all numerical inputs supplied

For ALL k=20n+15,n>=0, set

    l=3k, b=5k^2-k-2, x=10l^2,
    initial clock a=b-2, initial current I=x+2b-1,
    gap=4k^2-5k+1, y=x-gap,
    C_j=x+(j-2)b+j(j-3)/2 (1<=j<=l),
    C_tail1=x-l^2-b-2l-1, C_tail2=x-l^2-1.

Start from the COMPLETE coherent finite seen set

    V={0,I} union {C_j:j!=3} union {C_tail1,C_tail2}
                  union [y,x-1].                    (1)

No S holes or omitted old supplier entries are needed. The original word SS A^l S^l AA is actual greedy, has all original positive deficits>=1,maximal initial head2,return0,minH=-2/D0, ONLY supplied A target4/source1, ALL original free/classes3k+1 and original LOWfree/classes4. At original cuts2 and2l+3,

    Kold=gap+3, Knext=5,
    loss=Kold-Knext=4k^2-5k-1.                       (2)

Thus loss/(F_all+1) and loss/(K_all+1) tend to infinity. For ANY fixed C,C0 the inequality loss<=C*F_all+C0 (or K_all) eventually fails. No arbitrary nonlinear class bound, LOW-depth C1 claim or surjectivity claim is refuted.

At initial clock a, (1) ALSO satisfies all FOUR literal necessary filters:

    |V|<=a+1,
    I congruent upperTri(a) modulo2,
    EVERY v in V lies in[0,upperTri(a)],
    upperTri(a)<=I+s(2a-s+1), s=|V|-1.              (3)

The last is the OLD E755 sorted visited-clock-cover necessary budget. It is only a numeric necessary inequality, not a constructed past. No other canonical hypothesis is implied or silently added.

## Full actual-word producer, independent of the desired stock conclusion

The exact core A/S formulas, future tail candidates and original ledger are those derived in H06 for a general positive b, not its old scalar choice. At each ascending A_j its candidate is C_j; C3=J1=x+b comes from the original head S, while all other candidates and both tail candidates are preseeded in full. Every seed value is natural/positive except0 (x=90k^2 is ample). Head outputs J1=x+b,J0=x are positive and avoid the future full seed: C_j-J1=(j-3)(b+j/2) vanishes only at excluded j3; no C_j=x, tails are below x and padding is below x.

For core S landing Y_d=x+db-d(d-1)/2+l(2d-l), use H06's exact comparison

    Y_d-(A_e-epsilon)
      =delta(b+d)-delta(delta-1)/2-(l-d)^2+epsilon,
    delta=d-e, epsilon=0 (old A output) or1 (seed C_j).

Negative/zero delta cases are excluded as in H06, including the out-of-range epsilon1/r1 case. For delta>=2 a zero would require

    b<=l^2/2-l=(9/2)k^2-3k<5k^2-k-2,

impossible. For delta1 it requires b+l+epsilon=r(r+1), so4(b+l+epsilon)+1 is a square. Since k0mod5, that expression is3mod5 for epsilon0 and2mod5 for epsilon1; neither is a square. Thus ALL old ascending outputs and minimal seed entries avoid ALL S landings.

For head J_e,e0/1/2: same-height equality l(2d-l)=0 is impossible (l odd). Delta1's three roots l^2-2l,l^2-4l+1,l^2-6l+2 all exceed b for k>=15; the smallest difference is4k^2-17k+4>0. For delta>=2 the difference is at least2b+4l-l^2-1=k^2+10k-5>0. Negative delta cases are below the head values. Tail candidates are below Y0 and cannot block any S. This exhausts every minimal old value, head/core old output and future seed candidate.

Finally Y0=x-l^2<y,Y1=y-1, and

    Y2-x=k^2+10k-5>0.

Every Y_d for d>=2 is even larger. Hence NO S landing lies in the entire added interval[y,x-1]. The FULL seed enlargement (1) preserves every A/S choice by direct induction, without deleting any older mass or assuming future legality. The original H/B/source/positive/return facts then follow from the complete source proof in H06: only SAA at target4/source1 has area0; SSAAA has area-3 and other compatible prior-source windows have positive area1 or l^2+1. ALL free classes are pair-distinct (ascending heights differ, repeated tail height keys differ by l^2 or l^2+2l).

## Exact count and four filters

The minimal seed has l+3 distinct entries. C1 and both tail candidates lie below y, C2=x-1 is the ONLY overlap with the padding interval of length gap, and other positive minimal entries exceed x. Thus

    N=|V|=(l+3)+gap-1=4k^2-2k+3,
    Kold=4+gap-1=gap+3.

At the next current y, the added interval contributes no value STRICTLY below y. The old low three candidates and fresh Y0/Y1 give Knext5. All head/core A and other S outputs exceed x. This proves (2), with no substitution of old-stock cardinality for original free.

For (3), a+1-N=k^2+k-6>0. Since k3mod4, a=5k^2-k-4 is2mod4, so upperTri(a) is odd; I=100k^2-2k-5 is also odd. The largest seed is C_l=15k^3+(163/2)k^2-(17/2)k+4, at most15k^3+82k^2. Since a>=4k^2 and k>=15, upperTri(a)>=8k^4>=15k^3+82k^2. This bounds EVERY seed entry and current, not just the interval.

Put s=N-1=4k^2-2k+2. Then 2a-s+1=6k^2-9, s>=3k^2 and6k^2-9>=5k^2. Their product is at least15k^4. Meanwhile a<=5k^2 gives upperTri(a)<=(25k^4+5k^2)/2<=13k^4 for k>=15. Thus the sorted cover inequality in (3) holds with room to spare, even without its positive I term. The earlier H08 cardinality obstruction has been addressed by a new full-stock producer, not by removing stock or claiming necessary conditions sufficient.

## Meaning and finite controls

All-growing initial numerical value/base/stock and high free remain explicit. Four tested necessary canonical conditions do not supply source-before canonical sign chronology. D0 and LOW4 stay fixed, so the family is not a C1 counter. It stops any LOW-only stock-loss bound and any fixed linear ALLfree/class payment in this domain. A proof restricted to a genuinely derived canonical-provenance condition may still survive; (3) alone cannot supply it. The positive factor51/20 transported potential remains valid and its numerical current/base terms pay these examples; no contradiction is asserted.

Frozen k15/35 discovery and unused55/75/95 pass COMPLETE natural greedy/all-original mass-area source/positive/return/free-class/stock/filter verification. Losses824/4724/11824/22124/35624 and ALLfree46/106/166/226/286 are COMPUTED finite controls, not the all-k proof. The full seed is reconstructible from the explicit recipe/interval and exact cardinality/hash in CLOCK_BUDGET_STOCK_LOSS_PROTOCOL.json and clock-budget-stock-loss.log. No fresh canonical holdout, unbounded computation, new Lean/root/Audit adoption or stopped-job restart.
