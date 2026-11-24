# Departure A outputs supply a stock strip and a factor34/15 floor potential

PROVED-PAPER; not Lean checked, human review pending. H-20261123-10 strengthens the VALID earlier stock-floor/transport theorems with a NEW producer: every integer crossed upwards by consecutive floor-departure A outputs is already seen. A outputs may repeat or jump down. This supplies the missing next-cut stock internally, without a desired capacity Prop. Main new potential W=12a+15x-10K has multiplier34/15<3 at arbitrary depth. This is ONE edge/parent mechanism, not another cycle per coefficient or theorem.

## Exact all-word departure strip

Use H03/H05's ORIGINAL actual-State floor cut c, full old V_c/current x>0/base a=b+c, last floor visit v, next A cut c'=v+1/current y, and primitive return count m. Write s=(v-c)/2,z=X(v),r=x-z-3s+2m>=0,M=x-1-m-K>=0, K=|V_c intersect[1,x-1]|. Let the successive floor visits be c=u0<...<um=v and

    Z_i=X(u_i+1), i=0,...,m.

Every one is an actual A output: otherwise the next step would go below the supplied floor. The last output is Z_m=y and the first is Z0=x+a+1>x. For a primitive length2l_i/areaA_i between visits,

    Z_(i+1)-Z_i=2l_i-A_i<=1,                         (1)

because A_i>=3l_i-2 and l_i>=1. Thus if

    R=y-Z0=2m-s-r>0,

EVERY integer in[Z0,y-1] has already occurred as one of the departure A outputs. For any such integer, start at Z0 and choose the first sequence entry above it; the previous entry must equal it since upwards increments are at most1. Downwards jumps and repeated A outputs do not affect this argument. These values are positive, below y and strictly ABOVE original x. They are disjoint from the H05 old/current/floor-return subset, all of whose values are<=x. Consequently the supplied stronger transport is

    Knext>=max(0,min(x,y-1)-M)+max(0,R).              (2)

When R>0 one has y>Z0>x, so old transport is unclipped and the disjoint sum is justified. When R<=0 the added strip is empty and (2) is exactly H05's clipped inequality. Nothing from future stock is charged at the old cut; the new strip is used only in Knext at its actual clock.

## Main paid potential and complete two-case proof

Define

    W=12a+15x-10K, Wnext=12(b+c')+15y-10Knext.

For ALL cuts above,

    15Wnext<=34W-30.                                (3)

Let L0=min(x,z+2s), which is at most min(x,y-1). Put Delta=Wnext-(34/15)W. Substitute a'=a+2s+1,y=z+a',K=x-1-m-M,x=z+3s-2m+r and (2). Increasing M contributes at most-38M/3; a contributes- a/5. Drop these nonpositive terms to obtain

    Delta<=20s+(11/3)z-(34/3)r-10L0-10max(0,R)+13/3.

If L0=z+2s, this equals

    -(19/3)z-(34/3)r-10max(0,R)+13/3<=-2.

If L0=x=z+3s-2m+r, use 2m-s=R+r to get

    -(19/3)z-(34/3)r+10min(R,0)+13/3<=-2.

Both use only z>=1,r>=0 and the concrete supplied strip. This proves (3), including empty returns, decreasing currents and nonpositive R. Also

    W>=12a+5x+10>=15, P=a+2x<=2W/5-4.              (4)

No pure arithmetic helper is registered as a substantive Lean theorem. The substantive source is (1)'s all-output crossing interval and its disjoint combination with the old fresh-return stock.

## Arbitrary-depth time and original-source consumer

At the SAME successive last-level cuts c_j (all old history/sources retained), beta=34/15 and kappa=30/19 give

    W_j<=beta^j(W0-kappa)+kappa,
    c_(j+1)<=2W_j/5-b-5.                            (5)

The latter uses the already supplied H03 last-floor time bound, with optional additional K discount retained. Repeated numerical values/old stock are transported with the literal clipped set and paid current/base, not charged once to free classes. No unweighted LOWfree or coverage conclusion is assumed.

For a finite positive actual word starting at x>=1/base b, choose its LAST global minimum c0. OLD E764 supplies c0+2X(c0)<=2x and initial floor>=-D, where D=max{d>=0:b*d+d(d+1)/2<x}. Therefore W(c0)<=12b+24x=12P_initial. Put

    G0=12P_initial,
    G_j=beta^j(G0-kappa)+kappa,
    U_j=floor(2G_j/5-b-5).

The U's increase. At every supplied cut the last floor visit is <=U_j-1, leaving its next A INSIDE Q whenever Q>=U_j; the first global minimum also has c0<=2x-2<=U0-1. The SAME induction as the fully audited H05 uniform-envelope argument proves

    H(q)>=-D+j for ALL U_(j-1)<=q<=Q, j>=1.         (6)

For a fixed ORIGINAL positive-valued source u, use its actual X(u)/base b+u/full old stock, target j=D_u+2: its literal P2 height1 uses all precede u+U_(D_u+1). Other suppliers/new sources/non-P2 numerical blockers remain. For original TOTAL free<=R under the additionally named global positive ledger, F-H=S-EndN>=1 gives the corresponding exit with j=max(1,R+D). LOWfree is not substituted for total free.

For initial value0/source0, the first A gives current b+1 and original floor>=1 thereafter (old positive-area/running-minimum fact). At that ORIGINAL cut1 use G0=27(b+1)>=W(1), the same absolute b in U_j, and retain full stock. U0 excludes source0 height1 uses. No zero-current hypothesis is silently changed to positive and no old prefix is discarded.

## Strict improvement of the old clock envelope

A new coordinate alone would not prove a stronger horizon. Let P0>=2 and N_j=(2/5)G_j-4, so U_j=floor(N_j-b-1). OLD E764 gives B_j=3^j(P0-1/2)+1/2. With rho_j=(34/45)^j,

    B_j-N_j=3^j[(1-(24/5)rho_j)P0-1/2+(12/19)rho_j]
             +147/38.

For ALL j>=7, rho_j<1/6: (34/45)^2<4/7 implies its seventh power<(4/7)^3(34/45)=2176/15435<1/6. The bracket increases with P0>=2 and decreases with rho_j; its value at P0=2,rho=1/6 is1/190>0. Thus N_j<B_j uniformly for ALL initial P0>=2 and j>=7, i.e. the new clock is strictly earlier from the EIGHTH raised level onward. It may be weaker at shallow levels; either valid bound or their minimum can be used. No practical small cutoff or globally optimal all-depth clock rate is claimed.

## Supporting sharper recurrence for the earlier T

The SAME supplied strip also improves the earlier T=13a+20x-15K from VALID factor51/20 to

    13Tnext<=33T-166,
    T_j<=(33/13)^j(T0-83/10)+83/10.                  (7)

After the same substitutions, the earlier two-case proof at gamma33/13 has a/M nonpositive contributions0/-300M/13. For L0=z+2s, its remaining numerator is-27s-100z-165m-165r-195max(0,R)-66<=-166. For L0=x it is-222s+225m-360r-195max(0,R)-100z-66. If R>0 the first four terms reduce to-27s-165m-165r; if R<=0 use2m<=s+r to bound them by-219s/2-495r/2. Again <=-166. This proves (7).

At current1/full seen{0,1}/ANY base a>=0, a single actual A gives T0=13a+20,Tnext=33a+38 and exact equality in (7). Thus the slope33/13 and affine correction are optimal for this FIXED T among uniform affine bounds (and no smaller slope with any fixed correction survives a growing base). The full original S lift in E773 has first-cut Tnext=33b+23,T0=13b+20 and the same limiting slope. This is not a claim of all-j simultaneous actual sharpness, nor optimality of W or its clock horizon. P2/P0 still tends9 on that separate family; changing the paid stock term explains why there is no contradiction.

## Falsifier and status

Frozen new-predicate checks:256 discovery/16 unused-parameter States,7403 original-cut strip/consumer predicates,4294 positive strips,639 repeated-departure controls,72 nonvacuous new uniform-horizon targets, five exact(7) equalities and three full original S-prefix sharp-slope cases. This actual parameter sample had ZERO clipped cuts; the separate explicit AAASSSA and H06-H09 clipping families remain required controls, not silently claimed covered here. New independent abstract/clipped verification is recorded separately. Finite checks are COMPUTED; unbounded statements depend on the complete proof above. See DEPARTURE_STRIP_PROTOCOL.json/source-hashed receipts. One prospectively justified budget increase4->5 CPU seconds was for this genuinely NEW output-strip predicate, with unchanged no-child1CPU/10wall contract. No old census/failed Lean restarted, no new Lean adopted. C1/Q/H/SL/surjectivity and numerical-starting-cost payment from original LOW classes remain unproved.
