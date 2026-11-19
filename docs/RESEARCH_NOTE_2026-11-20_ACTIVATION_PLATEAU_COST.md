# A plateau refutes the coefficient-two activation cost

Conclusion: **REFUTED**, with a complete all-parameter PAPER construction below (not Lean-checked, human review pending) and separately **COMPUTED** exact witnesses. The conjecture that every original-positive root activation of depth r needs at least2r+2 PRIOR original free is false. This does not refute C1 or the remaining lower bound max(4,r+2). A new balanced plateau, rather than the OLD single-hill family, is the source of the improvement.

## One exact counter, before the general construction

Let W=SSAAASSSSAAAASAS. Put f before its target equal to SS A^30 W^2 S^9, with the target sign A. Its clock is q73, H_f(q)=19, B_f(q)=1485. It has37 PRIOR original free, all nonempty original prefixes through q have positive deficit, and the target is original free. Add r18 initial S: the same target has exactly source0, window length91, rise1 and area0. Thus37<38=2r+2. The finite output records every A source, not a supplied-tag assumption.

## All-(N,z,U) construction and quantifiers

For ALL integers N>=1,z>=4,U>=3 satisfying U^2=z^2+N(16z-10), set r=U-2,a=U+z and define f:Nat->Bool by the literal finite prefix

    SS A^a W^N S^(z-1), then target A at q=U+2z+16N+1.

After the target the sign function may be completed arbitrarily. Put g=S^r++f. EndN/free in each history is the original Nat0 predicate with EVERY old source, and positivity means S(k)-E(k)>=1 at each0<k<=q (and analogously in g). The claim is

    f target free, g target has sole source0,
    F_f(q)<=U+z-1+4N,
    f and g have positive deficits at every nonempty prefix through their targets.

No bound on upper height, run count or length is an extra premise. U>z follows from the root equation; hence these parameters also guarantee a>=9.

## Input motif, with scope kept explicit

The OLD E750 motif W has length16, mass0, heights in[-3,1], area -10. Its A offsets are2,3,4,9,10,11,12,14. Four targets4,11,12,14 have literal sources1,8,1,7 respectively, completely inside that W copy. These source windows survive any surrounding unchanged history. Therefore there are AT MOST4 original free per copy; cross-copy or pre-plateau sources can only reduce that count. No absence of cross sources is assumed for this upper bound. The W motif is an input, not a newly discovered counter or fresh control.

## Proposer: every supplier and positive-prefix obligation

1. In S^b A^a (b>=1), only the THIRD A is supplied. An initial-S source with j>=1 remaining S requires a prefix S^j A^(j+1), whose area is1-j^2; zero forces j1. A source within the A run has strictly positive area. Thus F=a-1 after the long A run. For b2, all nonempty prefixes are positive: the third A leaves deficit1, later free A leave it unchanged.

2. In f, let P=a-2 be the plateau base. The first two A of the FIRST W (offsets2/3) are original free. At offset2, the sole old-A-run source-height candidate leaves A^3 SS with relative area9, not0. At offset3 it leaves A^2 SS A with area5; the only additional W-internal source-height candidate is a singleton A of area1. Initial S heights0/-1 are too low to match those high source levels. These exhaust ALL sources. Before them the walk only takes two S, preserving positive deficit. After both, F_f>=a+1 forever, whereas every plateau height is<=a-1; hence deficit>=2 throughout all later copies, even if EVERY optional old/cross source exists. The final S run only increases deficit. This is the actual positivity producer, not an added positive Prop.

3. The source-height required at the original target is H_f(q)-1=U-2. It occurs exactly once in the first A run, at clock U+2. It never occurs in W or the final S run: plateau minimum is U+z-5>=U-1, and the final endpoint is U-1. The candidate source window is A^z W^N S^(z-1). All its intermediate relative heights are strictly positive (W minimum z-3>=1; final height1), so its area is positive. Thus EVERY original source fails and the target is original free.

4. In g, the literal head is S^U. Its root prefix is S^U A^(U+z) W^N S^(z-1), of mass1. The same word without W has area z^2-U^2. Each W at relative base z contributes16z-10, so the complete area is z^2-U^2+N(16z-10)=0. Hence root0 really supplies the target. Any new head source i has height-i and target height1, so its required height0 forces i0. Every other source shifts to an original f source, already excluded. This is a genuine, uniquely activated original-free target, not a co-supplied example.

5. The padded history g is positive too, although H02 did not require that premise. Its S^U A^a run again has exactly one actual A and F=a-1; afterward H_g<=z+1, while F_g never decreases. Thus deficit>=a-1-(z+1)=U-2>=1 on all later prefixes, regardless of every added or old supplier. The pure initial S and first A-run prefixes are positive separately. The target A is supplied only after a large positive margin and does not break positivity.

6. The PRIOR free upper bound follows from the exact a-1 in the first A run, <=4 per W copy and no A in the last S run. It excludes the final target A. No original A has been replaced by free, no full supply table was discarded and no inner prefix was reset to a BlockWord.

## Explicit affine family: failure of slope2, not just its constant

For ALL m>=0 set

    N=6m+2, z=25m+10, U=55m+20, r=55m+18.

The root equation holds identically: U^2-z^2=(30m+10)(80m+30)=2400m^2+1700m+300=N(400m+150). The general bound gives

    F_f(q)<=104m+37, while 2r+2=110m+38.

The gap is at least6m+1. More strongly, for EVERY c>104/55 and EVERY fixed C, sufficiently large m gives F_f(q)<c*r-C. Thus no such uniform linear lower bound is possible. The depth r is unbounded; this is a new general-mechanism no-go, not checking a higher fixed rank.

The original initial-S length is exactly2 and original minimum is exactly-2. Its low wallet (heights<=-1) has exactly the first two free A, independently of m. All plateau free are high. The new target is high, not a nearest-initial-source C1 target. D_near=1 and F_low=2 in this family, so it is NOT a C1 counter. The low-wallet/whole-free distinction and arbitrary-orbit reachability remain unchanged.

## Stronger rational slopes and the limitation of a linear lower bound

This is an additional PAPER derivation, not a finite extrapolation. Let kappa=p/q be any rational in(4,8) with p odd, q a power of2, in lowest terms. Define

    D=2q(8q-p),
    choose N0 with p^2*N0+10q^2=0 (mod D),
    N=N0+D*m for sufficiently large m,
    z=(p^2*N+10q^2)/D,  U=z+(p/q)*N.

The congruence has a solution because gcd(p^2,D)=1: p is odd and coprime to q, and gcd(p,8q-p)=gcd(p,8q)=1. Reducing modulo q gives q|N, so BOTH z and U are integers. For large m they satisfy N>=1,z>=4,U>z. Algebra gives U^2-z^2=N(16z-10), hence the same original-positive construction applies.

Writing t=kappa^2/(16-2kappa), u=t+kappa and b=10/(16-2kappa), we have z=tN+b, U=uN+b and u^2=t(t+16). Therefore the proved upper bound on original free divided by r tends to

    C(kappa)=1+(t+4)/sqrt(t(t+16)).

The identity (t+4)^2-(3/4)t(t+16)=(t-8)^2/4 shows that its continuous minimum is gamma=1+sqrt(3)/2, at t8/kappa=8(sqrt(3)-1). Odd-numerator dyadic rationals are dense in(4,8), so for EVERY real c>gamma one can choose such a rational kappa with C(kappa)<c. For EVERY fixed real correction C, sufficiently large m then gives

    F_f(q_target) <= U+z-1+4N < c*r-C.

Thus a universal activation-cost lower bound with ANY coefficient c>1+sqrt(3)/2 and ANY fixed additive correction is REFUTED on the ORIGINAL-positive domain. This is an upper obstruction on possible lower bounds, NOT a proof that gamma is optimal or is itself a valid lower bound. Actual optional sources could only make the counter cheaper. The surviving general lower coefficient1 remains the known max(4,r+2) input.

A concrete affine subfamily (no new computation claimed): kappa23/4, N72m+8,z529m+61,U943m+107 gives Fprior<=1760m+199 and r943m+105. Its leading upper ratio1760/943<2. The smaller discovery family above used kappa5 (odd numerator, q1), giving the previously displayed104/55. No larger-cutoff experiment or old graph is needed for these quantified statements.

## Falsifier / finite evidence and provenance

The exact frozen discovery was(N,z,U)=(2,10,20). Before execution the separate quadratic control parameters(2,54,68)/(4,235,265) were frozen; they gave(r,Fprior)=(66,129)/(263,515). A subsequent independent affine-family predicate was frozen at m1/m3, yielding(73,141)/(183,349). Each full original source table was independently computed by forward H/B equality and reverse literal suffix mass/weighted moment. Full outputs, hashes, revision, argv, CPU caps and raw logs are in[data packet](data/depth_general_20261120/ACTIVATION_PROTOCOL.json) and [affine protocol](data/depth_general_20261120/ACTIVATION_LINEAR_PROTOCOL.json). These are finite COMPUTED witnesses, not the all-m proof. The different parameters are not statistically independent; W itself was already known.

At the H02 checkpoint mathematical workers had used .182698 CPU seconds of a declared2-second budget; guard verification is separately1.120000 CPU seconds, as measured in its five wait4 receipts. Later daily jobs/totals are in CPU_SUMMARY.json; this earlier subtotal is not the final daily total. Every worker is a cooperative single Python process, no descendants, with wait4 usage and a predeclared per-process cap. This is NOT a general process-tree cumulative limit or OS address-space guarantee.

## Current decision

Stop H02's proposed2r+2 lower bound and any slope2-minus-fixed-constant repair. Retain the weaker max(4,r+2) lower bound and all original-history constraints. Local Lean may connect the new exact source geometry, but the all-m proof remains PAPER until separately checked. Human review pending. General C1/Q/H/SL/surjectivity and the main all-R low-free floor candidate remain unresolved.
