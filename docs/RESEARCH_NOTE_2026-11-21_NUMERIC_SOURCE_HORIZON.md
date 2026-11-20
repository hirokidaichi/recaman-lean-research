# Numerical positivity gives a fixed-source final-use clock

PROVED-PAPER, not Lean checked; human review pending. H-20261121-04 is a different mechanism from head padding: it uses the weighted value of one fixed numerical history. It gives an explicit, very large final-use clock for every fixed literal P2 source, and an exit time for a positive original ledger with bounded total original free. It does not pay LOW free in C1.

## Statement with finite quantifiers

Fix arbitrary integers x,b>=0, Q>=0 and signs e(0),...,e(Q-1) in {-1,+1}. Define

    H(0)=B(0)=0,
    H(t+1)=H(t)+e(t), B(t+1)=B(t)+H(t+1),
    X(t)=x+(b+t+1)H(t)-B(t).

Assume X(t)>0 for ALL 1<=t<=Q; X(0)=x is allowed to be0. The independent weighted-value recurrence is X(t+1)=X(t)+(b+t+1)e(t). No greediness, seed coherence, S freshness or bound on H above is assumed.

Put L=floor(x/(b+1)), U(s)=x+b*s+s(s+1)/2, and define the integer sequence

    s(0)=0, s(j+1)=s(j)+2*U(s(j))+1.

Then for ALL j>=0 and ALL t with s(j)<=t<=Q,

    H(t)>=-L+j.                                           (1)

The dependence on x,b is explicit. The iteration is not a practical finite enumeration bound and has not been numerically executed to enormous j.

## Proof: supply the lower floor, then raise it

First H(t)>=-L throughout. Choose a minimum m of H on [0,t], attained at v. If v=0 the claim is immediate. Otherwise B(v)>=v*m, so strict positivity gives

    1<=X(v)<=x+(b+1)m.

In particular m>=-floor(x/(b+1)). This is a running minimum argument over the ORIGINAL full prefix, not an assumed floor or a discarded old source.

The new edge is the following finite floor-raising lemma. Suppose ALL H(t)>=m on s<=t<=Q. Write y=X(s), a=b+s and rebase h(i)=H(s+i)-H(s), l=m-H(s)<=0. We claim that no h(t)=l occurs at local t>=2y+1.

If there is no visit to l, this is immediate. Otherwise let v be the first such visit. If v>0, every earlier local post-step height is at least l+1, so its prefix area C(v) satisfies C(v)>=v*l+v-1. Therefore

    1<=X(s+v)<=y+(a+1)l-v+1,
    v<=y+(a+1)l=:D<=y.                                  (2)

For any later visit t>v to l, the segment has even length t-v and stays at or above its starting height. Each odd-position post-step height relative to that floor is at least1. Its area is therefore at least (t-v)/2. The weighted-value identity at equal endpoint heights gives

    1<=X(s+t)<=X(s+v)-(t-v)/2.

Combining with (2) yields t+v<=2D<=2y, hence t<=2y. The first visit v also has v<=y. If instead v=0, then l=0 and the same even-segment argument directly gives X(s+t)<=y-t/2 at every later floor return. Positivity gives t<=2y-2; when y=0 there is no positive-time return. Thus the conservative cutoff2y+1 covers s=0,x=0 and all parity cases. Since heights are integers, ALL t>=s+2X(s)+1 have H(t)>=m+1.

Finally X(s)<=U(s), by replacing each of the first s signs in the direct weighted sum by +1. Induct on j. The initial floor was supplied above. If s(j)>Q the next assertion is empty. Otherwise apply the floor-raising lemma at s(j) and use X(s(j))<=U(s(j)). This proves (1) without a global height ceiling.

## Actual old-source consumer

Take ANY original literal source clock u<=Q. Set y=X(u), a=b+u; use the same recurrence s_(y,a) in the rebased suffix. A literal Win(u,q-u) requires H(q)-H(u)=1 (and its original area equation). Let

    J=floor(y/(a+1))+2, T_u=u+s_(y,a)(J).

By (1), ALL q>=T_u have H(q)-H(u)>=2. Thus EVERY original P2 use of source u is at q<T_u. No source is selected away: co-suppliers are retained and the same conclusion holds separately for each. For a finite old-source prefix, the maximum of its T_u bounds the last possible use from that prefix. The literal P2 equality also gives X(q)-(b+q+1)=X(u); E111 warns that a numerical blocker can satisfy this equality without the required height difference1. Such non-P2 blockers are NOT eliminated here.

E761 already bounded the NUMBER of uses of a fixed source using its numeric value/clock and allowed an unpaid last-use boundary. The new edge here supplies a TIME cutoff from positivity and successive floor raising. It is not a reproof of the E761 count, nor a constant depending only on original free.

## Original free budget consumer and infinite scope

For the SAME original sign history, let F(t) count its original free A, E(t) its supplied A, and S(t) its S. If the original positive-prefix condition S(t)-E(t)>=1 holds at every nonempty prefix, then

    F(t)-H(t)=S(t)-E(t)>=1.

Consequently, if its TOTAL original free through Q is <=R, put j=max(1,R+L). If Q>=s(j), (1) at the positive time s(j) would give H>=R and therefore F>=R+1, a contradiction. Hence

    Q<s(max(1,R+floor(x/(b+1)))).                         (3)

This is a derived free-budget EXIT horizon with explicit original numerical initial value/base. It does not input the desired free payment, replace A by free, or forget any source-before prefix. It is not the finite return inequality minH>=-h-R sought by H01/H02.

For ONE fixed infinite positive weighted walk, the finite result implies H(t) tends to +infinity: given any integer K choose j with -L+j>=K and apply (1) at every later t. Under the ADDITIONAL original positive-prefix condition, F(t) also tends to +infinity by F>=H+1. This statement does not apply to arbitrary exact Recaman orbits unless that original positive-prefix hypothesis is separately supplied. It proves none of the protected E001/E067/E070/E179 claims.

## Falsifier and scope audit

The frozen worker checked1103 numerical-positive prefixes,2683 nonvacuous floor-raising targets,10583 recurrence targets,367 literal P2 hits and96 targets beyond computed source cutoffs. It uses direct weighted values independently from the H/B identity and enumerates all positive words of length<=8 in the stated parameter sets. Discovery x=0/1/3,b=0/2; unused parameter controls (2,1),(7,1),(2,3),(7,3). These are finite parameter controls, not fresh canonical orbit data. Balanced words (AS)^(x-1) at (x,b)=(5,0),(20,3) return to floor0 at time2x-2 with final value1; the time cost cannot simply be dropped. The finite result is COMPUTED; the unbounded statements rely on the proof above. Source/input hashes, argv, current revision, limits and exact wait4 CPU are in [protocol](data/depth_general_20261121/NUMERIC_HORIZON_PROTOCOL.json) and its receipt.

Dropping numerical positivity fails already at x=b=0, word S: H(1)=-1 below the initial floor0. Replacing fixed x by a new larger State for each finite Q gives no infinite result: E759/E762 finite completions explicitly allow that change. The finite maximum cannot be promoted to a canonical-reachability certificate. Strict positivity is sufficient here; no claim that it is the weakest possible hypothesis is made. No counterexample to a nonnegative-only version was found or claimed.

No new Lean file, Audit/root registration or stopped checker job was used. Existing periodic positive-mass results E065/E119 assume eventual periodicity; the present floor mechanism assumes no periodicity. The E323 registry itself warns that its surviving content is bookkeeping: no unverified old drift/free inequality is used in (3). C1/Q/H/SL/surjectivity, arbitrary-depth LOW-free charging and a value-free final-use horizon remain unresolved.

## Stronger edge: keep the clock and remaining value together

The all-A envelope above is valid but unnecessarily expensive. The following NEW joint potential gives an exponential final-use horizon. Assume at a cut c that H>=m thereafter, y=X(c)>=1, and a=b+c. At ANY visit v>=c to the floor m, put z=v-c. Then

    2X(v)+z<=2y, hence z<=2y-2.                         (4)

To prove (4), if H(c)=m, the segment to v is balanced, nonnegative relative to its starting floor, and has area>=z/2 as above. If H(c)>m, let k>0 be its first floor visit and l=m-H(c)<=-1. The earlier first-visit estimate gives

    2X(c+k)+k<=2y+2(a+1)l-k+2<=2y.

Every later floor return subtracts at least half its elapsed balanced-segment length, proving the same inequality at v. No last-visit conclusion is assumed.

For the last such visit v, if the finite horizon includes v+1, the next step is A: a subtraction would fall below m, and all later heights must be >=m+1. Define c'=v+1,y'=X(v)+b+c' and the joint potential P=a+2y. Then (4) supplies

    c'<=P-b-1,
    P'=(b+c')+2y'=3a+3z+3+2X(v)
                    <=3a+2z+2y+3<=3P-1.               (5)

If the floor is never visited, retain c'=c and simply raise the lower floor; P>=2 implies P<=3P-1. This handles the empty-visit case explicitly.

For x>=1 let P0=b+2x, B_j=3^j*P0-(3^j-1)/2 and D_j=B_(j-1)-b-1 for j>=1. For every finite Q>=D_j there exists a cut c_j<=D_j with X(c_j)>=1, joint potential<=B_j and H>=-L+j at ALL subsequent times through Q. Induct using (5). Since D_j is increasing, the preceding cut exists. A last floor visit is at v<=P-b-2, so Q>=D_j guarantees v+1<=Q; no horizon endpoint is silently crossed. Thus

    H(t)>=-L+j for ALL D_j<=t<=Q.                     (6)

If x=0, positivity forces the first A, X(1)=b+1. The initial floor0 cannot recur at a positive time: a nonnegative balanced return has strictly positive area, giving X<=0. Hence c1=1 supplies floor1 and P1=3(b+1). For j>=2 use

    D_j=3^(j-2)*P1-(3^(j-2)-1)/2-b-1.

The same induction raises the floor to j. At x=b=0 the exact uniform thresholds are D1=1 and

    D_j=(5*3^(j-2)-1)/2 for j>=2.                     (7)

Use D_(L+2) in place of s(L+2) for the fixed-source consumer, rebased at its ORIGINAL numeric source value and clock. Use D_j in the bounded-free exit argument whenever its target j>=1 (j=max(1,R+L) suffices); x=0 with an original-positive nonempty word is impossible because original positivity forces first S. No initial source/prefix or co-supplier is removed.

## Exact weak-model sharpness; actual greedy scope remains separate

For x=b=0 start with A, current value1, time1, H1. At a stage with floor j, starting time c and value y, append (AS)^(y-1). Each AS pair returns to that floor and subtracts1 from the numerical value, so every value stays positive and the last floor value is1. Append A to start the next floor. At floor2 the start is c2=2,y2=3. Thereafter y_j=c_j+1 and c_(j+1)=3c_j+1. Thus c_j=D_j in (7), and the last visit to floor j is D_(j+1)-1. No uniform earlier threshold for H>=j is possible among these numerical-positive weighted walks. This is an ALL-j PAPER construction, not extrapolation from four checked levels.

The extremizers DO NOT certify canonical or greedy sharpness. Already AAASAS has outputs1,3,6,2,7,1: the last S repeats1 and is forbidden in an actual history. The all-level numerical extremizer is a weakened model with its seen-set condition deliberately absent. It refutes improving (7) from numerical positivity ALONE; it does not refute a stronger actual-greedy bound, the original LOW-free floor, or C1.

The separately frozen new-predicate worker checked1048 positive prefixes,12626 floor-visit pairs,638 constructed witness cuts and2978 nonvacuous uniform-floor targets. Unused parameter controls were (x,b)=(1,2),(7,3), distinct from its discovery parameters; the finite weak-model extremizers end floor1/2/3/4 at times1/6/21/66 with value1. These are COMPUTED controls, not the all-j proof or actual orbit data. See [new protocol](data/depth_general_20261121/FLOOR_CUT_PROTOCOL.json). No repair was needed, and the earlier quadratic-envelope statement was not falsified or rewritten as though it had failed.

## Sharper initial numerical floor, consumed without changing the ledger

For x>0 define D as the largest d>=0 with b*d+d(d+1)/2<x; for x=0 set D=0. At a negative running minimum H(v)=-d one has v>=d and H(t)>=max(-t,-d) for 1<=t<=v. Summing this cone gives

    B(v)>=-d*v+d(d-1)/2,
    1<=X(v)<=x-b*d-d(d+1)/2.

Thus H>=-D throughout. This improves the earlier convenient L bound. The floor is attained by the actual all-S segment S^D from coherent seed {0,x}: its positive outputs strictly decrease and are fresh, so no extra numerical history is assumed. For x0, the separate running-minimum argument gives H>=0. Examples x=1/3/4,b0 permit negative depths0/1/2 respectively, with the strict positivity boundary excluded at x3,d2.

Consume this floor in (6): replace L by D, use target index D+2 for a fixed source and max(1,R+D) for the original-free exit. The argument for raising floors is unchanged and supplies the cuts, not their conclusions as input. D depends on the original source VALUE and CLOCK. No original-free or LOW-free upper bound on that value has been supplied. The triangular cone is supporting numerical geometry; the new general consumer remains the joint clock/value floor potential and resulting time horizon.

## Independent audit of escape by summation by parts

There is also a proof of height escape that does not choose last floor visits. For n>=1, direct telescoping of e(k-1)=(X(k)-X(k-1))/(b+k) gives

    H(n)=X(n)/(b+n)-x/(b+1)
          +sum_(k=1..n-1) X(k)/((b+k)(b+k+1)).

All denominators are positive. Each pair k=2j-1,2j satisfies X(2j-1)+X(2j)>=b+2j because their absolute difference is b+2j. The pair's contribution is at least1/(b+2j+1), using the smaller of its two coefficients. Therefore

    H(n)>=-x/(b+1)+sum_(j=1..floor((n-1)/2)) 1/(b+2j+1).

The last sum diverges, independently confirming H tends to +infinity for one fixed infinite history. This weaker logarithmic estimate is an audit of the all-level conclusion; it is not separately counted as another parent success or as the optimal factor-three time bound. It even permits nonnegative X, but the main statements retain their frozen strict-positive domain.

The actual E323 source defines unsuppliedCount as additions not supplied by lag<=7, not the full original EndN-free census. Its drift inequality cannot be substituted for F>=H+1 in the original-free consumer. The latter identity uses the explicitly assumed original positive-prefix condition and ALL original sources. No protected claim or registered Lean signature was changed to hide this vocabulary difference.

## A supplied actual-stock condition, with the original prefix retained

Let M>=1 and consider an actual greedy State at an ORIGINAL cut c, with every integer1<=v<M already in its full seen set. If X(c)>=M, every later S landing is positive and fresh and therefore >=M, while every A increases the current value. Hence ALL later values are >=M. If X(c)<M but the next clock b+c+1>=M, subtraction is nonpositive and the first step is A with output>=M; start the same argument one step later. No assertion that the least missing M grows has been supplied.

At that supplied cut use the arithmetic walk Y(t)=X(t)-M+1>=1. Its weighted increments are unchanged. This is ONLY an arithmetic shift; it is not a new Nat-State obtained by deleting negative shifted stock or forgetting the old prefix. Apply the stronger theorem with initial y=X(c)-M+1 and base a=b+c, giving a relative floor -D and

    H_original(t)>=H_original(c)-D+j
       whenever t>=c+D_j(y,a).

For an arbitrary finite ORIGINAL old-source prefix u<c, put K=max_(u<c) H_original(u), if that prefix is nonempty. The supplied index j=max(1,K+2-H_original(c)+D) then excludes every one of those old literal P2 sources after its common time cutoff. Newer sources and non-P2 numerical blockers remain possible. If total ORIGINAL all-source free<=R and global original positive deficit holds, j=max(1,R-H_original(c)+D) instead forces the original free-budget exit. The F/H counters are NOT reset at c, and no relative BlockWord positivity is assumed in place of the original global hypothesis.

The stock premise is a concrete fact about seen, not the desired free conclusion. Omitting it fails: value5/base1/seen{0,5} subtracts2 to3, below the proposed M5 floor. Omitting both current>=M and the clock condition also fails even with the stock: value2/base0/seen{0,1,2,3,4} is forced to ADD1 to3, still below M5. These are exact one-step actual finite-State controls, not canonical histories. At M1 the consumer reduces to ordinary positivity.

This consumer shows where actual S freshness can pay a stronger numerical floor. It supplies no bound on the residual y=X(c)-M+1 from original LOWfree. E762's numeric translations retain the original finite ledger while changing numerical values, so one must not silently erase this residual or replace a finite State by a canonical prefix. The consumer is not separately counted as a new general theorem beyond the floor potential.

Actual filled-stock falsifier:7 frozen finite-State cases, including unused (M,x,b) controls (3,1,2),(8,1,9),(8,9,2), passed the concrete producer and58 nonvacuous late-A old-source checks. All original sources before/after the cut were computed from the SAME full sign prefix;71 excluded old-source positions are repeated position checks, not71 free charges or distinct theorems. See FILLED_STOCK_PROTOCOL.json/FILLED_STOCK_OUTPUT.json. No finite check supplies the unbounded proof or canonical reachability.
