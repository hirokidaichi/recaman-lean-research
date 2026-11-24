# Old numerical stock pays a last-floor potential discount

PROVED-PAPER; complete argument below, not Lean checked, human review pending. H-20261123-03/04 belong to ONE numerical mechanism in parent R-20261123-01. E764's last-floor potential is an INPUT. The new edge uses actual S freshness against the full OLD visited-value set, and then the gaps that primitive return areas must skip. Numerical stock is not original LOWfree.

## Exact domain and single-step statement

Fix ANY coherent natural finite State at an ORIGINAL cut c, with current x=X(c)>=1, full distinct seen set V_c containing x, and absolute next-step base a=b+c>=0. Continue by the actual greedy rule: at clock q take S iff X(q)-(b+q+1)>0 is absent from the ENTIRE old seen set, otherwise take A; retain every output. Let H increase by1 on A and decrease by1 on S. Fix a finite horizon Q>c with H(q)>=H(c) for ALL c<=q<=Q and H(Q)>H(c).

Let v be the LAST visit to H(c) before Q, c'=v+1, t=v-c and z=X(v). Then the next step is A, and H(q)>=H(c)+1 for ALL c'<=q<=Q. Put

    K=|V_c intersect [1,x-1]|,
    N=|V_c intersect [z,x-1]|,
    P=(b+c)+2x, P'=(b+c')+2X(c').

These are ordinary cardinalities of DISTINCT numerical values. In particular, K is measured at c, never at v or c', and not from list length or from values above x. The new inequalities are

    3t+6z+4N <= 6x,                                  (1)
    P' <= 3P-1-4K,                                   (2)
    c' <= c+2x-1-ceil(4K/3).                          (3)

The floor assumption is explicit geometry, supplied internally by successive last-level visits or a last global minimum when used below. Neither a desired capacity Prop nor a free/class conclusion is an input. Positive initial current ensures every subsequent actual value is positive.

## Primitive excursions and the old-stock price

List consecutive visits to floor H(c) from c through v. Their m nonempty segments are primitive nonnegative balanced walks, of lengths2l_1,...,2l_m; thus t=2 sum l_i. For a segment of length2l its literal post-step relative area A obeys

    3l-2 <= A <= l^2,       A congruent l modulo2.    (4)

Indeed odd post-step heights are at least1, internal even post-step heights at least2 and the endpoint is0. This gives the lower bound l+2(l-1). The tent bound H(k)<=min(k,2l-k) gives the upper bound. Parity H(k)=k mod2 gives the area parity.

The weighted-value recurrence at equal-height endpoints gives exactly X(end)=X(start)-A. Hence the m return values strictly decrease from x to z, the total drop is x-z=sum A_i, and

    x-z >= 3t/2-2m.                                  (5)

Each return ends with S, whose landing is fresh against ALL V_c and earlier outputs. Thus these m distinct values belong to [z,x-1] outside V_c, so

    m <= x-z-N.                                      (6)

Combining (5) and (6) yields (1). The old values below z number at most z-1, so K<=N+z-1, i.e. z+N>=K+1. Since X(c')=z+(b+c') and b+c'=a+t+1,

    P'=3a+3t+3+2z
       <=3a+6x+3-4(z+N)
       <=3P-1-4K.

Also (1) and N>=K-z+1 give 3t+2z+4K+4<=6x. With z>=1 this gives t<=2x-2-ceil(4K/3), proving (3). If v=c there are no excursions, t=m=N=0,z=x and K<=x-1; every argument remains valid. No nonexistent S at the starting cut is counted.

## Sparse old-stock packing

Choose ANY W subset V_c intersect[3,x-1] whose distinct values differ by at least3. Write p=|W| and

    d=max(K,ceil(13p/5)).

Then the stronger inequalities hold:

    P'<=3P-1-4d,
    c'<=c+2x-1-ceil(4d/3).                            (7)

To prove this, the m return values omit x-1-m of the integers1,...,x-1. Their complement partitions into the bottom tail[1,z-1] and the skipped integer blocks between consecutive floor values. A segment of area A contributes a block of length L=A-1. From (4), primitive areas cannot be2,3,5,6,8 or11: l=1 gives1; l=2 gives4; l=3 gives7 or9; l=4 gives10,12,14 or16; l>=5 gives at least13. Nonempty blocks have length at least3.

A skipped block containing k>=1 points of W has L>=3k-2. For k=1,2,3,4 the area exclusions strengthen this to L>=3,6,8,11 respectively; each bound is >=13k/5. For k>=5, 3k-2>=13k/5. The bottom tail containing k points has length>=3k, because W starts at3 and is3-separated. Every point of W is omitted (all return landings are fresh), hence

    x-1-m >= ceil(13p/5).

The same omitted count is >=K. Therefore m<=x-1-d. Rearranging (5) now gives 3t+2z<=2x+4m<=6x-4-4d, which substituted in the exact P' identity proves (7); use z>=1 for its time part. No maximal packing is assumed; sorted greedy packing supplies one possible W. The local interval price13/5 is attained by an area14/block13 with five3-separated points, but no optimality of the complete actual potential coefficient13/5 is claimed.

## Arbitrary-depth consumer, with all old history retained

For ANY j>=1 and actual finite continuation with H>=H(c0) through Q and H(Q)>=H(c0)+j, recursively choose the last level H(c0)+i visit after c_i and let c_(i+1) be its next clock. The horizon condition supplies every next A and the suffix floor; H(c_i)=H(c0)+i. Retain the ORIGINAL complete seen set and original absolute clocks at every cut. Let K_i be its literal old cardinality, d_i either K_i or any packing-refined value above, and P_i=b+c_i+2X(c_i). Iteration proves

    P_j<=3^j P_0-(3^j-1)/2
          -4 sum_(i=0..j-1) 3^(j-1-i) d_i,           (8)
    c_(i+1)<=P_i-b-1-ceil(4d_i/3).                   (9)

At a produced cut c_(i+1), the preceding positive floor value z is already seen and strictly below the A output. Thus K_i>=1 for i>=1. In particular

    P_2<=9P_0-8-12K_0,
    P_j<=3^j P_0-((7+8K_0)3^(j-1)-5)/2.             (10)

The second formula follows by summing K_i>=1 for1<=i<j; at j=1 it reduces exactly to (2). It is a valid bound, not an assertion that all j can attain equality.

A last global minimum of the SAME original actual word supplies a floor cut; its full old prefix remains in V_c. The all-depth recurrence pays depth dependence with P_0 and the explicitly weighted old-stock discounts. A single numerical value may contribute at several later cuts: its exact coefficient is4 times the sum of the corresponding powers3^(j-1-i), at most2(3^j-1). No one-time capacity, depth-independent maximum load, or replacement by original LOWfree is inferred. Values above the current cut value are deliberately unpaid and can become eligible later. Old E764 supplies numerical-source expiry and original-TOTAL-free consumers; the new discounts may be substituted there with the SAME supplied numerical input. No LOWfree-to-starting-potential or class-span payment has been supplied.

## Exact examples and assumption attacks

For ALL x>=1,b>=0, start from full stock{0,1,...,x}, current x, and word A(AS)^b A. Every A candidate is old or nonpositive. After the first A, each loop j=0,...,b-1 has A candidate x-1-3j, A output x+2b+3+j and S landing x+b-j. These S landings descend from x+b to x+1, fresh above the initial stock and below all preceding A outputs. The final A candidate x-3b-1 is also old or nonpositive. Therefore this is an actual greedy word with

    c1=1,c2=2b+2,K0=x-1,K1=x,
    P0=b+2x,P1=3b+2x+3,P2=9b+2x+8.

Both stock-discount steps attain equality. Taking b=0 and x arbitrarily large shows that4 in (2) cannot be increased even with a fixed additive correction. Taking x=1 and b arbitrarily large rules out P2<=alpha P0+C for any fixed alpha<9,C. This simple family starts with A and supplies no original positive-prefix condition; the separate original-S lift below supplies that stronger domain.

A sparse equality example is x=5,b>=4, full initial stock{0,2,3,4,5}, word AASSA, values5,b+6,2b+8,b+5,1,b+6. Both S landings are fresh, K=N=3,z=1,t=4, and (2)/(3) are equalities. This establishes an attained ceil-time example, not asymptotic optimality of the time coefficient.

Dropping S freshness fails on the raw x5/b0/stock{0,...,5} word ASA: its last S lands on old4 and Pnext17 exceeds the proposed13. Counting duplicate old-list entries fails at x2/b0/A with seen[0,1,1,1,2]; correct K=1, not3. Counting high values fails at x1/b0/A with seen{0,1,100,101}: K=0, not3. Counting future stock fails at x1/b7 after the first A: old K1 gives the correct73 bound, while future K8 incorrectly predicts45. These exact negative controls prohibit strengthening by silently changing the counted object.

## Finite falsification evidence, separate from the paper proof

Frozen stock_floor_probe.py checked372 discovery and48 unused-parameter States;36782 all-cut predicates (32943 with K>0;15733 nonempty returns),76468 iterated predicates and27959 primitive excursions. An independent signed-word constructor replayed99 discovery/181 parameter-held-out actual words,81 nonempty returns,226 noncontiguous stocks,254 two-floor targets and three sparse equalities. The independent code uses direct natural greedy choices and literal original prefix areas, rather than the first worker's state enumeration.

The packing/lift worker checked2056 primitive Dyck cases,7953 discovery and189 held-out-parameter stock-cut predicates. Packing strictly improved d>K on4304 checked targets (1608 with a nonempty return). These counts establish COMPUTED finite checks only. The all-depth claims rely on the proofs above. Sources, hashes, argv, revision, exact outputs and wait4 CPU are in data/depth_general_20261123/{STOCK_FLOOR_PROTOCOL,STOCK_FLOOR_INDEPENDENT_PROTOCOL,STOCK_PACKING_LIFT_PROTOCOL}.json and their receipts. Discovery/holdout are predeclared parameter partitions, not fresh canonical orbit evidence.

No Lean/root/Audit adoption, no protected/gate changes, no stopped-job restart. C1/Q/H/SL/surjectivity and K_LOW>=D remain unproved. The companion actual-history sharpness note retains all original S sources and identifies precisely why a factor improvement alone cannot erase the numerical/base cost.

Packing boundary audit: lowering W's minimum3 to2 fails at current3/base0/full stock{0,2,3}, first A output4: K1,p1 would give d3 and the invalid upper5, while Pnext9. The [3,x-1] domain is necessary for the displayed bottom-tail proof. This exact one-step counter does not weaken (7) in its stated domain.
