# Transported actual stock gives a floor potential with factor51/20

PROVED-PAPER; not Lean checked, human review pending. H-20261123-05, same numerical mechanism as H02-H04 in ONE parent R-20261123-01. The new producer transports literal old visited values into the next cut, retaining the loss when the new current decreases. Its consumer is an arbitrary-depth potential with multiplier51/20<3. Initial value/base and stock remain paid; no original LOWfree or canonical reachability is inferred.

## Exact original-cut statement

Use the complete actual State/floor/horizon/last-visit cuts of H03. At cut c write a=b+c, x=X(c), K=|V_c intersect[1,x-1]|. Let v be its last floor visit, c'=v+1, z=X(v), s=(v-c)/2, m the number of nonempty primitive floor returns, a'=b+c'=a+2s+1, y=X(c')=z+a', and K'=|V_(c') intersect[1,y-1]|. Define

    r=x-z-3s+2m, M=x-1-m-K, T=13a+20x-15K.

Then r>=0,M>=0,s>=m, z>=1 and, for EVERY such cut,

    K'>=max(0,K+m+1-max(0,x-y+1)),                     (1)
    20T'<=51T-260,       T'=13a'+20y-15K'.           (2)

There is no monotone-current hypothesis. The old stock is the FULL seen set at each ORIGINAL clock, not a newly supplied Prop asserting (1). The literal proof uses positive weighted values and S freshness; actual greedy A forcing supplies a subclass of this stated actual domain.

## Producer: keep every old value and price the clipping

The K old values below x, the old current x itself, and the m fresh S floor-return landings are K+m+1 DISTINCT retained values in[1,x]. Only max(0,x-y+1) integers of this interval lie at least y. Removing at most that many gives (1). Equivalently put L=min(x,y-1); then

    K'>=max(0,L-M).                                   (3)

The primitive area bound from H03 gives x-z>=3s-2m and hence r>=0. Fresh returns cannot land on the K old values, so M>=0. The exact potential slack is

    3P-1-4K-P'=4M+2r,   P=a+2x.                     (4)

This identifies the unpaid omitted integers and the primitive area excess separately. All quantities are supplied by the SAME original execution, with every old output and source-before prefix retained.

## Consumer: the piecewise inequality, with no hidden sign assumption

Because y-1=a+2s+z and a>=0, L>=L0=min(x,z+2s). Write

    Delta=T'-(51/20)T.

Substitute K=x-1-m-M, a'=a+2s+1, y=z+a', x=z+3s-2m+r, and (3). The dependence on M is at most

    -(153/4)M+15 min(M,L0)<=-(93/4)M<=0.

The explicit a coefficient is -3a/20<=0. Thus it suffices to set M=a=0 in this upper estimate, while retaining L0, giving

    Delta<= (111/4)s+(29/4)z-(51/4)m-(51/4)r
            -15L0-21/4.                             (5)

There are exactly two cases, covering equality as well:

* If L0=z+2s, (5) equals

      -(9/4)s-(31/4)z-(51/4)m-(51/4)r-21/4<=-13.

* If L0=x=z+3s-2m+r, (5) equals

      -(69/4)(s-m)-(31/4)z-(111/4)r-21/4<=-13.

Here s>=m and z>=1 were proved above, not introduced as desired conclusions. This proves (2). Empty returns have s=m=r=0,z=x and are covered. T is positive: K<=x-1 implies

    T>=13a+5x+15>=20,
    P<=2T/5-6.                                      (6)

No arbitrary arithmetic helper is registered as a Lean theorem. The substantive producer is the actual S/old-stock injection (1), which supplies the hypotheses of the two-case algebra.

## Arbitrary depth, and a supplied uniform clock envelope

Take the SAME successive original last-level cuts c_i as in H03, whenever the finite endpoint is at least j levels above its starting floor. With beta=51/20, iteration of (2) yields for ALL j>=0

    T_j<=beta^j(T_0-260/31)+260/31,                   (7)
    P_j<=2T_j/5-6,
    c_(j+1)<=2T_j/5-b-7.                            (8)

The final inequality follows from H03 c_(j+1)<=P_j-b-1, with its additional old-stock time discount optionally retained. Equations (7)-(8) give a base beta<3 instead of the old E764 base3 after a concrete change of potential. This does NOT contradict the companion P2/P0 factor9 examples: P and T count different stock terms, and converting (6) introduces an explicit initial envelope.

For completeness, the floor can be internally supplied for EVERY sufficiently long finite word without assuming its endpoint height. Start a positive actual execution at clock0/current x>=1/base b. Choose its LAST global minimum at c0. The OLD E764 running-minimum identity gives c0+2X(c0)<=2x and H(c0)>=-D, where D is the largest d>=0 with b*d+d(d+1)/2<x. Therefore

    T(c0)<=13(b+c0)+20X(c0)<=13b+26x=:G0.

Define rational G_j=beta^j(G0-260/31)+260/31 and integer U_j=floor(2G_j/5-b-7). These increase, because G0>=26>260/31. The first last-minimum visit is at c0<=2x-2<=U0-1, so if Q>=U0 its following A exists. Inductively, if Q>=U_(j-1), every preceding cut exists (the U's increase); the last visit to its floor is at v<=2T_i/5-b-8<=U_i-1 by the original last-floor bound. Thus its next A exists at c_(i+1)<=U_i. The transport proof applies and supplies T_(i+1)<=G_(i+1). Consequently for ALL j>=1 and ALL U_(j-1)<=q<=Q,

    H(q)>=-D+j.                                     (9)

A fixed original source u is excluded from literal P2 use once the rebased suffix has raised its floor above H(u)+1, using j=D_u+2 in (9) with ORIGINAL current X(u)/base b+u and FULL old seen set. Co-suppliers are retained; a numerical blocker without the P2 height equation is not excluded. The original-TOTAL-free exit consumer uses j=max(1,R+D) under the ADDITIONAL original positive ledger S-EndN>=1, since F-H=S-EndN. Neither consumer pays initial numerical data from LOWfree. No source-free conclusion or canonical past is assumed as a new Prop.

## Falsifier and exact missing-assumption controls

The frozen transport worker tested192 discovery States and16 unused-parameter States,46803 original-cut transport/T predicates (24633 nonempty returns),109358 iterated targets, and49185 independent abstract slack cases (27320 clipped). Its actual finite parameter sample happened to contain ZERO decreasing-current cuts: it cannot be described as actual clipping coverage. This gap was explicitly attacked by a NEW exact construction, not by extending that completed enumeration.

At x1000/base0/full stock{0,984,999,1000}, the actual word AAASSSA has values

    1000,1001,1003,1006,1002,997,991,998.

Its three initial A candidates999,999,1000 and final A candidate984 are old; S landings1002,997,991 are fresh and positive. Here x'=998<x,K2,m1,K'3. Omitting clipping would incorrectly require K'>=4; (1) correctly requires only1. This is an exact counter to the unclipped transport variant, not to (1), C1 or a canonical orbit. AASSA at x5/base4/stock{0,2,3,4,5} has first/final A outputs10,10, so counting all excursion-departure A outputs as distinct is also invalid. Its repeated A is legal.

All finite checks are COMPUTED. The unbounded statement (2)/(7)/(9) relies on the proofs above. See STOCK_TRANSPORT_PROTOCOL.json, TRANSPORT_NEGATIVE_PROTOCOL.json and exact source-hashed wait4 receipts. Budget was prospectively raised3->4 CPU seconds ONLY for this genuinely new transport/slack predicate, under the unchanged verified single-Python/no-descendant1CPU/10wall contract. H01's failed CPU remains counted; no stopped job or completed range was reopened. No Lean adoption, no new arbitrary hypothesis wrapper, no protected/gate changes. Beta51/20 is a convenient proved multiplier, not claimed optimal. The C1 depth-to-original-LOW-class/free payment remains unproved.

### Zero-valued initial source

The displayed source consumer uses X(u)>=1. If the original source is the initial x=0 at clock0, strict positivity forces its first step A, X(1)=b+1. The old running-minimum/positive-area argument gives H(q)>=1 for ALL q>=1: a negative running minimum or a later balanced return to0 would have X<=0. Thus use the actual original cut1, retain its full stock, take G0=33(b+1)>=T(1), and U_j=floor(2G_j/5-b-7) as absolute clocks. The same induction gives H>=1+j after U_(j-1); already U0 excludes source0's height1 uses. This special case is not obtained by pretending X(0)>0 or by deleting its source/prefix.

### Why the unpaid initial numerical term remains

OLD E762 translates any fixed finite actual word by an arbitrarily large numerical amount while pre-seeding its nonpositive-A candidates, preserving ALL original signs/sources/LOWfree and the full old stock. Apply that OLD constructor to this NEW T: the number of distinct added seed values is bounded by the fixed word's A count, while current increases without bound. At any fixed original cut, K is bounded by the fixed full-stock/output cardinality independently of the translation. Hence T grows without bound with that same fixed original ledger. This is an input-based necessity audit, not a new countermechanism row or another parent success. A numerical starting-potential bound from the original word ledger alone is therefore unavailable in this finite-State domain; canonical provenance or another paid hypothesis is still needed. A fixed finite translated family is never glued into one fixed infinite execution.

### The converted clock bound is strictly stronger at sufficiently many levels

Changing potential alone would not show a better clock bound. Here the comparison is explicit. Put P0=b+2x>=2 and kappa=260/31; G0=13P0. The new P envelope is

    N_j=(2/5)(51/20)^j(13P0-kappa)+(2/5)kappa-6,

whereas the OLD E764 envelope is B_j=3^j(P0-1/2)+1/2. Let r_j=(17/20)^j. Then

    B_j-N_j=3^j[(1-(26/5)r_j)P0-1/2+(104/31)r_j]
             +195/62.

For ALL j>=11, r_j<7/40: indeed (17/20)^4<21/40 and (17/20)^3<5/8, so its eleventh power is <(21/40)^2(5/8)=2205/12800<7/40. On this domain the bracket increases with P0>=2 and decreases with r_j; at P0=2,r_j=7/40 it equals207/775>0. Therefore N_j<B_j for ALL initial P0>=2 and ALL j>=11. The converted uniform clock U_j=floor(N_j-b-1) is strictly earlier than the old integer B_j-b-1 from the twelfth raised level onwards. At shallow levels it can be weaker; use either proven bound, or their minimum. No claim of optimal multiplier or practical small cutoff is made. This comparison is a PAPER consequence of the supplied actual-stock producer, not a new equivalent capacity wrapper or a separate progress cycle.
