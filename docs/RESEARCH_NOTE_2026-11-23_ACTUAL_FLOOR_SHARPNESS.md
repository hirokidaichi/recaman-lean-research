# Two-floor factor nine survives a full original S prefix

PROVED-PAPER; not Lean checked, human review pending. H-20261123-02/04, same numerical mechanism as the stock-floor inequality. The countermechanism is to a smaller uniform numerical amplification factor, not to C1 or a canonical orbit. Old E764's all-j extremizer was numerical-only and failed S freshness; this construction is actual greedy, with ALL original sources and old stock retained.

## All-parameter construction and exact statement

For ALL integers x>=1,h>=2,b>=h+3, take initial absolute base a=b-h, initial current

    I=x+h*b-h(h-1)/2,
    complete initial seen set V={0,I} union {1,...,x-1}.

Run the original word

    S^h A^3 S^2 (AS)^(b-4) A.                         (1)

The empty low interval for x=1 is allowed. This exact coherent finite State and its word have positive numerical values, actual greedy choices, original positive-prefix condition S-EndN>=1 at every nonempty prefix, initial S^h, final H=2-h, minH=-h, and D=0. The ONLY original supplied A is target clock h+2, supplied by original source h-1; every other b-1 A is original LOWfree and pair-distinct. This quantifies over a family of initial States, not one fixed infinite execution and not canonical prehistory.

At the ORIGINAL retained cut c0=h, current x and absolute base b, the next last-floor cuts and potentials are

    c1=h+1, c2=h+2b-2,
    P0=b+2x, P1=3b+2x+3, P2=9b+2x-4.                (2)

In particular for any fixed x,h and alpha<9,C, sufficiently large b violates P2<=alpha P0+C. Thus retaining an arbitrarily long prescribed initial S prefix, all old sources, positivity and the return condition does not justify a uniform factor below9 plus a fixed additive correction. It does not rule out a further paid stock/base-dependent bound.

## Direct greedy proof with the full seen set

After d remaining head S steps the head values have the form

    J_d=x+d*b-d(d-1)/2,  d=h,h-1,...,0.

Their successive gaps are b-d+1>=4. They strictly descend from I to x, remain positive, avoid the low old stock<=x-1 and never revisit a head output. Thus S^h is actual and all its old outputs remain present at c0. Now index the core relative to c0.

The first three A outputs are x+b+1,x+2b+3,x+3b+6, with subtraction candidates x-b-1,x-1,x+b respectively. The first two candidates are nonpositive or in initial low stock. The third is EXACTLY J_1, an original head S output, so A3 is forced by a genuine retained original source; it is not assumed as an adapter premise.

The next S outputs are x+2b+2 and x+b-3. The first lies strictly between J_2=x+2b-1 and J_3 when J_3 exists, and differs from every earlier core A output. For d>=3,

    J_d-(x+2b+2)=(d-2)b-d(d-1)/2-2>0:

b>=h+3>=d+3 makes the right side at least(d^2+3d-16)/2>0. The second S output is below J_1 and above all initial low values and x, hence also fresh. Both are positive.

For each j=0,...,b-5, the AS pair starting at relative clock5+2j has current x+b-3-j, A candidate x-9-3j, A output x+2b+3+j, and S landing x+b-4-j. Every A candidate is nonpositive or in the FULL initial low stock. Every S landing is new, decreases through x+b-4,...,x+1, and is below every head value J_d with d>=1 and earlier high core output. Repeated A outputs are legal. After these b-4 pairs the last floor value is x+1. The final A at relative clock2b-3 has subtraction candidate x-3b+3 (nonpositive or initially old) and output x+3b-1. This proves every actual greedy choice for ALL parameters, including b=5/h=2.

The core heights are0,1,2,3,2,1,(2,1) repeated b-4 times,2. It stays above its original level and ends two levels above it. The last visits to relative levels0 and1 are respectively clock0 and2b-3, proving the exact ORIGINAL cuts and (2). At c0, K0=x-1; at c1 the old positive values below its new current are low1,...,x-1, x and J_1=x+b, so K1=x+1. Both stock-floor potential steps attain equality:

    P1=3P0-1-4K0, P2=3P1-1-4K1.

## ALL original suppliers, free clocks and the positive ledger

Use original H,B with H(0)=B(0)=0, B(q+1)=B(q)+H(q+1). A source u<q supplies A at q precisely when H(q)=H(u)+1 and B(q)-B(u)=(q-u)H(u). No source is chosen away. Earlier head source heights above the required preheight have no compatible height equation.

The first core A (preheight0 relative) has no original source one level lower. Core A2 and every later AS-pair/final A have relative preheight1, so only the head endpoint c0 at relative height0 can be an original source: their intervening relative areas are respectively1, 9+3j and3b-3, all strictly positive, so none is supplied. Their class keys, relative to the unchanged original head, are distinct because those areas are distinct (1 versus >=9, with final3b-3 larger than all pair areas). The first A has a different source-height class key. Consequently all these b-1 A clocks are original free and pair-distinct; their preheight<=1-h places all in LOW.

Only A3 has relative preheight2. Its possible original sources at relative height1 are head clock h-1 and the first core A output clock h+1. The former window is SAA, postheight sum0 relative to that source, so it supplies A3. The latter one-A window has positive area1 and does not. These exhaust ALL original source heights. Hence EndN=1 from A3 onwards and zero beforehand. After S^h the original S count is already h, so S-EndN>=h-1>=1; during the head it is>=1 as well. Later S only increases it. Final H=2-h and minimum=-h give D=0 under the original return-depth definition. This is not a C1 counter: its free/class count b-1 grows, while D is0.

## Boundary and scope audit

The h>=2 condition pays the original positive ledger after its one supplied A; b>=h+3 pays head gaps and every freshness comparison; x>=1 pays positivity. The finite evidence is seven COMPLETE original-word natural replays with literal all-source mass/area checks (four discovery parameter triples, three unused parameter triples); each agrees with (2), the unique actual target/source and the original LOW census. See STOCK_PACKING_LIFT_PROTOCOL.json, stock-packing-lift.log and the source-hashed receipt. Finite checks are COMPUTED; the all-parameter statement is proved by the explicit inequalities above.

For x=1,h=2,b>=11 the small initial State V={0,2b}, initial clock b-2 cannot be a canonical prefix already by the OLD E755 necessary visited-cover inequality: tri(b-2)>4b-4. This shows why coherent continuation must not be called actual orbit reachability. The proof does not claim that passing this necessary bound would supply a canonical past. No initial source, other supplier mass or source-before prefix was deleted. No new Lean or stopped-job retry was used. The unresolved C1 step is still the payment from original LOW classes/free to numerical starting value/base, or an independent depth-span rule; a smaller factor alone cannot supply that payment in this domain.
