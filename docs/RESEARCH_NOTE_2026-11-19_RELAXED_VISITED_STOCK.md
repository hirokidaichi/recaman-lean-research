# Repeated all-visit counter and an explicit relaxed visited stock

H-20261119-02, parent R-20261119-01. Complete ALL-N PROVED-PAPER argument after separate proposer/falsifier/auditor passes; human review pending. The proof was frozen before computation. Canonical Recaman prefix reachability is NOT assumed or concluded. This different mechanism audits S-arrival novelty, finite stock capacity and elementary value range, rather than padding/source-prefix charging.

Let W=SSAAASSSSAAAASAS and w_N=W^N A (N>=1,T16N+1), n=1000(N+1), x=10n+100N+100=10100(N+1). H/B are the original sign-word height/area. Set a_q=x+(n+q+1)H(q)-B(q). Then a_(q+1)-a_q=(n+q+1)*sign(wq) exactly. Let R_q=a_q-(n+q+1) be the rejected subtraction candidate at any A. Define V0={0,x} plus R_(16j+r) for j<N,r∈{2,3,9,10}, plus R_(16N). This is an explicit finite set, NOT an oracle hypothesis that it avoids S arrivals.

## Exhaustive arithmetic argument

For q=16j+r inside a W copy, H/B repetition gives

    a_q=x+n*h+c_r+j*(16h+10), c_r=(r+1)H(r)-B(r), h=H(r).

The complete phase classes are:

| h | state offsets r and c_r | copy shift |
| -3 |9:-21|-38|
| -2 |2:-3,8:-12,10:-11|-22|
| -1 |1:-1,3:0,7:-4,11:0|-6|
|0|0:0,4:4,6:3,12:12,14:11,16:10|10|
|1|5:9,13:25,15:26|26|

At the final extra-A state T, h1/d=26N+1. S-arrival offsets are1,2,6,7,8,9,14,16. The only same-level duplicate among nonboundary phases is offsets3/11, BOTH A arrivals (allowed). Boundary16 of copyj equals origin0 of copyj+1 at the SAME physical clock, not a prior visit. Within a level, the S-arrival residues otherwise differ from every past state residue modulo the indicated nonzero shift. Different levels are separated because every residual term has absolute value<=54(N+1), whereas n=1000(N+1)>108(N+1).

Old rejection stock has these classes:

| A offset | rejection level h | residual d |
|2|-3|-6-38j|
|3|-2|-4-22j|
|9|-4|-31-54j|
|10|-3|-22-38j|
|final16N|-1|-6N-1|

For stock versus S arrivals, same-level residues differ: at-3, -6/-22 differ from -21 mod38; at-2, -4 differs from -3/-12 mod22; at-4 no S arrival exists. At-1, the final rejection would match offset1 only in the NEXT absent copyj=N, while offset7 differs mod6. Thus old stock avoids EVERY actual S arrival, not merely earlier ones. x is level0/residual0 and is not a later S arrival;0 is avoided by positivity.

All a_q and old rejection values are positive: their lower bound follows from x-4n-54(N+1)=6046(N+1)>0 (this bound is deliberately coarser than the individual offsets). Every old rejection is<x, so V0 lies in[0,x]. Also |V0|<=4N+3<=n+1. Since x<=11n and n>=2000, x<=n(n+1)/2. Thus elementary old-stock size/value bounds are derived.

At copy A offsets4/11/12/14, the original copy-contained Win sources1/8/1/7 imply R_q=a_u for u<q, by H(q)=H(u)+1 and B(q)-B(u)=(q-u)H(u). Those As are forced by past states. At the other four A and finalA the rejection belongs to V0 by construction. Every S has positive subtraction value equal to its NEW arrival, outside both V0 and ALL previous segment values. These facts prove the exact local greedy decisions for every q<T while retaining the entire V0 and segment history.

This realizes the E750 sign counter in a RELAXED local decision model with one explicit old stock for each N. It does not construct the canonical first n steps leading to V0/x. Original EndN0/free tags of w_N remain raw-word counts; adding a numerical old stock does NOT make them all of the canonical orbit's supply/blocker history. A reachable prefix/old stock realization is still missing. This is a no-go for excluding E750 solely by local subtraction novelty, elementary old-stock size/range; not a C1/standard-orbit counter.

## Falsifier and verification protocol

Attack N1/2 boundaries, first two S, repeated A arrivals, copy boundary chronology, absent next copy at the final A, zero candidate, x∈V0, stock cardinality/range, and cross-height collisions. Frozen finite verification uses existing N1/2/3 word controls as DISCOVERY (new stock predicate, NOT fresh histories). Holdout uses NEW W^N A parameters N5/11, not previously used N3/7. Every S arrival and every A decision is checked by an independent literal reverse scan against the entire old stock and prior segment; every A's original Win source set is separately reverse-exhausted. Finite checks stay COMPUTED; all-N is the residue/height proof only, human review pending.

Today's mathematical worker budget0->2 CPU seconds,1 per split/2wall, cooperative guard verified before this allowance. Hash/argv/revision/dirty hash freeze in RELAXED_STOCK_PROTOCOL.json. No child/math subprocess, no generic process-tree/OS AS claim. One cause-based repair, resource failure STOP/no cap expansion. Distinct mathematical reservation starts06:20:04.655053; actual>=25min must be confirmed, not planned credit. No fresh canonical embedding brute-force search or revival of any stopped old table/generator.

## Independent arithmetic and chronology audit

The same-height S-arrival comparisons are exhaustive: level-3 has just residue-21 mod38; level-2 arrivals-3/-12 differ from the other state-11 mod22; level-1 arrivals-1/-4 differ from repeated A-state0 mod6. Level0 S-arrivals3/11/10 have residues3/1/0 mod10; other states0/4/12 have residues0/4/2. The sole apparent residue0 collision is arrival16+16j with state0+16(j+1), which denotes the SAME clock, not an older visit. No second physical clock has the same value. Level1 has no S arrival; terminal A can revisit a past value without violating the rule. The finite terminal old blocker at level-1 agrees with S-arrival1 only at j=N, excluded by j<N. This excludes an erroneous infinite-periodic interpretation.

The uniform residual bound54(N+1) covers EVERY segment state, final state and all stock values relative to their displayed height classes. Cross-height separation is strict, n>108(N+1). Zero in the stock is exempt from the positive-value assertion; every actual state/rejected A value is positive. Stock size is an upper bound, not an assertion of distinctness or exactly n+1 prior distinct values. Finite membership is checked against ALL old stock and all earlier values. No old alternative source is removed.

## Precise obstruction to canonical reachability

For ALL N>=1 the ORIGINAL displayed V0 cannot be the set of valuesThrough n with a(n)=x. Its maximum is x and n>0. The real predecessor a(n-1) must equal either x-n or x+n. The latter exceeds the maximum. The former is level-1/residual0; the only old stock at level-1 has residual-6N-1, and cross-height separation excludes the remaining levels. Thus x-n is absent too. This argument is stronger than merely saying reachability was not checked. It does NOT refute the proved arbitrary-seed local continuation, but shows why local novelty/stock size/range are insufficient prerequisites for an orbit theorem.

An attempted finite17-clock Lean certificate using actual SeededReplay.run stopped on FIRST compile at kernel memory512MB (H02-LOCAL17-result.json). No resource/tactic/split retry or partial adoption. The ALL-N PAPER argument does not depend on this failed file. Finite discovery N1/2/3 and holdout N5/11 independently passed forward greedy/reverse novelty/all-source checks; COMPUTED, full worker CPU .068267s.

## Next falsifiable refinement, not yet evidence

Adding x-n alone preserves all future S novelty (level-1/residual0), but does not force the preceding A: its rejected candidate x-2n must also be old. This separates predecessor membership from a full preceding greedy step. An arbitrary finite preceding A-tail can be tested by explicitly including its distinct blocked candidates rather than assuming that its signs are executable. Such a result would still concern arbitrary old seeds and would NOT construct the canonical prefix or convert raw-word free into complete-orbit blocker counts.

## Arbitrary finite preceding greedy tail (ALL N>=1,L>=0)

This extension has a genuinely new explicit old stock; it is not a resource/tactic change to the stopped finite kernel. Put M=N+L²+1, n=1000M, x=(L+5)n+100(N+1), b=n-L. Keep the W-segment formula and its four-per-copy/final rejection set C_W. Define

    p_l=x-ln+l(l-1)/2             (0<=l<=L),
    c_l=p_l-(n-l+1)
       =x-(l+1)n+(l²+l-2)/2      (1<=l<=L),
    U={0,p_L} union C_W union {c_l:1<=l<=L}.

At time b start the actual greedy machine from current p_L with old visited set U. For l descending L,...,1, at time n-l the subtraction candidate is exactly c_l, already in U and positive, so an actual A-step arrives at p_(l-1). All original U persists. At clock n this reaches x after EXACTLY L greedy A-steps. No tail signs are assumed as an unproved Prop.

For disjointness from subsequent W S-arrivals, a tail visit p_l has relative height-l and residual l(l-1)/2>=0. A tail blocker c_l has relative height-(l+1) and residual(l²+l-2)/2>=0. The only future S-arrival heights are-3,-2,-1,0. At negative common heights their W residuals are strictly negative, whereas these new residuals are nonnegative. At height0, p0=x has residual0 and no later S arrival has residual0 as an exact value (the positive copy shifts prevent it). Lower heights cannot match. Every cross-height comparison is separated using R=54(N+1)+L²+1<=56M and n>2R. Original C_W versus W novelty and earlier W states is as in the exhaustive table. Thus EVERY future S arrival avoids ALL U, ALL L tail visits, and ALL earlier W visits. Every W A is blocked by C_W or a copy-contained past Win. The resulting complete local continuation is A^L W^N A under the ordinary numerical greedy rule.

Positivity: each W state/old W rejection is at least x-4n-54(N+1)>0; each p_l>=5n+100(N+1)>0, and each c_l>=4n+100(N+1)>0. All nonzero U elements are<=x: n>L² makes the tail offsets strictly negative, and the original W rejection offsets are negative. Stock size |U|<=4N+L+3<=n-L+1. For the elementary numeric range, b=n-L>=n/2 and 8(L+6)<=n. Since100(N+1)<=n, x<=(L+6)n<=n²/8<=b²/2<=b(b+1)/2. Hence ALL U lies within the standard elementary range for time b. This supplies both constraints, rather than assuming an admissible-stock predicate.

The original simpler V0 failed a one-step predecessor test, but the strengthened family has an actual greedy lookbehind of ANY finite declared length L. Therefore adding only a FIXED finite lookbehind to local novelty/stock size/range cannot reject every E750 W segment. It still does NOT construct U from canonical initial0 or prove that its unseen earlier sign history is positive/padded. W's raw Nat0 EndN/free census has its own exact scope; the preceding A^L (and the unknown history represented by U) cannot be silently dropped when making a claim about complete-orbit counts. In particular the whole raw A^L W prefix is not original-positive when L>0. This is a no-go for a proposed LOCAL decision filter, not a counterexample to positive original-history C1.

Independent frozen finite pairs all pass: discovery(1,0),(1,1),(2,3),(3,10), holdout(5,17),(11,31),(2,64). .033263 worker CPU seconds; cumulative mathematical workers .101530s of2s. Finite pairs are COMPUTED, the displayed all-(N,L) proof PROVED-PAPER/human review pending. Neither status is PROVED-LEAN.

## Additional necessary-condition and semantic pass

Canonical clock/value parity also does not reject these local models. Since n is a multiple of1000, n(n+1)/2 is even, and x is even. At b=n-L, p_L≡L(L-1)/2≡b(b+1)/2 mod2. Actual ±step transitions preserve the canonical triangular parity at every subsequent clock. This is a derived ALL-(N,L) parity fact, not an additional assumed visited-set oracle. Conversely, the construction says nothing about the chronological order or individual timestamps of all older U elements; the stock-size upper bound cannot supply that missing information.

A numerical positive blocked candidate is not automatically an original Win source. Win requires BOTH height rise1 and zero source-relative area. The identity a_q-(n+q+1)=a_u is forced by a Win, but its converse without the height constraint is false in general (the finite canonical t5 blocker already separates these notions in FiniteP2Semantics). Therefore the seeded replay must not be cited as proving a count statement about ALL orbit blockers or replacing original raw free by canonical-free. The proof uses copy-contained original Wins only in their safe sufficient direction.

The apparent strengthening to A^L W^N A uses a NUMERICAL tail, not a freshly declared padded BlockWord prefix. In particular, for L>0 its standalone sign prefix starts with A and has zero S-E on its nonempty A-only prefixes; it cannot be used as a counter to a theorem requiring global original positivity. The ALL-N root-cost theorem in the other mechanism really does retain global original positivity, unlike this relaxed orbit filter. These scopes remain distinct in the registry and next consumer.

## Exact state-level statement (auditor restatement)

For every N>=1,L>=0 there is an EXPLICIT Nat-valued State s=(p_L, list(U)) at clock b=n-L, with0 and current in seen, distinct-set cardinality<=b+1 and all seen values<=b(b+1)/2. The actual Recaman.step/CanSubtract recursion, without discarding any seen value, has sign sequence A^L followed by W^N A over the next L+16N+1 transitions. This is an existence result in the arbitrary-seed State domain, with fully derived novelty and positive blockers. If a seed seen LIST of length exactly b+1 is desired, multiplicities can pad it without changing any decision; this says nothing about a possible chronological prefix ordering, so no such padded list is presented as an actual past trajectory.

The explicit old U is chosen as a function of N and L before the replay; it contains rejection candidates that occur in the later sign proposal. This is legitimate for an arbitrary-state existence proof, because novelty versus ALL future S arrivals has been proved, but it supplies no causality claim for the unseen earlier prefix. A prohibition on using future information in an algorithm cannot itself exclude the existence of such a finite set: canonical reachability is a separate mathematical property that must be proved or used, not inferred from the construction's syntax.

For any proposed universal rejection test that uses ONLY local step decisions, arbitrary fixed L lookbehind, current/zero membership, cardinality, elementary triangular value range and clock/value parity, choose that same L and any N. The supplied s passes every listed test and its continuation contains W^N A. Thus those conditions alone do not exclude the E750 sign family. The conclusion does NOT quantify over tests that inspect full prefix reachability, complete old sign history or original-positive padded BlockWord membership. In particular no statement that EVERY relaxed stock is nonreachable is proved: the predecessor obstruction applies to the first displayed V0 only, while reachability of the strengthened U is UNDETERMINED.

## Table-coverage correction in the independent pass

The claimed complete phase table originally omitted offset15 at height1/residual26. It is now included. This is an A-arrival, not an S-arrival; hence no same-height S-novelty comparison or blocker class changes, and the uniform54(N+1) residual bound already covered it. Finite checks always visited all18 N1 states (including this one). The paper proof now explicitly covers all17 offsets0..16 and the final extra-A state, rather than relying on that computational fact to excuse an incomplete table. No worker rerun was needed or credited.

## Predecessor audit does not overreach the strengthened family

For the strengthened seed current p_L at time b=n-L, its two possible predecessor values would be p_L-b=c_L+1 and p_L+b. The latter EQUALS c_(L-2) when L>=3. Therefore the simple missing-predecessor argument for the original V0 must NOT be applied to the strengthened U. Its absence-of-reachability has not been proved. This exact equality is an auditor control against silently upgrading an unconstructed canonical prefix into a proven impossibility. The ALL-(N,L) local replay and the limited no-go remain valid regardless.

## Exact ALL-N original source classification (stronger support, no new parent success)

This audit now determines ALL original W^N A source sets, not just the four retained witnesses. For a target q=16j+r and an earlier source u=16i+s (0<=s<16), let d=j-i>=0. Sources must have h_s=h_r-1. Since B_(16j+r)=-10j+B_r, the Win area equation is

    (10+16h_s)d = (B_r-r*h_s)-(B_s-s*h_s).

Every possible original source is in one of these phase classes; if d0, require s<r. Source phase keys are: height-3: s9/key18; height-2: s2/key1,s8/key10,s10/key9; height-1: s1/key0,s3/key-1,s7/key3,s11/key-1. There is no height-4 source. The eight A cases are exhaustive:

| target offset r | required source height | target key | denominator | integral nonnegative solutions |
|2|-3|3|-38|none (-15/-38)|
|3|-2|2|-22|none (numerators1,-8,-7)|
|4|-1|0|-6|d0/s1 only|
|9|-4|--|--|no such source height|
|10|-3|19|-38|none (1/-38)|
|11|-2|10|-22|d0/s8 only|
|12|-1|0|-6|d0/s1 only|
|14|-1|3|-6|d0/s7 only|

At the final extra A q=16N, target key0/source height-1 gives only d0/s1 formally, but that would require i=N and hence a source after the target. All other phase fractions are nonintegral or negative. Thus the final A is free. Consequently for EVERY N, the COMPLETE original actual target/source list is precisely copy4->{1},11->{8},12->{1},14->{7}, translated by16j. All four optional A per copy and the final A are genuinely original free, so F_low=F_total=4N+1 EXACTLY, not merely an upper bound. The whole positive-prefix proof in E750 remains unchanged. This strengthens its PAPER support, without changing E750's label or treating the stopped all-N Lean source as accepted.

For the genuine initial-S cut h2, only the FIRST copy's targets4 and12 have exclusively old source1. In all later copies their copy sources are already local>=h. Source0 cannot supply any A here because no A starts at height1. The source equation above excludes any cross-copy old alternative. Hence D_near=2 for ALL N, while free=4N+1 grows. This is a concrete reason the family is not a C1/D<=free counter.

If one explicitly uses the different RAW word A^L W^N A, the old A-only prefix has no actual targets, and its S-E deficit is0 (NOT negative). Possible old sources for W offsets2/3/4/9/10/11/12 and final have lengths1 modulo4 and are excluded; for offset14 the old source length is16j+15 but its source area is6j+4>0. Thus no old A-prefix supply is added. Its raw low-free wallet at level L is L+4N+1 and visits at L are5N+1, error N-L. These facts do not make its initial nonempty A-prefix strictly positive. The numerical seeded replay's unknown earlier stock history is STILL separate from this explicit raw sign history.

The finite worker's field whole_raw_A_prefix_positive=False was a blanket scope annotation, not a measured property. For L0 it would be mathematically true for W^N A, and for L>0 the initial deficit is zero. Original worker output is retained unchanged; this correction must accompany any use of that field. No finite worker rerun or fake fresh holdout was needed.

## Independent exact deficit/target census from the source classification

All prefix source clocks are uniquely represented by16i+s (s<16); the terminal extra A has only earlier copies available. The source-phase table therefore covers all Nat0 alternatives, including cross-copy windows, rather than sampling a lag cutoff. A Win additionally requires a positive length; the only accepted d0 solutions have s<r, while the terminal d0/s1 is excluded by chronology.

For the original raw W^N A, A=8N+1/S=8N/E=4N/F=4N+1. Its within-copy deficits, relative to the copy's starting deficit, at prefix offsets0..16 are

    0,1,2,2,2,1,2,3,4,5,5,5,4,3,4,3,4.

At copyj add4j; the terminal extra A is free and leaves deficit4N. Thus every nonempty prefix is positive by a SECOND explicit argument independent of the earlier F>=2/height<=1 bootstrap. Its raw low wallet and two-level wallet are exactly4N+1 andN+1 respectively; all free phase heights are-2,-1,-3,-2, plus the terminal0. Initial exclusive-old D_near2 does not grow, even though the all-visit error grows by N. This prevents reading numerical replay or original positivity as evidence of a selected-target C1 failure.

## Further independent boundary result: the strengthened U is nonreachable too

The earlier text correctly left U reachability open after finding one permissible predecessor. A SECOND-step audit now proves nonreachability for EVERY N>=1,L>=0; this is an additional PAPER argument, not a finite canonical-orbit search. Here nonreachability concerns the explicitly prescribed seed at time b=n-L, not the validity of its subsequent greedy replay.

For L0, current x is the seed maximum and x±b are absent, as in the simple predecessor argument. For L1/2, p_L-b=c_L+1 is absent, and p_L+b has relative height0/residual-1 (L1) or height-1/residual-1 (L2). Neither matches U (at-1 the only C_W residual is-6N-1<=-7). Cross-height separation excludes other elements;0 cannot match the positive candidates. Thus no predecessor exists.

For L>=3, p_L-b=c_L+1 remains absent. The only possible predecessor is y=p_L+b=c_(L-2), so the last step would have to be S. The current p_L is therefore fresh at that step and the preceding visited set is U without p_L. A further predecessor must have value

    y-(b-1)=p_L+1, or
    y+(b-1)=x-(L-2)n+(L²-5L-2)/2.

The first has the same height as p_L, residual one larger. U's other same-height tail blocker c_(L-1) has residual one SMALLER than p_L, and C_W residuals at these heights are negative, so it is absent. For the second, the same-height tail blocker c_(L-3), when defined, has residual larger by3. C_W comparisons at L3/4/5/6 give respectively height/residual (-1,-4),(-2,-3),(-3,-1),(-4,2); none matches the C_W residual classes (-6N-1),(-4-22j),(-6-38j or-22-38j),(-31-54j). For L>=7 the height<=-5 is outside ALL C_W classes. No other same-height seed element exists. The same uniform n>2R separates every remaining class. Both further predecessor values are therefore absent even from U, a contradiction.

This shows exactly where the unseen earlier history fails, despite arbitrarily many valid greedy steps before W. The fixed-lookbehind no-go remains: for each fixed lookbehind length L_test choose a constructed A-tail L>=L_test; its missing earlier predecessor lies beyond that test. It does NOT produce a canonical Recaman counter. In particular the exact failure is outside the L explicitly realized steps, and increasing L changes the seed/clock, not the canonical orbit. The proof replaces the earlier UNDETERMINED status for this PARTICULAR U family, while preserving that earlier chronological audit as history.

A hand-checkable boundary control uses the frozen discovery pair N2/L3: n12000,x96300,b11997,current60303. The exact U is

    {0,48215,48269,48305,60240,60256,60278,60294,60302,60303,
     72274,72296,72300,84287}.

Its subsequent three greedy A arrive at72301,84300,96300, with old rejected candidates48305,60302,72300. Backward from the prescribed seed, the only possible predecessor is72300. Its own two possible predecessors60304 and84296 are BOTH absent from U. This control illustrates the ALL-(N,L) proof; it is direct exact arithmetic, not a new CPU/holdout result. Notice84296 is a later W S-arrival. Simply adding every missing backward value can therefore spoil the future novelty property; no unproved automatic prefix completion is permitted.
