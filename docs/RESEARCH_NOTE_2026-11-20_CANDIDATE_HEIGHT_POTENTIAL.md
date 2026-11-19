# A bounded candidate band has an explicit sign-height rank

**PROVED-PAPER**, human review pending, NOT Lean-checked. In an actual greedy continuation, a bounded NONNEGATIVE subtraction-candidate band supplies a quantitative monotone rank at ALL sign heights and depths. The rank is internally derived from positive numerical outputs; no rank-progress, original free payment or fixed source type is assumed. It does not prove sign heights bounded, C1 or surjectivity.

## Objects and exact principal statement

Let b:Nat and State s have current x; coherence is not needed here. Let X_t be the actual natural numerical value after t greedy steps of clocks b+1,b+2,..., and let f_t be its actual sign. H_t and B_t are cumulative sign height/area of THIS SAME full continuation, H0=B0=0. Then

    X_t=x+(b+t+1)H_t-B_t,
    c_t=X_t-(b+t+1) (an INTEGER subtraction candidate).

Fix Y:Nat and K=floor(Y/3)+1. At ALL actual A events p whose step clock n_p=b+p+1>=max(1,Y) and0<=c_p<=Y, define

    Phi_Y(p)=K*H_p-floor(c_p/3).

For ANY two such events p<q, Phi_Y(q)>=Phi_Y(p)+1. In fact H_q>=H_p, and equality forces c_q<=c_p-3. No depth, upper excursion, period, source count or word length bound is input. Candidate c may be negative outside the selected band; those events are not silently counted.

## Proposer lemma: a small candidate pays a permanent future sign floor

At any actual A clock p, put n=b+p+1 and y=c_p (an integer). If y<=n+6, then EVERY future H_t>=H_p-1.

Suppose t>p were the FIRST future time at H_p-2, with L=t-p. The first A gives relative height+1; L>=4. All other earlier relative heights are>=-1, and before the final-2 the walk must also pass0 at a different position. Hence the relative area Ar_p(L)>=-L+2: baseline-1 on L-1 positions and-2 at the last, plus2 for the first+1 and1 for the forced0. The exact numerical window identity gives

    X_t=X_p+(b+t+1)(-2)-Ar_p(L)
       =y-n-2L-Ar_p(L)
       <=y-n-L-2<=y-n-6<=0.

But EVERY positive-time greedy output is strictly positive, contradiction. This is kinematic positivity, not a new unproved supplied-count assumption. It also applies when y<=0.

Constant6 cannot be replaced by7. For EVERY n>=2, let b=n-1,y=n+7 and initial State(value=2n+7,seen={0,n+7,2n+7}). Actual greedy signs are ASSS, with outputs3n+7,2n+6,n+4,1. Each S output is positive, distinct and outside the seed (n1 is deliberately excluded). The sign walk reaches-2. Thus the threshold is sharp for this stated arbitrary-State floor lemma.

## Exact candidate/area identity and paid rank

For p<q, write L=q-p, d=H_q-H_p and n_q=b+q+1. Directly subtracting the value equations gives

    sum_(i=p+1..q) [H_i-(H_p-1)] = n_q*d+c_p-c_q.

At a selected event p, y=c_p<=Y<=n_p, so the preceding lemma supplies H_i>=H_p-1 for ALL i>p. The sum on the left is nonnegative and includes the first A contribution2. If d<=-1, the right side is at most-n_q+Y<0 because n_q>n_p>=Y, contradiction. Thus d>=0.

If d0, q cannot be p+1; the first A contribution2 and the DISTINCT endpoint contribution1 show the sum>=3. Therefore c_p-c_q>=3. At equal height, floor(c/3) decreases by>=1. At a higher height, K gained units pay the maximum possible reset of floor(c/3), which is at most K-1. In BOTH cases Phi increases by>=1. This states the load/boundary correction explicitly rather than calling an unweighted quantity monotone without payment.

At a single fixed height this gives at most floor(Y/3)+1 selected events. That count is SHARP for EVERY Y>=0: set m=floor(Y/3), n=Y+2,b=n-1,current2Y+2, and seed{0,current} union {Y-3j:0<=j<=m}. The exact word(AS)^m A has candidatesY,Y-3,...,Y-3m at the SAME H0. Its S outputs are current-1,current-2,...,current-m, all positive/distinct, above every seeded blocker and below current. Each A is forced by its seed (or the last0 candidate). For Y6, candidates6/3/0 at H0 have Phi -2/-1/0.

## Independent all-time fresh-value wallet (stronger small-y count)

Fix a numeric candidate y:Nat and sign height k, and order M>=1 A events with c_p=y,H_p=k, without a late-clock restriction. For every consecutive pair p<q the same identity gives mean height k-1 on the bridge. Since the first A rises to k+1, some intermediate height must be BELOW k-1 (otherwise the mean is larger). Let v be the FIRST S landing at k-1. The area relative to k-1 accumulated before v is>=3 (first2, a later1, final0). Hence

    X_v=y-sum_(i=p+1..v)[H_i-(k-1)] <=y-3.

This is a positive fresh S output, so X_v belongs to{1,...,y-3}. These bridge intervals are disjoint and all S outputs are globally fresh against the ENTIRE old stock, so they give distinct values in that finite wallet, also avoiding whatever was seen at the first event. Therefore

    M-1<=max(y-3,0),  M<=max(1,y-2).

If y0/1/2/3, the wallet is empty and M<=1. The proof keeps the first event as the explicit boundary term and never reuses a numeric output as an original free A. This all-time bound uses S freshness, whereas the later clock-band rank needed only numerical positivity.

## Recurrence and fixed-original-source consumers

For a fixed y, after its clock threshold any later use of the SAME candidate has STRICTLY HIGHER H. Indeed if d<=0, the candidate/area identity has nonpositive RHS while the proved future floor and first A give positive LHS. Thus if a fixed y recurs infinitely, its sign heights tend to+infinity. More generally the band rank shows that infinitely many selected nonnegative candidates in[0,Y] force H->+infinity along those events: heights are nondecreasing and each height allows at most K events. This is a necessary condition, not a proof that recurrence is impossible.

A fixed literal original P2/Win source u has fixed y=X_u and hit height H_u+1; its original window identity gives c_p=y at every hit. Hence it can supply at most ONE A after n_p>=max(1,y), and at most max(1,y-2) A in all time by the fresh wallet. Every finite original source prefix therefore supplies only finitely many A overall. After the maximum of its source values, at most one later target per distinct(y,H_u) pair remains (at most one per original source is a weaker bound). This is an explicit cardinality bound, NOT a computable final-use clock and NOT a bound on all old NUMERICAL blockers: the same number may block non-P2 A at DIFFERENT sign heights, exactly the distinction in E111.

For reference, all H_t>=-floor(x/(b+1)): at a running global minimum m attained at r, B_r>=r*m and X_r<=x+(b+1)m; natural nonnegativity gives that lower bound. This supports finite-strip counts but is not needed to assume H globally bounded. No arbitrary old sign prefix is erased.

## Quantified original-source clock consumer

This is a corollary of the SAME floor and common-source span, not a second independent progress claim. Fix one unchanged original Win source u, put a=b+u and y=X_u, and list ALL its M A hits in a finite continuation. If M>=2, EVERY nonfinal hit at step-clock n_i satisfies n_i<=y-7: otherwise y<=n_i+6 supplies the permanent floor, and the candidate/area identity excludes the later equal-y/equal-height hit. The first source window has mass1/area0, hence odd length>=3 (length1 has area+1), so n_1>=a+4.

Apply the E760 span bound to the first M-1 hits, set k=M-2, and retain the last hit as the explicit boundary. Then

    10k-2*(k mod2) <= y-a-11.

In particular y<a+11 forces M<=1; otherwise M<=2+floor((y-a-9)/10). The parity-sensitive inequality is the principal bound; its simpler floor consequence is deliberately conservative, with NO claim of sharp attainment. Every nonfinal use is paid by a clock below y-6, while the last use is the one boundary correction. For a finite original source prefix, summing these finite capacities gives an upper bound on its union of supplied A; co-supplied targets may be overcounted, never undercounted or silently deleted. The upper bound depends on source VALUE and CLOCK, not a depth-independent constant per source and not original free. No explicit final-use clock follows, because the last use can be arbitrarily late in this argument.

The stronger threshold max(1,y-6) is valid for a fixed-height/same-candidate capacity; the earlier principal band rank intentionally uses the conservative n>=max(1,Y), which is needed in its proof of NONDECREASING heights across DIFFERENT candidates. These thresholds must not be swapped. The all-time fresh-wallet and this clock-capacity proof are distinct supporting bounds on the same source family, not two allocations of the same free.

## Falsifier, old controls and evidence scope

Frozen threshold family discovery n2/3 and unused parameter controls17/29 passed actual full-stock replay. The sharp count family tested Y0..7 plus10/17/50, with every S fresh. A separate canonical500-step trace and the OLD sqrt6 counter are regression controls for NEW predicates, not fresh orbit data or general proof. The old counter has candidate10 at local0/21, with H0/1, so it satisfies the new late-height increase while still refuting its OLD square-root-six claim. No stopped use-gap method is reopened and no stronger clock-gap estimate is inferred. All724 regression steps satisfied the stated floor, capacity and candidate-decrease predicates.

Source/argv/hash/cap/CPU evidence is in[data protocol](data/depth_general_20261120/CANDIDATE_HEIGHT_PROTOCOL.json). Finite checks are COMPUTED; all-parameter claims rest on the proofs above and remain PAPER/human-review-pending. The current512MB vacuity helper STOP is not bypassed by default build; no new Lean module is adopted.

## Remaining C1 obligation

The paid rank uses bounded numerical candidates and sign height of actual updates. Abstract C1's original LOW-free wallet is a different object, and its arbitrary raw sign-positive histories do not supply these numerical hypotheses. H is not proved bounded, candidate bands are not shown to cover all relevant A, and general C1/Q/H/SL/surjectivity remain open. The new principle gives a real monotone quantity at arbitrary depth and finite original-source consumption; those limits must accompany every consumer.

### Separate across-height predicate audit

The first finite worker checked the future floor, per-height drop and equal-candidate ascent, but did not explicitly evaluate the principal Phi across DIFFERENT candidates. The separated auditor froze a new predicate on the19 hashed existing traces/Y0..100: full greedy replay checked independently,4292 selected events/3811 rank comparisons PASS. Source-capacity checks independently tested1268 steps/200 source-target pairs/7 repeated sources;103 positive blocked additions without P2 were kept outside the source claim. These are COMPUTED regression checks of NEW predicates on existing histories, not fresh orbit data or the all-parameter PAPER proof. See RANK_PREDICATE_PROTOCOL.json / SOURCE_CAPACITY_PROTOCOL.json and raw receipts.

## Endpoint consumer and a proved eligibility boundary

For any horizon Q, the selected-event count is<=K*(H_Q+floor(x/(b+1))+2): the internally supplied future floor bounds every selected height above by H_Q+1, and initial numerical positivity bounds it below. No global H ceiling is assumed for this finite-horizon inequality. The complete proof and exact all-T State transport preserving the original word ledger but making EVERY candidate>clock (hence no eligible event for ANY Y) are in [numeric-band transport](RESEARCH_NOTE_2026-11-20_NUMERIC_BAND_TRANSLATION.md). This identifies band/lateness coverage as a real unpaid canonical/provenance obligation, not a free assumption.
