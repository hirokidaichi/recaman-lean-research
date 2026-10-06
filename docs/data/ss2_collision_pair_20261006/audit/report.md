# Independent final audit: H-20261006-01

**PASS for the finite COMPUTED result and the auxiliary PROVED-PAPER geometry. The local Hall target remains CONJECTURED and the attempted capacity route is correctly STOPPED.** No blocking defect or mathematical repair is requested. No Lean theorem was implemented or audited in this unit.

Reviewer: /root/issue81_auditor, separate explicitly authorized session. Date: 2026-10-06 JST. Reviewed base ba7fe41e3c96d0762198731d658b10dbfd9f53d1 in the p2-terminal-tail-bound worktree. Repository access was read only; auditor artifacts are in this /tmp directory. Divergent primary main and its dirty files were not used.

## Source and target audit

Frozen C++ SHA256 is 184f9c96d9f9c24d4b4a009e555adbd6c6a66b401e42eb351efc22e8ef9343b4, matching protocol-frozen.md. The Python verifier hash is d016fff233909a2cea0e678c95ccd73d5da9e15ed990227cea2edbe50e427263. Discovery hash is e2d9c27a731cb15040cd7a72fdc312798e4591caaa8dbba5cb5ff9f6fcdae40b; holdout is 3e2b1df919d4010d920aed4c70c74ca086e0cc53006d2f6ff0701bcea8e94367. The reviewed Sol report hash is 70fb50c4fbe8e3e13c03f6963f2e607f28701689e82c60707ec5534c59e44571.

The exact target is all positive periods and positive-mass periodic histories, specified current-A lowSS windows at distinct phases L, plus two phase-distinct/current-A minimal SS2 windows outside L with equal true-oldest phase. It asks |N(L union {v,w})| >= |L|+2, with actual original-window neighborhoods. The source does not assume Hall, NoSAAS, an owner map, orbit realization, or lag<p.

Donor minimum means first positive P2 among ALL P2 windows, not first window having SS2. Thus there is a unique donor lag at a given phase. For any arbitrarily specified lowSS P2 window d, its least positive P2 prefix d0<=d has SS<=1 and N(d0) subset N(d). This proves the minimum-window reduction for all lowSS lag assignments simultaneously, even when the original witnesses are nonminimal or A-ended. The code's disjoint low/two classification does not remove a legitimate selected member.

Positive mass is retained in the target and makes the lag search exhaustive. It is not needed for the auxiliary geometry; no zero/negative-mass finite claim is inferred using the positive-mass termination formula.

## Exhaustive algorithm audit

For a phase t, let M and Q be backward mass and moment of one period, and m_r,Q_r of its first r signs. For d=kp+r, 0<=r<p, summing the k whole blocks gives mass kM+m_r and moment kQ+pM*k(k-1)/2; the remaining block contributes kp*m_r+Q_r. M>0 uniquely determines k=(1-m_r)/M when integral and nonnegative. The source checks every residue r and takes the least positive zero-moment candidate. This covers every possible P2 lag. Since m_r>=-r, k<=p and d<p(p+1). No heuristic cutoff or floating arithmetic enters.

At p<=22 the signed accumulators and shifts are in range; moment products are widened to long long. Mass zero is excluded before division. r=0 and the no-P2 case are handled correctly.

Rotation canonicalization visits every word of positive mass modulo rotation, retains imprimitive words, and weights a representative by its actual orbit size. The first repetition is the orbit size; a noncanonical rotation must occur before repetition. Current phases are all inspected, so donor ordering and phase relabeling are retained. The all-labelled-word counts independently match binomial sums.

SS counts overlapping pairs only inside the newest-first window; oldest is its final S's one-based offset, then reduced modulo p. Neighbor masks deduplicate the actual S phases over the whole window, including repeated periods. The code checks every same-oldest donor pair and all 2^|low| subsets, including empty L. The subset-union recurrence removes the least set bit and adds precisely that member's mask. No larger-L-only or global-D-only surrogate is substituted. Asserts for terminal tails/group size abort on a violation; they do not silently filter cases.

## Independent recount and replay

I implemented independent.cpp using direct one-sign-at-a-time mass/moment accumulation, independent bit-built rotations, and an independent per-subset union loop. It does NOT use the quotient formula or the parent's subset recurrence. It can stop a phase once SS>2 because SS is prefix-monotone: neither a lowSS first P2 nor an SS2 first P2 can occur after that point. Otherwise it searches the proved safe p(p+1) bound. This is the same frozen p=1..22 domain, not a new search range.

All 22 period summaries agree exactly in all 10 compared fields (including lowSS/SS2 phase counts, wrapping donors, collision groups, pairs, subsets and minimum slack). Counts:

- 178,373 rotation representatives; 3,716,111 phase-labelled positive-mass words.
- 16,108 minimal SS2 phases among representatives, including 954 with lag>=p.
- 24 same-oldest donor pairs in those representatives; 86 pair/subset tests.
- Discovery p1..18: 3 pairs / 10 subsets. Holdout p19..22: 21 / 76.
- No local Hall violation; observed minimum slack is 3, not a universal slack theorem.

The pair and subset counts are on word representatives; do not call them millions of nonvacuous collision tests, or necessarily canonical pair-orbit counts. The 2,613 direct phase checks in the original code can include repeated checks of a word having several pairs.

The original Python certificate verifier replayed all 16 emitted record witnesses successfully. It independently checks window words, actual current-A signs, first-P2 minimality, SS2/lowSS, sigma, tails and exact neighbor masks. I also reran Sol's existing boundary replay; output matches byte for byte. The independent aggregate replay is stronger than checking emitted minimum-slack records alone.

The E133 control is genuine: forward AAAASAASASASASSS has p16/mass2; current3/lag11 yields AAASSSASASA (proper mass-one prefix moments 1,-3,-2,-1); current12/lag19 yields SASASAASAAAASSSASAS (proper mass-one prefix moments 10,11,2,1). Both are minimal/current-A/SS2, share sigma9, and have terminal-A 1/0. The latter wraps the period and covers all D. This falsifies oldest injectivity, not the requested Hall inequality.

## Auxiliary paper proof audit

**PASS as PROVED-PAPER for the following necessary geometry only.** Existing E363 and full-endpoint modular injectivity show each common-oldest group has at most two phase-distinct donors: equal maximal terminal-A length gives equal full endpoint phase and hence equal current phase. The two-donor collision must therefore have tails 1 and 0. Minimality is used to obtain that tail bound. No positive period mass is needed for this argument.

Periodically shift one actual window to align its oldest S to the same integer s, retaining signs, minimality and SS. Let the A-ended donor have clock t_A, length d, word W_A=C A, and the S-ended donor have clock t_S, length f, word W_S. Then C ends S, has SS2, mass0 and moment -d. Distinct phases imply distinct lifted clocks.

If t_A>t_S, the shared history gives W_A=X W_S A, with nonempty X ending at the actual current A of t_S. The SS2 budget of W_S exhausts the SS2 budget of W_A, so X is SS-free. Mass forces mass(X)=-1. Every SS-free word ending A has mass>=0, by pairing each S with its immediately following A. Contradiction. Thus t_A<t_S.

For k=t_S-t_A>0 the actual split is W_S=X C, with |X|=k, final A at t_A, and ss(X)=0. Append mass gives mass(X)=1; append moment and mass(C)=0 give moment(X)=d. Length gives f=k+d-1. Both P2 lengths are 3 modulo4, so k=1 modulo4.

For SS-free mass-one X ending A: if X starts A, its r S letters are isolated between exactly r+1 A letters, hence X=(AS)^r A and moment r+1=d. If X starts S, each S is followed by a nonempty A run; exactly one run has the one extra A. Thus X=(SA)^j A (SA)^h with j>=1,h>=0, k=2(j+h)+1 and moment=j+(2j+1)+h=3j+h+1=d. The stated congruences j+h even and 3j+h=2 modulo4 follow. The earlier erroneous 'both j,h odd' restriction is absent from the final argument. This is a necessary classification, not a converse claiming every parameter yields donor windows.

The classification overlaps E145; it should not be registered as an independent new allocation theorem. Current-A and same-history alignment are essential in the chronology proof. Without deriving terminal0/1, this exact statement has not been established for arbitrary nonminimal donors.

## Limits and decision

The geometry does not produce the missing second S or control all lowSS endpoints in the shared core. E368 only gives an injective lowSS image F and one extra sigma, hence |N|>=|L|+1. Requiring a further S specifically inside the two donor neighborhoods while holding F fixed is a stronger sufficient method; the original |N| target permits lowSS rematching. No such extra phase or independent transition rule is proved here.

The README and final intended labels are appropriately restrained: finite computation COMPUTED; auxiliary chronology/necessary geometry PROVED-PAPER; original all-period local Hall CONJECTURED; this capacity route STOPPED. General Hall, multiple collision groups, SS>=3, E070, E067, and surjectivity remain unaffected. No source axiom audit or Lean rebuild is required because no Lean proof source changed in this unit.

Reopen only with a separately falsifiable endpoint/core interaction that advances beyond F union {sigma}; a larger census or assumed augmenting-path condition is not that input. No repository or GitHub changes were made by this auditor.
