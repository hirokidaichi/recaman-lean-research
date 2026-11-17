# M4 / low free3: last-minimum return and source-visit accounting

後続の夜調査でM5/low free<=4も全深さ・全上昇幅で排除した（[E735紙上証明](RESEARCH_NOTE_2026-11-17_POST_RETURN_HIGH_FREE.md)、全体未Lean・人間レビュー未）。以下はこのノート作成時点の証拠と停止記録を保持する。

結論：**M=4・low free<=3を満たす元履歴は存在しない**。前史の深さ・上昇幅・長さ・run数を制限せず、必要な四つの供給元を置けないことを紙上で示した。以下の強い訪問数上界を **PROVED-PAPER（E-729、未Lean・人間レビュー未）** とする。初稿のCONJECTUREDから、反証passと[別の意味監査](data/pc4_source_order_20261117/SEMANTIC_AUDIT.md)を経て判定した。一般のM<=F_lowやC1は未証明。

## Objects and precise target

Use the original0 sign history throughout. H(k)=sum(i<k)sign(f(i)); B(k)=sum(1<=i<=k)H(i). EndN0(q) means f(q)=A and some u<q has H(q)=H(u)+1 and B(q)-B(u)-(q-u)H(u)=0. A free clock is f(q)=A and not EndN0(q).

Let h>=1, T>=h, initial h signs S, H(T)=2-h, and every nonempty prefix through T satisfy actual supplied+1<=S. Write

    F_low(T) = #{q<T : free(q), H(q)<=1-h}.

The stronger proved-paper conclusion used here is:

    F_low(T)<=3  =>  #{q<T : H(q)=-h-2} <= F_low(T) <= 3.

It bounds **all visits**, including S clocks, free A and actual A, not only selected supply sources. In the PC4 parent, the first source family needs four distinct such clocks, so this conclusion excludes every order of both source families without imposing a chronological order on their keys. The parent pattern is Z^4 A with Z=ASSSSAAA, each plateau A actual, all five boundary-source sets {h-1}, and positive prefixes through T+33. E728/PIVOT supplies the four original prehistory clocks. Standard Recaman orbit reachability is not claimed.

## A. Derive a floor from the low-free budget

**Claim A.** Under the hypotheses just given and F_low(T)<=3,

    min_{0<=k<=T} H(k) >= -h-4.

Assume instead that the global minimum m<=-h-5. Let v be its last occurrence in[0,T]. Since H(T)=2-h>=m+7, v<T. Recovery from m through m+2 produces two distinct original free A at heights m and m+1, both in[v,T). This uses original0 floor exclusion: below the global minimum there is no source; at height m+1, a possible source has height m but its whole window area is nonnegative and its final summand is positive. No prefix is removed.

The first two A in an initial-S^h history are always original free, at heights<=-h and<=1-h. Indeed, the first has no earlier A; before the second only one A exists, and the only possible mass1 window is a single A with nonzero area. If two A occurred before v, these two low free together with the two recovery free would give four distinct low free. Consequently at most one A occurs before v.

Let R be the first clock after v with H(R)=2-h. It exists and R<=T. Every A in[v,R) starts at height<=1-h by first return. The possible single A before v also starts at height<=-h. Thus **every A before R is low**, and in particular

    original total free on[0,R) = F_low(R) <= F_low(T) <= 3.

This equality is asserted only at this proved prefix, not on all[0,T]. The parent positive-prefix condition restricts to R. Apply the existing checked theorem
`Recaman.BlockOldRay.positive_r3_additions_free_bound` with n=0, a=0, w=[], B=R:

    A(0,R) <= 2*free(0,R)+1 <= 7.

Its empty BlockWord and prefix equality are valid (`BlockWord.nil` and seg(f,0,0)=[]). There is no fresh r3 enumeration or stopped-job restart.

But H(R)-H(v)=2-h-m>=7, hence at least seven A occur in[v,R). The bound A(0,R)<=7 forces equality everywhere: m=-h-5, no A before v, exactly seven A and no S between v and R. Therefore the exact prefix is

    S^(h+5) A^7.

Among a consecutive A run following only S, the only supplied A is the third. For the A with a earlier A in that run, a source inside the run has a length1 A window with area1. A source in the initial S segment requires exactly a-1 remaining S (mass1); the area of S^(a-1) A^a is a*(2-a), zero only at a=2 among admissible a>=1. Thus the seven A have six original free. All seven begin at heights from -h-5 through1-h and lie before R, contradicting F_low(T)<=3. This proves Claim A.

## B. Pay every visit two levels above an original floor

**Claim B.** For any original sign history, integer m and T, assume H(k)>=m for every0<=k<=T and H(T)>m+2. Set c=m+2. Then

    #{q<T:H(q)=c} <= #{q<T:free(q), H(q)<=c}.

There is no positive-deficit assumption and no upper-height bound in this claim. Partition all visits at c into three disjoint classes.

1. **Free A visits.** Pay each with itself, at height c.
2. **Actual A visits.** Existing `Recaman.FloorSupplyFreeBudget.actual_floor_supply_count`, specialized to n=0, a=0, empty BlockWord and K=T, bounds their count by original free at height m. Its stronger injection theorem supplies distinct earlier floor free; all source alternatives are already covered by actual EndN0. This does not charge every source separately.
3. **S visits.** After such a clock q the height is c-1. Before the endpoint above c there is a first return r(q)>q to height c. Its immediately preceding clock r(q)-1 is A at c-1=m+1, hence original free by floor exclusion. It is <T. If q<q' are two S visits, the first return from q is no later than q', so r(q)-1<q'<=r(q')-1. These images are distinct.

The three wallets have heights c, m, and m+1, respectively, so they are disjoint. Adding the three injections/count bounds proves Claim B. The first descending visit, an S visit followed by a long high excursion, and the last S visit are included. The terminal-height condition guarantees that the last payment exists inside[0,T); without it the word S at T1/m-2 has one c0 visit and no free.

## C. Apply A and B to the source question

Claim A supplies the global floor m0=-h-4; it need not be attained. Claim B at m0 has c=-h-2 and H(T)=2-h>c. Its free wallet is contained in F_low(T), because c=-h-2<=1-h. Hence every such history with F_low(T)<=3 has at most three original clocks of height -h-2 before T.

In the PC4 domain, boundary source h-1 implies H(T)=2-h. The four offset5 A clocks T+8j+5 have source height -h-2. No source is inside the plateau (whose heights are all>=-h-1), and their four different area keys24j+15 prohibit reusing a source clock. This yields four distinct visits before T, contradicting C. The second source family cannot repair the contradiction. The proof retains all original history, free tags and possible sources and does not require standard orbit realization.

The same conclusion rules out F_low<=3 for every supplied PC plateau with M>=4, but does **not** prove M<=F_low for M>=5/F_low>=4. This is a fixed-free-budget result. An internally derived floor is not an imposed search ceiling; nevertheless it does not establish a uniform arbitrary-rank charging law or C1.

Independently of Claim A's free3 condition, Claim B also pays M<=F_low for every M when the whole prehistory has floor>=-h-4. Thus an unrestricted parent counter must have M>=5, F_low>=4 and some height<=-h-5. This is a corollary of the same proof, not a new experiment or an arbitrary-depth assumption.

## Falsification evidence and audit

New structural probes are frozen in `data/pc4_source_order_20261117/PROTOCOL.json`. Discovery reuses the small length12 prefix space and is not fresh holdout:4096 words,2636 eligible A cases,99 last-minimum interfaces,64364 B cases; no violation. Frozen structured holdout:84 words,114 A cases,13371 B cases; no violation. **Its last-minimum-interface population is0**, so it supplies no independent evidence for that interface. These computations are not the proof above and do not justify larger searches. The finite probe method is STOPPED after its planned jobs.

Counterfactual high-free control: S^h A^r S^(r-2), h>=2/r>=3, has positive original prefixes and ends at2-h with only two low free but r-1 total free and unbounded upper height. The count identities also hold for h1, but that subcase fails the positive-prefix condition and is not the positive control. Replacing the whole-history low budget by a total-free budget would be invalid. The audited proof uses only the first return R after v. The separate semantic pass checked source provenance, the exact old theorem signatures, the return taken after v rather than on the initial descent, and disjointness of all three payment classes. The independent forward-area checker passed10 fixed cases and saved full source tables/payment maps. Two targeted S^(h+2) A^(r+4) S^r controls exercise a genuine last-minimum interface and arbitrarily extensible high free; they are verification, not a repaired holdout. No mathematical/resource-capped job was retried and no conjecture repair was needed.

## Handoff and next decision

The requested PC4 existence question is settled negatively on paper. The hypothesis card is PROVED-PAPER for nonexistence; the all-M parent stays CONJECTURED. The strongest evidence is the A->B->C argument using the existing checked original rank/floor theorems, not finite absence. There are no Lean changes or new kernel-checked theorems. Original0 sources/free and prefix positivity are retained throughout.

Changed files are the PC4 card, this note, E729 registry/frontier/proof-map/portfolio entries, the parent-card follow-up and the new reproducible packet. Guard fixtures, probe discovery/holdout and independent audit commands with exact argv/resources/hashes and raw outputs are in the packet. Publication/validation receipts are separate from research time. The unrelated11/07 daily journal is preserved.

The next unresolved smallest cost case is M5/low free4. The present rank-three input cannot simply be renamed rank-four. A next bounded question would need a new proof that a low-free4 history controls its first-return prefix or its source visits; it does not authorize restarting stopped r4 tables, the old SMT model, or source-order generators. No further M4 range expansion is warranted. Local progress is complete PC4 exclusion; a fixed-free-budget argument does not supply a uniform arbitrary-rank charge or reset the daily depth-general tracker.
