# M5 / low free4: original chronology before the last minimum

結論：**M=5・low free<=4の実現可否は未決着**。反例は得られず、不存在も証明していない。ただし深さ・上昇幅・長さを制限せず、候補が満たすべき次の条件を紙上で得た（**E-730 PROVED-PAPER、未Lean・人間レビュー未**）。

1. 最後のglobal minimum以前のAは高々3個。
2. その最小値から最初にH=2-hへ戻る元prefixでは、総freeも高々4個。
3. 必要な二つの供給元族は、それぞれ5対象のうち少なくとも4対象について、**全供給元が最後の最小値より後**にある。元履歴や代替sourceは削除していない。

これで「高い前史に多数のA/freeを蓄え、最後に深く下がって必要sourceを準備する」候補を除いた。残るのは、最小値以前のAが0〜3個で、その後に両族の大半を同時に準備する場合。固定free予算の必要条件であり、一般Mの費用不等式やC1の解決ではない。

## Exact original domain and dependencies

Use the original0 history throughout. For f:Nat->Bool, A=true and S=false, let H(k)=sum(i<k)sign(f(i)) and B(k)=sum(1<=i<=k)H(i). An original source u for an A at q satisfies

    0<=u<q, H(q)=H(u)+1,
    B(q)-B(u)-(q-u)H(u)=0.

EndN0(q) requires f(q)=A and at least one such source; free(q) requires A and no such source. Let h>=1, T>=h, initial h signs S, and H(T)=2-h. Set

    F_low(T) = #{q<T: free(q), H(q)<=1-h}.

The chronology theorem below needs F_low(T)<=4 and m=min(H[0,T])<=-h-5. It does **not** need positive prefixes. In the PC5 parent, those hypotheses are derived: E729 excludes low free<=3, and E729's floor+2 all-visit accounting excludes floor>=-h-4 when five distinct first-family sources are needed. Hence a PC5 counter has F_low(T)=4 and m<=-h-5.

The full parent retains original positive prefixes through L=T+41, f[T,L)=Z^5 A, Z=ASSSSAAA, every plateau A actual, and each boundary T+8j's complete source set exactly{h-1}. The boundary gives H(T)=2-h. E728/PIVOT provides the first source family at c=-h-2, with five distinct normalized keys24j+15, and the second at c+1 with keys16j+11. All these sources are before T; no possible source is removed. The standard Recaman orbit is not asserted to realize this abstract history domain.

Inputs are the first-four-A and three-low-free recovery arguments of E728, the original floor exclusion/recovery in `BlockSuffixPositivity`, and the source-spacing argument of E728. E729 supplies only the parent's necessary deep visit, not a free4 rank theorem. The stopped old r4 table/SMT/generators are not used as mathematical inputs or restarted. In particular the known A10/free4 tail counter is a **padded-old-prefix** example, not a global initial-S/free4 counter; it blocks a blind general rank-bound substitution but does not itself refute a new theorem restricted to this original domain.

## A. At most three A before the last global minimum

Let v be the last clock attaining m on[0,T]. Since H(T)=2-h>=m+7, v<T. There are two distinct original free A at heights m and m+1 in[v,T): the first upcrossings from those levels after v. The source for a floor A would be below the global floor; a source for a floor+1 A would be at the floor and its window has nonnegative relative heights with positive final summand. This accounts for sources before v too. Both free are low, so there are at most two low free before v.

Suppose at least four A occurred before v. The globally first two A are original low free. The first-four facts of E728 then imply:

- The third A cannot be free, because a free third A is low. Thus it is actual, and the first three A are consecutive.
- The fourth A is free. Since the two pre-v low-free slots are used, its height is>1-h. At that clock only three A precede it, so the number of preceding S is<=h+1. Consequently the whole history up to that clock has floor ell=-h-1.

There is no A at height<ell between the fourth A and v. Otherwise take the first such A at q<v. After the first descent below ell there has been no A below ell to return upward, so the descent up to q is monotone; q is a new strict global minimum. It is therefore an original low free, the third one before v, a contradiction. Before the fourth A the whole floor was already>=ell, so in fact no A below ell occurs anywhere before v.

Because m<=ell-4, let t be the last visit to ell before v. The following two facts now hold:

    H(k)>=ell for every k<=t;
    f[t,v) is all S, and v-t=ell-m>=4.

For the first fact, an earlier visit below ell followed by a return to ell would require an A below ell before v, which was just excluded. The second follows because any A during this final descent would also be below ell. The clock t is after the fourth A, whose height is above ell. Thus the globally first two free A are before t.

Let b be the first return to ell after v. It exists before T because H(T)=ell+3. Consider the comparison word g(i)=f(t+i), only for0<=i<b-t. **This is not a replacement of the original history or an assumed BlockWord at t.** For every A at q in[t,b), H(q)<=ell-1. Each possible original source must have height H(q)-1<=ell-2, whereas every clock before t has height>=ell. Therefore every original source lies in[t,q). Translation is a bijection of complete source sets:

    Sources_f(q) = {t+u : u in Sources_g(q-t)}.

Indeed, the mass condition is invariant under translation, and summing H(t+i)-H(t) cancels the constant H(t) in the relative-area condition. Thus original actual/free tags for these A are exactly preserved in both directions. No positive-prefix or new-old-word assumption is transported or needed.

The comparison g begins with at least four S, visits height<=-4 relative to t, and returns to0 at b-t. Apply E728's three-low-free recovery statement with initial parameter h'=2: its initial two S, deep visit<=-h'-2=-4 and endpoint>=2-h'=0 are supplied. It yields at least three free in g at heights<=-1. By the full-source equality, these are three **original** low free in[t,b), at heights<=ell-1<=1-h. Together with the globally first two free before t they give at least five distinct low free before T, a contradiction.

This proves A[0,v)<=3. The two original recovery free used at the beginning are **not added again** to the final count: the contradiction is two before t plus three in[t,b), not2+2+3. Depth and all upper excursions were unrestricted; the monotone descent and local floor used at t were derived under the contradictory case.

## B. A genuine original prefix with total free at most four

Let R be the first visit to2-h after v, so v<R<=T. Every A in[v,R) is at height<=1-h. Before v there are at most three A. The first two are low free; if the third is free it is also low by E728. If the third is actual it may be high, but contributes no free. Therefore every original free before R is low, and

    #{q<R: original free(q)} = F_low(R) <= F_low(T) <=4.

This is a statement about the original prefix[0,R), with all original sources. It does not assert that every A before R is low. The parent's positive-prefix condition restricts to this prefix, but there is no available proved free4 analogue of the rank-three bound used in M4. Nor can this equality be extended from R to T: arbitrarily many high free may occur later. B is a new necessary interface, not a completed rank-four proof.

## C. At least four targets of each source family are entirely after v

Take two original sources at the same height belonging to different target keys of the first family. The bridge between them has net mass0, length2r and relative area a nonzero multiple of24. Any such bridge satisfies |area|<=r^2 and area congruent to r modulo2. Thus r is even and r>=6. At least six A occur between those source clocks. For the second family's nonzero multiples of16, the same argument gives r>=4, hence at least four A.

Both endpoints cannot be before v, because A[0,v)<=3. Consequently at most one of the first family's five targets has **any** pre-v source, and at most one of the second family's five targets has any pre-v source. At least four targets in each family have all their sources in(v,T). A source cannot equal v because its height is c or c+1, both above m. Selecting one source for each of these eight targets gives eight distinct clocks after v, but the result does not discard alternative sources.

This is not a claim that there are at most two source clocks before v: one target may have several old sources. It is not an ordering of the target indices by source time. It does not yet show that the eight forced later source sets cannot coexist. The exact area keys, the parent's full boundary uniqueness and the original free4 budget remain simultaneous unresolved constraints.

## Falsification and independent finite verification

The new run-family protocol and hashes were frozen before execution in[data/pc5_source_order_20261117](data/pc5_source_order_20261117/PROTOCOL.md). It tests arbitrary source alternatives on each original history, large upper A reservoirs followed by deep descent, and prehistories with two or three separated A. Its finite ranges are not imposed on the theorem or parent.

- Discovery:24,960 positive histories; frozen same-family holdout:4,136 positive histories. No auxiliary or parent counterexample. **Both jobs have0 histories with low free<=4**. They do not test the target conditional population and do not establish the chronology theorem or source nonexistence. Best low-free counts in the chosen d5/7 discovery subfamilies are5/7, and in d6/10 holdout subfamilies8/12. These are family minima only.
- The finite family is STOPPED after its two planned jobs. No range/resource extension follows finite absence. Original all-source tables for all A in the four best records are preserved.
- A separate reverse literal mass/weighted-area verifier, without importing the discovery evaluator, passed11 fixed cases. It agrees on all sources of the four saved records. Targeted controls verify the guarded complete-source translation and show its failure if the old-floor condition is dropped. They are verification, not repaired holdout.
- The concrete original prefix `SS AA SSS AAA`, h2/T10, has positive prefixes, endpoint0, low free4 and two A before its last minimum. Thus simply extending M4's **unqualified** at-most-one-A conclusion to low free4 is false. Its minimum is-3, so it does not refute the deep chronology statement above. This control is not a PC5 parent counterexample.
- The existing high-free control S^h A^r S^(r-2), h>=2/r>=3, has low free2 and total free r-1. Its two finite instances were checked. The old SAAA/S4A4 control loses original source0 for target11 when reset at cut4; it demonstrates why a source-preserving comparison must be proved, not assumed.

All guard commands, exact argv, source/input hashes, raw output and CPU/wall receipts are in the packet. The guarded workers are one cooperative Python process with no descendants; they are not described as a general process-tree security sandbox. Guards passed, mathematical and verifier jobs passed first time; no retry/repair. New mathematics remains PROVED-PAPER or COMPUTED as stated. No Lean file was changed or new kernel theorem claimed.

## Handoff and next decision

H-PC5 and auxiliary all-visit bound A remain CONJECTURED; mechanism B and the above necessary consequences are PROVED-PAPER, with the separate semantic audit in the packet. The bounded unit accepts a strict new source/free condition; it has not answered PC5 existence. The unsuccessful finite-family method is STOPPED. The chain source height exclusion -> exact source translation -> three-free recovery -> pre-minimum A<=3 -> two-family chronology is complete on paper, but not Lean-checked or human-reviewed.

Changed files: this note, PC5 card, registry/frontier/proof-map/portfolio and parent-card follow-up, and the new reproducible packet. Validation and publication are recorded separately from research time. The unrelated11/07 journal is preserved. The initial15-minute gate found the strict chronological edge; no finite-absence continuation was used. The25-minute different-mechanism reservation concerns the exact old-source transport argument, not a nominal completed100-minute daily run; actual elapsed work and unused reservation are recorded honestly in RESULT.json.

The next bounded question is whether, with at most three A before v and original total free<=4 at the first return R, the four forced post-v targets of each family can have their exact24/16-spaced source keys simultaneously. Keep both families, the original history and all sources. A new inequality paying these post-v source requirements, or an exact source-compatible counterexample, would change the frontier; another larger run-family enumeration or a numeral change in the old r3 theorem would not. Do not restart the stopped r4 table, SMT or loaders merely because this necessary condition was found.

Local progress is the strict chronology reduction. The source-transport equality is an elementary height-exclusion step within a fixed-free-budget proof, not a uniform arbitrary-rank payment or an unrestricted depth operation. General M<=F_low, C1 and the daily depth-general stagnation count remain unchanged.
