# Audit of the remaining PAPER interfaces,2026-11-17 evening

These interfaces are not upgraded to Lean by successful downstream builds. This pass checks the precise upstream statements against the original M5 application. Same-agent auditor role; human review pending.

## E729 floor-visit payment

The required input is Claim B of FOUR_PERIOD_SOURCE_ORDER, not its stronger low3 hypothesis. Claim B applies to ANY original floor m0 through T and an endpoint above m0+2. At source level c=m0+2, every free A visit pays itself at c; every actual A visit is paid injectively at floor m0 by the existing original FloorSupplyFreeBudget theorem; every S visit pays the free A immediately before its first return to c, at m0+1. Those three wallets have different heights. Two S visits cannot use the same first-return A: the first return after the earlier S is no later than the later visit. The endpoint condition pays the last S visit before T.

At n0/a0/empty BlockWord, the checked floor-supply theorem's old-prefix hypothesis is genuinely supplied by the original empty prefix. It is NOT reassumed at the deep minimum. For m0=-h-4 the target level is c=-h-2, and every wallet lies at height<=1-h, so the entire payment is inside the original low budget. Five different24-key source requirements give five distinct clocks at c; no source ordering is assumed. Hence any M5/low4 parent must visit a height<=-h-5. No search depth or imposed floor is used.

## E730 old-A confinement

Let v be the last ORIGINAL minimum m through T. There are two distinct original low free after v at m and m+1, so at most two low free precede v. If four A precede v, the first two are low free, the third must be actual and makes the first three A consecutive, and the fourth is free. That fourth must therefore start ABOVE1-h. Only three A precede it, so at most h+1 S precede it; the whole earlier history stays above ell=-h-1.

There can be no A below ell before v. The first such A would follow a monotone descent below the prior floor, would itself be a new original minimum/free, and would consume a forbidden third pre-v low free. Consequently the last visit t to ell before v has both facts needed for the comparison: EVERY original clock before t has height>=ell, and the entire interval[t,v) is S. An earlier descent below ell followed by a return to t would require the already forbidden A below ell. The descent has at least four S because m<=ell-4.

Let b be the first return to ell after v. Every A in[t,b) starts below ell. Its source height is at most ell-2, while every clock before t has height>=ell. Thus every original source lies at/after t, and literal translation preserves every window in BOTH directions. The comparison word begins with four S, visits<=-4 and returns to0. E728's three-low-free recovery lemma explicitly does NOT require positive prefixes, so it is valid with initial parameter2 at this comparison. No new positive-prefix or BlockWord assumption is inserted at t. Its three free map to three ORIGINAL low free in[t,b). Together with the first two free before t this gives five, not a double charge of the two preliminary recovery frees. This proves old A<=3.

## E730 first-return total free and the downstream inputs

R is the first d=2-h visit AFTER v, not a visit on the initial descent. Every A in[v,R) starts at height<=d-1 by first return. Before v there are at most three A: the first two are low free, and the third, if free, is also low by E728's original first-three argument. Therefore EVERY original free before R is low; total original free[0,R)<=4 follows exactly there. It is not extended to the later prefix T, which may contain arbitrarily many high free.

Since v is the last minimum through T and R<=T, every intermediate height after v through R is strictly greater than m. The first two signs at v/v+1 must be A; otherwise the path returns to or goes below m. Both A are original free by the original floor/floor+1 window exclusion, giving old free<=2. Set p to the ACTUAL A count before v. For p0/1/2 the old paid amounts0/1/2 are the original first-two-free facts. For p3, E738 now derives the literal triple from actual A3/free<=2; initial h>=1 supplies a preceding S, so its third A is actual and old paid is2. The original floor gives the final S run at least3, also checked by E738.

All inputs of E737 are therefore supplied for K=R-v, without assuming its height conclusion. E737 gives H(R)<m+7. The parent-derived m<=-h-5 and H(R)=2-h give H(R)>=m+7. This is the contradiction. The second16-key family and every alternative source remain in the original parent; they cannot repair failure of this already necessary first-return condition.

Verdict: complete PAPER connection, still not an unconditional Lean PC5 theorem. No high-free truncation, reset of Nat0, bounded depth/upper excursion, or finite search cutoff enters this chain. The remaining uncertainty is independent human review and formalization of these precise upstream/free-budget interfaces, not an unresolved search range.
