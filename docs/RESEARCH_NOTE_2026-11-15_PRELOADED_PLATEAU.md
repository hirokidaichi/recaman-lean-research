# Preloaded source plateau: no fixed latest-free load

2026-11-15, H-20261115-07/H10. PROVED-PAPER, independent semantic audit pending; not yet Lean. This extends E711's two-target obstruction to every N, even at fixed depth bound5/initialS2 by the final refinement below. It does not refute D<=total original free or C1.

## Exact statement

For every integer N>=1 there is a finite original sign history f, initial all-S length h+1, and N distinct targets q_j=T+8j (0<=j<N), with:

1. Every nonempty prefix of the whole finite word satisfies actual EndN0 count+1<=S count. There is no bound on excursion depth, run count, or preceding free count.
2. Each q_j is an original actual A with unique original Win source h, so is not EndN f (h+1) q_j. The source lies in the original initial-S prefix.
3. There is no original free A between q_0 and q_(N-1). Consequently all N exclusive old-S targets have the same latest preceding original free.

Thus no fixed finite load on that particular latest-free assignment can work. Another global pairing or a history-dependent reserve is still possible. These histories are not asserted reachable by the standard Recaman orbit.

## Coordinates and the eight-step plateau

Use normalized height H and cumulative absolute area B from the clock h just before the last initial S. Write A for +1 and S for -1; B(t) is the sum of heights after steps 1..t. At an A target q with height x, a prior clock u supplies it exactly when

    H(u)=x-1,   B(q)-B(u)-(q-u)H(u)=0.

Put Z=ASSSSAAA. Starting at height1/area0, its successive heights are 2,1,0,-1,-2,-1,0,1 and its cumulative absolute areas are 2,3,3,2,0,-1,-1,0. Hence Z returns to the same pair (H,B)=(1,0). A final A makes the last boundary a target too.

The nonboundary A at offsets5/6/7 of cycle j needs a source at height -3/-2/-1, respectively. Measured from the plateau start T, its absolute area is 0/-1/-1. If X runs from that source height c to plateau height1, the required source-relative area of X is

    Ar(X)=c*q-B_tail(q),

where q=8j+offset. The three values are -24j-15, -16j-11, -8j-6. The offset6 constant is 11, not13: this follows from B_tail(6)=-1. No empirical label is substituted for an actual source.

## Backwards construction of all intermediate sources

Start with X=AAAA, whose initial height is -3 and final height1. Fix its final cumulative area at0. The cumulative area at its initial clock is2, since its absolute heights are -2,-1,0,1. Its only height0 clock has cumulative area -1.

For each required intermediate A (any fixed finite order; for example cycles j ascending, offsets7,6,5), extend X to the left as follows. Its current initial height c0 belongs to {-3,-2,-1}. To put a new initial clock at the desired c in that set, prepend the monotone connector from c to c0. Call this Y. It stays at negative heights. Compute a=Ar(Y), and let a* be the required integer above.

At height c, AS has mass0/source-relative area+1, while SA has mass0/source-relative area-1. Prepending l copies to a suffix changes its source-relative area by precisely +/-l, because the prepended word has mass0. If a<=a*, prepend (AS)^(a*-a); otherwise prepend (SA)^(a-a*). The resulting word has initial height c, final height1, and source-relative area a* exactly. Its initial clock is the new original Win source for the selected future A. Extending farther left never changes any already established suffix or its Win.

After all obligations, prepend the monotone connector from -3 to the current initial height. This sets the initial height back to -3 and preserves every established source. All added steps have absolute height<=0 after each step, except for the fixed final A of the base AAAA. Thus, with the final B fixed at0, every clock of the added part has B>=2. In particular, every height0 clock created by an AS loop at level-1 has B>=2. The base's height0 clock still has B=-1. There is no height0/B0 clock in X. Its initial cumulative area D is an integer >=2, and its absolute area is -D.

This is a finite deterministic construction for every N. Its length may grow quickly; no bound on that length is used in the mathematical claim.

## Attach a first source without creating a local alternative

Choose m>=2 with E=m^2-7-D>=28. The hill

    J = S A^(m+1) S^(m+3)

has mass-3 and area m^2-7. Choose b in {0,1,2,3,4} with 7b congruent to E modulo5 and a=(E-7b)/5>=0. Then E=5a+7b. At height-3, an AS loop has absolute area-5 and an SA loop has absolute area-7. Let

    P = J (AS)^a (SA)^b X.

It has final height1 and total area0, and starts S. The filler ends with cumulative area D>=2 and the seed X ends with area0.

List all possible height0 clocks of P. The origin has B0. The first upward crossing after the leading S has B=-1. The downward crossing of J has B=m^2-1>0. The fillers do not visit height0. The seed clocks at height0 have B>=2 or B=-1 as proved above. Therefore the origin is the unique height0/B0 clock of P. This is an all-clock classification, not a selected-witness check.

In every later Z cycle, the height0 clocks have B3 and B-1, so add no source of height0/B0. All boundary targets have height1/B0. Their original source is consequently unique, namely the normalized origin. No choice of a different local source can remove the obstruction.

## Original positive history and the common latest free

Choose h=m+1 and the full word

    S^h P Z^(N-1) A.

Its initial all-S segment has length h+1 because P starts S and then A. Throughout P and the plateau, normalized height is at most m (including the final plateau A, since m>=2). After the initial h S, every original nonempty height is therefore <=-1; the earlier padding also has negative height. Thus S>=A+1 and actual supplied count<=A prove the required positive inequality on every nonempty prefix of this same history. No A-to-free replacement is made.

The normalized origin is original clock h, inside the initial-S cutoff h+1. Earlier padding clocks have normalized height>0 and cannot supply a target of normalized height1, whose source height must be0. The uniqueness proof above handles every later clock. All boundary A are exclusive old-S supplied.

Between consecutive boundary targets, the only A are the first boundary itself and offsets5/6/7. The boundary is supplied by h; each other A has its preloaded actual source from X. Therefore there are no original free A in that whole plateau. At least one free precedes it: the very first A after S^(h+1) needs a source below the previously attained global minimum and so has no original Win. The finite nonempty set of preceding free clocks has a greatest element. It is the same latest free for all N targets.

## Scope of the no-go

The quantified mechanism refuted is a uniform bound on the number of exclusive old-S targets sent to their latest original free. The whole original prefix can contain many free, and their number is not controlled in this construction. D<=F and C1 are not refuted. The history-dependent minimal head E712 and its exact loss accounting E713 remain valid. This construction explains why a replacement charging rule must use older free or a reserve that changes with the prehistory, rather than only the last free.

No Lean implementation from stopped H01 is reused. Finite certificate checks, if run, are COMPUTED illustrations only. The all-N result rests on the explicit integer interpolation, all-clock source classification, and original-prefix positivity argument above.

## Fixed finite verification / independent implementations
The predeclared N1,2,3 forward indexed all-source certificates passed (word lengths48,315,9465); their latest-free loads are1,2,3 and full original free counts18,131,4300. Fixed N4 has406785 clocks,13 plateau A and four exclusive targets; reverse literal weighted-area scanning exhausted all original source clocks for every plateau A. Source is1101/cut1102, targets406760,406768,406776,406784. All original nonempty heights are negative. These are COMPUTED illustrations, not the all-N proof and not a fresh-prefix holdout. Worker CPU .037778+.712162 seconds; controller separate; same declared5-second daily mathematical worker budget. Protocol/sourcehash/argv and exact outputs are in `data/depth_general_20261115/PRELOADED_PLATEAU_PROTOCOL.json` and `preload-*.log`. No search/cutoff enlargement follows.

## Broader interpolation support, not the exclusive plateau theorem
For every finite suffix v, a constructed prehistory can supply every A of v. Induct on the number n of requested prefix clocks. At n0 there are no obligations. Given prefix p for q<n, complete p++take(n,v) to a mass1/area0 word by prepending z (E716). Every previous suffix window remains at the clock shifted by |z|, and the new whole word is the nth window. Iterate to n=|v|. Adding more S than the full constructed length keeps all those windows, puts every nonempty original prefix below0, and thus makes every prefix actual-positive. The prehistory can contain many free; resetting that boundary to BlockWord would invalidate the argument. Empty v has no target obligations.
The unrestricted one-window completion helper H08 was accepted after its one simp repair at512MB. H09's new all-prefix induction/positive realization implementation failed after one repair on a List.take normalization and is STOPPED/packet-only. The broader all-suffix assertion remains PAPER; no failed bytes/partial declaration are adopted. This support lemma does not prove the negative-height/exclusive all-N construction by itself and is not extra independent G credit.

## H10 refinement: the load is unbounded at fixed depth7

The growing hill above is valid but unnecessary. A new bounded-height area reservoir removes that dependency. Keep exactly the same seed X, whose initial level is-3, initial cumulative area D>=2, final level1/area0. Define

    J_D = SAAAS (SA)^(D+3) S^4.

SAAAS has mass1/area3, prefix heights -1,0,1,2,1 and prefix areas -1,-1,0,2,3. Each SA at height1 contributes absolute area1, while its height0 clock has current area3+j>=3. After D+3 such loops the height is1 and area D+6. The final four S have heights0,-1,-2,-3 and total area-6. Thus J_D has mass-3/area D and all prefix heights in[-3,2]. Its only height0/area0 clock is the origin: the initial second clock has area-1, the loop clocks have area>=3, and the last downward crossing has area D+6>0.

Put P=J_D X. Then P starts S, has final height1/area0, retains all seed source windows, and its only height0/area0 clock is the origin. The seed is bounded below by-4 and above by1, so P and every later Z cycle have heights in[-4,2]. Consequently the fixed padding h=3 gives the full history

    S^3 J_D X Z^(N-1) A

with all original heights in[-7,-1] after the origin (the first padding heights are -1,-2,-3). Its maximal initial S segment has fixed length4. The unique old source is fixed clock3, and the cutoff is fixed4. All N plateau targets remain exclusive, and no original free lies between them. This proves a stronger no-go: there is no finite bound on latest-free load depending only on excursion depth or initial-S length, since both may be fixed at7 and4. The full prehistory's free count still grows, so it is not a D<=F/C1 counterexample.

Fixed new-construction certificate N1/2 has lengths27/1415, original free10/693 and common latest-free load1/2. N3 has62651 clocks and nine plateau A; the reverse literal scan exhausts every original source for those A, all three selected targets have unique source3, and all nonempty heights remain[-7,-1]. Loader D2/3/11/100 boundary checks also passed. These are COMPUTED illustrations only. This is new mathematical input, not an increase of the old hill construction's cutoff. Worker CPU .030438+.096954 seconds, controller separate, daily math worker total1.137019 of5. No further range enlargement is authorized from finite absence.

## H11 final refinement: fixed depth5 and initialS2
The same fixed-height loader allows padding h1, provided positivity uses original free rather than the stronger A<S shortcut. The word now starts SSAA. A2 is free because its required source is below the prior minimum; A3 is free because its only possible source is2 and the one-step area is1. Thus every prefix after4 has free>=2. Throughout the finite history original Fw<=1 and Fw>=-5, so S-EndN=free-Fw>=1. Earlier nonempty prefixes contain no actual supply and have S>=1. E718 kernel-checks this domain lemma from the actual SSAA prefix and height ceiling, without assuming free2.
The selected N targets still have height1/area0 in coordinates at source1, hence unique original source1 by the complete zero-height/area classification. Initial cutoff2 is fixed. Source0 has normalizedheight1, so cannot be another source for these height1 targets. No preloaded source or previous free is removed. All-N latest-free load is therefore unbounded already at fixed excursion depth5 and initialS2. This is compatible with E663's depth5 fullgap: those targets have final S-gap0 and the whole original free count is large.
Fixed new-domain N1/2 certificates have lengths25/1413, free10/693, latest-free23/1403, selected targets24 and1404/1412 with source1. N3 reverse exhausts all sources for nine plateau A in62649 clocks and verifies the two early actual free. All-N and its source uniqueness remain PAPER; finite checks COMPUTED. Worker CPU .030780+.096236; mathematical daily total1.264035 seconds. E717 separately kernel-checks the arbitrary-D bounded-height loader and no zero-area return; E716/E717/E718 are support, not the full all-N kernel theorem.

Final auditor clarification: N1 has actual depth4; the N>=2 subfamily has depth5. The fixed bound5/initialS2 suffices to refute every depth-only latest-free load bound. See `data/depth_general_20261115/INDEPENDENT_QUANTIFIER_AUDIT.md`.
