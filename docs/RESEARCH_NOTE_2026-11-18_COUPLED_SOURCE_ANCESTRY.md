# Two fixed sources defeat the ancestor-free assignment

Conclusion: source-prefix-only original-free charging has unbounded load even with genuine initial-S h1 and full height band[-4,2] FIXED. Section6 gives N-1 nonshort low images with unique original source4, whose ENTIRE permitted free wallet is{1}. Thus no fixed capacity works for ANY assignment confined to those source prefixes, not only the frozen rho. This is **REFUTED by a complete all-N PAPER construction**, not an all-N Lean theorem; human review pending. The whole low wallet is>=N+2 and D_near=N, so D_near<=F_low/C1 and actual Recaman orbit reachability are not refuted. Earlier sections retain the first, weaker source-potential families and their verification; these are one mechanism, not extra parent successes.

## Fixed rule being refuted

For each exclusive initial-S target at relative height2, choose the latest low A images a,b at relative heights0,1. Choose a unless it is an internal SAA endpoint, in which case choose b. A free image pays itself. Otherwise choose the latest original source u of the image, then the latest low free at/before u; if none exists, choose the earliest low free before the image. No change to this rule is made after seeing the counter. In particular this is different from E715's latest-free-before-target rule.

## 1. Explicit family in normalized coordinates

For N>=1 put P=6N-2. Begin a normalized word with SSSAA, at clocks0..4, using H(0)=B(0)=0, B(t)=sum_{i=1}^t H(i). For j=0..N-1 define

    r=4+6j, a=(r-4)/2,
    psi_j=18j^2+18j+5=((r-1)^2+1)/2,
    q_j=psi_j+2r-2=18j^2+30j+11.

At clock psi_j the height is-1 and B=1-2psi_j. Append:

1. A^r S^(r-2), reaching height1/B0 at q_j;
2. AS, so q_j is a genuine A, returning to height1/B3;
3. descend with S to height-r-3, inserting a copies of AS at height-2 and a+7 copies at height-3;
4. append A^(r+2), returning to height-1.

The next clock is psi_(j+1). Finally truncate just after the A at q_(N-1), and prepend S^P. Global initial cut h=P+1, global old source P=h-1, local source P+2>=h, selected targets t_j=P+q_j. The length is18N^2-2.

The unmodified ascent/descent word A^r S^(2r+2) A^(r+2) has length4r+4, net height0, and mean height-2 when begun at-1. Its B increment is-2(4r+4). The added AS at1 contributes length2/B3, an excess7 over mean-2. Each AS at-3 contributes length2/B-5, an excess-1. Each AS at-2 contributes excess+1. Thus a/(a+7) loops cancel that7 exactly. Total stage length is

    4r+4 + 2(1+a+a+7) = 6r+12,

which equals psi_(j+1)-psi_j. Hence B=1-2psi is preserved at every psi. The area of A^r S^(r-2), starting at-1 and ending1, is(r-1)^2=2psi-1, proving B(q_j)=0. This is an integer construction, not interpolation by a search result.

## 2. Every old-source alternative is classified

An original Win from u to t has H(u)=H(t)-1 and B(t)-tH(u)=B(u)-uH(u). Define K_c(u)=B(u)-cu.

For a selected target q_j, the required source has H=0 and B=0. In the entire normalized prefix, the ONLY such clock is0:

- the base SSSAA has no further H0 clock;
- the upward H0 crossing in stage r has B=-(r-1)^2<0;
- the downward H0 crossing after the target's AS has B=3;
- all remaining loops and the final ascent stay below0.

Earlier global padding has normalized heights>0. Therefore EVERY selected target has complete original source set{P}. It is EndN0 and not EndNh, at H(t)-H(h)=2. No selected-source-only shortcut is used.

For a low image psi_j, the required source has H=-2 and K_(-2)=1. Its ONLY source is normalized clock2. The base's other H=-2 clock4 has K=0. In any stage r put

    D=(r+1)^2+7.

At the downward H=-2 crossing the key is D. Its a AS loops visit that level with keys D..D+a. The a+7 AS loops at-3 visit H=-2 with keys D+a-1-i, 0<=i<a+7; the smallest is D-7=(r+1)^2>=25. The final ascent's H=-2 clock has key0, since the final step to psi increases K by1. These exhaust all clocks at that height. Neither alternative has key1. Global padding cannot introduce the lower height-2.

Thus every psi_j has complete original source set{P+2}, including the first short case. The two supply chains share fixed sources at DIFFERENT heights; the added loops maintain both potentials simultaneously.

## 3. The unchanged map has load N-1

Between psi_j and q_j, the last A at normalized height-1 is psi_j, and at0 it is psi_j+1. For j>=1 the preceding stage ends with at least six consecutive A, so psi_j is NOT an internal SAA endpoint. The chosen image is therefore psi_j. Its latest source is P+2. There are no A, hence no free, at/before P+2. The earliest original free is P+3, at normalized height-3, so it is low and is the fallback for EVERY j>=1. The second original A at P+4 is also free (its only possible source is P+3 with nonzero one-step area).

For j=0 the low image psi0 is a short SAA endpoint. The rule instead chooses psi0+1, which is free; no claim about sharing that first charge is needed. Consequently N-1 distinct targets are assigned to P+3. Given any proposed finite load L choose N=L+2. This refutes every depth/length-independent load bound for THIS rule, not every possible assignment.

## 4. Original domain and disjoint available free

The largest normalized height is at most r_(N-1)-1=6N-3. After padding P, every nonempty global height is<=-1. Since original EndN count<=A count, S-A>=1 implies actual EndN+1<=S at every nonempty prefix. This supplies the original positive domain, not an assumed new history.

The only H1/B0 A in each stage is q_j, so D_near=N. Each completed descent, j=0..N-2, attains a new global minimum -r_j-3, lower than all earlier heights. Its first outgoing A is original free, because a source would have to start one level lower than that global minimum. These N-1 distinct low free, together with the first two free P+3/P+4, give F_low>=N+1. Hence this construction deliberately has enough free; the proposed rule ignores useful free AFTER its reused source. It is neither a counterexample to D<=F nor a standard Recaman orbit realization.

## Falsifier / verification / stop

The original frozen small-word query had no counter (discovery24575 words/controls, independent parameter holdout6142; exact count in packet), and is not a proof. The new quadratic coupled-source formula was derived on paper, frozen BEFORE its checks, and is not a cutoff enlargement of that absence search. N1/2/3 discovery and N4/7/11 holdout compared a forward original (height,key) bank against a literal reverse mass/area scan at EVERY A, including uniqueness of every selected source/image and the exact unchanged rho rule. These finite runs are COMPUTED only; the all-N conclusion uses the exhaustive classifications above. See data/depth_general_20261118/COUPLED_PROTOCOL.json and coupled-*-summary.json.

Stop the fixed ancestor-before-source map. Do not repair its name or numerical load and repeat the query. A new assignment must consume the free created after a reused source, or transport an explicit stock balance; existence of an injection is not an admissible input. First source/free construction gate has new general-mechanism evidence before its15-minute deadline. Independent later mechanism and local audit still remain; completion of this unit is not the end of today's parent cycle.

## 5. Stronger family: genuine initial S run, no fallback branch

The first family permits the chosen cut h inside a longer S run. This satisfies the frozen quantifiers, but does not by itself refute a rule restricted to a MAXIMAL initial run. The following independent integer construction removes that limitation, and repeats the latest-before-source branch rather than the fallback.

Start the normalized word with

    SASSSAA A^3 S^8 A^5.

It has length23, H=-1, B=-42. The original source at0 has H0/B0; the local source4 has H=-2/K_(-2)=4. For j>=0 put

    r=7+8j, a=r-7,
    psi_j=32j^2+48j+23=((r-1)^2+10)/2,
    q_j=32j^2+64j+39=psi_j+2r+2.

Starting at psi_j append AA, then two AS loops at height1, then A^(r-2) S^(r-2). It ends at height1/B0 at q_j. Append AS at q_j (so it is an actual A target), descend to-r-3 with a AS loops at-2 and a+21 AS loops at-3, and append A^(r+2) to height-1.

There are now three AS loops at1, producing excess21 relative to mean height-2; the21 extra AS loops at-3 cancel it, and the a pairs at-2/-3 cancel each other. Total stage length is4r+52+4a=8r+24, exactly the difference of successive psi. Thus H(psi)=-1/B(psi)=4-2psi is preserved. The first hill has area(r-1)^2+6=2psi-4, so B(q)=0. These calculations also prove every prescribed source window.

The COMPLETE source classification is again elementary. For level0/B0, only origin0 qualifies: the initial seed's other level0 clocks have B=-1,-10,-6; each stage's upward crossing has B=4-2psi<0, and its downward crossing after q's AS has B=3. The two pre-target AS loops stay at heights1/2 and their level1 keys remain negative before q. All other pieces stay below0.

For level-2/K=4, only clock4 qualifies. The base's other level-2 clock6 has key3; the seed hill's downward/ascending level-2 keys are19/3. In stage r, the downward key is

    D=2q+10=(r+1)^2+24.

The loops at-2 have keys D..D+a; the loops at-3 have keys D+a-1-i, 0<=i<a+21, all at least D-21=(r+1)^2+3>4. The final upward crossing has key3. These exhaust ALL sources, not chosen witnesses.

Truncate after the A at the final q, then prepend S^P with P=8N-1. The global genuine initial S length is h=P+1, immediately followed by A. Every selected t_j=P+q_j has complete source set{P}= {h-1}; its latest low A image is P+psi_j, nonshort even for j0 because the seed ends with A5. That image has complete source set{P+4}. The only A at/before P+4 is the first original free P+1=h. Hence the unchanged rho sends ALL N targets to that same free, through its primary latest-before-source branch. No fallback is used.

The maximum normalized height is r_(N-1)-1=8N-2=P-1, so all nonempty global heights are negative and all original positive-prefix inequalities follow as in section4. The source-level1/B0 classification gives D_near=N. The first A at1, the seed's new minimum at18, and the first A after each completed later descent give at least N+1 distinct original low free. Thus the stronger family also satisfies D_near<F_low and is not a C1 counter. Its exact length is32N^2+8N+7.

N1/2 discovery and separately frozen N3/5 holdout passed the full forward/reverse source audit at EVERY A. N2 has h16, targets54/150, images38/118, common local source19 and common assigned free16; F_low39. These finite checks are COMPUTED. The all-N no-go is PAPER with the exhaustive key lists above, not Lean-checked. See GENUINE_PROTOCOL.json and genuine-*-summary.json. This strengthens the same mechanism result and does not create another parent cycle or generalization-success count.

## Kernel attempt / adoption boundary

The initial160-clock finite Lean attempt H01-KERNEL had missing namespace imports and reported excessive kernel memory at the declared512MB limit. It is STOPPED after one attempt, repairs0, with exact bytes and receipts quarantined as STOPPED_AncestorSourceCollision.lean.txt. No import/tactic/split/resource-only retry is made, and no failed source is imported by Recaman/root/Audit. Neither finite kernel acceptance nor an all-N Lean proof is claimed. The mathematical PAPER construction and independent exact Python verification remain the stated evidence.

## 6. Fixed depth4, fixed top2, genuine h1: the whole source-prefix wallet fails

There is a stronger all-N construction with EVERY parameter h/depth/upper height fixed. Begin with SASSSAA, at clock psi0=7/H=-1/B=-10. It has three original free (clocks1,5,6) and the only A at/before local source4 is free1. The old source0 has H0/B0; the local source4 has H=-2/K_(-2)=4.

At a stage clock psi>=7 with psi=1 mod3 and psi=3 mod4, put

    k=(2psi-8)/3,
    a=the unique element of{0,1,2} for which psi+52+16k+4a=1 mod3.

Append AA (reaching1), then(AS)^k at1, then AS (reaching2 and down to1). Its endpoint is

    q=psi+4+2k,   H(q)=1,   B(q)=8-2psi+3k=0.

Now append AS at q, descend to-4, inserting a AS loops at-2 and19+7k+a AS loops at-3, then append AAA to return to-1. The bare A3 S6 A3 stage has length12 and mean height-1, hence excess12 relative to mean-2. The k+1 high AS loops have excess7 each; a/-2 and19+7k+a/-3 loops cancel the total12+7(k+1) exactly. Its full length is52+16k+4a. Thus the next psi again satisfies B=4-2psi, has the required residue1 mod3 by the choice of a, and preserves residue3 mod4 because the added length is a multiple of4. This is a finite integer recurrence for every number of stages.

All heights stay in[-4,2]. The first three A are original free, and every later prefix has F>=3/H<=2, so original S-E=F-H>=1. Early prefixes of SASSSAA are directly positive. The genuine initial S run is EXACTLY h1 for all N; no large negative padding or unbounded height is used.

Complete source classification remains explicit. The ONLY H0/B0 clock is0: base clock2 has B=-1; the upward H0 crossing has B=4-2psi<0; the downward one after q's AS has B=3. The high AS loops are at1/2, other loops below0. The ONLY H=-2/K4 clock is4: base clock6 has key3; in a stage the downward key is D=2q+10=26+7k. The loops at-2 have keys D..D+a; those at-3 have keys D+a-1-i for0<=i<19+7k+a, whose minimum is D-19-7k=7>4. The final ascending key is3. These are all clocks at that height.

Therefore each q has complete source set{0}, and every low image psi has complete source set{4}. The latest low A before q is psi, the latest higher low A is psi+1. Except at j0, the preceding AAA makes psi nonshort; hence the frozen map selects psi and sends it to the unique original free at/before4, namely1. Its load is N-1, despite FIXED h1/depth4/top2/width6. Every fixed load depending on any of these parameters is refuted by choosing N larger.

This also refutes MORE than the deterministic rho. For all these later images the entire allowed source-prefix wallet is the singleton{1}. ANY assignment, even one depending on the target and choosing any original source (the source is unique), must reuse1 if it spends only free at/before that source. No matching constrained to that wallet can exist for two such images, and no fixed per-free capacity works for all N. This is not a no-go for assignments allowed to spend original free AFTER the reused source.

The selected target set is exactly the N stage q (the other H1 clocks have negative B or B3). After every completed stage its A leaving floor-4 is original free, since no original height-5 source exists. Together with the initial three free this gives F_low>=N+2 before the truncated last target. D_near=N<F_low, so the parent count inequality and C1 remain unrefuted.

Frozen N2/3 discovery and N4 holdout checked complete forward original banks. N2/3 exhaust EVERY A by independent reverse mass/area too; for the larger N4 word only every selected target/image/partner and the initial free are reverse-exhausted, and full-all-A reverse is NOT claimed. The all-N theorem is PAPER from the recurrence/key classification, not a Lean theorem or a finite-absence extrapolation. This stronger fixed-band construction supersedes the weaker variable-depth obstruction for the generalization verdict; it is not another parent cycle or a second counted success.
