# NoSAAS next pass

Conclusion: PROVED-PAPER branch reduction and REFUTED total-collision elimination. Global circular NoSAAS eliminates the internally doubled start-S prefix with a nonempty tail, but same-oldest minimal SS2 collisions remain. This does not add NoSAAS to the original local Hall claim and does not prove its capacity inequality.

Base revision 65c25ab742ab4aa749bfd5f48438dbcb7b774d1d. Worktree read-only; all output in this /tmp directory. Existing E133 card/source and October 6 card were searched first. Existing NoSSMassOne classification and E166 leading-run bound are dependencies, not new results.

## Uniform reduced alternatives (PROVED-PAPER)

Use the independently audited geometry W_A=C A and W_S=X C after lifting common oldest S to the same integer, with A-ended donor clock t_A<t_S, lag d=d_A≥11, and X noSS/end-A/mass1/moment d. Impose explicitly the additional hypothesis that the whole integer stream has no chronological SAAS; this forbidden palindrome is equivalent in newest-first orientation.

The prior necessary classification was:

1. X=(AS)^r A, with r=d−1 and clock separation k=2d−1.
2. X=(SA)^j A (SA)^h, j≥1,h≥0, d=3j+h+1, k=2(j+h)+1.

If j≥1,h≥1, the doubled A is bracketed by S: the last SA of (SA)^j, the extra A, and the first S of (SA)^h form SAAS. So the second alternative must have h=0. Consequently d=3j+1, j≡2 mod4 by d≡3 mod4, and d≥11 implies j≥6 and d≥19. Since X then ends SAA, C cannot begin S (otherwise SAAS crosses the join); thus C begins A. Minimality excludes initial AAS (leading-run2), and E166 bounds every SS2 P2 leading A run by3. Therefore C's leading A run is 1 or3. No periodic seam qualification weakens this exclusion: every substring of an actual window is a substring of the global stream.

Both remaining alternatives force an actual clean current-A source distinct in phase from both donors:

- In alternative1, the S-ended donor has newest past AS. At t_S−2,t_S−1,t_S the signs are SAA. NoSAAS forces e(t_S+1)=A, so the source t_S+1 has past lag3 AAS and current A.
- In alternative2, X ends SAA, so e(t_A+1)=A as well as current e(t_A)=A. If C has leading A-run1, source t_A+1 has past AAS. If C has leading A-run3, source t_A−1 has past AAS (the already-known leading sibling mechanism).

Each clean source has a different phase from either donor: periodic equality would transport its P2 lag3 window to that donor, contradicting positive-proper-prefix minimality since donor lag≥11. This is a source-existence constraint, not an extra S outside the lowSS endpoint image. In particular its lag3 endpoint may already be in a donor neighborhood, so no capacity increment follows merely from adding this source.

## Exact NoSAAS collision (REFUTED elimination; COMPUTED validation)

Take period p33, ascending phases:

`SASASSSAAAASASASASASASASASASASAAA`

Its mass is3 and its cyclic repetition has no SAAS. Current phases10 and31 are A. The specified words are:

- Current10, lag11: W_A=AAASSSASASA, mass1/moment0/SS2; oldest offset10 and phase0.
- Current31, lag31: W_S=(AS)^10 A AAASSSASAS, mass1/moment0/SS2; oldest offset31 and phase0.

Both are minimal in the exact positive proper prefix sense. This example is compatible across the periodic wrap: signs31 and32 are A, and the final cyclic A run has length3 rather than2. The forced clean source is phase32, whose actual past is AAS. It illustrates alternative1.

There is also a direct paper check of minimality. Set C=AAASSSASAS. Its prefix lengths with mass0 are 0,6,8,10 and respective moments 0,−9,−10,−11. X has mass1, moment11, and all its mass-one proper prefixes have strictly positive moments. After X, a prefix of X C has mass1 exactly when the C prefix has mass0, yielding total moments11,2,1,0. Only the full word is P2. For W_A the mass-one prefix positions are1,5,7,9,11, with moments1,−3,−2,−1,0; again only the full word is P2. SS2 is wholly in C's SSS run. The global circular word has only alternating regions and SSS/AAAA/AAA exceptional runs, so no two-A run bracketed by S occurs.

Pre-run protocol and source hash are in hypothesis-card.md. Frozen command:

`python3 /tmp/recaman-ss2-next-sol61-20261006/check.py > /tmp/recaman-ss2-next-sol61-20261006/output.json`

Script SHA256 a0667b91b68878d2ecc0298e679a678257eee216d84c6bc0bb9da0f29b5a42d4. One constructed candidate, no exhaustive range and no claimed holdout. Exact JSON output is retained. No adaptive repair was executed; the candidate was frozen with two explicit A seam letters before its sole validation run.

## Frontier meaning and next question

The remaining geometry is narrower ONLY on the explicitly NoSAAS branch: start-S with h>0 is gone; pure alternating X and start-S h=0 survive as alternatives (an exact example confirms the former). The general no-NoSAAS local Hall problem still has all original branches. A same-oldest injectivity proof cannot be recovered merely by adding NoSAAS.

Next bounded structural question: in either NoSAAS remaining alternative, can the forced clean sibling's actual lag3 endpoint and the two overlapping SS edges of C (possibly in one SSS run) force a second distinct S outside the complete lowSS endpoint set? This is stronger than local Hall and must first be falsified; if it fails, return to full-neighborhood slack rather than continue named charges. The parent's independently frozen complete-endpoint candidate addresses this interaction. Do not infer extra capacity from clean-source existence alone.

Status: this short pass is complete with one uniform exclusion/reduction and one exact counterexample to total collision elimination. Original Hall remains CONJECTURED; no Lean implementation, registry, git or repository edits.

## All-period padding family (PROVED-PAPER)

The p33 counterexample extends to every period p≥33. Keep C=AAASSSASAS and V=(AS)^10 A C, so |V|=31 and mass(V)=1. For every integer n≥2, define ascending period P_n=reverse(V) A^n and extend it periodically to all integer clocks. Its period parameter is p=31+n and its period sign mass is1+n>0. This construction does not claim that p is the least period; the research hypotheses require only a positive period parameter.

Current10/lag11 still sees C A: clocks0..9 are reverse(C), and the older sign at clock−1 is the final A of P_n. Current10 itself is the A immediately after reverse(C). Current31/lag31 sees V, and current31 is the first appended A. The clocks10 and31 are distinct phases because p≥33. Oldest S is clock0 for both, with offsets10 and31 respectively. Thus all the previously proved finite word mass/moment/minimality/SS checks apply unchanged; their lags and words do not depend on n.

The finite string reverse(V) equals reverse(C) A (SA)^10. It has no SAAS. In its interior the only exceptional maximal runs are SSS and AAAA; every other run is alternating. Appending A^n merges with the final A of reverse(V), forming a terminal A run of n+1. This run is bounded on both sides, cyclically, by S, and has length at least3. Consequently it cannot produce SAAS. No other run changes at the seam, and all the remaining internal runs still have length1 or at least3. Therefore the entire periodic stream is NoSAAS for every n≥2.

Boundary n=1 produces p32, period mass2 and the same two valid donors, but its terminal cyclic A run has length2, bracketed by S. The SAAS seam is clocks29,30,31,0 modulo32: S,A,A,S. Hence n=1 fails global NoSAAS. The required n≥2 threshold is exact for this padding family.

This is an explicit infinite family of NoSAAS oldest-S collisions, not a local Hall counterexample, not an orbit construction, and not evidence against E067/E070. It prevents treating a no-NoSAAS or NoSAAS finite census with p≤22 as an all-period collision exclusion. No further census or computation is needed: the constant word checks were already frozen and executed, while the n-dependent argument is a run/seam proof.

## Pure alternating prefix and one SSS run: two excluded S phases (PROVED-PAPER)

This is a new, restricted capacity subcase, independently checked from the parent's proposal. Assume the original actual periodic donor-pair hypotheses, explicitly add global NoSAAS, assume X=(AS)^(d−1) A, and assume the two SS edges of C belong to one SSS run. They cannot belong to a longer run since ss(C)=2. Write s for the integer oldest S and q for the chronological first S in that run, so q,q+1,q+2 are S. The following argument proves that phases s and q are distinct and both avoid every actual current-A lowSS S-ended P2 endpoint. No assumption about a chosen owner or Hall condition is used.

First, q can never be the integer S-ended endpoint of any positive-length current-A window with SS≤1. Its current clock u is greater than q. If u=q+1 or q+2, the current bit is S, contradicting current-A. If u≥q+3, the endpoint-q window contains all three S signs and at least two SS edges. Periodic lifting gives the same exclusion for the phase of q and every lowSS endpoint phase. This exclusion does not even need P2.

It remains to prove phase(q)≠phase(s). If q>s and the phases coincide, periodicity reproduces the SSS run at s,s+1,s+2. All these signs and q,q+1,q+2 lie inside C. The SS edges starting at s,s+1,q,q+1 include at least three different integer edges: if q=s+1 there are three, otherwise four. This contradicts ss(C)=2. Therefore a possible phase equality would require q=s exactly.

Suppose q=s. In newest-first orientation C=T SSS, so T is SS-free, ends A (otherwise C has a fourth consecutive S), and mass(T)=3 because mass(C)=0. NoSAAS forbids every A-run of length2 bracketed by S. The final run of T is also bracketed on its old side by C's SSS, so this applies to it. If T begins A, its initial A-run cannot have length2 either: that would start the minimal donor W_A=C A with the proper P2 prefix AAS (d≥11). Count A-runs versus isolated S signs:

- Start-A/end-A T has one more A-run than S signs. Since mass(T)=3, its total extra A count beyond one per A-run is2. Every A-run therefore has length1 except exactly one run of length3 (two runs of length2 were excluded). Thus T=(AS)^a AAA (SA)^b with a,b≥0. Direct append formulas yield length(T)=2a+2b+3 and moment(T)=5a+b+6. For C=T SSS, moment(C)=−a−5b−9 and d=length(C)+1=2a+2b+7. P2(W_A)=P2(C A) therefore requires a−3b−2=0, hence a=3b+2≥2.
- Start-S/end-A T has exactly as many A-runs as S signs. Its extra A count is3. Since every run is bracketed by S in C and length2 is forbidden, the only possibility is one run of length4. Thus T=(SA)^j AAA (SA)^b with j≥1,b≥0. Its length is2j+2b+3 and moment7j+b+6. Hence moment(C)=j−5b−9 and d=2j+2b+7. P2(C A) requires 3j−3b−2=0, which is impossible modulo3. This disposes of the potential missed A^4 case.

The surviving start-A form has a≥2, hence C begins AS. At clocks t_A−2,t_A−1,t_A the signs are SAA. Global NoSAAS forces e(t_A+1)=A. But X=(AS)^(d−1) A ends ASA (d≥11), and its old-end A is the actual sign at t_A; consequently e(t_A+1)=S. Contradiction. Thus q=s is also impossible, proving phase(q)≠phase(s).

E368 excludes phase(s) from every actual current-A lowSS P2 endpoint. The preceding run argument excludes phase(q) from every lowSS endpoint. Both phases are actual S phases in C, hence in the donor neighborhood. For any lowSS set L with its original arbitrary specified windows, use E368 lowSS_endpoint_image to get |L| distinct normalized S endpoints F contained in N(L). The distinct phases(s),phase(q) lie outside F and inside the donor neighborhood, giving |N(L∪{v,w})|≥|L|+2.

This proves local Hall only for the explicitly additional NoSAAS + pure-alternating-X + single-SSS-run subcase. It does not cover start-S h=0, separate SS runs, arbitrary-NoSAAS violations, multiple collision groups, or SS≥3. Its new input is the exclusion of oldest phase equality with the chronological first S in the SSS run, proved from actual bit chronology and the two exact T mass/moment classifications. It is not a reformulation of Hall. No new computation or Lean implementation was performed; this is a paper proof using the already audited geometry and existing E368 normalization/exclusion.

## Start-S h=0 and oldest SSS: the next-oldest S also avoids lowSS endpoints (PROVED-PAPER)

The remaining NoSAAS/single-SSS-run subcase has X=(SA)^j A. If the SSS run's chronological first S q is strictly later than the common oldest s, the preceding periodic duplication argument already proves distinct phases(s),phase(q), and q's lowSS endpoint exclusion applies unchanged. Only q=s remains. Normalize s=0.

The preceding exact T classification applies when C=T SSS. Its start-S/A^4 form is arithmetically impossible; its start-A form gives

C=(AS)^a AAA (SA)^b SSS, a=3b+2.

Thus d=|C|+1=8b+11. The h=0 collision-prefix condition d=3j+1 forces 8b+10=3j, hence b=3r+1≥1, j=8r+6, and a=9r+5, for an integer r≥0. These are necessary consequences, not newly inserted hypotheses. The A-ended current is t_A=d−1 and the S-ended current is t_S=t_A+2j+1.

We claim integer endpoint1 is impossible for every current-A P2 window with SS≤1. Its chronological signs, from endpoint1 through just before t_A, are

SS (AS)^b AAA (SA)^a.

This starts with one SS edge. The cumulative mass starts−2; each AS pair alternates−1/−2; the AAA run reaches−1,0,1; each subsequent SA pair alternates0/1. Whenever the cumulative mass is1, the next/current sign is S, except at the final clock t_A where the current sign is A. At t_A the window from endpoint1 has mass1 but moment−1: it is C with its oldest S removed, so its moment is moment(C)+(d−1)=−d+(d−1)=−1. Its actual lag is d−2 (not d−1). Hence no endpoint1/current-A P2 window exists up to and including t_A.

From t_A through t_S−1 the subsequent chronological signs are reverse(X)=A(AS)^j. Starting from the previous mass1, this yields cumulative masses2/3 throughout, ending at mass2 with last sign S. Thus no P2 mass1 endpoint1 window has current between t_A+1 and t_S.

Any later endpoint1 window already contains its initial SS edge, so SS≤1 allows no additional adjacent SS edge anywhere after t_S−1. Its extra chronological segment begins A because that previous sign was S; otherwise a second SS would arise immediately. This segment is SS-free and begins A. Every S in such a segment is immediately preceded by an A, giving #S≤#A and nonnegative added mass. Therefore every later candidate window has total mass at least2. It cannot be P2. This establishes endpoint1 exclusion at every positive lag, with no future cutoff, including beyond arbitrarily many periods.

Periodically lift any S-ended lowSS endpoint congruent to1 to the integer1; current-A, P2 and SS count are preserved, contradicting this all-clock exclusion. Phases0 and1 are distinct: p=1 is impossible since the stream has both the actual S at0 and current-A donors. Both phases are actual S in C. E368 excludes phase0 from all lowSS endpoints, and the new argument excludes phase1. Together with the actual normalized endpoint image F⊆N(L), this supplies |L|+2 distinct actual S phases in N(L∪{v,w}).

Combining both collision-prefix alternatives proves the NoSAAS + single-SSS-run local Hall subcase entirely. The second excluded S is phase(q) when q>s; in pure-alternating X the case q=s is impossible; in start-S h=0 with q=s the second excluded S is phase(s+1). The general no-NoSAAS claim and the NoSAAS case of two separate SS runs remain unproved. This is a genuine endpoint/core interaction beyond E368, not an owner or Hall assumption. The proof is paper-only; no new computation or Lean changes were made.
