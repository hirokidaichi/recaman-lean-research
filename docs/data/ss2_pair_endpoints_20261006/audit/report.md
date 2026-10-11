# Independent audit of the SS2 pair endpoint short pass

**PASS for the endpoint diagnostic and the stated auxiliary paper proofs, with one factual correction required in the handoff: the frozen p<=22 output already contains ONE cyclic-NoSAAS collision, at p22.** It is not true that those periods have no NoSAAS collisions. The new endpoint/core inequality remains CONJECTURED; all its finite checks are COMPUTED. Neither a local Hall proof nor a counterexample to local Hall was obtained.

Date 2026-10-06 JST. Separate auditor /root/issue81_auditor. Base 65c25ab742ab4aa749bfd5f48438dbcb7b774d1d. Repository access was read only. Files and reproducible audit commands are under /tmp/ss2-pair-next-audit-20261006/. No divergent primary-checkout results were used.

## Endpoint/core source and quantifiers

The source ss2_pair_endpoints.cpp matches frozen SHA256 fd55113d524a85189df42aa05a66f3cec644775a5df2909ea03aa9a0eacbc03e. Included ss2_collision_pair.cpp matches 184f9c96d9f9c24d4b4a009e555adbd6c6a66b401e42eb351efc22e8ef9343b4. The positive-mass quotient/moment formula, rotation enumeration including imprimitive words, first-P2 donor convention and 1-based oldest offsets were already independently audited for H-20261006-01 and remain unchanged.

For the new E_low set, the code correctly loops over every possible P2 residue/quotient candidate at every current-A phase, retains SS<=1 AND the actual full endpoint S, and does not break at the first P2. Thus nonminimal eligible windows are included. Enumeration of t in [0,p) represents all Int current clocks by periodic transport, without restricting window position to the donor core. The endpoint mask is a union, so duplicate endpoints/witnesses do not inflate the complement. The donor neighborhood mask covers the actual entire windows, including wrapping windows. Bitwise complement is intersected with the donor mask; irrelevant bits beyond p cannot contribute.

Minimum-prefix reduction from the old neighborhood statement would NOT justify reducing E_low to first P2 witnesses. The card correctly distinguishes this. Positivity is essential to the exhaustive finite-lag formula; no all-lag conclusion for nonpositive mass is claimed. NoSAAS is recorded only as a diagnostic and does not filter the general target.

The implication to the original local Hall target is valid: for any chosen L, E368 constructs a distinct endpoint image F of size |L| lying in N(L), and F subset E_low. Two distinct members of N_pair minus E_low are outside F and inside N(L union pair), giving |N|>=|L|+2. The converse is not asserted; original-neighborhood slack or rematching may rescue local Hall when this stronger test fails.

## Independent replay

independent.cpp is an auditor implementation using direct one-sign prefix mass/moment accumulation, independent bit-built rotations, and direct endpoint collection. It uses neither the quotient formula nor the parent's endpoint collector. Donor classification may stop once prefix SS>2, and endpoint collection once SS>1: these are sound because SS never decreases under extension. Otherwise it scans the full proved p(p+1) bound. Endpoint enumeration does not stop on its first P2.

All 22 representative/pair counts and all 24 pair records agree with the source output. For each pair, E_low mask, donor-union mask, complement mask/count, and number of eligible endpoint witnesses match exactly. The parent's separate Python direct scanner also passes for every pair and every full witness list. It verifies actual donor current signs, minimum P2 lag, exact SS/word/oldest and cyclic NoSAAS flags.

Finite results:

- Same 178,373 positive-mass word representatives as the earlier frozen domain.
- Discovery p1..18: 3 pairs, minimum uncovered count5, no violation.
- Reused holdout p19..22: 21 pairs, minimum uncovered count6, no violation.
- Overall 24 pairs, minimum uncovered5, no violation of the candidate >=2.
- There is ONE cyclic-NoSAAS pair, at p22; all other 23 pairs fail global NoSAAS.

These are reused finite ranges and not new independent evidence over a larger domain. No universal lower bound5 or all-period endpoint theorem follows.

## Required correction and useful p22 control

The p22 pair already in holdout.jsonl has mask349565, ascending word ASAAAAASASASASASASASSS, mass2 and no cyclic SAAS. Donors are phase5/lag19 with AAASASSSASASASASASA and phase18/lag31 with SASASASASASAAAAASASSSASASASASAS. They are current-A, minimum P2, SS2, tails1/0, and share oldest phase9. Their core extension is X=(SA)^6 A, so this is a concrete witness for the paper's second alternative, not only a warning against finite extrapolation.

E_low={1}, with actual phase4/lag3 AAS witness; the donor complement has9 phases. The clean phase4 is t_A-1 and is distinct from both donors. nosaas_controls.py independently recomputes all P2 prefix positions, SS, signs, sigma, X, the cyclic forbidden-pattern check and the clean source.

The p33 construction remains correct and useful, but should not be presented as needed because p<=22 had zero NoSAAS pairs, or as the least-period NoSAAS collision. No least-period assertion was proved.

## NoSAAS branch reduction: PROVED-PAPER

The prior audited chronology gives W_A=C A and W_S=X C after aligning actual oldest S times, with d_A>=11, C ending S, and X SS-free/end-A/mass1/moment d_A. The extra hypothesis for this section is global integer-stream NoSAAS. It is explicitly stronger than the original H-01/H-02 premises. SAAS is a palindrome, so changing chronological versus newest-first orientation does not alter the forbidden block.

The prior alternatives were X=(AS)^(d_A-1) A, or X=(SA)^j A (SA)^h. If j,h>=1, the final SA of the left block, the extra A, and the first S of the right block form SAAS. Hence the second branch has h=0. Then d_A=3j+1; d_A=3 modulo4 implies j=2 modulo4; d_A>=11 implies j>=6. The join X C would form SAAS if C began S, so C begins A. Its leading A run is <4 by E166 (SSGapBudget.ss2_leading_run_lt_four), and cannot equal2 because initial AAS is a proper P2 prefix (E132). It therefore has length1 or3. This proves the stated necessary two-form reduction.

The clean-source consequences are also valid:

1. First branch: the most recent donor signs at t_S-2,t_S-1,t_S are S,A,A. NoSAAS forces e(t_S+1)=A. At that current clock, past3=AAS.
2. Second branch: X ends SAA, so e(t_A+1)=A. If C starts A,S, source t_A+1 has past3=AAS. If C starts A,A,A,S, source t_A-1 is A and has past3=AAS.

Any equality of this clean source phase with either donor phase would periodically transport its lag3 P2 prefix to that donor, contradicting donor minimality and lag>=11. Thus the clean source is distinct in phase. This does not give a phase outside the selected lowSS image: the source can already be in L, and its endpoint can be already used. Existence alone supplies no extra capacity.

A wording nit was reported and corrected in Sol's live report: C has two overlapping SS edges, possibly one SSS run, not necessarily two separate SS regions.

## p33 and the all-period family: REFUTED injectivity / PROVED-PAPER construction

The p33 word SASASSSAAAASASASASASASASASASASAAA has positive mass3, global cyclic NoSAAS, donor phase10/lag11 AAASSSASASA and donor phase31/lag31 (AS)^10 A AAASSSASAS, both current-A/minimal P2/SS2 with oldest phase0. Independent direct summation checks all positive prefixes; only each full donor is P2. Phase32 is the forced distinct clean source. This validates the first alternative.

The proposed infinite family is correct. Set C=AAASSSASAS, V=(AS)^10 A C (length31, mass1), and P_n=reverse(V) A^n for every integer n>=2. Let p=31+n. Then mass(P_n)=1+n>0. The donor at phase31 sees exactly V at lag31 and is current-A because phase31 is the first padding letter. The donor at phase10 sees C A at lag11; its only older wrapped letter is the final padding A at phase p-1. Its current sign is the fixed A at phase10. Both windows and their minimum-P2/SS2 properties are independent of n. Since p>=33, phases10 and31 are distinct; both true-oldest clocks are0.

Inside reverse(V), all A runs have length1 except the fixed AAAA run, and its final A lies after S. Padding merges that final A into a terminal run of length n+1. It is cyclically followed by the initial S; n+1>=3 prevents a two-A run bounded by S. Thus no new SAAS appears at the seam and the whole periodic history is NoSAAS. The n=1 boundary gives exactly the SAAS seam at clocks29,30,31,0 modulo32, so the padding restriction is sharp for this construction.

Accordingly same-oldest injectivity is REFUTED even with global NoSAAS, with a complete paper family for every period parameter p>=33. This family does not refute the endpoint/core inequality, local Hall, E070, E067, or orbit realization. It is not a construction of an actual Recaman orbit.

## Decision and next direction

The genuine paper outputs are the necessary NoSAAS two-form reduction, its distinct clean-source consequence, and the explicit NoSAAS collision family. They use an additional NoSAAS premise and do not close the general Hall or endpoint/core claim. Both forms have actual witnesses (p22 and p33), so neither remaining branch can be dismissed.

Retain the endpoint/core claim as CONJECTURED with COMPUTED survival, and stop this proof route until a concrete structural interaction proves a second phase excluded from every lowSS endpoint. Studying that interaction on an explicitly declared NoSAAS branch is a bounded next question, but clean-source existence is not itself such an interaction. A failure of the stronger endpoint target would not by itself refute the original full-neighborhood inequality. No new Lean module or research promotion is justified by the finite tests alone.
