# Independent entry audit: issue #82 / H-20261001-07

2026-10-01 JST. Separate read-only audit session `/root/issue81_auditor`; reused as explicitly authorized independent auditor. Base `f6594be0bf04ea1baf6fb460a69c0c6b05dc1379`, worktree `/Users/hirokidaichi/.codex/worktrees/p2-terminal-tail-bound/recaman-lean-research`. No repository files or git state were modified.

**Verdict: PASS to begin the exact all-k Lean formalization.** The paper's mathematical argument is complete at the informal level. No counterexample or additional mathematical premise is needed. This is an entry verdict; final source and semantic/kernel audit remain required.

## Exact scope

C=SAAASSAAASS, V_k=(SA)^k C (AS)^(3k), for every k:Nat, with newest-first A=+1/S=−1. The intended conjunction is P2, absence of every positive proper P2 prefix, exactly two overlapping SS pairs, NoSAAS of A::V_k, length8k+11, actual newest-S offset1, actual oldest-S offset8k+11, maximal terminal A-run0, and unbounded offset span8k+10. The newest S is a literal bit of the word, not a Hall owner. There is no owner map, onto family, tightness, periodicity or actual-orbit assertion.

For any bound C0, choosing k=C0 proves span>C0. The card phrase 'an explicit k exceeds C0' should be read/clarified as 'an explicit k makes the span exceed C0': k itself equals C0 in the proposed witness. This is a prose ambiguity, not a mathematical obstruction or a change of the intended claim.

## Independent mathematical challenge

The sum identities check: mass core=1, moment core=0, |core|=11. Left SA padding has mass0 and momentk; shifting core contributes2k; right3k AS pairs contribute−3k. Total moment0 follows for every k.

The decisive part is minimality rather than this arithmetic. The proposed complete prefix partition is correct:

1. Prefix lengths d≤2k lie wholly inside (SA)^k and have mass−1 or0, never1.
2. For 2k<d<2k+11, the complete core table gives mass1 exactly at d=2k+3,2k+5,2k+7, with global moments3k+4,3k+3,3k+4.
3. From d=2k+11 through the full endpoint, mass1 occurs exactly at d=2k+11+2i, 0≤i≤3k. Moment=3k−i. The full endpoint is i=3k; every proper visit has i<3k and positive moment. Odd partial AS pairs have mass2. At k=0 no index in this third region is proper.

The converse position classification is true, as is the direct classification. It must be proved, not omitted after proving only P2/minimality. To obtain an explicit pair index i from a zero-mass AS prefix, establish the even complete-pair form or equivalent exact take identity. The existing `alt_A_zero_prefix_moment` proves a useful doubled-moment equation; alone it should not be described as the exhaustive position classification.

NoSAAS is literal substring absence (`SSFreeSupply.NoSAAS` quantifies over all decompositions). Internal core four-grams are SAAA,AAAS,AASS,ASSA,SSAA. The current-A plus SA block is alternating. All possible left-join four-grams are ASAA,SASA,ASAS; all right-join four-grams are ASSA,SSAS,SASA. None is SAAS. A length4 substring cannot meet both joins because core length11. At k=0 the right join is absent and the only left-join crossing is ASAA. Existing `saasCount_pre_alt` requires an S-headed suffix and `saasCount_post_alt` an S-ended prefix; this fixed core satisfies both. Preserve those endpoint conditions when invoking the lemmas.

SS counts include overlap. Alternating pads introduce none, the left A|S and right S|A joins introduce none, and the fixed core has two. The current A likewise introduces no SS. First and last signs are genuinely S, including k=0. A generic appended-S oldestOffset lemma or direct recursion can establish the true oldest offset equals the whole length; reverse.takeWhile id then gives the maximal A-tail0. Do not replace these assertions by a marker variable or merely a chosen endpoint.

## Frozen evidence and independent replay

The new frozen protocol, experiment script, and imported `terminal_a_budget.py` SHA256 values match PRE_RUN_SHA256SUMS. The execution-base file correctly records f6594be while the unchanged script intentionally embeds historical base cbe51b7. Discovery k0..10 and holdout k11..80 are explicitly reused; both new replay JSON objects equal the corresponding old JSON results.

An independent numeric-list implementation used direct prefix sums, rather than importing either experiment's checker. Command:

`python3 /tmp/Issue82EntryIndependent.py`

Exit0. Exact summary in `/tmp/Issue82EntryIndependent.json`: 81 words, 26,811 proper prefix lengths (including d=0), 9,963 mass-one visits, every position/moment table matched, no failed premise, exact join sets as above. Boundary k0 length11/span10 and endpoint k80 length651/span650. No census extension was performed, and these finite checks are COMPUTED, not the all-k proof.

`lake env lean docs/data/ss2_word_offset_span_20261001/core_controls.lean` also exited0; `/tmp/Issue82EntryCoreControls.log` is empty. This kernel-checks the fixed core table and local NoSAAS/endpoint controls, not yet the all-k theorem.

The predeclared negative controls match: wrong core AAASSSASASA at k1 gives P2 prefixes7 and19, so minimality fails despite total P2/SS2. One extra AS pair gives length21, mass1, moment−1, and earlier P2 prefix19. Arbitrary P2 cores and arbitrary right-padding counts are therefore not valid implicit generalizations.

## Missing implementation edges and continuation gate

No new mathematical conjecture is needed. Formalization must still produce:

- complete and converse proper mass-one prefix classification with exact moments;
- all-prefix minimality without an externally assumed positivity invariant;
- all-k NoSAAS with both joins, including k0;
- actual first/last-S/oldestOffset and terminal-run equalities;
- an unbounded witness carrying the entire substantive conjunction.

Continue within the predeclared 90-minute route gate. Stop on a genuine counterexample, any unproved prerequisite, a cutoff or finite-certificate substitute for the all-k proof, or a need to weaken the conjunction. Do not repair the core or silently redefine the marked S after observing a failure. Preserve E-122 as the origin of the padding construction; the new unit is the fixed-SS2 minimal family and its word-only span consequence. Protected claims and general #73 remain unchanged.

The core mathematical route is feasible using existing append/alt/SS/SAAS lemmas and finite core facts; prefix completeness is the weakest unfinished edge. A final separate source/RWCT audit and theorem-applied kernel controls are still required after implementation.
