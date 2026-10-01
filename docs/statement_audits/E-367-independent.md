# Independent final audit: issue #82 / E-367

2026-10-01 JST. Reviewer: separate read-only Codex session `/root/issue81_auditor`. No repository files or git state were changed by this reviewer; all artifacts are under `/tmp`.

## Verdict

**PASS.** The source proves the exact fixed-SS2 abstract-word construction for every Nat parameter, with complete proper-prefix classification in both directions, actual first/oldest S, zero maximal terminal A-run, and a full-premise unbounded-span witness. No blocking source or semantic defect, extra unproved premise, or missing quantifier was found.

This is a word-only obstruction to a constant bound, not a bound or counterexample concerning a Hall owner, actual Recamán orbit, general T6 or capacity. The proof reuses E-122 padding; it is not a new general padding method. Final repository-wide checks, registry/G5 integration and GitHub state are the root session's responsibility; this audit does not claim issue closure or merge.

## Reviewed source and dependency scope

`Recaman/SS2WordOffsetSpan.lean` SHA256:

`96c943898e01037fab88dc9df6a65c3966b46e30555995ae2060972bdbc773c2`

The hash was checked before and after the review and did not change. The module directly imports only `OneSSMultiplicity` and `LagSevenDonorCoverage`. Its 96-module local import closure has no untracked dependency except the new module itself. No uncommitted draft module, issue #81 theorem, assumed owner family, or computational output file is imported into the proof.

No `sorry`, `admit`, `native_decide`, user-defined axiom, unsafe proof surrogate or partial proof definition occurs in the new source.

## Binder and semantics audit

The only construction parameters are `k : Nat`, actual finite Bool words and their prefix lengths. `word k` is definitionally `(SA)^k ++ SAAASSAAASS ++ (AS)^(3*k)` using the pre-existing `alt`, `mass`, `moment`, `P2`, `ssCount`, `NoSAAS` and `oldestOffset` definitions.

`proper_mass_one_prefix` quantifies over every proper prefix index d and derives all four position/moment alternatives from actual mass-one content. Its hypotheses are exactly properness and mass-one, not the desired table or a positivity invariant. The terminal-block moment is correctly an Int subtraction, and `i<3*k` is retained. `proper_mass_one_positions_iff` proves the converse by constructing the real prefixes, not merely restating the forward implication. Its left side includes properness and mass-one; its right side cannot accidentally include the complete word. At k=0 the terminal-block alternative has no witness.

`word_minimum` excludes every d strictly smaller than word length, including d=0; this is a harmless strengthening of positive proper minimality. The unbounded theorem uses the requested positive-index version. No cutoff on k, d, or bound C0 appears.

`history_noSAAS` proves the original decomposition-based predicate on `true :: word k`; the leading A is explicit. This is not a substitute predicate over internal core positions only. `word_ssCount` uses the original overlapping SS count.

`word_newest_S` asserts actual index0 is S. `word_oldestOffset` uses the existing recursive largest-S-offset function. `word_true_oldest_S` additionally proves the selected position holds S and every index at/after that one-based offset is outside the word. `word_terminal_length` uses actual reverse.takeWhile id. Thus the span is measured between two real S positions; no unconstrained marker or endpoint standing in for an S is involved.

`exists_unbounded_span C0` chooses k=C0 and carries P2, all proper-prefix exclusion, SS2, NoSAAS with current A, length, newest-S bit, oldestOffset, oldest-S bit, maximal terminal A-run0, exact span8k+10, and strict span>C0. This suffices to refute a uniform constant bound from these word properties. It makes no assertion that index1 is an owner or that any V_k occurs in the Recamán sequence.

## Proof-chain audit

1. Existing append and alternating mass/moment equations give total mass1 and moment0 for the fixed core and precisely 3k trailing AS pairs.
2. `alt_A_zero_prefix` is a genuine induction on the alternating word and prefix index; it proves every mass-zero bounded AS prefix consists of i complete pairs. This supplies the entry audit's main missing edge rather than inferring prefix completeness from doubled-moment arithmetic alone.
3. `core_mass_one_prefix` exhausts all indices0..11. Only 3,5,7,11 have mass1, with moments4,3,4,0. The bound11 is appropriate for the fixed literal core, not a cutoff on the family.
4. The forward prefix proof splits at d≤2k and r=d−2k≤11. The first region has nonpositive mass. The core region shifts mass-one moment by3k. At r=11 properness forces k>0 and realizes i=0. In the remaining region the alternating-prefix lemma gives a concrete i, and properness gives i<3k. The result is exhaustive.
5. The converse realizes all three core positions and each i<3k by exact take identities. Thus both directions preserve the intended positions and moments.
6. Strictly positive proper mass-one moments contradict P2 moment0, giving all-k minimality.
7. SA/AS SS lemmas preserve the count through both joins. The SAAS-count lemmas are used with the actual S-headed/S-ended core, so their endpoint conditions hold. Literal core SAAS-count0 plus the established positive-count-of-occurrence lemma proves whole-word NoSAAS. Adding current A cannot create a pattern starting at that A; occurrences further inside are excluded by the whole-word result.
8. `word_ends_S` handles k=0 separately and splits off the final AS pair for k+1. Induction proves oldestOffset(u++[S])=|u|+1, connecting the terminal bit to the real selector. Last-S then proves maximal A-tail0. These are exact all-word arguments and do not rely on finite data.

## Independent kernel applications and counterfactual controls

`/tmp/Issue82Independent.lean` imports the new module and was accepted by Lean. It deliberately applies the family theorems rather than only recomputing examples:

- Literal k0 and k1 words agree with `SAAASSAAASS` and `SASAAASSAAASSASASAS`; k7 has length67.
- `checked_family k` consumes P2, every proper prefix, SS2, current-A NoSAAS, newest S, true oldest S and zero terminal length theorems. Boundary k0 minimality and k1 history NoSAAS are instantiated. k7 has oldestOffset67, actual bit66=S and bit67 absent.
- The converse classification at k7 constructs proper mass-one prefix17 (core case) and prefix65 (last proper trailing-pair case). The forward classification then derives moments25 and1 respectively. At k0, the complete-core index11 is explicitly excluded from the proper classification.
- `bound_1000` consumes `exists_unbounded_span 1000` and retains P2, minimality, SS2, current-A NoSAAS and terminal-A0 together with span>1000. This is a theorem application, not a new finite census.
- The wrong-core word `SA ++ AAASSSASASA ++ AS^3` is separately kernel-checked to be P2/SS2 of length19 but have P2 prefix7. It is not passed off as a member of the proved family.
- The extra-AS word `SA ++ core ++ AS^4` has length21, mass1, moment−1, and P2 prefix19. The kernel checks both the earlier P2 and failure of total P2.
- `ssCount "SSS"=2` checks the overlap convention.

The finite ranges from entry review remain reused k0..80. No fresh holdout or expanded census is claimed. The entry report and numeric-list checker independently checked all 26,811 proper prefix lengths and 9,963 mass-one visits in those ranges, including both joins and k0.

## Manual R/W/C/T classification

R = real structural word proof, W = imported/proved corollary or arithmetic helper over actual words, C = unproved obstruction assumed, T = free arithmetic/tautology. Conservative totals for the 23 declarations: **R/W/C/T = 5/18/0/0**.

| Class | Declarations | Reason |
|---|---|---|
| R | alt_A_zero_prefix | All-prefix induction deriving complete AS pairs |
| R | core_mass_one_prefix | Complete finite classification of the fixed core |
| R | proper_mass_one_prefix | Exhaustive all-k three-region classification with moments |
| R | proper_mass_one_positions_iff | Converse realizes every listed proper prefix |
| R | oldestOffset_append_S | Word induction tying the existing selector to the actual final S |
| W | core_mass; core_moment; core_length | Kernel-evaluated fixed-core facts |
| W | word_length; word_P2; alt_take_pairs | Existing append/alternating identities and arithmetic |
| W | word_minimum | Positive-moment consequence of the new prefix classification |
| W | word_ssCount; word_saasCount_zero; word_noSAAS; history_noSAAS | Existing padding/occurrence lemmas applied with the correct fixed-core joins |
| W | word_newest_S; word_ends_S | Direct fixed/alternating endpoint consequences |
| W | word_oldestOffset; word_true_oldest_S; word_terminal_length; word_span | Consequences of actual S termination, length and selector lemma |
| W | exists_unbounded_span | Full-conjunction corollary with witness k=C0 |

These are classifications, not five independent research advances. The research unit is the exact fixed-SS2 family. The unbounded conjunction is an appropriate corollary of substantive prefix and endpoint proofs; it does not need to be advertised as a novel padding method.

## Verification and axioms

Exact commands, exit codes and SHA256s are in `/tmp/Issue82IndependentCommands.json`. All five final commands exited0:

- `lake env lean Recaman/SS2WordOffsetSpan.lean`: no errors or warnings; empty `/tmp/Issue82SourceCheck.log`.
- `lake env lean /tmp/Issue82Independent.lean`: all independent controls and theorem applications pass; `/tmp/Issue82Independent.log`.
- `lake env lean /tmp/Issue82Axioms.lean`: all 23 theorem axiom sets are subsets of `{propext, Classical.choice, Quot.sound}`; the three literal core facts use no axioms. `checked_family` and `bound_1000` have only the same allowed set. No sorryAx occurs in the successful controls. Log: `/tmp/Issue82Axioms.log`.
- `python3 scripts/report_vacuity.py --all Recaman/SS2WordOffsetSpan.lean`: 0/23 flagged; `/tmp/Issue82Vacuity.log`.
- `python3 scripts/harness_gate.py --lint-module Recaman/SS2WordOffsetSpan.lean`: 20/23 meet the substantive heuristic; word_length, word_newest_S and word_terminal_length are detected wrappers. This is acceptable because the registered result contains genuine all-k prefix proofs. Log: `/tmp/Issue82Lint.log`.

One initial auditor control used malformed pipeline notation inside a proposition; its parser error was corrected under `/tmp`. No research source, theorem, frozen protocol or hypothesis was changed. All final controls compile cleanly.

## Decision and limits

Proceed with the exact restricted result after the root completes project-wide checks and record integration. No source repair is requested. The evidence excludes a word-only uniform bound on newest-to-oldest S distance even with minimal P2, SS2, NoSAAS, explicit current A and zero terminal A-run. It does not refute any proposed distance bound that additionally requires the marked S to be supplied by an actual owner family. Any such next research question needs its own precise owner condition and falsifier; central claims remain unchanged.
