# Independent final audit: H-20261002-01

2026-10-02 JST. Separate explicitly authorized research auditor `/root/issue81_auditor`. All repository access was read only; reviewer sources, reports and logs are under `/tmp`.

## Verdict

**PASS for the exact all-length low-SS tight-avoidance and one-donor strict-capacity statements.** No blocking semantic or source defect was found. No proof change is requested. This advances the all-length low-SS class; it does not settle tight sets containing high-SS members, general deletion Hall, all-supplier capacity, orbit realization or any protected central claim.

The source is kernel accepted independently. The parent still owns the complete repository validation, Audit/G5/registry integration and GitHub workflow; this audit does not claim issue closure or merging.

## Source and dependencies

Reviewed `Recaman/SS2LowSSTight.lean`, SHA256:

`8e0bcf9497e11fafd93fb5f625f43a8b6f788ebe8d1de4f6c471e979ddc63a73`

The same hash was verified before and after review. Its single direct import is the accepted `SS2ShortTight`; the recursive local import closure has 111 modules, with no untracked member except the new module itself. The proof does not import computation outputs, other-session uncommitted drafts, or a newly defined unproved obstruction. All actual mathematical definitions are reused.

## Exact binder/conclusion audit

`lowSS_tight_avoids_donor` explicitly quantifies over periodic e, positive p, a nodup phase list B contained in [0,p), arbitrary lag, actual current-A member signs, actual member P2 and SS≤1 windows, concrete neighborhood tightness, and an arbitrary Int donor clock u/Nat length d with P2, exactly SS2 and no positive proper P2 prefix. Member minimality, S-ending, lag bounds, donor current A, period drift, NoSAAS, OS, owner distance and ambient Hall are absent.

Its conclusion excludes `phase p (u-oldestOffset (past e u d))` from the original neighborhood formed using the original lag values. It is not limited to normalized prefix neighborhoods. `hmin` covers every positive proper prefix, not a finite list of discovered positions. P2 is the pre-existing mass1/moment0 predicate, and SS counts overlapping pairs. No hypothesis is the conclusion or a definitionally equivalent avoidance assertion.

The integer and modular endpoint theorems concern the supplier's full endpoint and the donor's true oldest S. They do not claim arbitrary non-tight neighborhoods avoid the donor. `lowSS_endpoint_image` supplies a normalization function, not an assumed owner: each chosen f(b) is positive, at most original lag, is P2/low-SS, ends at a real S, has an injective phase image, and lies in original N(B). These properties are constructed from the explicit input windows.

`lowSS_strict_capacity` uses arbitrary nodup/in-range current-A low-SS U with explicit lag witnesses and one arbitrary minimal SS2 donor. It has no tightness premise and concludes only `|U|+1≤|D|`. It does not add one unit for each donor or assume donor endpoints are distinct. The absence of donor current-A is genuine and has an explicit current-S theorem application in the independent controls.

## Proof-chain audit

1. `ss2_P2_suffix_has_prefix` extends the accepted literal-AAS suffix argument to arbitrary P2 v. For Y=xA, the exact append equations give mass(Y)=−n and M(Y)+|Y|+(|Y|+|v|)n+M(A^n)=0. At n=0, the derived mass/defect constraints invoke E-366's real prefix theorem. Nonempty v is obtained from its mass1, so the output prefix is proper. At n>0, M(Y)+2|Y|≥3 and all remaining terms are nonnegative, a contradiction. No positive-moment conclusion is assumed.
2. `oldest_ne_lowSS_endpoint` derives the chronological order using SS2 versus low-SS and constructs the actual same-stream split. It then transfers the genuinely nonempty remainder into a proper donor prefix, contradicting donor minimality. It does not assume the donor ends S or that the cover is earlier.
3. `oldest_phase_ne_lowSS_endpoint` lifts modular equality to exact integer equality by shifting the supplier clock. Periodicity transports its actual A/P2/SS≤1 properties; no d<p or lag<p hypothesis is introduced.
4. `lowSS_endpoint_image` invokes E-128's same-history S-prefix witness, not its old restricted or S-ended capacity corollaries. In-window positivity/bounds justify the one-based to zero-based offset conversion f−1; hence the normalized endpoint belongs to the original neighborhood. Existing modular endpoint injection plus phase range gives nodup of the image.
5. In the tight theorem, image subset and equality of finite lengths derive surjectivity onto N(B). I inspected the cardinality helper `mem_of_subset_nodup_length_eq`: it proves this by adding a missing point to the nodup source and contradicting the cardinality bound. Thus the needed onto property is proved for this class, not an assumed general OS/Hall property.
6. `oldestOffset_getD` recursively proves a positive selector points at S. `oldestOffset_pos_of_ss_pos` derives positivity because selector0 would make the whole word an all-A replicate with SS0. `donor_oldest_is_S` checks the selector is in range and transports its bit to the actual stream clock. This supplies the entry audit's extra required edge for the strict inequality at arbitrary donor length; it does not use lag11 or the special #82 family.
7. The strict-capacity proof adjoins one actual donor S phase to the injective low-SS endpoint image. Modular endpoint disjointness gives nodup, and all entries are actual subtraction phases. A finite cardinality bound then gives precisely one unit of slack.

Both comparison directions in the chronology argument are covered by the previously proved exact oldest-cover lemma. Normalization is used in the direction supported by E-128, with f≤lag retained; no converse claim that arbitrary normalized endpoints preserve the original whole window is made. Tightness, not endpoint disjointness alone, is what upgrades endpoint-image avoidance to original-neighborhood avoidance.

## Independent theorem applications and controls

`/tmp/LowSSTightIndependent.lean` compiles using ordinary kernel checking and applies the new theorems explicitly.

- **Nonempty tight example:** p18 stream `AAAASSAAAASAAASASS`, B=[2,8,11,13], with lag11=7 and other lags3, donor u7/d11. `p18_tight_application` supplies all original hypotheses and derives avoidance. The set includes w1; no pure-AAS restriction is hidden.
- **Long supplier and donor:** p36 stream `SASASASSAAAASASASASASASSAAASSAAASASA`, supplier current15/lag15 (SS1), donor current35/length19 (minimal SS2). `p36_endpoint_application` and `p36_long_supplier_slack` apply the new endpoint and strict-capacity theorems. There are16 subtraction phases. The singleton U=[15] is not asserted tight.
- **Nonminimal A-ended low-SS member:** p28 stream `ASSASAAASASASASSAAASSAAASASA`, current7/lag7 has word AASASSA, SS1/P2, proper P2 prefix3 and an A endpoint. `p28_normalization` consumes `lowSS_endpoint_image` and proves its selected f(7)=3, with that endpoint inside original N([7])=[1,2,4]. `p28_nonminimal_supplier_slack` applies strict capacity with donor u27/d19. The original full endpoint is phase0/A and is not substituted for the normalized S endpoint. This directly exercises the newly advertised no-member-minimality/no-member-S-ending scope.
- **Donor current S:** define e36S by changing only the period36 sign at residue35 to S. The supplier window and donor past are unchanged. The kernel checks e36S35=false, and `p36_current_S_donor_slack` still applies strict capacity. No donor-current-A premise has slipped into the source.
- **Tightness removed:** p17 stream `ASSAAAASASASSSAAA`, B=[8],lag7 is a current-A low-SS w1 singleton. Its minimal SS2 donor at u0/d11 has oldest phase7 in N(B)=[1,2,7]. Neighborhood length3 differs from B length1. Thus an arbitrary low-SS singleton's interior S can cover the donor; only endpoints are unconditionally disjoint.
- **True-oldest boundary:** AAASSSASASA has oldestOffset10 despite length11. The new generic selector-bit lemma is applied to this A-ended donor and returns S at its actual selected offset.
- **Structural lemma nonvacuity:** the new generic prefix lemma is applied to the actual nonminimal P2 word AASASASASSSAAAS, decomposed as `(AASASASASSS A) ++ AAS`; it produces a proper P2 prefix. Its premises are satisfiable.

The frozen entry negative controls remain exact finite evidence for removing donor minimality or the SS2 condition. The independent entry computation reproduced 916 donors and 10,206 current-A suffix candidates without violation. Those reused finite ranges are COMPUTED evidence, not the proof. No census range was expanded for this audit.

## R/W/C/T manual assessment

Conservative declaration totals: **R/W/C/T = 3/6/0/0**. R means real structural word/image proof; W means valid transport/application/corollary; C means an unproved key obstruction supplied; T means free arithmetic or tautology.

| Class | Declarations | Reason |
|---|---|---|
| R | ss2_P2_suffix_has_prefix | New arbitrary-P2 suffix contradiction over actual words |
| R | lowSS_endpoint_image | Same-history normalization and actual injective image inside original neighborhood |
| R | oldestOffset_getD | Generic recursion connecting the existing selector to an actual S bit |
| W | oldest_ne_lowSS_endpoint; oldest_phase_ne_lowSS_endpoint | Exact same-stream and periodic consequences of the new structural lemma and accepted chronology |
| W | lowSS_tight_avoids_donor | Tight finite image becomes onto, then endpoint disjointness applies |
| W | oldestOffset_pos_of_ss_pos; donor_oldest_is_S | Accepted tail/SS facts and the generic selected-bit lemma |
| W | lowSS_strict_capacity | Actual disjoint extra phase plus finite cardinality |

These are not three separate research results. The bounded unit is the all-length low-SS avoidance mechanism and its one-unit consequence. The final corollaries are legitimate because the structural edge is actually established; they should not be advertised as new general Hall/owner theory.

## Executed verification

All final command records, exit codes and source/log hashes are in `/tmp/LowSSTightIndependentCommands.json`. Each command exited0:

- `lake env lean Recaman/SS2LowSSTight.lean`: empty `/tmp/LowSSTightSourceCheck.log`, no warnings/errors.
- `lake env lean /tmp/LowSSTightIndependent.lean`: all six named theorem applications plus concrete controls pass; `/tmp/LowSSTightIndependent.log`.
- `lake env lean /tmp/LowSSTightAxioms.lean`: all9 theorem axiom sets are subsets of `{propext, Classical.choice, Quot.sound}`; selector lemmas use only propext/Quot.sound. All6 named application theorems likewise use only permitted axioms. `/tmp/LowSSTightAxioms.log`.
- `python3 scripts/report_vacuity.py --all Recaman/SS2LowSSTight.lean`: 0/9 flagged, `/tmp/LowSSTightVacuity.log`.
- `python3 scripts/harness_gate.py --lint-module Recaman/SS2LowSSTight.lean`: 9/9 pass the substantive heuristic, `/tmp/LowSSTightLint.log`. This does not override the conservative manual classification above.

No sorryAx, user-defined axioms, `sorry`, `admit` or `native_decide` occurs in the accepted new source or successful independent controls. No failed mathematical attempt or counterexample to the exact frozen claim was found.

## Remaining limits and decision

Proceed with the restricted claim once the parent completes full repository validation and records integration. Do not infer injectivity among multiple SS2 donors; the theorem supplies one spare S phase in total. Do not infer that all tight sets have low-SS members. Nonempty tight avoidance, arbitrary-lag endpoint/slack, nonminimal/A-ended normalization, actual oldest S and donor-current-S behavior have all been independently exercised. High-SS members remain the next separate research question, requiring their own bounded statement and falsifier.
