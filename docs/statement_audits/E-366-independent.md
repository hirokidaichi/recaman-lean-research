# Independent final source and semantic audit: issue #81 / E-366

2026-10-01 JST. Reviewer: separate Codex audit session `/root/issue81_auditor`, explicitly authorized by the user. Repository read only; all reviewer artifacts were written under `/tmp`.

## Verdict

**PASS for the exact issue #81 mathematical statement.** No blocking source or semantic defect was found. The result is arbitrary in donor length `d : Nat`, donor clock `u : Int`, and period `p > 0`; only the tight subset's member windows are restricted to minimal P2 lags 3,7,11. The final theorem derives Hall on the short subset internally. It neither proves nor assumes general all-lag Hall, general T6, OS, an owner-distance bound, positive drift, or actual Recamán orbit realization.

This verdict audits the source and independently checks its kernel acceptance and examples. The root session subsequently reported `./scripts/check.sh` success (394 jobs, 2,625 declarations, only allowed axioms); that whole-repository result was not independently rerun by this reviewer. The root must finish G5/registry/handoff integration and its final project checks before committing. The audit does not assert GitHub issue closure or PR merge.

## Exact reviewed sources

- `Recaman/SS2ShortTight.lean`: `9d6d7cb61be6496d5738b0136f96bf099da97aa7f182ca36563b9f6593ac4c8d`
- `Recaman/OwnerFamilyLagEleven.lean`: `0bc2293b5d67f7ef5865f7a3f67b2fbf10aeb76bfa92eac9a086cc893c5846f4`
- `Recaman/PeriodicOwnerFamilyLagEleven.lean`: `a90c8f2ac7e6b98dfda4a260434d2e44d3e35781c3212f6a04b7952e9ef6b4c0`

All hashes remained unchanged at the end of the source review. The latter two changes extract existing internal constructions into `ownerFamily_of_minimal` and `tight_owner_family`; existing exported exclusion theorem signatures remain unchanged. They are reusable proof extraction, not separate mathematical advances.

The new module's recursive import closure contains 110 local modules. The only untracked member of that closure is `SS2ShortTight.lean` itself. It does not import `SS2OldestPattern` or `ShortTightDonorAvoidance`, the original checkout's uncommitted drafts. The explicitly extracted two helper changes were reviewed in this unit.

## Binder and conclusion audit

`short_tight_avoids_donor` has exactly the phase list, periodicity, range, current-A, lag, P2, member-minimality, donor-minimality, and tightness inputs written in issue #81. `hBmin` and `hmin` quantify over **every positive proper prefix**, not merely prefixes of bounded discovered length. The conclusion uses `u - oldestOffset (past e u d)`, with the actual existing recursive largest-S-offset definition; it does not substitute `u-d`.

Neither the conclusion nor neighborhood avoidance is a hypothesis. The local `OwnerFamily` premise retains all concrete window, current-A, own-within-window, and onto conditions. Its conditional local theorem is consumed only after the final periodic theorem constructs that family from short Hall and tightness.

The donor-current-A argument `_hA` is deliberately unused: the source proves a stronger local statement. Retaining that argument in the final requested interface does not weaken the requested conclusion. Do not describe it as essential. The final proof also handles arbitrary terminal A tails directly; it does not need to consume E-363's `t≤1` corollary. E-362's defect/first-P2 results are used substantively. This is a valid strengthening of the local proof route, not a change to issue #81's quantifiers.

## Dependency and chronology audit

1. `shortOff_le_window` proves the offset lies **within the supplied window**, including lag3 and lag7 cases. `short_window_hall` maps every member injectively to an actual subtraction in its own chosen neighborhood. The image is not merely some subtraction phase or an offset bounded by 11. Thus every sublist of B has Hall, and `tight_owner_family` is applied with U=B.
2. The short-family classification applies E-357 to exclude lag11 and w2. AAS and w1 both remain. The proof does not assume the previously refuted pure-AAS claim.
3. For a w1 member at clock t, its older SS subtraction t−7 can only be covered by that member among the surviving windows; onto therefore gives `own t=t−7`. Onto at t−1 then forces an AAS member at t+2. Alternative w1 offsets 1,6,7 are each discharged by respectively inconsistent ownership and concrete sign conflicts. No next-A is assumed.
4. The word-level A-ended suffix bound derives prefix ceiling2 when the intervening mass is zero. `defect_pos_before_p2` and first-P2-ending-S then give a genuine proper P2 prefix. No defect positivity, prior moment positivity, or no-P2 conclusion is smuggled in as an input.
5. For a trailing A-run of positive length, the A-ended moment lower bound contradicts the exact append moment equation. AAS and w1 suffix exclusions hold at all word lengths and need no finite census assumption.
6. `oldestOffset_split` and `past_oldest_split` derive the all-A tail after the actual oldest S. `oldest_cover_clock_lt` proves the covering current clock precedes the donor clock: otherwise the donor's entire SS content is a suffix of a word with at most one SS. This treats the boundary/empty-intervening-word issue rather than assuming the needed clock order.
7. `past_oldest_cover_decomposition` constructs the intervening prefix from the same actual stream. It does not quantify over an unrelated convenient history. AAS proper-prefix contradiction and w1 moment contradiction then consume the real decomposition.
8. In `owner_member_avoids_oldest`, the member AAS case uses its sole S offset3. For w1, offset1 uses the forced future AAS; offset6 uses the actual embedded current-A AAS at t−3; offset7 uses the w1 endpoint exclusion. All three S offsets are covered.
9. The periodic conclusion takes a covering phase witness, forms the congruent clock `t = s+1+i`, transports its window/signs by periodicity, and contradicts the integer-line owner theorem at the exact oldest clock s. It has no upper bound on p or d and does not require d<p.

## Independent controls and counterfactuals

The entry audit independently recomputed the frozen motif census using absolute stream coordinates, and checked frozen SHA256s. It reproduced P2 counts 1,4,29,263,2724,30554 and minimal SS2 counts 0,0,7,46,216,647 at lengths 3,7,11,15,19,23, all terminal0/1 counts, and zero violations among 3,664 completed placements. These are COMPUTED finite checks on reused ranges, not proofs.

The final independent Lean file `/tmp/Issue81Independent.lean` uses ordinary kernel `decide`, not `native_decide`, and successfully checks:

- Overlap convention: `ssCount "SSS" = 2`.
- True-oldest convention: `AAASSSASASA` has length11 but oldestOffset10.
- **Minimality-removed negative control:** p16 stream `SAAASSSASASASAAA`, u=15,d=15,B=[3],lag3. The donor is P2 with SS2 and oldest15, but has P2 prefix3. N(B)=[0] and its oldest phase is0. All remaining small premises are satisfied. This prevents silently weakening donor minimality.
- **Nonempty w1 positive control and actual theorem application:** p18 stream `AAAASSAAAASAAASASS`, u=7,d=11,B=[2,8,11,13], with lag11=7 and other lags3. The premises include a w1 member and the final theorem is applied to derive avoidance, with no axiom outside the allowed set.
- **All-length positive control and actual theorem application:** p26 stream `SASASASSAAASSAAASASAASAAAA`, u=19,d=19,B=[24],lag3. All final theorem premises are constructed, including every proper donor prefix and every member prefix, and the final theorem derives avoidance. This ensures a genuinely nonempty case beyond d=11.
- **Additional independent audit negative control, SS restriction removed:** p4 `SAAA`, u=3,d=3,B=[3],lag3. P2/minimality/current-A/tightness hold, but SS=0 and oldest phase0 belongs to N(B)=[0]. This is a complete periodic counterexample, not merely a compatible local motif.
- **Additional independent audit negative control, tightness removed:** p17 `ASSAAAASASASSSAAA`, u=0,d=11,B=[8],lag7. Donor is `AAASSSASASA`, a minimal SS2 word. The member is w1/current-A/minimal. N(B)=[1,2,7] and the true oldest phase7 belongs to N(B). Tightness alone fails (3≠1). This realizes the isolated-w1 countermodel and shows why the owner-forced future AAS is needed.

The two additional counterfactuals are independent audit controls; they are not retroactively part of the frozen discovery/holdout experiment.

## R/W/C/T manual classification

R = actual word/stream structural proof; W = genuine applications/corollaries/algebraic helpers; C = unproved obstruction supplied as premise; T = free arithmetic/tautology. Conservative new-module totals: **14/9/0/0**. These are classifications of declarations, not 14 independent research advances; the unit is the one arbitrary-length avoidance theorem.

| Class | Declarations |
|---|---|
| R | short_window_hall; w1_owns_oldest; w1_future_aas_member |
| R | moment_ending_A_budget; suffix_mass_ending_A; ss2_intervening_prefix; ss2_aas_oldest_has_prefix |
| R | oldestOffset_le_length; oldestOffset_split; ssCount_append_replicate_A; oldest_cover_clock_lt; past_oldest_cover_decomposition |
| R | owner_member_avoids_oldest; short_tight_avoids_donor |
| W | shortOff_le_window; member_window_aas_or_w1; w1_next_addition |
| W | moment_replicate_A_nonneg; p2_append_A_tail_data; ss2_no_w1_oldest |
| W | past_oldest_split; oldest_not_aas_endpoint; oldest_not_w1_endpoint |

The two extracted helper constructions in existing modules are W for novelty accounting. Their full signatures and constructions are substantive and are not vacuous, but the underlying mathematics was already present.

## Executed verification

Working directory: `/Users/hirokidaichi/.codex/worktrees/p2-terminal-tail-bound/recaman-lean-research`.

- `python3 scripts/report_vacuity.py --all Recaman/SS2ShortTight.lean Recaman/OwnerFamilyLagEleven.lean Recaman/PeriodicOwnerFamilyLagEleven.lean`: new module 0/23 flagged; owner module 0/32; periodic module 3/10. The three periodic flags are pre-existing `emod_congr`, `e_of_emod_eq`, `e_phase`, not new issue claims. No fully flagged modules.
- `python3 scripts/harness_gate.py --lint-module Recaman/SS2ShortTight.lean`: 23/23 passes the substantive heuristic. Manual classification above intentionally does not equate every helper with a research result.
- `lake env lean Recaman/SS2ShortTight.lean`: exit0; source-check log empty (no errors/warnings).
- `lake env lean /tmp/Issue81Independent.lean`: exit0, all independent kernel controls and both final-theorem applications accepted.
- `lake env lean /tmp/Issue81Axioms.lean`: exit0, all 23 new theorem axiom sets are subsets of `{propext, Classical.choice, Quot.sound}`. The periodic family extraction and both independent applications have the same allowed set. No `sorryAx` or user-defined axiom appears in successful runs.
- Direct source and import inspection: no `sorry`, `admit`, `native_decide`, unsafe/partial proof surrogate, new axiom, or dependency on the other-session uncommitted draft modules.

One initial auditor-control elaboration failed because an unbounded Nat prefix binder was handed directly to `decide`; it was replaced with a proved finite-range certificate and an explicit membership conversion. This changed only the auditor's `/tmp` harness, not research source or target. The final commands above completed cleanly.

Reviewer artifacts: `/tmp/Issue81Independent.lean`, `/tmp/Issue81Independent.log`, `/tmp/Issue81Axioms.lean`, `/tmp/Issue81Axioms.log`, `/tmp/Issue81SourceCheck.log`, `/tmp/Issue81Vacuity.log`, `/tmp/Issue81Lint.log`, `/tmp/Issue81IndependentCommands.json`, `/tmp/issue81_independent_entry_counts.json`. The structured command JSON records all five final command exit codes as 0 and the corresponding source/log hashes.

## Remaining boundaries and decision

No mathematical repair or new assumption is requested. Complete the root's remaining repository integration and final project check, retain the restricted claim, and then the result is ready for commit/PR. Keep E-001/E-067/E-070/E-179 unchanged. Long-member tight B, general T6/deletion Hall, and orbit realization remain outside the result. The future research decision must target a separately falsifiable condition for longer members, not claim this theorem closes those questions.
