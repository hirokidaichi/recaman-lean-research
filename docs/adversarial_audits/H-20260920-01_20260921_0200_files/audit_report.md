# Independent adversarial registration audit: E-360

## Conclusion

Final decision: **PASS for the corrected three-symbol E-360 registration**. The seven live files are byte-for-byte identical to the approved payloads, the mathematical source hashes are unchanged, and the independent post-application gates and full check pass. The initial two-symbol draft was rejected because it omitted `w1_owns_oldest`, one half of the exact W hypothesis card. No Lean theorem or mathematical premise changed in that correction.

This audit does not approve any declaration after line 358 of `Recaman/ShortTightDonorAvoidance.lean`, `SS2OldestPattern`, the used p32/p33 holdout as independent evidence, arbitrary lag, general Gate T6, E-070/E-067, an actual-orbit statement, or surjectivity of the Recaman sequence.

## Bounded question and stopping rule

Question: can the frozen Q/W core be registered as exactly one new `PROVED-LEAN` row, E-360, with a truthful official G5, no missing result from the exact cards, no hidden conclusion, no circular premise, and no novelty inflation?

Acceptance: frozen source hashes; exact next ID; cited statements exist; exact W and Q match the claim; defined premises are expanded; G1-G5/protected/lint/vacuity/Lean/full check pass; finite controls show satisfiable premises and rejected weakenings; original Q-card assumptions imply the formal Q hypotheses; no excluded theorem is imported into the claim.

Stop: reject on a source hash change, any failed gate, a formal/informal mismatch, a required unreviewed symbol, or the 02:25 JST deadline.

## Revision and source boundary

- HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`
- `Recaman/ShortTightDonorAvoidance.lean` lines 1--358: `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`
- `Recaman/OwnerFamilyLagEleven.lean`: `0bc2293b5d67f7ef5865f7a3f67b2fbf10aeb76bfa92eac9a086cc893c5846f4`
- `Recaman/PeriodicOwnerFamilyLagEleven.lean`: `a90c8f2ac7e6b98dfda4a260434d2e44d3e35781c3212f6a04b7952e9ef6b4c0`

These equal the requested frozen hashes. The repository was dirty at entry; the audit made no repository edits. All audit sources and raw outputs are under `/tmp/recaman-audit-20260921-0200-sol/`.

## Approved claim and symbols

The corrected row cites exactly:

1. `Recaman.ShortTightDonorAvoidance.w1_owns_oldest`
2. `Recaman.ShortTightDonorAvoidance.w1_next_addition`
3. `Recaman.ShortTightDonorAvoidance.short_tight_avoids_ss2_donor`

W is explicitly conditional on `OwnerFamily e mem own lag` and states both conclusions of H-20260920-01: a w1 member owns `t-7`, and `e(t+1)=true`. `OwnerFamily` expands to `window`, `addA`, `own_mem`, and `onto`; none assumes either conclusion. `own` is function-valued. Existing `ownerFamily_of_minimal` and `tight_owner_family` construct dependencies and are not counted as E-360 novelty.

Q quantifies a positive-period sign word and a nodup tight list B of in-range current-A phases with minimal P2 windows of lag 3/7/11. A minimal lag-11 SS=2 donor's `trueOldestPhase` is outside `neighborhood e p B lag`. Q has no ambient U, assumed Hall, or positive-drift premise because `short_window_hall` proves Hall for the actual short sublists.

The old H-20260917-01 Q is a corollary: `U.Nodup` plus `B.Sublist U` gives `B.Nodup`; U completeness gives in-range/current-A/P2 facts for B; minimal lag gives `hB_min`; and `u0 in U` with lag 11 gives donor P2 and minimality. Positive drift, the remaining full-U facts, assumed Hall, and `u0 notin B` are unused stronger premises.

## Adversarial attacks

- Hidden conclusion / H-to-H / x=x: absent. Harness lint calls all three cited theorems substantive. Q has only concrete hypotheses. W's defined Prop is named and expanded.
- Contradictory premises: refuted by a direct finite owner family with members `{-3,0,2}`, windows `{AAS,w1,AAS}`, owners `{-6,-7,-1}`, and next sign A. Qp8 (`SSAASAAA`, donor at 3, B={7}) satisfies every listed Q premise and has N(B)={4}, true-oldest phase 0.
- Circularity through E-351: no source call to `TightHallAugmentation`, `hall_forces_membership`, `w1_sibling_forced`, or `aas_after_w1_forced` occurs in lines 1--358. W needs E-357/E-353, not W or Q as a premise.
- Local w2 leak: the newest-S local placement has a w2 candidate at endpoint 6/offset 7. The proof does not discard it locally; `member_window_aas_or_w1` invokes E-357 `no_w2_member`. This dependency is necessary and present.
- False fixed offset 11: seven donor oldest offsets recompute to `[10,10,10,11,11,10,11]`. The p15 control has true offset 10/phase 8 while fixed offset 11 is phase 7 with A. The registered theorem uses `trueOldestPhase`.
- Tightness deletion: p11 `AAAASASASSS`, donor at 3, B={5}, N={4,9,10} covers the true oldest phase 4 and is not tight. Thus tightness is not decorative.
- SS2 deletion: p12 `AAAASAAASSSS`, donor window `AAASSSSAAAS`, B={7}, N={4} is tight and covers true oldest phase 4, but donor SS count is 3. Thus SS=2 is not decorative.
- Onto deletion: p8 `SSAAAASA` has a w1 at 7 and next S. A singleton with own(7)=0 satisfies the root window/addition/own-member facts but cannot cover all three S clocks `{6,1,0}`. A multivalued ownership relation could relate the root to all three, showing why single-valued `own` matters.
- E-240 regression: p18 `AAAASSAAAASAAASASS`, B={2,8,11,13}, N={4,5,10,17} remains a tight non-pure-AAS configuration and is not incorrectly eliminated.
- Proper-U and positive W: p20 has full U={4,7,9,19} with tight B={4,7,9}; p10 `SSAAAASAAA` has the same tight w1 triple and next A.
- Scope jumps: the row, G5, frontier, and proof-map make no finite-to-infinite, word-to-orbit, G2-to-general-T6, or issue-closure inference.

The independent premise-matrix script is newly written for this audit. `independent_controls.py` was copied from the prior 01:30 audit and independently rerun only as a regression; it is not represented as an independently designed implementation or new holdout.

## Validation

- `lake env lean Recaman/ShortTightDonorAvoidance.lean`: exit 0.
- `python3 scripts/harness_gate.py --lint-module Recaman/ShortTightDonorAvoidance.lean`: exit 0; 20/21 substantive, only `tight_w1_next_addition` a wrapper; all three E-360 symbols substantive.
- `python3 scripts/report_vacuity.py --all`: exit 0; ShortTight 0/21 flagged.
- pre-registration `bash scripts/check.sh`: exit 0; 392 jobs, 359 registry rows, 154 PROVED-LEAN, 2572 axiom reports.
- corrected isolated registry/G5 `--check-registry`: exit 0; 11 gated PROVED-LEAN rows.
- corrected isolated protected check: exit 0; 4 central rows unchanged.
- corrected official `--audit-template E-360`: exit 0; all three normalized signatures occur verbatim in G5.
- direct `#check`/`#print axioms`: exit 0; only `propext`, `Classical.choice`, `Quot.sound`.
- `qw_premise_matrix.py`: exit 0; positive Q/W and OwnerFamily witness plus drop-SS2/drop-tightness/drop-onto/multivalued-owner controls.
- reused prior checker, independently rerun: mathematical assertions pass. Its first wrapper command then failed because zsh reserves variable `status`; the output is preserved and a second run with variable `rc` exited 0.

Raw output is in `raw/`. Failed isolation setup attempts are retained: one attempted a not-yet-created workdir, one used relative copy paths from the isolated cwd, and the first isolated G5 run omitted prior audit files. These are procedural failures only; later corrected runs are separately named and retained.

## Remaining uncertainty and next decision

No mathematical or registration-meaning blocker remains for the corrected registration. At 02:21:08 JST, all seven live payloads compared byte-identically with the approved files and had the approved hashes. The three mathematical source hashes and HEAD were unchanged. Live G1--G5 reported 11 gated rows, protected claims reported 4 unchanged rows, and `git diff --check` exited 0. The independent live `./scripts/check.sh` completed at 02:21:19 JST with registry 360 / PROVED-LEAN 155, 392 jobs, and 2572 axiom declarations, exit 0. Exact output is retained in `raw/post_apply_identity_gates.raw.log` and `raw/post_apply_full_check.raw.log`.

The final scope remains limited to the three cited symbols and the exact conditional claims above. No excluded later declaration or broader mathematical conclusion is approved.

The historical missing daytime entry audit and the 01:00 first-checker source/raw retention gap remain disclosed; this audit does not rewrite them or impose a permanent human-approval condition.
