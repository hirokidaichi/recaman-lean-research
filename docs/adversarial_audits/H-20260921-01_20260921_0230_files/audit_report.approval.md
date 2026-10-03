# H-20260921-01 independent adversarial audit

## Verdict

**Mathematical and semantic verdict: pass (`合格`) for the exact restricted corollary.**

`Recaman.ShortTightDonorAvoidance.short_supply_donor_deletion` is nonvacuous and its
`deletedNeighborhood` conclusion is the exact Hall inequality after removing the donor window's
true-oldest subtraction phase. It is not a new mathematical input. It is the already registered
E-360 tight avoidance Q combined with `short_window_hall` and the pre-existing generic deletion
lemmas from `TwoSSAvoidTight`.

Recommended card status is **`PROVED-LEAN`**, because the exact declaration is accepted by Lean and
is already included in `Recaman/Audit.lean`. This recommendation does **not** authorize or justify a
new evidence-registry row. It should be recorded as an audited restricted corollary of E-360/E-188,
with no frontier advance or new-input claim. Parent retains the actual promotion decision.

## Frozen target

- HEAD: `08c08565c743f39350c9b959e1df7d30aa1cae5d`.
- `Recaman/ShortTightDonorAvoidance.lean` SHA-256:
  `bb12f35acc8e48c584cead52d675e36b034afda22f0f28ecfd245031f70fee85`.
- Registry SHA-256: `012c7e42974931c115efc2e64d9a254deaeb58ff78ac440af713cdb1a497a076`.
- Exact source is lines 363-391 and is captured in `target_signature.repo_snapshot.raw.log`.
- The theorem quantifies periodic `e`, positive `p`, a nodup list `U`, a lag function, a natural
  anchor `u0`, and a list sublist `B` of `U`. Every member of all of `U` must be in range, current A,
  and have a minimal P2 lag exactly 3, 7, or 11. The length-11 window at `u0` must be minimal P2 with
  `ssCount = 2`. The conclusion is
  `B.length <= |deletedNeighborhood e p B lag (trueOldestPhase e p u0 11)|`.
- It does not assume `u0 in U`, that `U` is complete, positive period mass, an actual Recaman orbit,
  or any lag at least 15. Those omissions are scope boundaries, not silently supplied facts.

## Proof and dependency audit

The proof restricts the all-`U` hypotheses to `B`, obtains ordinary Hall for `B` from
`short_window_hall`, then splits on `|N(B)| = |B|`.

- Tight branch: E-360 Q (`short_tight_avoids_ss2_donor`) proves the true-oldest phase is not in
  `N(B)`; `deleted_hall_of_not_mem` makes deletion a no-op.
- Nontight branch: ordinary Hall plus inequality gives strict slack; `deleted_hall_of_slack` absorbs
  deletion of at most one nodup neighborhood element.

There is no conclusion hypothesis, hidden unproved `Prop`, contradiction premise, `H -> H`, `x=x`,
pure free arithmetic theorem, or circular use of the target. `deletedNeighborhood` is literally
`neighborhood.filter (y != s)`. `trueOldestPhase` uses `oldestOffset`, not fixed offset 11.
`neighborhood` is a nodup list of actual subtraction phases, so the generic one-element deletion
bound has the claimed meaning.

The harness calls the theorem syntactically substantive, but that does not establish novelty. The
case split is useful packaging; donor-specific content is entirely Q. Ambient `U` itself can be
eliminated in favor of assumptions directly on `B`, confirming that universal-sublist presentation
adds no new inequality or classification.

## Fixed controls

The final independent checker was written for this audit, uses no seed, and was rerun from its saved
source. All target premises and conclusions were recomputed rather than copied from the writer.

- p8 `SSAASAAA`, full short `U={3,7}`, donor `u0=3`: lags are 11 and 3; all range/current-A/P2/
  minimal assumptions hold. For donor-containing `B={3}` and `B={3,7}`,
  `N(B)={0,1,4}` and true-oldest phase 0 is really removed, leaving `{1,4}`. Hall survives in both.
- Same p8 word, tight `B={7}`: `N(B)={4}`, true oldest 0 is absent, exercising the tight/Q branch.
- p11 `AAAASASASSS`, donor 3, full short `U={2,3,5}`: all target premises hold. The named nontight
  `B={5}` has `N={4,9,10}` and deletion gives `{9,10}`. This is a positive slack example, not a Q
  counterexample.
- E-240 p18 `AAAASSAAAASAAASASS`, donor 7: full short `U={2,7,8,11,13}` satisfies all premises;
  the known tight `B={2,8,11,13}` has `N={4,5,10,17}` and avoids true oldest 14. All 32 sublists of
  this `U` satisfy the deleted Hall conclusion. The refuted pure-AAS route is not used.
- False-offset p15 `AAAASAAASASASSS`, donor 3: true oldest offset is 10, phase 8. With the true
  offset, all target premises and all 16 sublist conclusions pass. Fixed offset 11 would instead be
  phase 7, which is A, so filtering phase 7 is a no-op and is not evidence for deletion of the
  intended oldest subtraction. The Hall inequality may still pass under that wrong no-op; this
  control distinguishes semantics, not merely the Boolean conclusion. Across the seven donor words
  the independently recomputed oldest offsets are `[10,10,10,11,11,10,11]`.
- SS=3 p12 `AAAASAAASSSS`, candidate donor 3, `U=B={2,5,7}`: all U assumptions and donor P2/
  minimality hold, but `ssCount=3`, not 2. `N={4,10,11}` and deleting oldest 4 leaves `{10,11}`;
  `3 <= 2` is false. This is a valid one-premise weakening counterexample, not a target refutation.
- Empty `B` passes. Duplicate `U` is excluded. The p10 W and p20 proper-U controls have the expected
  short supplies but no specified/minimal lag-11 SS2 donor, so they are nonapplicability controls.

No finite control is used to infer the universal theorem; universality comes from the Lean proof.

## Automated checks

- Vacuity: `0/21` flagged, exit 0.
- Harness lint: `20/21` substantive; target marked substantive, exit 0.
- Direct Lean module check: exit 0.
- Independent full `./scripts/check.sh`: exit 0, 392 jobs, 2572 axiom reports, allowed axioms only.
- Writer's repaired packet full check independently agrees: exit 0, 392 jobs, 2572 reports.

Automatic passes support source integrity but are not the semantic verdict.

## Packet corrections

The first writer packet falsely labeled an ASCII-normalized transcription as raw `sed` output,
omitted the replay source, and presented a check summary as raw output. This was rejected. The writer
preserved the bad transcription as `target_signature.ascii_rejected.log`, replaced it with actual
Unicode source, saved `control_replay.py` plus command metadata and unedited stdout, labeled the
human digest as a summary, and saved full combined check output. The repaired target signature
matches the source; the normalized definition excerpts are now explicitly marked non-verbatim.

## What is and is not added beyond E-360

Added: a convenient simultaneous Hall-after-one-deletion corollary for every list sublist of a
chosen all-short minimal supply list, covering both tight avoidance and slack absorption.

Not added: any new donor avoidance fact; completeness of `U`; `u0 in U`; positive drift; lag 15 or
larger; a full all-lag supply theorem; general Gate T6/G2; E-070 or E-067; finite-to-infinite or
periodic-to-actual-orbit transfer; Recaman surjectivity or nonsurjectivity.

## Remaining uncertainty and decision

No mathematical uncertainty remains for this exact Lean statement at the frozen hash. The general
all-lag/deletion problem and actual-orbit consequences remain wholly open. Daytime pre-formalization
independent entry audit and the 01:00 first-checker source/raw gap remain historical process defects;
this post-hoc audit must not relabel them as completed.

Procedure: **`合格`** for the corrected packet and exact corollary. Promote the hypothesis card to
`PROVED-LEAN` only with the explicit annotations “existing audited corollary”, “no new registry row”,
and “no new mathematical input”. Do not register a new frontier result, and do not extend E-360 to
general T6.
