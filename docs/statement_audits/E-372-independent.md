# E-372 independent semantic audit

- Reviewer: separate Codex `sss_semantic_audit` session, 2026-10-11.
- Result: **PASS** for the exact local statement, not full E-370.
- Reviewed module: `Recaman/SS2InternalSSS.lean`.
- SHA256: `50c2fb72b83027939dd9653f75f3f4d9153809cd76eff494af0d67ef6c11e249`.
- This report is transcribed by the parent from the independent review.
  The reviewer did not edit any source or rerun the frozen holdout.

## Binder and dependency review

All seven declarations refer to concrete words or actual same-stream
windows. `P2` is the existing mass-one/moment-zero predicate; `past` is
newest first; SS count includes overlapping edges. No assumed exclusion,
matching, Hall condition or conclusion-level unproved Prop occurs.

The first SSS clock cannot be a low-SS P2 endpoint: P2 forces lag≥3 and
the actual oldest triple contributes two edges. For phase separation,
equal phases of s and q transport q+1 to s+1. Edge starts s,q,q+1 are
distinct and in the same window. In particular q=s+1 gives SSSS and
three edges; the list helper correctly includes the shared-vertex case
j=i+2. The final donor theorem composes this with E-368 oldest-S exclusion.

| Theorem suffix | R/W/C/T class |
|---|---|
| ssCount_append_SSS | W |
| internal_sss_ne_lowSS_endpoint | R |
| internal_sss_phase_ne_lowSS_endpoint | W |
| ssCount_pos_of_pair | R |
| ss2_triple_no_later_pair | R |
| internal_sss_phase_ne_earlier_S | R |
| donor_internal_sss_two_excluded_phases | W |

Conservative total: **4/3/0/0** (real content / wrapper / conclusion-level
conditional scaffold / tautology). Seven declarations are not seven
independent advances.

## Independent controls

Donor nonvacuity, kernel checked: chronological ASASASSSAAA, p=11,u=d=11,
past AAASSSASASA, P2, SS=2, no positive proper P2 prefix, oldestOffset=10,
s=1, internal q=5. The same stream at t=10,l=3 is current-A lowSS AAS,
with endpoint 7 distinct from both excluded phases 1 and 5.
The reproducible Lean stdin source is saved in
`docs/data/internal_sss_phase_20261011/independent_controls.lean.txt`.

Wrapping nonvacuity: chronological SASSSA, u=d=7, s=0,q=2 has SS=2 and
negative period mass; neither d≤p nor positive mass is necessary.

Independent weakened-statement countermodels (not full-premise failures):

| Removed condition | Stream, parameters | Failure |
|---|---|---|
| u-d≤s | all S, p=1,u=4,d=3,s=0,q=1 | same phase, earlier S outside window |
| s<q | all S, p=1,u=d=3,s=q=0 | the two clocks coincide |
| q+2<u | all S, p=1,u=d=3,s=0,q=1 | third triple sign lies outside window |
| SS≤2 | all S, p=1,u=d=4,s=0,q=1 | three SS edges |
| designated periodicity | SAASSS repeated with period6; designated p=3,u=d=6,s=0,q=3 | phases collide despite exactly two edges |
| p>0 | same stream, p=0,u=0,d=6,s=-6,q=-3 | phase0 maps both negative clocks to0 |

The reviewer also exhaustively checked the q=s+1 boundary in binary words
of lengths4..10: 769 eligible sign placements, all with at least3 SS edges.
This auxiliary enumeration is exploratory, not additional frozen holdout.

## Commands and results

- `python3 scripts/report_vacuity.py --all Recaman/SS2InternalSSS.lean`:
  0/7 flagged, exit0.
- `python3 scripts/harness_gate.py --lint-module Recaman/SS2InternalSSS.lean`:
  7/7 substantive, exit0 (heuristic).
- `python3 experiments/internal_sss_phase_probe.py controls`: the three
  intended weakening failures, exit0.
- `lake env lean --stdin` with the final source, independent concrete
  controls and seven `#print axioms`: exit0; only propext, Quot.sound,
  Classical.choice. One unused-simp-argument warning was in a control,
  not the research module.
- Saved discovery/holdout outputs and probe SHA256 were inspected: 37 and
  6,857 pairs, zero violations. Holdout was not repeated.

## Limits

Do not claim q=s solved, a two-donor collision classification, neighborhood
cardinality, general Hall/T6, separation from every S inside arbitrary
low-SS windows, an actual Recamán orbit result, or surjectivity. Only
endpoint phases are excluded. E-370 remains PROVED-PAPER.
