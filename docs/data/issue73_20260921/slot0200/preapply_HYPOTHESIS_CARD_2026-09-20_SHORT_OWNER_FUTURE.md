# Hypothesis card: a short-window owner forces the next addition

- ID: `H-20260920-01`
- Owner: current daytime research session (proposer, falsifier, formalizer, auditor are separate passes)
- Created: 2026-09-20 14:29 JST
- Status: `CONJECTURED`
- Source revision: `08c08565c743f39350c9b959e1df7d30aa1cae5d`
- Deadline: 2026-09-20 16:30 JST
- Research branch: issue #73, local input W for short tight donor avoidance.

## Exact statement

For every `e : Int → Bool`, `mem : Int → Prop`, `own : Int → Int`,
`lag : Int → Nat`, assume the existing `OwnerFamilyLagEleven.OwnerFamily e mem own lag`.
For every integer `t`, if `mem t` and `past e t (lag t) = w1 = SAAAASS`, then
`own t = t - 7` and `e (t + 1) = true`.

The family assumptions are exactly: member windows are among the twenty minimal P2 words
of lengths 3/7/11; each member is an addition; each member owns one subtraction in its window;
every subtraction in every member window is owned by a member. No injectivity, periodicity,
full supply set, positive drift, future symbol or oldest-S ownership is assumed.

Periodic consequence sought: with the existing E-359 hypotheses (periodicity, nodup U,
Hall on U, tight sublist B, phase bounds, additions and minimal P2 windows of lengths 3/7/11),
`phase p t ∈ B` and `past e t (lag (phase p t)) = w1` imply `e (t+1)=true`.
If the local proof succeeds, compose this with E-348/E-350 to prove that the true oldest S
of a lag-11 SS=2 donor is not in N(B). Hall remains a hypothesis. No general Gate T6,
unrestricted-lag capacity, orbit generation, surjectivity or issue closure is claimed.

## Why it would matter

- This supplies the missing future sign in H-20260917-01 without using E-351's
  `aas_after_w1_forced`, which already assumes that sign.
- E-356 observed the w1 three-member pattern; E-357 only formalized exclusions of lag 11
  and w2. The proposed future sign and donor avoidance are additional conclusions.
- The exact local ownership constraint is independent of last night's rejected output
  parser and empty proper-U census. Neither implementation is repaired or reused as a gate.

## Dependencies and paper-proof target

1. E-357 excludes lag-11 and w2 members, leaving AAS and w1.
2. The older S at t-7 belongs to an SS pair. E-353 forces its covering short member
   to be w1 at t, hence `own t=t-7` by the onto property.
3. The newest S at t-1 must have an owner. Exhaust the AAS/w1 covering offsets.
   AAS gives the owner t+2 and sign A at t+1. The three w1 offsets either reuse t
   (which already owns t-7) or clash with an A bit of the root.
4. E-358 plus the already implemented periodic lift supplies this actual owner family.
5. A donor-covering lag-7 window is one of E-348's three placements, each forcing
   S at that window's next clock, contradicting step 3. AAS coverage is E-350.

The weakest new input is step 3. None of OS, motif decomposition, W or Q is a premise.

## Falsification plan (fixed before new computation)

- Discovery: exhaust all local placements of AAS/w1/w2 covering root S offsets 7 and 1;
  root clock 0; explicitly include the addition bit at each owner clock.
- Boundary: independently re-evaluate translated copies at negative and positive clocks;
  periodic phase identifications in the known p=8/p=10 and E-240 examples.
- Weakened history: remove onto and exhibit a one-member model with next S; remove
  single-valued ownership and exhibit why one member can then consume all three S values.
  Distinguish these from counterexamples to the full statement.
- Regression: known p10 `SSAAAASAAA`, E-240, false donor offset 11 and SS≥3 controls.
- Holdout: the previous card's p32/33 sample is not touched during local discovery.
  Any new sample run will be frozen in a separate protocol before execution. Exhaustive
  local classification and kernel proof do not depend on statistical extrapolation.
- One permitted repair: only after a specific counterexample identifies a missing premise;
  no changes merely to exclude that example or impose a period cutoff.
- Stop: counterexample to full statement; circular dependency; need to assume future A;
  or no audited proof by the session deadline. Do not replace W by a tautology.

## Acceptance and evidence

Acceptance: a complete local argument plus a Lean statement with the exact scope above,
nonempty examples and negative controls, lint, statement audit and `./scripts/check.sh`.
Computation alone is not a proof. A separate-agent audit has not been performed in this
daytime session; the old weekly card and its independent-audit status are not overwritten.

| Time | Label | Command / artifact | Result |
|---|---|---|---|
| 14:29 JST | `CONJECTURED` | source revision above; E-348/350/353/357/358/359 source read | statement and local proof obligations fixed |
| 14:31 JST | `COMPUTED` | `python3 -u experiments/issue73_20260920/short_owner_future.py`; `data/issue73_20260920/daytime/local_regression.jsonl` | unique older-S owner; newest-S has AAS at 2, w1 at 0, and w2 at 6; E-357 is required to exclude w2. Three donor overlaps all force next S. Positive finite family and known periodic controls pass |

### Falsifier correction and complete local paper argument

The first probe assertion incorrectly omitted the locally compatible w2 owner at clock 6,
offset 7. Its source and failing output are preserved as `short_owner_future_v1.py` and
`local_v1_failure.log`. This was an error in the expected local table, not a counterexample
to the stated owner-family implication: step 1 explicitly uses E-357 to exclude all w2
members. The corrected table retains w2 and only removes it at that stated dependency.
No hypothesis, range or conclusion was changed. No overnight failed gate was repaired.

After E-357, every member window is AAS or w1. Put the root at t. Its S clocks are
t-7, t-6, t-1 and its A clocks include t-5,t-4,t-3,t-2,t.
The pair at t-7,t-6 and E-353 show that a short window owning t-7 is w1 ending at t;
thus onto forces own(t)=t-7. Onto at t-1 supplies another owner v. For an AAS owner,
v-3=t-1, hence v=t+2 and its bit v-1=t+1 is A. A w1 owner has S offsets 1,6,7.
Offset 1 gives v=t and contradicts own(t)=t-7. Offset 6 gives v=t+5, whose S bit
v-7=t-2 contradicts the root's A. Offset 7 gives v=t+6, whose S bit v-6=t contradicts
the root addition. These exhaust every owner. This proves the local implication.
It uses neither injectivity nor a finite set of members.

The nonempty finite model has members {-3,0,2}, words {AAS,w1,AAS}, owners {-6,-7,-1}.
Deleting onto permits the singleton {0}, own(0)=-7 and e(1)=S. Replacing own by a
multi-valued relation permits the root to own all three S values, again with e(1)=S.
These are weakened-model counterexamples only. E-240 remains allowed.
The concrete period-20 cycle `SSAAAASAAAAAAAAASAAA` has full supply {4,7,9,19};
B={4,7,9} is a nonempty tight w1 triple. This demonstrates a proper-U example without
extending last night's empty census. The original full-U condition is not used by the paper
argument; this is a theorem-strengthening candidate, not an assumed deletion of a premise.

## Semantic audit

- Does the final theorem mention the actual sign word and windows? Pending.
- Is future A, oldest ownership, or donor avoidance hidden in a premise? Must be no.
- Are the family premises supplied from periodic tightness and Hall? Pending.
- Nonvacuous: the known w1 triple is the positive control; next-S singleton without onto
  is the negative control.
- General periodic Hall and all-lag conclusions remain outside scope.

## Decision

Proceed with falsification, then paper proof; formalize only if the local obligations pass.
Do not promote the prior Q/W card or frozen overnight artifacts in this session.

## Bounded extension fixed at 14:42 JST: discharge Hall on the short subset itself

The source candidate for W and Q compiles, and the full repository check passes. Before
extending it, fix the next exact obligation: for every periodic e of period p>0 and every
nodup list A of addition phases below p with P2 windows of lengths d≤11, show
`A.length ≤ (neighborhood e p A lag).length` using the already proved short injection
`ShortReservoirCapacity.short_phase_injective`.

The new obligation is **locality**, not a new selector: prove
`1 ≤ shortOff e u ≤ lag u`. Together with `short_image_is_S`, this puts the existing
injective image of A inside N(A), not merely inside all subtraction phases D.
P2 windows with lag 3/7/11 are the exhaustive small cases. For lag3 the existing
phi7 rule chooses offset3; for lag7 its bound is7; for lag11 its bound is11.
The abstract countermodel A={a}, N(A)=empty, D={s}, injection a→s explains why the old
capacity into D alone would not imply Hall. Locality must be proved explicitly.

Acceptance: no Hall assumption in the final short-subset corollary, exact image-in-N proof,
unchanged lag bound and all validation. Stop if the existing selector can leave the actual
window, or if eliminating Hall requires the desired capacity as a premise. This is a
composition candidate in the same module, not a claim about unrestricted lag.
The original frozen holdout source/output stays unchanged; any new formal source hash is
recorded separately and the earlier successful build is not reused for the changed source.

### Extension result at 14:44 JST (independent audit pending)

The extension compiles. `shortOff_le_window` proves the missing locality,
`short_window_hall` maps each list into its actual neighborhood, and
`short_tight_avoids_ss2_donor` has no Hall or ambient-U assumption. Its remaining hypotheses
are p>0, periodicity, nodup B, phases below p, current additions, minimal P2 windows of
length 3/7/11, tightness, and a minimal lag-11 SS=2 donor. `short_supply_donor_deletion`
then preserves Hall after deleting that subtraction on every sublist of a short minimal
supply list U, by tight/slack cases. This last restriction is on ALL of U and must not be
dropped when describing the result. It is not the full all-lag supply theorem E-070.

The first full build passed with 2557 axiom reports before the extension. A fresh full check
is required for the changed candidate. The frozen holdout completed with 2000 words at
each period: p32 donor-bearing words 147, Q_nonempty 1347, W 326; p33 donor-bearing words
164, Q_nonempty 1598, W 341. All violation counts zero. This is finite evidence, not the
reason the new universal quantifiers are valid. The holdout is now USED.
