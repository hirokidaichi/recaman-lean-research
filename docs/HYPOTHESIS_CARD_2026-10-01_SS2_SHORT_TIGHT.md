# Hypothesis card: arbitrary-length SS=2 donor versus short tight subsets

- ID: H-20261001-06 (issue #81)
- Status: PROVED-LEAN (E-366)
- Branch: codex/ss2-short-tight-any-donor
- Base: 8186f0004b01e1e5ce3cbd9b0061433fa1e25295
- Scope: one bounded unit; proposer/falsifier/formalizer/auditor passes separated.

## Exact statement

For every p>0, e:Int→Bool with e(x+p)=e(x), nodup B:List Nat,
lag:Nat→Nat, all b in B satisfy b<p, e(b)=A, lag(b) in {3,7,11},
P2(past e b (lag b)), and no positive proper P2 prefix.
Assume length(neighborhood e p B lag)=length B.
For every u0:Int and d:Nat, e(u0)=A, W=past e u0 d,
P2(W), ssCount(W)=2, and no positive proper P2 prefix imply
phase p (u0-oldestOffset(W)) not in neighborhood e p B lag.
No bound on d or p, ambient Hall, NoSAAS, drift or owner-distance premise.
Words are newest first; S offsets are one based and count overlapping SS.

## Why it matters

Remove the donor-length=11 restriction of the short-tight result, while
retaining short members. Do not claim arbitrary-lag tight subsets, general
Gate T6, Hall on all suppliers, actual-orbit realization or surjectivity.
This completes the unfinished H-20260920-05 direction; it is not a new
claim discovered from an unlabelled reuse of that draft.

## Provenance and informal dependency chain

E-362 defect positivity and E-363 terminal bound are accepted Lean inputs.
E-357 short OwnerFamily exclusions, E-358 Hall matching, E-359 periodic
lifting, ShortReservoirCapacity short injection, and PairedSubtractionCoverage
are accepted inputs. Preserve all explicit owner-family fields.
Other-session draft hashes are in data/ss2_short_tight_20261001/draft_provenance.json.
Those drafts are hints, not accepted dependencies; do not edit their files.

1. True-oldest decomposition W=X S A^t and terminal SS=2 budget give t<=1.
2. Prohibit AAA immediately newer than the oldest S of a minimal SS2 donor.
   The real window splits as (x A) AAS A^t. For t=0 the intervening word
   has mass0 and defect0; its A-ended SS<=2 suffix bound gives ceiling2.
   E-362 derives positive defect if no P2 prefix, a contradiction. For
   t>0 use the A-ended moment budget to contradict moment0.
3. Prohibit a current-A w1=SAAAASS window ending at that same S. In
   (x A) w1 A^t the prefix has SS<=1, so moment+length>=2 contradicts P2.
4. Short owner members are AAS or w1. Ownership forces the future AAS
   member of each w1; handle all its S offsets 1,6,7, not just an endpoint.
5. Derive short Hall from the concrete short injection, extract the
   integer owner family from tightness and lift the local exclusion by
   periodic congruence. No current-A/next-A premise may be fabricated.

Weakest useful unfinished edge: all-length stream motif exclusion in 2/3,
with exact chronological decomposition and real oldest offset. The periodic
result must consume this edge; pure arithmetic/wrapper results are insufficient.

## Falsification protocol fixed before computation

Script experiments/ss2_short_tight.py, freeze SHA before runs.
Discovery: all P2 words at lengths 3,7,11,15,19, filtered by SS=2 and
minimality. Independent literal binary enumeration through length11.
Holdout for this exact probe: length23. These lengths have been used by
previous repository probes; explicitly reused ranges, not virgin holdout.
Check all three completed-w1 placements (oldest at offsets1,6,7) and AAA,
including stream positions outside the donor word as unconstrained signs.
The current donor A is fixed at offset0.

Negative controls: nonminimal p16 SAAASSSASASASAAA, u0=15, B=[3], lag3;
relax completed w1 to an isolated current-A w1 (report compatible witness);
remove the SS=2 restriction (report first witness if found).
Positive nonempty controls: E-240 p18 and an explicit constructed periodic
word with a length19 donor and disjoint AAS member; both terminal t=0/1
word controls. Independently verify all premises, not only the conclusion.
Log source revision, hashes, exact commands/output and denominator counts.
No census extension on zero violations. Computation is not proof.

## Acceptance and stop

Exact all-length local exclusion and the periodic theorem accepted by Lean,
Audit/G5/lint/check.sh and a separate-session semantic review, including
nonempty cases and weakened-premise controls. One substantive module; do
not register helpers as separate research results. Protected labels unchanged.
First 90 minutes: establish local and periodic dependency chain; stop if
it needs a length cutoff, OS, arbitrary-lag Hall or an unproved distance
bound. Any counterexample is REFUTED with literal witness. At most one
explicit repair, never silently weaken the issue statement.

## Semantic audit / decision

Pending before implementation. Independent-auditor authorization requested;
while pending, only the card, falsifier and existing-PR integration proceed.
Initial hypothesis remains CONJECTURED.

## Falsifier results before formalization

`python3 experiments/ss2_short_tight.py discovery` and `holdout` passed.
All 3,021 discovery P2 words include 269 minimal SS2 words; length23
contains 30,554 P2 words, 647 minimal SS2 words. All four completed
placements tested per minimal SS2 word, zero violations (3,664 checks).
The independent binary enumerator matched all 34 P2 words through length11.
The p16 control fails exactly donor minimality and the target conclusion.
The p18 w1 control and p26 length19 donor/nonempty B control satisfy every
premise and avoid the true oldest phase.
An isolated w1 at offset1 is compatible with AAASSSASASA, so the future
AAS ownership input is essential. Dropping SS=2 permits the AAS control.
All outputs are COMPUTED, reused ranges, not a proof or fresh virgin data.

## Independent entry gate

User authorized a read-only sub-agent audit. Auditor /root/issue81_auditor
returned PASS before Lean implementation. An independent absolute-coordinate
probe reproduced all counts and 3664 zero-violation tests, and matched frozen
hashes. The auditor checked E-362 local defect reasoning, empty-prefix/clock
boundaries, w1 ownership at offsets1/6/7, and the Hall extraction from the
short injection. Critical obligation: shortOff must lie within each actual
window, not merely be <=11. No circular use of general Hall/OS/next-A found.
This is permission to formalize the frozen statement, not a proof label.
The earlier pending-audit line records history; the entry gate is now passed.

## Formalization and final decision (2026-10-01)

The exact issue #81 statement is proved by
`Recaman.SS2ShortTight.short_tight_avoids_donor`. No quantifier or premise
repair was made. The donor current-A assumption is retained even though
the proof does not need it. The planned use of E-363 t<=1 was unnecessary:
the A-ended moment budget handles all terminal lengths directly. E-362
is used after deriving the actual prefix ceiling, not assuming it.

Selected draft fragments: shortOff_le_window / short_window_hall and short
owner-family classification/ownership came from ShortTightDonorAvoidance;
oldest decomposition, A-tail algebra and local motifs came from
SS2OldestPattern. These were checked in the new module, with
ss2_intervening_prefix reimplemented through the accepted E-362 proof.
Both existing owner-family modules only expose their prior internal
constructions as named helpers; the exclusion signatures are unchanged.
The source hashes in draft_provenance.json identify proof hints, not an
unreviewed import. No other uncommitted primary-checkout file was adopted.

The strongest evidence is the kernel-checked all-d/all-p statement plus
independent semantic audit, including direct applications to nonempty B.
Full repository check: 394 jobs, 2625 declarations with permitted axioms.
Lint/vacuity checks pass but are not treated as semantic evidence. Exact
commands, output and controls are in data/ss2_short_tight_20261001.

Failed attempts and negative evidence: no counterexample to the frozen
statement was found. Nonminimal donors, donors without SS=2 and non-tight
B each have concrete counterexamples in the semantic controls. Isolated
w1 overlap is possible; the owner-forced future AAS cannot be omitted.
These controls refute weakened statements, not the accepted theorem.

Remaining uncertainty: B still has lag 3/7/11, and this is an abstract
periodic-stream theorem. It does not give general all-lag B, deletion Hall,
Gate T6 or an orbit realization. Stop this unit after integration. Any
next attempt must identify a separate falsifiable long-member condition;
do not resume a finite-lag certificate census on this evidence alone.

Handoff: changed one new research module, two extracted helper proofs,
root imports/Audit, registry/statement audits, this card, proof map/frontier,
reproducible probe records and viewer manifest. The pre-run protocol is
preserved unchanged as protocol.frozen.md; earlier CONJECTURED and pending
entry-audit text above records the chronological protocol, not current status.
