# C1 depth 2026-10-23: first-eighth-A protocol (before any run)

Cycle R-20261023-01; hypothesis H-20261023-01. Registered 06:09 JST.
New method: the old-window count barrier, then a stopping line at the first eighth total A.
This is not an extension of yesterday's length-32 or UNKNOWN solver runs.

## Frozen population and acceptance

Padded BlockWord prefix, original-base Endable from **all** P2 windows, tail starts at deficit 0,
every nonempty tail prefix has deficit≥1 and at most three nonsupplied A.
Candidate: no eighth total A can be reached. A witness refutes this stronger candidate only;
it refutes the depth card only if an endpoint with d=1 and depth≥5 also exists.
Stop on a literal witness or exhausted complete graph; never silently raise the A threshold.

Before eighth A, at most seven preceding A imply local P2 length≤13.
The paper count barrier excludes old P2 when S≥13. Before that, any old suffix mass≤13.
Select the earliest actual old start over the finite prefix to obtain one common BlockWord
suffix of mass≤13, preserving all tail supplies. No prefix-deficit preservation is assumed:
tail deficit is reset to 0, and its increments use the preserved actual supplies.
Thus enumerate all BlockWord prefixes of mass≤13, including the empty prefix.

State before S saturation: exact prefix and tail (S≤12, A≤7).
State after S≥13: exact total A≤7 and nonsupplied A≤3, last 13 signs, S flag 13.
All local P2 clocks depend on these signs, old windows are excluded, and d≥13−7>0.
Consecutive extra S after the last-13 suffix becomes all S is a self-loop, not a length cutoff.
Initial A/zero-deficit steps are rejected. A depth bound is not imposed.

## Discovery, holdout, independent audit, CPU

- Discovery: complete graph for prefix mass 0..8, hard CPU cap60 seconds.
- Independent holdout shard: prefix mass9..13, cap60 seconds, fixed before viewing discovery.
  These contexts were seen in yesterday's different length-bounded problem; the new unbounded-S
  reachability question is fixed independently here. No claim of statistically unseen motifs.
- Independent audit: second implementation, direct backward mass/moment and literal long-S
  representatives (13/26/257/4097 signs in gaps), cap120 seconds total.
- Total additional exploration CPU budget **240 seconds**, reallocated from the local exploration
  allowance; elapsed research budget unchanged, CPU never added to journal work seconds.
- Compilation/Lean checking are validation, separately recorded; no solver/network computation.
- Every worker must have CPU/wall guards, exact source SHA256, HEAD + dirty snapshot hash,
  argv, raw stdout, completion/guard status. No run after07:45; all workers terminated by08:00.
- Source and full argv are frozen in RUNS.json before their executions. Source repair once only,
  with reason/version recorded; old artifacts are not overwritten.
- A complete finite computation is COMPUTED, not PROVED-LEAN. A compression argument not yet
  kernel-checked stays paper evidence, and must pass a separate semantic audit.

## Second mechanism, frozen 06:16 JST before implementation/run

Question: is the first-eighth-A exclusion still true if each old window chooses its own
BlockWord area signature, without a common prefix? Same stopping line/deficit/free-A budget;
local P2 remains exact. Each old flag is optional when its r/area is in the E-384 spectrum,
and impossible otherwise; local supply, if present, is forced. A SAT path is a countermodel
to this relaxation, not a literal-word counterexample. Acceptance is a full graph or such a path.
Stop on one relaxed eighth-A path; no repair or added constraints in the same version.
Use at most30 additional CPU seconds within the existing240-second total (unused reserves).
Source/argv frozen in SIGNATURE_RUN.json before execute. No holdout rebranding:
this is a mechanism diagnostic, with independent exact-word check of any relaxed path.
If no path, independently verify its graph before using it as a mathematical input.

## Independent finite certificate, frozen 06:18 JST

Construct the relaxed graph a second time by BFS with normalized whole-tail lists,
all suffix mass/forward-area tests, and the quadratic bounds (mass1 area exactly1).
Write every state and every accepted S/A0/A1 successor to an indexed certificate;
verify transitions independently before generating Lean data. CPU cap30s within240s total.
The checker must reject a missing edge, forbidden tag, bad index, or unsafe eighth-A state.
Do not interpret a closed graph theorem alone as the actual-word theorem: the actual-word
simulation (local windows and necessary old signatures) is a distinct proof obligation.

## Next unit H-20261023-02, frozen 06:43 JST

From all eight z words with final deficit1 and nonsupplied≤3, enumerate every future y with
at most one further nonsupplied A, positive deficit, and height≥−4 through the current clock.
Local P2 exact, each old signature independently optional. Check Z at every height≤0 state.
Stop on a negative Z relaxation witness or full completion; stack512/wall28s/CPU30s are protection
guards and their use makes the run incomplete. No word-length or S cutoff in the mathematical domain.
Source/argv in Q_RUN.json before execution. Independent validation reserved30s within the same240s
total actual exploration CPU cap; old finished reservations are released, not added to work time.

## H-20261023-03 local rank input, frozen 07:04 JST

The parent endpoint question and its stopping/limitations are fixed in the rank card.
The stronger all-prefix A≤2^r−1 claim is attacked first on the fixed known prefix
SAAA | SSSSAAAASA (expected r2,A5,d2); this does not attack the d=1 parent directly.
Then first-sixteenth-A actual-word reachability uses old mass≤14, local lag≤29,
S saturation29, all BlockWord prefixes mass≤14. Discovery mass0..4 and independent holdout
mass5..14 are fixed before either run, each CPU30s / wall28s. No word-length/S cutoff;
stack1024 and memo1000000 are protection guards and make a run incomplete if reached.
Any sixteenth-A witness with d>1 is only an auxiliary counterexample, not a parent refutation.
CPU remains within240s total; sources/argv/hash in HIGHER_RUNS.json before execute.

## Rank repair v2 and mechanism switch, frozen 07:08 JST

The all-prefix exponential inequality is refuted by the fixed literal ledger. Repair once to
P=A−2(d−1)≤2^r−1, for every nonempty positive-deficit prefix; end d1 recovers the parent.
Record maxima and first relaxed violation, if any, for r0..4. First-sixteenth-A stopping line remains
an auxiliary input, not an assumed whole-word A bound. Use independent optional old signatures,
instead of looping over3708 actual prefix contexts (which hit its wall guard).
CPU30s/wall28s within240s total; no extension of the stopped actual-prefix run.
Source/argv frozen in RELAXED_HIGHER_RUN.json. A relaxed violation needs an actual common prefix
and full all-start ledger before it refutes the repaired word claim.

## Independent higher-budget audit, frozen 07:14 JST

Rebuild the r≤4 first-sixteenth-A graph using full forward levels/integrals, literal all-BlockWord
area spectra mass1..14, and literal last29-word normalization after S≥29. Reverse traversal order.
Compare node/state counts, all endpoint sets, highest A, and maxima of repaired P. No use of the
discovery model's quadratic formula or backwards-moment routine. CPU30s/wall28s within240 total.
After S≥29 and A≤15, P≤3*15−2*29+2=−11, so forgetting the exact S count cannot hide a P violation
or an endpoint d1. Source/argv in HIGHER_INDEPENDENT_RUN.json before execution.

## Q4 follow-through, frozen 07:16 JST

Use the fixed16 endpoint roots (the previous8 plus8 with AN4) from the complete independently
verified higher relaxation. Same Q graph definitions, all future lengths, depth≥−4, Ay≤1,
original-base deficit positive, guardF≤0. CPU30s/wall28s for discovery and independent audit;
stack512/states500000 are protection guards only. Q4_RUNS.json freezes both source hashes and argv
before either run. This remains COMPUTED: no kernel certificate for the r4 depth supply.
