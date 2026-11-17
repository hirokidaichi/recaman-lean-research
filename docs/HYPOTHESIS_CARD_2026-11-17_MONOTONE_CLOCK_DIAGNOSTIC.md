# H-20261117-MC: does increasing order alone imply interval capacity?

- Status: CONJECTURED; work state: bounded diagnostic completed, methods STOPPED.
- Owner: Codex, user-requested unscheduled strategy consultation, 2026-11-17.
- Source revision: 82ad51a (full revision recorded in execution protocol).
- This is not the scheduled daily parent cycle; do not rewrite its tracker or the planned H01/H02 cards.

## Exact question

For every finite sign word sigma[0..N), sigma in {-1,+1}, and strictly increasing positive integer weights w[0..N), let H(t)=sum(i<t)sigma(i), X(t)=sum(i<t)sigma(i)w(i). An A at b is supplied if some 0<=s<b satisfies H(b)-H(s)=1 and X(b)-X(s)=w(b). Is the number E of supplied A at b<N at most the number S of minus signs?

At w(i)=i+1 this is exactly the existing interval capacity H, since the mass equation cancels the constant shift. The generalized question is stronger. A counterexample to it is NOT a counterexample to H, C1, D<=F, or a realizable Recaman orbit.

## Why / arbitrary-depth connection

This tests a proof-mechanism boundary: does a proposed argument need equal clock increments, or only their order? Depth, length and runs have no bounds in the conjecture. No free-count conversion or matching is assumed. The 2D rewrite is already known (H-20261020-01 and geometry_attempt.md); it is not new evidence. Only an exact counterexample or a proof independent of fixed depth changes the mechanism assessment.

## Acceptance and stopping

Accept an exact integer counterexample checked by two independent summations, or a complete paper proof. Search failure is OBSERVED only and stops this method. No Lean implementation, old stopped search restart, cutoff extension, or conjecture promotion from absence. One discovery job, at most 5 CPU seconds / 8 wall seconds; one independent verification job at most 1 CPU second / 3 wall seconds. Guard fixtures budget separate, at most 2 CPU seconds and 3 wall seconds each. Worker CPU begins at 0 until protocol/hashes and guard checks are saved. No paid services.

Discovery is a deterministic beam (seed 20261117, width 300, lengths 1..32). At each node allow A/S with next weight previous+1 or previous+2, plus an A at any weight forced by an earlier source and exceeding the previous weight. Keep 150 best E-S nodes (tie by E, then a frozen random key), plus 150 random nodes. Stop on first E>S. This is not exhaustive. No discovery range is called fresh relative to other sign-word searches.

Holdout: no statistical holdout/no absence claim. If a certificate is found, independently check every source using interval sums and the transformed weights 3w+7. This is verification, not independent discovery. A paper all-parameter construction may be extracted only after these checks. Small/boundary controls: empty word, one sign, A-only, S-only, SAAA with linear clock, constant-weight AAA as a deliberately invalid monotonicity control. No mathematical repair planned.

## Roles and dependencies

Proposer: generalized capacity above. Falsifier: finite weighted histories, preserving both mass and weighted equations. Formalizer: deferred unless a useful new mathematical input survives. Auditor: separate pass recomputes all sources, checks strict increase, interval endpoints, and the distinction from H. Existing dependency chain H -> periodic capacity is preserved; this diagnostic does not establish H.

## Evidence and decision

COMPUTED: the frozen beam completed 33,860 candidate extensions without E>S, worker CPU 0.109402 seconds. This is only the recorded finite selection, not all words up to length32. General statement remains CONJECTURED. Finite discovery method STOPPED; do not enlarge its range on this evidence. No witness existed to independently verify or test with transformed weights. Small-control verification was not completed; this further limits the use of the negative result.

Local progress: none. Depth-general progress: none established by this unit. No registry/protected-claim change. A renamed Hall condition, potential without paid overlap, or known planar rewrite is not acceptance.

Separate already-frozen-map audit: ANCESTOR_PROTOCOL.md records evaluation of H-20261117-01 on existing certificates. E711 and E715 N1/N2 completed all target/psi literal-source checks, without collision. E711 maps its targets14/62/70 to12/60/48; the formerly colliding62/70 now separate. E715 N2 maps4/1404/1412 to2/1403/1342. N3 did not complete before the1CPU-second cap, exit signal24. Method STOPPED, no resource/implementation retry, no conclusion about N3 or general injectivity. Original planned H01 mathematical question remains CONJECTURED; its parent daily allocation is unchanged.

The consultation's decision is in RESEARCH_NOTE_2026-11-17_PREHISTORY_COST_PIVOT.md. These diagnostics do not constitute a completed daily parent cycle and do not reset its stagnation tracker. No Lean files changed. Actual guard/discovery/audit usage, script hashes, exact argv and outputs are in data/monotone_clock_20261117. Resource-stop output is retained, not rewritten as a successful full check.
