# Hypothesis card: periodic capacity extension from bounded-excess reservoirs

- ID: `H-20260910-04`
- Owner: Codex, four roles sequentially
- Created: 2026-09-10 JST
- Status: `PROVED-LEAN` (E-100)
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`

## Exact bounded question

Fix R,L≥0 and a p-periodic Boolean stream e, p>0. Let U,Q be finite
duplicate-free sets of phases. Every u∈U is A and has an injective charge
ψ(u) to an S phase at some backward offset1≤j≤L. No supply assumption
on U is needed for the proposed combinatorial statement.

Every t∈Q is A, has exact preceding A-run length m (the m preceding
signs are A, and the next preceding sign is S), has some P2 lag
4m−1≤d≤4m−1+4R, and satisfies

`m≥max(3,R(R+1)+1,4R+L+2)`.

Must |U|+|Q|≤number of S phases? No positive period sum, actual-orbit
realizability, preassigned Q charge, or Hall/matching assumption.

Proposed mechanism: each Q source has a reservoir of offsets m+1,...,2m−1.
It contains at most2R As by H-03, hence at leastm−1−2R Ss. H-02 excludes
two Q sources in the same exact A run. Reservoirs belonging to different
runs should be disjoint modulo p. A radius-L charge into one reservoir
can originate only inside it or in the next L positions, hence can
occupy at most2R+L of its Ss. At leastone unused S remains in each
reservoir; choosing it gives an injective extension.

## Weakest new lemma and informal dependency audit

On the integer line, write a=t−m and b=u−n for exact run starts, t<u.
If b≤t, the S just before either start forces a=b, giving n=m+(u−t)
and contradicting H-02. If b>t and the reservoirs overlap, the later
reservoir contains the entire earlier A interval[a,t], with m+1>2R
As, contradicting H-03. A common phase lifts to a real intersection;
periodicity preserves the assumptions. Each reservoir has no internal
phase repeats because the exact A run plus its preceding S forces m<p.
This disjointness is the first new gate, before finite counting.

## Frozen falsifier / acceptance / stop

- First test the stronger abstract geometry, independent of P2: arbitrary
  periodic words, selected A phases with exact runs m≥max(3,2R+1),
  reservoir A count≤2R, and at mostone source per exact cyclic A run.
  Enumerate periods3..13 discovery,14..18 holdout. R=0..3.
- Include reservoir intervals wrapping across phase0, multiple sources,
  and a negative control dropping the same-run uniqueness condition.
- For every candidate reservoir, compute the maximum number of its Ss
  reachable by an injective radius-L A→S map using bipartite matching,
  for L=0,1,3,7. Test occupancy≤2R+L and free S when m≥4R+L+2.
- P2 applications: structured sharp and nonsharp words embedded periodically
  by adding a current A, and concatenations separated by S buffers;
  parameters and holdout ranges must be frozen in the script before running.
- Acceptance: complete all-period paper proof and, if feasible, Lean
  derivation from exact P2/sign assumptions. Finite matching success is not proof.
- Stop on overlap, occupancy violation, or capacity counterexample satisfying
  every stated hypothesis. Do not repair by assuming an injection for Q.

## Evidence

`PROVED-LEAN`: `Recaman/SupplyReservoirGeometry.lean` proves line
disjointness from the actual P2/sign/band assumptions. `Recaman/BoundedPeriodicSupply.lean`
lifts it modulo every positive period, proves the unused-S pigeonhole,
constructs the new choices, and proves
`periodic_capacity_extension`. The hypotheses contain only the previously
available short injection; no matching or capacity is assumed for Q.

Audit: `./scripts/check.sh` passed with1,306 declarations, including20
new geometry/capacity declarations. Exact log:
`docs/data/issue73_20260910/check04_reservoir_capacity.txt`.

`COMPUTED`: command
`python3 -u experiments/issue73_20260910/reservoir_capacity.py`, exact output
`docs/data/issue73_20260910/reservoir_capacity.txt`. All binary periodic
words of periods3..18 passed the abstract geometry and maximum matching
occupancy checks for R0..3, L0,1,3,7. At period18 there are262,144 words;
the exact counts of eligible reservoirs/pairs are in the frozen log.
Structured P2 cases use R0..4 discovery,5..12 holdout; L0,3,7,11;
run index threshold+delta with delta0,1,5; one or three source runs.
All312 cases passed. The structured family for positive R has actual
excess4, so it checks a broad nominal band but does not sample every
possible excess within it. H-03 separately checks extremal density words.

`REFUTED` control: removing same-run uniqueness from the claim of
pairwise-disjoint reservoirs fails already for a long A run following Ss.
The first counterexample in each period is recorded. This does not refute
the capacity inequality: nested reservoirs might admit multiple charges.

Semantic audit: reservoir coordinates are offsets m+1 through2m−1;
source t itself is A and there is an S immediately before the exact run.
The exact-run assumptions imply m+1<p, so each reservoir has distinct
phases even if the supply lag exceeds p. A short charge can originate
inside the reservoir or its next L positions; the proof includes wraparound.
The current U injection need not be a P2 supply injection, making the
theorem stronger than its intended U≤11 application. The new choices use
Classical.choice, within the allowed audit basis.

Decision: accept the all-period structural capacity extension. E-070
remains open because only a bounded-excess, long-run subclass is covered.
A next gate is whether nested same-run reservoirs permit removing the
quadratic multiplicity threshold from this capacity theorem.
