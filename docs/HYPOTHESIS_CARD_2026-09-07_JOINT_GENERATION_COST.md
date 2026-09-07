# Hypothesis card: joint generation cost / connected history gate

- ID: `H-20260907-06`
- Owner: parallel agent `joint_generation`
- Created: 2026-09-07
- Status: `REFUTED` candidate C; `PROVED-PAPER` enrichment no-go; separator `STOPPED`
- Research branch: pattern 3, joint birth constraints, falsification first
- Source revision: `612fcfaf74bfb49f3ae05a268057c82f70dcca26`
- Roles: proposer → falsifier → paper formalizer → auditor (same agent, separate passes)

## Bounded question and exact statement

A single generated history has connected value support: for a trajectory
`x_0,...,x_B` with `|x_t-x_(t-1)|=t`, every consecutive pair in the sorted
visited support differs by at most `B`. This uses every historical transition,
not just the cardinality or triangular value bound.

Test the candidate separator C: for every admissible E-056 family instance
(even `w>0`, even `D≥10`, `D²−8D>w`, finite `F⊂[0,w)`), there is no finite
superset `S` of its frozen initial seed such that simultaneously

1. `|S|≤B+1`, `max S≤B(B+1)/2`, and the endpoint has canonical parity;
2. consecutive sorted seed values differ by at most `B`;
3. the exact greedy continuation from the same endpoint at clock `B` still
   follows `SS(AS)^J S A^D S^D`, lands at `w` before wrap, and violates
   `7h≤16v`.

This is a necessary joint-support gate, not a claim that connected support is
sufficient for actual provenance. If C is false, record the explicit enrichment
and, if possible, a general reason that finite support connectivity cannot
separate the family. Do not add a new wrapper or repeat the fixed #71 census.

## Why it would matter

The original E-056 seed has high resource islands. An actual generated prefix
must reach those islands through earlier values. Extra bridge values may
contaminate the future subtraction freshness; C tests exactly that possible
mechanism before attempting more costly full chronological reconstruction.
A refutation rules out this specific compressed joint-generation invariant.
It does not refute canonical survival or any general birth-sensitive inequality.

## Known dependencies and stopped approaches

Read AGENTS, AI_RESEARCH_PROTOCOL, README, status report, ROADMAP, relevant
GLOSSARY/PROOF_MAP/RESEARCH_PORTFOLIO entries and E-044/E-050/E-056/E-057/E-058/E-059.
E-044 is local producer tuple multiplicity; E-050 affine phase capacity no-go;
E-056 is arbitrary finite-prefix exact seeded survival violation; E-057 is a
canonical weighted-drop counterexample; E-058 is the two-rail finite census;
E-059 stops positive survival without an independent joint-generation input.
C adds a global support constraint not present in those payloads, but deliberately
does not claim full timestamped joint generation.

## Falsification plan

- Boundary: minimal `w=2,D=10`, and smallest admissible D for each F.
- Weakened history: add only values outside every future fresh subtraction output.
- Discovery: F equal to canonical prefixes at horizons `0,4,128`.
- Frozen holdout: F equal to canonical prefixes at horizons `1000,10000,200000`.
  These prefixes are old source data, not new unseen Recamán observations.
  Only the new frozen connectivity-enrichment claim has a separate holdout.
- Acceptance: one exact greedy counterexample refutes C; a paper enrichment lemma
  should explain whether this failure is structural rather than parameter tuning.
- No numerical coefficient repair. If connectivity can be added while preserving
  the counterexample, stop this separator and identify the missing chronological
  information. No initial Lean implementation.

## Evidence log

Completed below under Reproduction / evidence log; initial statement above was frozen before the runs.

## Semantic audit

Completed below under Auditor. Support connectivity is not actual birth-clock
consistency or greedy-prefix reachability.

## Decision

See final decision below: candidate C refuted; connected-support separator stopped.

## Result: C is REFUTED; connected-support separator is STOPPED

**Conclusion:** forcing every initial resource island into one support whose
adjacent gaps are at most the historical clock does not separate E-056. It can
be done for the entire family while preserving every greedy step of the bad
continuation. The original separator C is `REFUTED`; the uniform enrichment
argument below is `PROVED-PAPER`; the finite independent replays are `COMPUTED`.
The positive joint-generation route has not passed its continuation gate.

### Proposer: why connectivity was a nonvacuous gate

For any finite sequence `x_0,...,x_B` satisfying
`|x_t−x_(t−1)|=t` for `1≤t≤B`, let S be its support. If `u<v` are adjacent
sorted values of S, the path between a visit to u and a visit to v must cross
this cut in some single step. Because no visited value lies between them,
that step has size at least `v−u`; because its clock is at most B, `v−u≤B`.
This is a complete paper proof of a necessary condition on a jointly generated
support. It does not use the greedy sign choice.

The minimal E-056 seed has gap 8,247 at B=4,094, so the condition actually
excludes that seed. The falsifier then asks whether excluding that exact sparse
presentation also excludes harmless supersets of the seed.

### Falsifier: exact boundary counterexample

Take `F={0}`, `w=2`, `D=10`, `v=102`, `J=51`, `h=256`, `B=4094`,
`c=4199`, `x_B=12543`. Add exactly the seven values

```text
4300, 8394, 16798, 21001, 25205, 29410, 33616
```

to the original seed (fully printed in `birth_discovery.txt`).
The seed grows from 61 to 68 values; its maximum remains 33,729; its maximum
adjacent gap decreases from 8,247 to 4,094. The seed has the required bound
`68≤4095`, triangular range and canonical endpoint parity.

The exact greedy word remains `SS(AS)^51 S A^10 S^10`, lands at 2 at clock
4219, has no residue increase before that landing, has five relevant positive
blockers all used once, and has survival slack
`16·102−7·256=−160`. No bridge value equals one of the 64 fresh subtraction
outputs. This is a countermodel with arbitrary initial history, not the
canonical sequence and not a history actually generated from a single value.

### Paper formalizer: general enrichment lemma

**Lemma 1 (continuation-preserving extension).** Let a finite greedy
continuation start from `(B,x,S)`, and let Q be the set of outputs of all its
subtraction steps. For any finite added set T disjoint from Q, continuation
from `(B,x,S∪T)` has exactly the same values and signs through that word.
Proof by step induction: a prescribed subtraction candidate belongs neither
to the old seen set nor to T, and so remains fresh; a prescribed addition was
already forced by nonpositivity or old membership, both preserved on extension.
The new seen set at each time is exactly the old seen set union T. Conversely,
if T meets Q, the corresponding first prescribed subtraction cannot occur.

**Lemma 2 (safe support bridge).** Let finite nonempty S contain 0, let
`S∩Q=∅`, and write `q=|Q|<B`, `M=max S`. There is a finite T disjoint from Q,
contained in `[0,M]`, such that all adjacent gaps of `S∪T` are at most B and

```text
|T| · (B−q) ≤ M.
```

For each adjacent original pair `u<v` with `v−u>B`, start at y=u and choose the
largest integer z≤y+B outside Q. Among the q+1 integers
`y+B−q,...,y+B`, one is outside Q. Hence `B−q≤z−y≤B`, and `y<z<v`.
Insert z and repeat until the gap to v is at most B. Each insertion advances
by at least B−q, so the process terminates. The inserted forward intervals
are disjoint within and across original gaps; their total length is at most M.
This proves the size bound, all gap bounds, and disjointness from Q.

**Theorem (connected support cannot rescue this survival bound).** For every
admissible family parameter choice above and finite set `F⊂[0,w)`, there is
such an enrichment satisfying all three payloads of C, hence violating C.
Indeed, the original word has exactly `q=J+D+3` subtraction outputs, and
`D≤J`, so `q≤2J+3`. Its parameters satisfy

```text
B = 80J+14+2·((5J+1) mod 2),    c=B+2J+3,
|S| ≤ |F|+J+D,                 max S ≤ D·c+4J.
```

The last bound follows directly from the seed formulas: low-rail blockers are
at most 5J, the endpoint is `3c−J−3`, and the high blockers
`(p−2)c+2J+p(p−3)/2`, `4≤p≤D`, are at most `D·c+4J` because `D²<2J`.
All F values are less than w<2J. Since

```text
2D(B−q) − (D·c+4J)
  = D(B−2q−2J−3)−4J
 ≥ D(74J+5)−4J > 0,
```

Lemma 2 uses fewer than 2D added values. As `|F|≤w<2J` and `D≤J`,

```text
|S∪T| < |F|+J+3D < 6J < B+1.
```

The maximum does not increase, hence triangular range is preserved; endpoint
parity does not change. Lemma 1 preserves the exact word, every subtraction's
freshness, the first late landing, the no-wrap segment, the one-use resource
payload and the same strict survival-ratio violation. This proves the uniform
no-go, not merely the six computed examples. No Lean proof was attempted.

### Auditor: what this does and does not establish

- Every genuine history satisfies the gap condition; the test is not vacuous.
- The construction covers the entire admissible parameter family and every
  finite set F below w, rather than adding a specially selected fixed prefix.
- The extra points are genuine elements of the initial seen set, not phantom
  resources inserted during the continuation. Their later effect is checked
  at every greedy step.
- These values are not supplied birth clocks, predecessors, or a global
  sign chronology. The augmented set need not occur as any actual orbit's
  prefix; graph connectivity does not provide that claim.
- No new independent survival inequality, run coexistence theorem, or global
  non-surjectivity consequence follows. The paper theorem only eliminates this
  particular compressed replacement for joint generation.
- This differs from E-044 (one local producer tuple allowing many events),
  E-050 (affine phase potential), and E-056's published payload (density, range,
  parity and arbitrary low F). It strengthens the countermodel with connected
  support but intentionally does not claim chronological provenance.

### Reproduction / evidence log

Commands, both run on the stated source revision:

```sh
python3 experiments/parallel20260907/birth_connected_support.py --mode discovery > docs/data/parallel20260907/birth_discovery.txt
python3 experiments/parallel20260907/birth_connected_support.py --mode holdout > docs/data/parallel20260907/birth_holdout.txt
```

Script SHA-256:
`366686ed8aaf18ff018f347e21d40fbf7aa23e9b926e028a8f080edbb1a8c600`.
The output includes exact parameters, seed/bridge counts, maximal gaps, survival
slacks, and bridge-list hashes. Discovery horizons 0/4/128 and holdout horizons
1000/10000/200000 all passed without repair. These are six exact finite tests
of the new frozen enrichment, not six new discoveries about canonical survival.
At the largest input, only 1,161 bridges were added to 1,497,274 seed values,
with B=107,997,214 and the unchanged ratio slack −4,049,902.

### Final decision and next independent question

Stop support connectivity as a candidate separator. Do not spend time tuning
its coefficient, counting bridges, or formalizing this no-go merely to add
Lean declarations. It has low priority for reaching a global proof.

The next useful question, if this branch receives another bounded cycle, is:
**can the blocker producer runs and all their companion values be assigned one
common chronological greedy history without placing a companion in the
consumer's future-fresh set Q?** Unlike connectivity, this must require actual
birth clocks, sign conditions, and order between different runs. A concrete
finite family of producer assignments, independent of the desired survival
inequality, must be proposed before doing more experiments. No such useful
finite assignment model was established in this unit. The unknown connection
to a permanent missing value therefore remains unchanged.

Changed files: this card, the one `birth_connected_support.py` experiment, and
two exact output logs under `docs/data/parallel20260907/`. No Lean, registry,
frontier, Git or issue state was changed by this agent.
