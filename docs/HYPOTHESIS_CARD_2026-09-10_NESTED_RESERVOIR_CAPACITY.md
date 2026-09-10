# Hypothesis card: capacity for nested reservoirs without a multiplicity bound

- ID: `H-20260910-05`
- Owner: Codex, four roles sequentially
- Created: 2026-09-10 JST
- Status: `PROVED-LEAN` (E-101)
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa` (full revision recorded by scripts)

## Exact bounded question

Fix B,L≥0, p>0 and a p-periodic sign stream. U is any set of A phases
with an injective backward radius-L charge to S phases. Q contains A
phases with exact preceding A-run length m≥2B+L+2. Each Q reservoir of
offsets m+1,...,2m−1 contains at most B As. There may be many Q phases
in one run. Must |U|+|Q|≤D?

If true, E-098 with B=2R would give a P2 bounded-excess capacity theorem
for `m≥max(3,4R+L+2)`, removing E-100's R(R+1)+1 threshold. The stronger
abstract density statement has no P2, signed-gap, or minimum-lag assumption.

## Informal dependency chain and weakest new lemma

Reservoirs from different exact A runs are disjoint: intersection makes
one reservoir contain the other's A run of length m+1>B. Within one
run they share the right endpoint and are nested in increasing m.
Each reservoir has at least m−1−B Ss and at most B+L can be occupied
by the old short map. Hence at least m−1−2B−L=m−M+1 remain, where
M=2B+L+2. Among Q phases in that run with index≤m there are at most
m−M+1 distinct indices. Greedy selection in increasing m should work.

The weakest new lemma is a finite matching construction for these nested
reservoirs, without assuming the existence of a Q matching. A direct
induction may select a largest run index, extend a matching for smaller
indices, and bound previously used S positions in the new reservoir.
The proof must handle cyclic run starts and repeated phases explicitly.

## Frozen falsifier / acceptance / stop

- Enumerate every binary periodic word of periods3..13 discovery,
 14..18 holdout; B=0..3 and L=0,1,3,7.
- Q is ALL A phases satisfying the density and run threshold, not an
  arbitrary one-per-run subset. Match all radius-L A→S edges first in
  every way for small cases, or use an adversarial flow/cut formulation
  that detects a bad existing short injection. A single convenient short
  matching is insufficient to validate the extension statement.
- Separate Hall test on Q's reservoirs after each tested short matching;
  record same-run multiplicity and wraparound cases, and test the abstract
  count conditions directly even where a full matching enumeration is costly.
- Structured tests include one long A run following an S block, with many
  eligible Q phases, and multiple such runs, with sizes beyond discovery.
- Before executing any expensive matching variant, freeze its exact limits
  and parameters in the script and describe any sampling as OBSERVED.
- Acceptance: complete all-period paper/Lean construction or a counterexample.
- Stop on a valid counterexample; do not add a hidden one-per-run or matching
  assumption to rescue the claim. E-100 remains independently proved.

## Evidence

`PROVED-LEAN`: `Recaman/NestedReservoirCapacity.lean` proves the abstract
density theorem `density_periodic_capacity_extension` without P2 or a
same-run multiplicity hypothesis. Its explicit rank construction is
`rankCharge`. The P2 specialization
`bounded_excess_periodic_capacity_extension` needs only
m≥max(3,4R+L+2), with no quadratic threshold or minimum-lag premise.
The lag lower bound is derived through E-098 and is not a supplied assumption.

`COMPUTED`: command
`python3 -u experiments/issue73_20260910/nested_reservoir_capacity.py`, exact
log `docs/data/issue73_20260910/nested_reservoir_capacity.txt`. At period18,
all262,144 words produced374,457 eligible parameter cases and1,282,083
nonempty Hall subsets;121,353 cases had multiple Qs in the same run and
29,751 had a wrapping reservoir. Maximum Q size8; minimum Hall slack0;
zero violations. For each Hall subset the test maximizes occupancy by an
arbitrary old short matching, so it does not choose a convenient old map.
Structured B0..8/L0,1,3,7/extra0,2,7/one or three runs produced432 cases.
For Q size≤16 all Hall subsets were checked; larger cases checked only
each run's prefixes. The restricted structured tests are not exhaustive
Hall verification and are not a substitute for the general proof.

Audit: `./scripts/check.sh` passed with1,318 declarations,12 new declarations
in Audit. Exact log `docs/data/issue73_20260910/check05_nested_reservoir_capacity.txt`.
No new axioms beyond the allowed basis. The older E-100 remains correct
but its stronger threshold is superseded for capacity applications.

Semantic audit: all Q phases are included in the finite count, not merely
one representative per run. Distinct source phases with a common reservoir
phase are shown to have the same cyclic run start. Equal rank charges then
force equal run lengths and hence equal source phases. Free S ranks start
at0; at the boundary m=M, the count guarantees one target. The old image
is filtered using one common phase list, so periodic wrap does not change
which S positions are unused.

Decision: use E-101 as the strongest capacity extension. E-096/E-097 remain
independent supply-geometry results, but their gap/multiplicity statements
are not needed as premises of the new abstract capacity theorem. The
remaining obstacle is supplied phases with shorter runs or larger reservoir
density; this result does not establish all-lag E-070.

## Construction fixed after falsification, before formalization

The full finite protocol passed. A simpler explicit construction replaces
matching induction: in the newest-first list of unused S positions of a
source with run index m, select zero-based rank m−M. The lower bound
m−M+1 guarantees this rank exists. For two sources in the same run the
shorter reservoir is a prefix of the longer one, and the same fixed
filter (S and not in the old image) preserves prefixes. Distinct m give
distinct ranks in a duplicate-free common list. Different runs have
separate reservoirs. Thus no general Hall theorem or assumed Q matching
is needed in the Lean proof.

Prior stopped-branch search also checked the genuine candidate-reuse
interval crossing counterexample in `Recaman/ForcedCandidateReuseBalance.lean`.
Those are full reuse intervals, not the restricted middle reservoirs here;
the new proof must derive its own interval property from density and exact
run signs and does not assume generic reuse-interval laminarity.
