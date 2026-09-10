# Hypothesis card: one-SS minimum supply per A run

- ID: `H-20260910-27`
- Status: `PROVED-PAPER` (E-127)
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`
- Roles performed sequentially.

## Exact bounded question

For any two-sided Bool stream avoiding SAAS, at most one current A in each
maximal A run has a prefix-minimum P2 window containing exactly one SS.
Consequently, for every finite periodic NoSAAS word, the number of such
phases is at most its number of cyclic A runs, and hence at most its S count.
No positive-mass assumption or period bound is allowed in the paper theorem.

Acceptance: a complete overlap argument from the H22 two-family classification,
plus a complete finite-period falsifier. Stop on any counterexample or
if the argument assumes canonical reachability or silently extends the
claim to the union with clean/short supply. Do not repair a failed offset.
This tests a structural run-multiplicity bound; the preceding-S map is only
its corollary. It is not a repair of the stopped centered map or a constant
budget per SS pair: arbitrarily many different A runs can share one SS.

## Dependency chain before verification

H22 says a minimum one-SS window starts S (family A) or AS (family B).
Thus only the first or second current A in a run can qualify. If both do,
let u be the first source's past window and Av the second source's past
window. u and v are prefixes of the same backward history, both start/end S.
u has exactly one enlarged internal A gap, of length4. v has exactly one,
of length3. Whichever prefix is shorter has an internal enlarged gap that
persists unchanged in the longer S-ended prefix, a contradiction. Therefore
at most one source occurs per run. Cyclic runs start after distinct S phases.

## Frozen falsifier

All binary periods1..11 discovery,12..17 holdout, all mass signs included.
Discard only cyclic words containing SAAS. Directly scan every A phase's
backward prefixes through2p; record its first P2, retain it only if SS count1,
and test uniqueness of the preceding-S-of-run image. Any one-SS window has
d≤2p: if the period has an SS then2p+1 signs contain two copies of an SS edge;
if it has none, no such window exists. Thus this scan is complete for the
tested predicate, including balanced periods. Explicitly test all-A/all-S.
Separately search unrestricted periods≤13 for a NoSAAS-premise control;
a miss there is only an incomplete negative-control search, not a theorem.

## Evidence and decision

- `COMPUTED`: the frozen all-mass periodic scan through p17 passed. At p17 there are 40,598 NoSAAS words and 4,335 qualifying phases. The unrestricted control search through p13 found no counterexample; necessity of NoSAAS for the final bound is not established by that miss.
- `PROVED-PAPER`: the complete prefix-comparability and cyclic-run argument is recorded in `docs/ONE_SS_RUN_CAPACITY_2026-09-10.md`. Every internal gap of an S-ended prefix persists unchanged in an extension, so gap4/gap3 exclusivity rules out both first and second A being one-SS supplied.
- Not `PROVED-LEAN`: this depends on the full paper classification E-121, not only its Lean family constructors. No Lean module was added for this claim.
- The at-most-one-per-run condition does not limit how many different runs share an SS; it is compatible with E-122. It does not establish disjoint images from the clean/short maps. Combining the classes remains the next obstruction.


- Final union-map control: every family-B source at t forces a clean AAS source at t+1 under NoSAAS. Their current maps both use S at t−2. Positive period13 `SSAAASASASAAA`, phases11/12 and charge9, is independently computed in `one_ss_union_control.txt`. The run bound remains true; naively combining these particular maps is `REFUTED`.
