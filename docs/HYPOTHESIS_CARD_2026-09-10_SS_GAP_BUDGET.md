# Hypothesis card: all-SS gap budget

- ID: `H-20260910-26`
- Status: `PROVED-LEAN` (E-126)
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`
- Roles: proposer, falsifier, formalizer, auditor, sequential.

## Bounded question and acceptance

For every finite Bool word w with mass 1 and no SAAS, containing at least
one S, encode it uniquely as A^a S A^g1 S ... S A^gr S A^v.
Let k be its number of adjacent SS pairs, including overlaps, and B the
number of internal A gaps of length at least 3. Prove

`a + v + 2*B <= k + 2`.

The stronger exact identity is `a+v+sum(max(g-1,0))=k+2`.
The proposal treated NoSAAS as needed for the inequality; the semantic audit
below distinguishes the stronger premise-free large-gap version from the
all-enlarged-gap version. P2 implies mass 1, so it is a corollary;
the first moment is not needed and will not be added as a vacuous premise.
The Lean statement must connect the actual word, actual NoSAAS, and actual
SS count to its gap data, not assume the desired budget in another type.

This controls all SS counts with one inequality, rather than extending a
fixed-small-defect table. It does not give inter-window disjointness, an
A-to-S assignment, or E-070. Stop if only an unconnected numeric gap proxy
can be proved, if a declared finite control fails, or if formalization
exceeds the remaining research timebox. No constant repairs are permitted.

## Repository search and dependencies

The SS-free and one-SS cards contain the special extra-A budgets 2 and 3.
No general all-SS theorem was found in Recaman or the stopped portfolio.
Reuse OneSSGapAlgebra.gapWord and OneSSMultiplicity.ssCount. Every Bool word
has an exact gap representation; internal gap 0 is an SS, and NoSAAS forbids
gap 2. Summing g = 1 - 1[g=0] + max(g-1,0) proves the identity. Each large
gap consumes at least two extras, which proves the inequality.

## Frozen falsifier

Raw binary words of lengths 1..13 discovery, 14..19 holdout. For every
mass-1 word containing S, verify the exact identity with no language
restriction, and the inequality with NoSAAS. Check decoder round trips,
overlapping SS pairs, zero endpoint runs, and a single S.
Use unconstrained words to find the required NoSAAS negative control for
counting *all* enlarged gaps (length at least 2) at cost 2. This distinguishes
the gap-length-3 inequality, which in fact may need weaker assumptions,
from the claim that every nontrivial internal gap costs at least 2.
Audit this distinction before recording the theorem's premise list.

## Evidence and decision

- `COMPUTED`: raw mass-one words through length 19 pass the exact budget and both inequalities. `python3 experiments/issue73_20260910/ss_gap_budget.py > docs/data/issue73_20260910/ss_gap_budget.txt`.
- `PROVED-LEAN`: `SSGapBudget` connects arbitrary actual word representation, actual overlapping SS count, and actual NoSAAS to the exact budget and inequalities. `every_P2_budget` covers all P2 words, not just an assumed numeric encoding.
- Semantic audit sharpened the premise distinction before registration: counting gaps of length at least 3 needs only mass 1; counting every enlarged gap (length at least 2) uses NoSAAS. This is a proved stronger statement, not a repair after a failed inequality. `ASAAS` has mass 1, SS 0, endpoints 1/0, and one gap 2, so the latter inequality fails without NoSAAS; the control is also Lean-certified.
- The exact equality does not use moment 0. The P2 corollary excludes the no-S case via the existing `not_p2_all_A`, rather than assuming an S exists.
- Full audit: `check26_ss_gap_budget.txt`. This is a structural inequality, not an inter-window capacity theorem. No additional SS-count table or offset repair is authorized by this result.

