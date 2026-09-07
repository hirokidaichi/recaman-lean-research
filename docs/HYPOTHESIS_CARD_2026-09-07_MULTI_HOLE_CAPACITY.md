# Hypothesis card: finite holes and a shared capacity

- ID: H-20260907-08
- Owner: root; proposer → falsifier → paper formalizer → auditor
- Created: 2026-09-07
- Status: `PROVED-PAPER` (finite absorption in the stated abstraction); hole-only deficit route `STOPPED`
- Base revision: `612fcfaf74bfb49f3ae05a268057c82f70dcca26`
- Pattern: ⑤ finite candidate set; eliminate the need to name a permanent hole in advance

## Bounded question / exact model

Can the remaining finite hole set alone carry a positive conserved deficit in the
unlimited-band hole-hopping abstraction already used by E-031?

Fix a finite set M of positive integers. At an abstract arc entry choose a residue c in
{0,1,2}. Remove the largest remaining hole of that residue, if it exists. After removing
v, repeatedly remove the largest remaining hole below v with residue (v-1) mod 3,
until no such hole exists. This is exactly the combinatorial transition in
`experiments/hole_hopping_closure.py`; it does not certify canonical entry or band survival.

The falsifier tests the universal claim:

> For every finite nonempty M, some finite sequence of legal abstract arcs removes all M.

If true, no predicate depending only on M, preserved under every arc in this abstraction,
can hold initially and exclude the empty set. This would reject a specified proof class,
not the possibility of a canonical resource bound with additional state.

## Why it matters / weakest missing edge

The desired nonconstructive route needs a finite nonempty M, all absent at a certified H,
and a strict upper bound on the number of distinct members that can first appear after H.
Such a bound must be strictly below |M|. Merely naming this count is not a new lemma.
If hole-only dynamics allows emptying every M, a bound must constrain actual future
entry classes, band survival, or a nonrenewable resource external to M.

## Acceptance and stop (frozen before computation)

- Produce a complete paper proof of the finite absorption claim or a smallest counterexample.
- Test all subsets of 1..12 as a fixed exhaustive regression, including empty/singleton,
  one-residue sets, consecutive sets, and the canonical delayed first-hit control 4@131.
- Discovery/holdout: not a fitted conjecture; 1..12 is a frozen finite regression of a
  proposed all-finite-sets proof. Do not call it an unused canonical holdout.
- Stop this abstraction if every finite M reaches empty. Do not extend the horizon or
  claim that the abstraction is the actual orbit. No more than one model repair in this unit.
- Time scope: initial triage, approximately 20 minutes; other patterns are investigated separately.

## Provenance / no-go

- `HoleHopping.chain_lands_first_fresh`, `comb_sweep`, and residue bookkeeping are
  PROVED-LEAN, but require the relevant actual trajectory/freshness conditions.
- E-031 already computed that unlimited-band combinatorics can fill 852655 in a large
  hole list. This unit asks for a precise general statement of that abstraction limitation.
- E-056 defeats survival from seed density/range/parity, one-use, and fixed-prefix inclusion.
- E-052/E-053 forbid combining a free eventual cutoff with an unrelated checked prefix.

## Evidence, semantic audit, and decision

### Paper proof

If M is nonempty, choose c = max(M) mod 3. The first removal of that arc is max(M),
and subsequent removals cannot add a hole. Thus the resulting set has strictly smaller
cardinality. Induction on |M| gives a sequence of at most |M| nonempty arcs ending at
the empty set. For M empty, zero arcs suffice.

More strongly, repeatedly using any fixed permutation of the three entry classes also
empties M within at most 3|M| attempted arcs. In any three consecutive attempts, either
some removal occurs, or M remains unchanged throughout; in the latter case the attempt
whose entry equals max(M) mod 3 would remove max(M), a contradiction. Hence every
three attempts while M is nonempty decrease cardinality at least once.

The nonempty-arc bound |M| is sharp: for M={1,4,...,3k-2}, every nonempty arc removes
exactly one member. Its next demanded residue is 0, while every remaining member has
residue 1. It therefore takes k nonempty arcs. No fixed bound independent of |M| follows
from the three residue classes alone.

Finally suppose a predicate P on finite hole sets is preserved under every abstract arc,
P(M0) holds for some finite M0, and P(empty) is false. Apply preservation along the
finite path just constructed. This proves P(empty), a contradiction. This no-go concerns
predicates depending only on the remaining set and closed under the whole abstraction.

### Exact regression

Command: `python3 experiments/parallel20260907/holes_capacity.py`.
Source revision and script SHA-256 are in
[`data/parallel20260907/holes_capacity.txt`](data/parallel20260907/holes_capacity.txt).

- `COMPUTED`: all 4,096 subsets of 1..12 empty under the greedy maximum-entry policy;
  maximum 5 nonempty arcs, zero bound violations.
- `COMPUTED`: all 24,576 subset/permutation combinations empty within 3|M| attempts;
  maximum 12 attempts, zero violations.
- `COMPUTED`: one-residue families of sizes 0,1,2,12,100,1000 take exactly that many
  nonempty arcs.
- `COMPUTED`: the canonical holes M={4,5,19}, all absent through clock128, are all
  filled by clock99734 (first occurrences 131,129,99734 respectively).

These computations are regressions of the all-finite-sets argument, not its proof.

### Semantic audit and decision

The abstract rules are the E-031 rules with arbitrary entry classes and unrestricted
band survival. The proof makes no claim that its sequence of abstract arcs is realizable
from `stateAt H`. Therefore it refutes only hole-set-only preservation in this abstraction,
not a canonical invariant that constrains entry or survival. Conversely any proposed
hole-only invariant that claims closure under every stated rule must admit the empty set;
the paper statement implies exactly this intended consequence.

The canonical control also defeats a universal claim that every nonempty finite set of
current holes retains a hole forever. It does not rule out some specially chosen set M.
No counterexample to the absorption claim was found and no repair was needed.

Decision: stop pattern⑤'s hole-only abstraction. A serious second attempt must provide
an independently proved limit on future entries/survival or a resource with a strict
budget below |M| whose replenishment is controlled. Merely counting remaining holes,
three residue classes, or initial arcs cannot supply that missing bound. This is a
precise extension of the existing E-031 obstruction, not a new non-surjectivity proof.
