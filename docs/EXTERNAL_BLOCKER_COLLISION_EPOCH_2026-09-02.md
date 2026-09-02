# External blocker collision epoch

Date: 2026-09-02  
Hypothesis: `H-20260902-01`  
Decision: `STOPPED`

## Conclusion

The proposed same-candidate collision test does not reopen branch A.  The exact H4 statement was
not refuted, but both its discovery and frozen holdout populations are empty: the standard orbit
has no candidate with four supplied successor demands through clock 20,000,000.  Raising the
threshold to eight, the only predeclared repair, preserves the same defect.

This is a semantic failure of the evaluator, not evidence for a collision theorem.  The test asks
for a property only after several recurrences of one candidate, while the hypothetical infinite
recurrence is itself the unresolved branch-A premise.  Consequently a same-candidate finite-use
threshold is not an independently falsifiable external-blocker-debt invariant.

## Frozen definitions

At a positive forced-addition use of candidate `c` at state clock `m`, the successor demand is
`w=c+m`.  The use is counted only if `w` has already occurred by clock `m+1`.

- `w` enters `S_c` if its first occurrence was a legal subtraction landing.
- If `w` was first produced by addition at clock `b`, its positive birth candidate
  `e=w-2b` enters `E_c`.
- H4 required `E_c ∩ S_c ≠ ∅` by the first four supplied uses of `c`.

These definitions use exact recurrence, history membership, first occurrence, and actual birth
type.  They do not use target occurrence, future return, or canonical reachability as a premise.

## Reproduction

Base revision (working tree contains the new probe):

```text
b0cde869612789d1351441168dced4ec6f24167c
```

Commands:

```bash
c++ -O3 -std=c++20 -Wall -Wextra -Wpedantic -Werror \
  experiments/external_blocker_collision_probe.cpp \
  -o /tmp/external_blocker_collision_probe

/tmp/external_blocker_collision_probe 2000000
/tmp/external_blocker_collision_probe 20000000
```

Discovery output:

```text
external-blocker-collision horizon=2000000 suppliedUses=1568 candidates=1567
candidates4=0 candidates8=0 everCollided=0
H4=not-refuted
H8=not-refuted
```

Frozen holdout output:

```text
external-blocker-collision horizon=20000000 suppliedUses=4798 candidates=4797
candidates4=0 candidates8=0 everCollided=0 maxSuppliedUses=2 mostReusedCandidate=723
max-use-detail uses=984,4596, E=643, S=
H4=not-refuted
H8=not-refuted
```

The labels `not-refuted` are literal falsifier results.  They must not be read as positive
evidence because `candidates4=0` and `candidates8=0`.

## Strongest evidence

- `COMPUTED`: through 20M there are 4,798 supplied successor-demand events but 4,797 distinct
  candidate values.  Only candidate 723 repeats, and only twice.
- `COMPUTED`: that two-use example has external birth blocker 643 and no subtraction-born demand,
  hence no `E/S` collision.
- The fingerprinted arbitrary seed from the previous epoch supplies candidate 20 three times,
  still below H4.  It therefore cannot make the test nonvacuous.

These facts do not state that four supplied uses are impossible, nor that an infinite rigid stream
cannot exist.

## Failed approach and semantic audit

The intended logic was that repeated demand supply would eventually force a value to serve both as
an external addition blocker and as a fresh subtraction landing.  The probe shows that the chosen
finite threshold cannot test this logic on either available exact population.  Absence of a
four-use example is also not a theorem and cannot be converted into a uniform use bound.

Lowering the threshold after seeing the data is not permitted by the card.  It would not help the
frontier anyway: the exact two-use example already has no collision.  Raising it to H8 is the one
allowed repair, but strictly worsens the empty-domain problem.

## Next decision

Do not formalize H4/H8 and do not try another same-candidate threshold.  A future A-branch unit may
reopen only with a quantity that:

1. aggregates debt across different candidate values or a fixed clock window;
2. has nonempty canonical and arbitrary-seed falsification populations before the conjecture is
   assumed;
3. produces a cutoff-independent strict inequality or unavoidable collision;
4. survives the existing parent-merge, overlapping-interval, and three-use fixed-seed examples.

Branch-A status remains unchanged: the infinite fixed-seed supply no-go is `CONJECTURED`, while
the present ancestry/drift route and this collision-threshold route are `STOPPED`.

