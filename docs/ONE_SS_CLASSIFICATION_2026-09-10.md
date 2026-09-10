# One-SS minimum P2 windows: complete gap classification

`PROVED-PAPER`: exactly two families occur. This is a structural classification,
not an A→S injection or a capacity theorem. The all-parameter family P2 equations
and gap encoding are `PROVED-LEAN`; arbitrary-word exhaustion and prefix
minimality below are not yet Lean statements.

Words are newest-first; A=+1,S=−1. P2 means mass1 and backward moment0.
A proper prefix corresponds to a shorter supplier lag. Assume exactly one
adjacent SS pair and no contiguous SAAS.

## Statement

Write the unique S-gap encoding as

`A^g0 S A^g1 S ... S A^gn`,

where n is the number of S signs. A P2 word is prefix-minimal exactly when:

- **Family A:** g0=gn=0; one internal gap z is0 and a different gap j is4;
  all remaining internal gaps1; n=6j−2z+1.
- **Family B:** g0=1,gn=0; one internal gap z is0 and a different gap j is3;
  all remaining internal gaps1; n=4j−2z+1.

In either case 1≤j,z<n and j≠z. The length is2n+1. This includes the short
lag7 and lag11 cases; it does not start at an arbitrarily chosen large lag.

## Exhaustion of arbitrary P2 words

Mass1 gives n+1 As. Each adjacent SS corresponds to exactly one zero internal
gap, including overlapping pairs in a longer S run. Hence exactly one internal
gap is0; the other n−2 internal gaps are positive. No SAAS says none of these
positive internal gaps is2. The n−2 mandatory As leave exactly3 extra As.
A positive internal gap can consume either no extras or at least2 extras.
Consequently the complete allocation list is:

1. No enlarged internal gap, and g0+gn=3 (four endpoint allocations).
2. Exactly one internal gap3, and g0+gn=1 (two endpoint allocations).
3. Exactly one internal gap4, and g0=gn=0.

No other allocation is possible. Put a=g0 and let h be the excess at the
enlarged gap j (h0,2,3; j is irrelevant for h0). The kth S position is
`2k−1+a−1[k>z]+h*1[k>j]`. Thus

`sum S positions = n²+n(a−1+h)+z−hj`.

Since the total length is2n+1, moment0 is exactly

`n(2a+2h−5)=2hj−2z+1`.                                   (1)

For h0, a0/a1 require z≥n, and a3 requires n<0. The only surviving case
is a2,gn1,n=2z−1. It begins AAS, a proper P2 prefix (n≥3).
For h2,a0, (1) gives n=2z−4j−1. Since z<n, z≥4j+2. Before the zero gap
there is therefore the complete prefix with4j+1 S signs, only one enlarged
gap3 at j, and both endpoint gaps0. It has length8j+3 and moment0:
its S position sum is `(4j+1)²+2(4j+1)−2j`, giving the required triangular
half-sum. It is shorter than2n+1. Equivalently it is the previously proved
SS-free clean family at parameter j.
The two remaining allocations are precisely family A (h3,a0) and B (h2,a1).
The arithmetic split and the room for the earlier clean prefix are Lean-checked.

## Both displayed families are minimal

First, mass and equation (1) show that every displayed family word is P2.
The explicit list constructor `gapWord a (familyGaps n j z h)` certifies this
for every legal parameter in Lean, including n, j and z without finite bounds.

Suppose a proper prefix were P2. It inherits no SAAS and has either zero or
one SS pair.

If it has no SS, the established SS-free classification (E-109) applies.
Such a P2 prefix is either AAS or starts S, ends S, and has exactly one
internal A gap3, with every other internal gap1. Family B starts AS, so it
cannot have either type. Family A starts S and has no internal gap3: a prefix
before its gap4 has only gaps1, a prefix ending within gap4 has it as an
endpoint gap, and a prefix after it retains the full internal gap4. Thus
family A cannot have either SS-free P2 type either.

If the prefix has one SS, apply the complete seven-allocation analysis above
before discarding nonminimal cases. Family A has g0=0 and its only possible
enlarged internal gap is the original gap4; a prefix cannot turn a partially
included end run into an internal gap3. Thus its only possible P2 allocation
is family A with the same j,z. Equation (1) then fixes the number of S signs
to the original n and the endpoint gap to0, so the prefix is the whole word.
For family B, g0=1 excludes every surviving allocation except family B itself;
again j,z and (1) fix n and the final endpoint gap0. This is also the whole
word, a contradiction. Both directions are complete.

## Evidence and limits

Frozen generator through n257 tested17,771 P2 words:5,483 minimal A,8,128
minimal B,128 with the earlier AAS prefix, and4,032 with the earlier clean
prefix. Discovery n≤63 and holdout n64..257 were fixed before the run. A raw
binary enumeration through length17 exactly matched the generator (11 P2
words,7 minimal). Computation is corroboration, not the proof above.

The centered-rule counterexample `SASAAAASSASASAS` is family A at n7,j2,z3.
It still refutes the proposed fixed charge; classification does not rescue
that rule. No capacity or Hall statement follows merely from two families.

Artifacts: `experiments/issue73_20260910/one_ss_classification.py`, its exact
output under `docs/data/issue73_20260910/`, and `Recaman/OneSSGapAlgebra.lean`.
