# One-SS minimum supply: one source per A run

`PROVED-PAPER` (E-127). This theorem uses the complete two-family paper
classification E-121. It is not yet a Lean theorem. It bounds the one-SS
class alone, not its union with the clean/short classes.

## Statement

Let e be any two-sided Bool stream that has no SAAS. Call a current A at t
one-SS supplied if its shortest P2 backward window exists and contains
exactly one adjacent SS pair, with overlapping pairs counted separately.
At most one such source lies in any consecutive run of A signs.

Consequently, in every periodic NoSAAS word of positive period p, the
number of one-SS supplied A phases is at most the number of cyclic A runs,
which is at most the number of S phases. The period mass may be positive,
zero, or negative. The one-SS lag has no fixed numerical upper cutoff.

## Proof of the run bound

By E-121, a shortest one-SS P2 window is family A or family B. Family A
starts S and ends S, with exactly one enlarged internal A gap of length4.
Family B starts AS and ends S, with exactly one enlarged internal A gap of
length3. All other positive internal gaps have length1. Therefore a family-A
source is the first A after an S, and a family-B source is the second A
after an S. No third or later position in an A run can be a one-SS source.

Suppose one run had two sources. They must be consecutive times t,t+1,
with family A at t and family B at t+1. Let u be the first source's shortest
backward P2 window. Write the second source's shortest window as A v,
removing its first A, which is the sign at t. Then u and v are both prefixes
of the same backward history at t. Both start and end with S. The internal
A gaps of v are exactly those of the family-B word, since only its initial
endpoint A was removed.

The prefixes are comparable by inclusion. Every internal A gap of the
shorter S-ended prefix persists, with the same length and both bounding S
signs, as an internal gap of the longer prefix. If u is shorter, its gap4
would be an internal gap of v, which only has gaps0,1,3. If v is shorter,
its gap3 would be an internal gap of u, which only has gaps0,1,4. Equality
is impossible for the same reason. Every case is a contradiction.

An A run unbounded to the left cannot contain a qualifying source, since
the displayed windows force an S one or two signs before it. Thus no
unmentioned finiteness assumption on runs is needed.

## Periodic capacity

If the period is all A, every backward word has positive moment and hence
has no P2. If all S, there are no A sources. Otherwise each cyclic A run has
a unique preceding S phase and different runs have different such phases.
The run bound gives an injection of qualifying sources into those S phases.
This also handles runs crossing the chosen period boundary. No step assumes
that a periodic word is canonically realizable.

This map uses the S immediately preceding the current A run (backward
offset1 for family A and2 for family B). It is a consequence of the run
multiplicity proof, not an offset adjustment of the refuted centered rule.
Many distinct A runs can share one old SS pair, so the theorem is consistent
with the unbounded shared-SS demand of E-122.

The images may overlap images used for clean or other short sources.
Therefore separate inequalities for clean supply and one-SS supply cannot
be added to conclude a capacity bound on their union.

## Why the separate maps cannot simply be combined

For every family-B source at t, the signs at t−2,t−1,t are S,A,A.
NoSAAS forces e(t+1)=A. Its past3 word is AAS, a minimum clean P2 window.
The run-predecessor map sends t to t−2, and the clean lag3 map sends t+1
to (t+1)−3=t−2. Thus every B source produces a collision between these
particular maps. This is a paper implication from the exact local signs,
not a capacity counterexample or a claim that no alternative map exists.

An explicit positive-mass periodic example is `SSAAASASASAAA`, p13, mass3.
It avoids cyclic SAAS. Phase11 has minimum one-SS lag11, word ASASASAAASS;
phase12 has minimum clean lag3, word AAS. Both proposed charges are S phase9.
The independent direct moment scan is saved in
`docs/data/issue73_20260910/one_ss_union_control.txt`, from the same-named
Python source. This concrete control is part of the final semantic audit,
not a repaired run-capacity rule.

## Finite falsifier and limits

The frozen direct enumerator checked all binary periods1..17, filtered only
by cyclic NoSAAS, with all period-mass signs included. It directly scanned
backward moments, found the first P2, and checked the proposed per-run
uniqueness only when that first window contained exactly one SS.

The2p scan is complete for this predicate: a periodic word without an SS
has no one-SS window, while a window of2p+1 signs has2p adjacent edges and
therefore contains two copies of every cyclic SS edge. Thus a one-SS
window must have length at most2p. This is an argument about this class,
not a replacement for the general positive-mass P2 cutoff.

The source and exact output are
`experiments/issue73_20260910/one_ss_run_capacity.py` and
`docs/data/issue73_20260910/one_ss_run_capacity.txt`.
Discovery was periods1..11 and holdout12..17. At p17 alone,40,598 NoSAAS
words and4,335 qualifying phases passed. An additional unrestricted
period≤13 search found no counterexample to the run bound; this does not
justify dropping NoSAAS from the paper proof. No additional range or rule
repair was attempted.
