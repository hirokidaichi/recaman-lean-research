# C1 depth: old-window count barrier and an A-count stopping line

Cycle R-20261023-01 / card H-20261023-01. Main depth claim is PROVED-LEAN (E-386); az<=3 Q is PROVED-LEAN (E-387). General Q/C1/H remains CONJECTURED.
Original left base is always 0. Here `A` counts **all** additions, not only nonsupplied additions.

## Unit 1: a necessary count barrier (proposer, before implementation)

Let `v=w[n,b)` have a additions and s subtractions, length l=a+s, mass f=a−s.
Suppose an actual P2 window starts at t<n in a padded BlockWord prefix and ends at b>n.
Its old suffix has mass r=1−f=s−a+1≥1 and area B>0. The split identity gives

```text
B + areaW(v) + l*r = 0.
```

For fixed a,s, moving every S before every A minimizes area:

```text
2 areaW(v) ≥ a(a+1)−s(s+1)−2as.
```

Each adjacent AS→SA swap lowers area by 2, so this also follows by induction on letters.
The old suffix has `r(r+1)≤2B+2` by E-381. Substitution and cancellation give

```text
0 ≤ 2s(2a−s−2).
```

If s=0, r≥1 forces a=0 and l=0, contradicting b>n. Therefore s>0 and

```text
a ≤ s ≤ 2a−2.
```

The boundary a=2,s=2 is still excluded by B≥1: required B≤0.
Thus no old window exists with at most two preceding tail additions.
This statement uses the **same actual word** for the BlockWord suffix and P2, not independent tags.
It does not prove the desired depth bound or bound nonsupplied additions by all additions.

## Falsifier plan and next finite-state question (frozen before execution)

Attack empty tail/s=0, one/two additions, equality s=2a−2, and the known old supply
`SAAA | SSSSAAA` (a=3,s=4, B=2). Equality is attainable there.
Dropping BlockWord can fail: its quadratic lower bound is indispensable.
No CPU search has yet been run for this unit.

Next candidate (CONJECTURED, fixed before computation): every prefix of a positive-deficit
excursion after a padded BlockWord, with at most three nonsupplied A, has at most seven total A.
Accept a full finite-state reachability certificate with a mathematically justified unbounded-S compression,
or a literal eighth-A witness with the original-base Endable ledger. Stop this candidate on a witness;
do not increase the A barrier silently. First eighth A is the stopping line, not a word-length cutoff.
For clocks before that stopping line, local P2 has length≤13 (at most seven previous A),
and old P2 is impossible once total S≥13 by the new count barrier.
Consequently all S gaps can be saturated only after preserving the last 13 signs and the S≥13 flag.
Before saturation retain exact S count; after it d>0 follows from A≤8 and S≥13.
Proof of this compression and independent checks are required before interpreting its graph as complete.

## First gate and new evidence (06:23 JST, before final semantic audit)

The count barrier has passed `lake env lean Recaman/BlockSuffixPositivity.lean`.
Its boundary is sharp at `SAAA | SSSSAAA`, so the factor two cannot be lowered blindly.
This changes the candidate set; the first15-minute continuation gate passes. The C1 exploitation
allocation continues; the conditional45-minute switch to joint-area/common-prefix is not triggered.

The first-eighth-A search finished both preregistered shards: mass0..8 (127 prefixes,
393507 visits) and mass9..13 (1993 prefixes,6163475 visits). Highest total A was7.
An independent all-start F/area implementation finished all2120 prefixes and6556069 visits,
again highest A7, endpoint depth at most4, and exactly the eight known z words.
It checked44 literal long-gap cases (11 distinct saturated contexts × four gaps13/26/257/4097).
The planned cap was128 contexts, but only11 qualifying contexts were reached; do not report128.
CPU: roughly1.14s user+system across the three graph runs, within the240s cap; exact logs are saved.

### Independent old-signature relaxation

Allow each old window its own BlockWord suffix signature (no common prefix), while preserving
all local P2 windows exactly and allowing either absent/present old supply when the signature fits.
This stronger model also cannot reach the eighth A: DFS4086 visits; independently constructed
BFS certificate3324 distinct states. Its only optional-old states are

| tail before an A | total A | total S | nonsupplied A |
|---|---:|---:|---:|
| SSSSAAA |3|4|2|
| SSSASSAAA |4|5|3|
| SSSSSSAAAA |4|6|3|

Thus common-prefix coupling is not needed for this particular first-eighth-A exclusion.
It is not a claim that arbitrary signatures can all be realized by one prefix.
All results here remain computational until the certificate and actual-word simulation are checked.
The generated finite-graph checker is a separate object; proving it closed does not by itself prove
the orbit/word depth claim. The simulation is explicitly the next Lean obligation.

An additional reduction follows from the same count barrier: before the eighth A an actual old
suffix has r=s−a+1≤a−1≤6, not merely13. A common representative of mass≤6 therefore suffices;
the computations above deliberately covered the larger mass≤13 set and need not be rerun upward.

## Final verified outcome

E-385/E-386/E-387/E-389 are PROVED-LEAN after the complete check406 jobs/2743 declarations.
E-386 supplies the card's original-base full-length depth4 statement and eight-word membership.
E-387 uses the312-state future checker plus the supplied fresh-minimum location to prove Q for all future lengths/depths when az<=3, and excludes every old P2 start.
The Int adapter preserves the same original p in Endable/countP and is an application adapter, not an additional research result.
E-389 supplies the finite first-supplied-A gap bound and one history-supported terminal ray.
The r4 follow-through is [E-388 / COMPUTED](RESEARCH_NOTE_2026-10-23_C1_FOUR.md), not a Lean theorem.
Next: [macro simulation](HYPOTHESIS_CARD_2026-10-24_C1_FOUR_KERNEL.md).
