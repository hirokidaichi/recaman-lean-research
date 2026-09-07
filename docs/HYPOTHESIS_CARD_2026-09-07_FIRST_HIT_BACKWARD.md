# Hypothesis card: backward first-hit source classification

- ID: `H-20260907-05`
- Owner: entry_barrier worker (four roles separated sequentially)
- Created: 2026-09-07
- Status: `STOPPED`
- Research branch: pattern 2, backward first-hit analysis
- Source revision: `612fcfaf74bfb49f3ae05a268057c82f70dcca26`

## Exact bounded question fixed before computation

For every canonical first occurrence a(T)=m with 1<=m<T, strip the largest suffix
of alternating addition/subtraction pairs immediately before the final subtraction.
Classify the source that remains, the required old low-candidate rail, and any fresh
band values. Does this classification force a nontrivial source restriction beyond
late_landing_iff and the forward chain identities?

Two proposed restrictions to falsify before any formalization:
(A) a late first hit whose predecessor m+1 was already visited before T-2 cannot
have an addition immediately before the final subtraction;
(B) in the maximal backward descending-chain segment, every positive blocked small
candidate was present before the chain began (no internal supply).
(A) is a local exclusion only; it is not itself a global target-avoidance result.
(B) will be tested and then either proved with exact scope, repaired once, or stopped.

## Why it would matter

A backward classification is useful only if it removes source cases or yields a new
causal constraint. A restatement of the entrance equality or of complete history is a stop.
No earlier-smaller regenerate, fixed-clock enumeration, or survival-ratio repair is allowed.

## Falsification plan

- Small canonical first hits, endpoints m=1 and T=m+1.
- Negative controls 4@131 and 19@99734 must remain admitted.
- Weakened-history actual step pair from H-20260907-04.
- Discovery/regression: canonical clocks 0..1,000,000, all late first occurrences;
  this is already-explored repository territory and will NOT be called a new holdout.
- Unused holdout: none yet. Only freeze one after a genuinely new statement survives;
  a local algebraic proof requires no statistical holdout.
- One permitted repair: add the precise non-overlap inequality identifying whether
  a small candidate could equal a value produced earlier in the same segment.
- Stop: all source constraints reduce to existing chain equations, or canonical
  counterexamples violate the proposed provenance restriction.

## Acceptance

Return exact source formulas and exhaustive finite classification, a paper proof if available,
and one explicit strongest remaining source obligation. No Lean implementation in this pass.

## Second pass, fixed before running it

The first pass's transported blocker history also holds for E-056; it does not separate
canonical from seeded trajectories. The exact next falsifiable candidate is:

(C) For every canonical late first hit (T,m) whose maximal backward chain has an SS
source and k>0, every required small blocker b=m+3j (1<=j<=k) has FirstAt(a,b,tb)
with tb<=b.

This adds an SS-source and a genuine canonical first-hit condition to a birth-clock/value
comparison. The general birth contraction branch was previously stopped; this is a bounded
negative-control test of whether the new source restrictions distinguish it, not a revival
of that branch. The bound tb<=b is the intrinsic late-first-occurrence threshold, not a
fitted constant. If false, preserve the first full canonical coexistence witness and stop
this refinement without shifting the bound. Test range is the same 0..1,000,000 regression,
not holdout. Small cases and 19@99734 remain controls.

## Paper result: frozen old rail and source classification

For a late first hit a(T)=m, let k be the maximal number of AS pairs immediately
before the final S, and put p=T-1-2k, h=m+1+3k. Then a(p)=p+h=T+m+k. For i<k,
the small candidate used at p+2i+1 is b_i=h-1-3i=m+3(k-i).
The lower and upper values within this chain are respectively

```
L_j = p+h-j                 at p+2j,
U_j = 2p+h+j+1             at p+2j+1.
```

Before the use of b_i, all produced values are L_j (j<=i) or U_j (j<i). But

```
L_j-b_i = p+1+3i-j > 0,
U_j-b_i = 2p+j+2+3i > 0.
```

Thus none of them can first produce b_i. Since the actual addition at its use
requires positive b_i to be seen, b_i was seen strictly before clock p. This proves
(B) uniformly, with no extra non-overlap assumption: the permitted repair is unused.
The k blockers are distinct and positive; 0 and a(p) are distinct from them. Canonical
history has at most p+1 distinct values, hence k+2<=p+1, so k<=p-1 and T>=3k+2.
These are `PROVED-PAPER`, not Lean-audited declarations.

For k>0, p>=2. If the transition at p is S, maximality of the stripped suffix forces
the transition at p-1 to be S too: the source is SS. If it is A, the two additions
at p,p+1 end before S at p+2. The existing no-double-addition-run theorem forces
p-1 to be A too. Therefore

```
a(p-2) = a(p)-p-(p-1) = m+5k+3-T >= 0,
T <= m+5k+3.
```

For k=0 and source A, a(T-2)=m+1, a comb predecessor. In the genuinely late range
T>=m+4, m+1 must itself be a first occurrence at T-2: any subtraction is fresh,
and an addition cannot produce a positive value smaller than its clock. Consequently
restriction (A) follows in that range. The originally broader boundary version (A)
was tested with zero violations but is not promoted to a paper theorem here.

## Exact finite classification (COMPUTED)

Canonical [0,1,000,000] contains 286,261 late first occurrences:

| Source | k=0 | k>0 |
|---|---:|---:|
| A | 285,663 | 3 |
| S | 265 | 330 |

The three positive-length A sources are (T,m,k)=(23,18,2),(77,75,5),(136,132,1).
All satisfy the paper bound. No violation of (A) or (B) occurred.

The required negative controls remain admitted:

- 4@131: k=0, A source from the first hit 5@129, then 5 -> 135 -> 4.
- 19@99734: p=99715, k=9, SS source, old blockers 46,43,40,37,34,31,28,25,22.
- 61@181653: p=181648, k=2, SS source, old blockers 67 and 64.

## Second-pass falsification: restriction (C) is REFUTED

Of 330 positive-length SS chains, 215 contain a blocker first born after its own value.
There are 62,919 required blocker occurrences across these chains. The first counterexample
is already the parent of the 4@131 control:

```
T=129, m=5, p=120, k=4
SS source: a(118)=377 -> a(119)=258 -> a(120)=138
word from clock 118: SS(AS)^4 S
old blockers: 17,14,11,8
late-born blockers: 17@25,14@31,8@16
```

All four blockers are jointly generated by the canonical orbit before p. The fresh
lower rail 137,136,135,134 and final value 5 coexist with those old blockers exactly as
required. The proposed birth-time/value contraction fails even though T/m > 25.
No constant repair or added arbitrary delay threshold was attempted.

## Evidence and reproducibility

| Label | Command / dependency | Result |
|---|---|---|
| `PROVED-PAPER` | argument above; `DescendingChain`; `NoDoubleAdditionRun` | frozen old rail, k<=p-1, and SS/A source classification |
| `COMPUTED` | `python3 experiments/parallel20260907/entry_probe.py --limit 1000000` | complete classification and negative controls |
| `REFUTED` | `python3 experiments/parallel20260907/entry_source_birth.py` | C fails at 5@129; 215 bad chains |

Exact outputs with source revision and script hashes are
[`entry_probe.txt`](data/parallel20260907/entry_probe.txt) and
[`entry_source_birth.txt`](data/parallel20260907/entry_source_birth.txt).

## Semantic audit and decision

The old-rail transport is stronger than per-use membership in its time parameter but is
not a new canonical separator: actual seeded countermodels also satisfy its proof. The
finite classification and source bound do not exclude the 19 landing. The narrow source
restriction (C) is directly refuted by a genuine jointly generated canonical example.

Therefore the attempted route to a global barrier is `STOPPED`. There is no independently
supported new canonical inequality from this pass; we should not turn the classification
into a wrapper issue or reopen earlier-smaller regeneration. No Lean implementation was made.

The remaining obstruction is simultaneous existence of (i) the old arithmetic-progression
blocker rail and (ii) the fresh descending band at a canonically reached SS source. Merely
asserting that the required rail/band configuration cannot complete is equivalent to
excluding the landing and is not an acceptable next lemma. A next investigation would have
to propose an independent joint-birth inequality that separates the fully canonical 5@129
and 19@99734 controls while constraining later sources. No such inequality has been identified
here. Prioritize another branch that actually supplies one; preserve this two-rail packet
as its falsification input.
