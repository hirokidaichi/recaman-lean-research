# Hypothesis card: bounded history summaries and a two-step entrance

- ID: `H-20260907-04`
- Owner: entry_barrier worker (proposer, falsifier, paper prover, auditor performed separately)
- Created: 2026-09-07
- Status: `PROVED-PAPER`
- Research branch: pattern 1, inductive state abstraction
- Source revision: `612fcfaf74bfb49f3ae05a268057c82f70dcca26`

## Exact statement fixed before computation

For every finite set F of natural numbers, natural B with every x in F satisfying x <= B,
positive m <= B with m not in F,
and positive modulus Q, there exist arbitrarily large clocks n with two finite seen sets H0,H1 and
one common current value v such that:

1. H0 and H1 agree on all values <= B, contain F and v, omit m, and have equal
   cardinality, maximum, sum, and residue-count vectors modulo Q.
2. Both satisfy |Hi| <= n+1, max Hi <= n(n+1)/2, and v has canonical clock parity.
3. Actual Basic.step transitions at clocks n+1,n+2 from (v,H0) hit m in one branch
   and do not hit m in the other.

This is a proposed no-go for *exact two-step prediction* from the listed summary,
not a claim that no sound inductive invariant or canonical-specific abstraction exists.
No canonical reachability of either full seed is claimed.

## Why it would matter

Separate a concrete finite summary from the history membership needed at a first-hit entrance.
An explicit indistinguishable pair prevents mistaking count/max/density/low prefix/residues
for a closed deterministic state description. This is different from a survival-ratio counterexample.

## Provenance and dependencies

- Basic.step, CanSubtract; no unverified canonical trajectory assumptions.
- Existing E-056 is a broader finite-prefix survival countermodel, but it does not address
  equality of aggregate summaries with different immediate target reachability.

## Falsification plan

- Small m=1 and Q=1, boundary of strict positivity, candidate equal to current value.
- F containing a canonical prefix, while m is a genuine hole at that prefix cutoff.
- Discovery: exact finite algebraic instances, n chosen by the explicit construction.
- Holdout: none needed for a universal paper construction; finite regression is not holdout evidence.
- One repair allowed for arithmetic boundary assumptions only.
- Stop: construction needs a hidden future witness, cardinality/range/parity fails, or conclusion
  is upgraded from weakened histories to canonical orbit without proof.

## Acceptance and stopping

Acceptance is an explicit formula plus complete paper argument and exact Basic.step regression.
Do not implement Lean in this first pass. If successful, close the tested summary branch and identify
which extra information would distinguish the pair.

## Paper proof (PROVED-PAPER)

Choose n arbitrarily large, with

- n >= max(B+2, |F|+5, 4Q+m+5, 10), and
- n(n+1)/2 congruent to m+3 modulo 2.

The parity condition always has arbitrarily large solutions (triangular parity has
period four). Put c=n+m+2, v=2n+m+3, C=F union {0,v}, and

```
H0 = C union {c+Q, c+2Q}
H1 = C union {c, c+3Q}.
```

All four exchange values lie strictly between B and v-1 and are distinct. Thus the
low window agrees, both cardinalities are |C|+2, both maxima are v, and both added
sums equal 2c+3Q. All four exchange values have residue c modulo Q, proving equality
of every residue count. The chosen n gives |Hi|<=|F|+4<=n+1 and
v<=3n-6<=n(n+1)/2. Also v has the prescribed canonical parity and m remains absent.

From H0, subtraction at n+1 is legal because v-(n+1)=c>0 and c is fresh. At n+2
its candidate is c-(n+2)=m>0, still fresh; the path is v,c,m. From H1, c is seen,
so the first transition adds to 3n+m+4. Its next candidate is 2n+m+2=v-1,
which is above F and every exchange value and below v, hence fresh. The second
path is v,3n+m+4,v-1, and neither new value is m. This completes all quantifiers.

## Canonical negative control (COMPUTED)

The universal construction does not require either state to be canonical. A separate
exact counterfactual starts with the real history at clock 99,732, current value 199,486.
Replace the two historical values 99,819 and 99,885 by the two fresh values 99,753 and
99,951. These two pairs have equal sum and lie in one residue class modulo 66.
The following data agree between the real and modified histories:

- membership throughout [0,99,752];
- cardinality 74,019; maximum 592,216; sum 6,531,531,584;
- every residue count modulo 66;
- the entire canonical prefix through clock 37,424 is included.

The real path is 199486 -> 99753 -> 19. The modified path is
199486 -> 299219 -> 398953. The modified seed is NOT claimed to be canonically
reachable. This is a fixed witness found after the initial protocol, not holdout data.

## Evidence log

| Label | Command / source | Result |
|---|---|---|
| `PROVED-PAPER` | construction above | Universal two-step summary indistinguishability |
| `COMPUTED` | `python3 experiments/parallel20260907/entry_probe.py --limit 1000000` | Four exact constructions, including m=1 and canonical-prefix seeds, pass |
| `COMPUTED` | `python3 experiments/parallel20260907/entry_canonical_swap.py` | Canonical/modified pair above passes all equality and path checks |

Exact output, source revision and SHA-256 appear in
[`entry_probe.txt`](data/parallel20260907/entry_probe.txt) and
[`entry_canonical_swap.txt`](data/parallel20260907/entry_canonical_swap.txt).

## Semantic audit

- The result excludes exact two-step prediction from THIS summary, not sound
  nondeterministic abstract transitions, all possible invariants, or canonical-specific proofs.
- A sound abstraction may include both futures; an invariant could still exclude the entire
  ambiguous abstract state from some later canonical region. Neither possibility is refuted.
- Adding candidate c membership distinguishes this pair. Iterative adaptive refinement is not
  disproved, but would require a proof that the retained membership information closes.
- Density/range/parity/prefix inclusion are explicitly included; canonical joint generation is
  deliberately absent, and this is the mathematical limitation.
- No Lean source changed; no `PROVED-LEAN` claim is made.

## Decision

Stop the tested aggregate-only deterministic abstraction (`STOPPED` as a research branch).
Retain the explicit no-go as `PROVED-PAPER`. Its strategic score is low for a positive proof,
but it is a useful regression for future state summaries. Reopen only with a specified extra
relation that separates the canonical counterfactual and has a proved transition rule.
The next bounded question is whether a proposed adaptive high-candidate membership rule
can preserve that relation without expanding to the full history; no such rule was found here.
