# Independent scope and paper-proof audit of the five patterns

- Auditor: entry_barrier worker, acting in a separate read-only audit pass.
- Date: 2026-09-07.
- Base revision: `612fcfaf74bfb49f3ae05a268057c82f70dcca26`.
- Scope: H-20260907-04 through H-20260907-08, their exact logs/scripts, and existing
  `Recaman/PeriodicCandidateNoGo.lean` / `docs/PERIODIC_CANDIDATE_NOGO_2026-09-01.md`.
- This file is the only file edited in this audit pass. No additional computation is
  being presented as a mathematical proof; no Lean audit was performed here.

## Conclusion

The first, second, third and fifth units justify stopping their *tested proof classes*,
not declaring any of the five broad research methods impossible. Pattern 4 has a valid
reduction to a new positive-sign-sum finite-word obstruction. At the time of this read,
its all-period combinatorial lemma is still being independently proved/audited by the
other workers. Its discovery/holdout census is not an all-period proof.

No fatal algebraic error was found in the inspected completed paper arguments. Two
small details were identified and have now been corrected by pattern 4's author:
discard the entire finite preperiod history, and use n>=max(1,2C+1) for the displayed
numerical bound. I reread the corrected card. Neither is a substantive new hypothesis.

## Scope table for the final ranking

| Pattern | What the evidence actually excludes | What remains allowed |
|---|---|---|
| 1, aggregate state summary | Exact deterministic two-step target prediction on arbitrary finite-history states from the specified low window, count/max/sum/modulus summary | Sound nondeterministic abstractions, predicates that exclude an ambiguous abstract state, adaptive summaries, and any canonical-only reachable-state invariant |
| 2, backward first hit | The particular SS-source claim that every small blocker was born no later than its own value | Other first-hit obstructions; source-dependent inequalities; a stronger joint-birth relation. The old-rail transport remains a valid local theorem |
| 3, joint generation | Replacing chronology by a bounded-gap connected support, even together with E-056's other payloads | Timestamped birth/predecessor consistency, simultaneous producer-run realizability, and stronger global inequalities |
| 4, macro induction | If the all-period word lemma is completed: eventual repetition of one fixed finite sign word in an exact finite-history continuation | Variable-length blocks, aperiodic macro schedules, symbolic systems with infinitely changing block parameters, nonperiodic avoidance, surjectivity or its negation |
| 5, multiple holes | A hole-set-only predicate preserved under every arc of the arbitrary-entry/unlimited-band abstraction and excluding empty | A specially chosen canonical finite hole set protected by restrictions on actual entries, band survival or an independently bounded resource |

Thus a rank should compare the next **independent mathematical input** available in
these units, not probabilities that an entire broad method can ever work. None of the
five completed finite experiments is evidence of a permanent missing canonical value.

## Pattern 1 checks

The exchange family H0=C union {c+Q,c+2Q}, H1=C union {c,c+3Q} has matching
cardinality, sum and each residue count because all four exchange values lie in the
same class modulo Q and the pair sums agree. The stated clock bound puts all exchange
values above B and below v-1. The two paths v,c,m and v,3n+m+4,v-1 follow the actual
strict-positive/fresh rule. The parity choice permits arbitrarily large n, not every n.

The canonical swap is particularly useful as a regression because H0 is actual. H1
is still an arbitrary modified seed; inclusion of a canonical prefix through 37424 does
not assert that the intervening history can be generated. A deterministic function
restricted to canonical states could always recover the unique history from its clock;
that possibility is expressly outside this no-go.

Minor notation: for F empty, read B>=max F as `for every x in F, x<=B`, or adopt
max(empty)=0. The proof and explicit empty-F regression need no extra assumption.

Novelty boundary: E-056 already separates prefix/density from full reachability. This
unit adds *equal* aggregate summaries and opposite immediate target reachability, not
an independent obstruction to canonical survival.

## Pattern 2 checks

For the frozen chain formulas, before b_i is used, produced lower and upper values
satisfy L_j-b_i=p+1+3i-j>0 and U_j-b_i=2p+j+2+3i>0. Consequently no first production
of b_i lies in this chain. Since b_i is positive and forces addition, it must lie strictly
before p. Distinct blockers, 0 and a(p), together with the canonical history bound,
justify k+2<=p+1. This is a correct strengthening of the time at which membership is
known, but is a corollary of local formulas plus history monotonicity/counting.

The source split uses maximality of the stripped AS suffix and the already proved
no-run-of-exactly-two-additions lemma. For k>0, p>=2 and an A source forces the
previous sign to be A; subtracting those two additions yields
`a(p-2)=m+5k+3-T`, hence the claimed inequality. No new global supply estimate occurs.

The original broad restriction (A) is only computationally tested. The card promotes
only the T>=m+4 case to paper proof, which is correct because producing m+1 by addition
at clock T-2 is then impossible. Final reporting must preserve this distinction.

The explicit 5@129 witness directly refutes C with canonical provenance and also
explains the later 4@131 control. Neither the census nor C's failure means all backward
methods fail. No fresh independent positive lemma was obtained in this pass.

## Pattern 3 checks

Connected-support necessity is sound: a path from one side of a support gap to the
other must cross it in one step, whose size is at most B. It imposes no ordering or
greedy sign chronology on the sorted support.

Continuation-preserving extension is also sound. Additions remain forced on enlarging
history, while a prescribed subtraction remains legal exactly when no added value
matches that subtraction output. A step induction gives the equality of future paths.

For the bridge lemma, among q+1 consecutive proposed points one is outside Q; every
inserted advance is between B-q and B. All advances are disjoint inside the original
gaps, so the cardinality bound |T|(B-q)<=max S follows. The E-056 substitutions
B=80J+14+2*((5J+1) mod 2), c=B+2J+3, q=J+D+3<=2J+3 give
`2D(B-q)-(Dc+4J)>=D(74J+5)-4J>0`. The density estimate and unchanged maximum/parity
therefore follow. No lost fresh subtraction value was hidden in the bridge set.

Novelty boundary: this is a stronger E-056 countermodel, now with connected support.
It does not settle compatibility of the producer intervals found in #71 with a single
chronological trajectory. The card accurately stops only this compressed replacement.

## Pattern 4: consistency with the earlier periodic no-go

Let epsilon_t be the sign into clock t. For balanced period sum S=0, the value-period
drift is

```
D_r = sum_(i=1)^p i*epsilon_(r+i).
```

The earlier candidate-period drift is `C_r=D_r-p`. Therefore

```
sum_r D_r = 0,
sum_r C_r = -p^2,
D_(r+1)-D_r = C_(r+1)-C_r = p*epsilon_(r+1),
```

up to the explicitly chosen phase-origin shift. These claims are consistent. Since
p>0 and epsilon is always +1 or -1, the D_r cannot all be zero; sum zero then forces
a negative phase. Thus a nonnegative *value* walk excludes the balanced case even
without a candidate floor. This is an application/variant of the old balanced
arithmetic, not a new positive-drift supply theorem.

For S<0 the common leading quadratic coefficient is negative, so nonnegative values
are impossible. For S>0 the old theorem permits quadratic divergence; that is exactly
the case the new blocker-supply argument must address. One must not claim that the
old periodic theorem already excludes all periodic exact Recaman continuations.

### Positive-drift supplier lag

On each eventual phase write `x_n=A*n^2+b_r*n+c_r`, where A=S/(2p)>0 and the finite
phase sets satisfy |b_r|<=B, |c_r|<=C. A candidate at a sufficiently late addition tends
to infinity. Therefore remove as potential suppliers **all** seed and preperiod values
up to the onset of the polynomial formula, a finite set. Restrict the supplier j to the
remaining polynomial tail.

For n=t-1, j=n-d>=0 and candidate equality x_n-x_j=n+1, one indeed has

```
n+1 >= (A*d-B)*(n+j)-2C.
```

To obtain the displayed `(B+2)/A` bound cleanly, choose n>=max(1,2C+1). If Ad-B<=0
it is immediate. Otherwise divide by n+j>=n and use
`n+1+2C<=2n`, obtaining Ad-B<=2. Without this positivity case distinction the same
conclusion still follows, but an informal division argument should not silently reverse
an inequality. The weaker phrase merely n>=2C does not by itself yield the exact
constant 2 for small n; the preceding sufficiently-late quantifier permits this repair.

There are finitely many phases and lags. A nonidentical affine equality holds for at
most one t, so an addition phase recurring infinitely often needs at least one lag
with both coefficients identically correct:

```
sum_(i=1)^d epsilon_(t-i)=1,
sum_(i=1)^d i*epsilon_(t-i)=0.
```

The script's moment with weights i-1 equals -1, an exactly equivalent condition.
Writing d=qp+r yields 1=qS+s_r, s_r>=-r, r<p, so q<=p and the finite search bound
p(p+1) is safe. Subtraction freshness is not needed for this *necessary* addition
supply condition. Proving that no positive-sum word meets it for every A phase would
be sufficient; observing that fact through period 18 is not.

Essential assumptions remaining: finite history before the periodic tail, exact greedy
forced-addition behavior, nonnegative values, signs in {+1,-1}, and eventual fixed finite
period. Infinite preload invalidates the finite-supplier elimination. A fixed finite word
repeated with changing length or signs does not satisfy the hypothesis.

## Pattern 5 checks

Choosing the residue of max M always removes at least one member in the stated
abstraction. Cardinality induction proves at most |M| nonempty arcs. The cyclic
three-class argument also works because if an entire three-attempt block made no
removal, M stayed constant and its maximum's class was nevertheless tried. The family
{1,4,...,3k-2} verifies sharpness of the nonempty-arc bound.

Predicate preservation gives a genuine no-go only when it is quantified over every
arc admitted by that abstraction. The actual orbit has additional entry and survival
constraints; the constructed emptying path need not be canonically realizable. The
canonical example {4,5,19} refutes a universal claim about every current finite hole set,
not an existential claim about some specially protected finite set.

Novelty boundary: this makes the E-031 unrestricted-hole-hopping limitation uniform
and explicit. It does not produce a strict canonical capacity below the number of holes.

## Handoff recommendation

Preserve separate statuses for (a) a proved no-go/transport theorem, (b) the candidate
it refutes, and (c) the broader research direction. If pattern 4's word lemma is completed,
rank its new obstruction as a structural restriction on proof strategies, not as a proved
route to non-surjectivity. If it remains open, label it CONJECTURED with COMPUTED finite
support. None of the present units licenses claiming that the road to a permanent missing
value is now known.
