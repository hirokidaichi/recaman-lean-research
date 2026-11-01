# Issue 73: independent geometry / height-area pass

- Base revision: `b4b5afaaac126acaa0c4fc0042bdaa4fafd289a1`.
- Owner: joint_generation / geometry; no shared source or Lean edits.
- Initial status: `CONJECTURED`; statement frozen before new computation.
- Four roles: proposer → falsifier → paper formalizer → auditor, sequential.

## Bounded question

Let a p-periodic word ε have entries ±1 and positive sum S. Let H be its
integer height walk. Call an addition phase t an escape phase if, after that
addition, the walk never again reaches its previous height: equivalently
`Σ_(i=0)^(k-1) ε_(t+i)≥1` for `1≤k≤p`. Periodicity and S>0 then give the
same inequality for all k≥1.

Candidate G1: every escape phase has no P2 supplier lag, where P2 is
`Σ_(i=1)^d ε_(t-i)=1` and `Σ_(i=1)^d i ε_(t-i)=0`.
An escape phase always exists by the elementary last-upcrossing/cycle argument.
Thus G1 would prove the desired obstruction without a matching argument.

Acceptance: prove G1 for all periods or give an exact counterword. The single
allowed structural refinement, if G1 fails, is whether at least one escape
phase is unsupported; no numerical coefficient or period-bound repair.
Stop a selector if its defining claim has a counterexample; no general theorem
will be inferred merely from a finite scan.

## Context and falsification

The P2 finite-lag reduction is already independently audited. κ-minimum,
longest run, maximum period moment and oldest-S maps have recorded failures;
none is reused as a premise. P2 is a necessary supply condition only and does
not enforce subtraction freshness.

Small cases: all-plus words, SAAA's one supplied phase, and the earlier
counterwords SSASAAA and SSSSAAAASAAA. Weakened-history control: P2 may supply a
local A while the whole word is unrealizable as a greedy orbit.

New finite selector discovery: all words through period 12, stopping at the
first exact G1 violation. No new holdout or canonical-sequence census is
claimed. A counterexample is replayed with exact integer sum/area arithmetic.

## Outcome: escape selector and its permitted repair are REFUTED

G1 first fails on `SAAAA` (p=5,S=3): escape phases are 1,2,3, and phase 3
is supplied at lag 3. Thus being a last upcrossing does not itself prohibit a
past tangent contact.

G2, the permitted repair “some escape phase is unsupported”, passed the new
finite selector discovery through period 12. It was then refuted by an explicit
algebraic construction, not by extending that period horizon. The simplest
member is

```text
A^5 S^4 (AS)^8 = AAAAASSSSASASASASASASASAS,
p=25, S=1, unique escape phase t=0,
d=119, sum=1, weighted sum=0.
```

The main P2 obstruction is not refuted: this word still has eleven unsupported
A phases, namely 1,3,4,9,11,13,15,17,19,21,23. The counterexample only rules out
selecting an unsupported phase solely by the last-upcrossing/cycle condition.

### PROVED-PAPER: an infinite family defeating G2

For every integer r≥1, put

```text
k=5r,  m=4r(5r−3),
w=A^k S^(k−1) (AS)^m,
p=2m+2k−1=40r²−14r−1,  S=1.
```

Its unique escape phase is 0. From phase 0 the forward height is always
positive: it rises from 1 to k, descends to 1, then alternates between 2 and 1.
Every later A in the initial run starts at height at least 1, and the end of
that cycle returns to height 1, so it is not an escape phase. Every A in the
final alternating section returns to its starting height after the following
S. This proves uniqueness without invoking a census.

At phase 0, the backward period is `(SA)^m S^(k−1) A^k`. Write its partial
signed sum as U and its partial first moment as V. Direct arithmetic gives

```text
U_p=1,           V_p=3m+k²,
r0=2m+3 < p,    U_r0=−3,    V_r0=−5m−6.
```

Take `d=4p+r0=200r²−80r−1`. Four complete periods followed by r0 terms give

```text
U_d=4−3=1,
V_d=4V_p+6p+4p U_r0+V_r0
   =4(3m+k²)−6(2m+2k−1)−5m−6
   =4k(k−3)−5m=0.
```

Therefore its only escape phase has a P2 supplier. This is a complete
all-r paper counterexample to G2. The fixed exact regressions r=1,2,3,4
confirm p=25,131,317,583 and d=119,639,1559,2879. The paper proof, not those
four finite checks, supplies the universal quantifier.

This family also identifies the obstacle to applying a one-period cycle
lemma: the supplier uses four complete backward periods before its final
partial period. Positivity of forward height in one period says nothing that
excludes this accumulated first-moment cancellation.

## A geometric descent lemma that remains valid

The failure above does not invalidate the following necessary constraint.
It was derived independently on paper; no experiment supplies its proof.

For a positive-sum word, put `R=p/S` and write the periodic formal value path
as `x_(pq+r)=Aq²+B_r q+C_r`, `A=pS/2`. Define

```text
u_r = B_r/S−r,
κ_r = C_r−B_r²/(4A).
```

Both u and κ are phase invariants: replacing r by r+p modifies the polynomial
coefficients according to the period translation and leaves these two values
unchanged. If a source state s just precedes a supplied A, write a for its
actual next phase and j for its P2 supplier phase, at backward lag d measured
from s. Coefficient comparison gives

```text
u_a−u_s = R−1,
u_j−u_s = d−R,
κ_a+κ_j−2κ_s = −R.
```

For the last equality, actual and hypothetical-minus polynomials have
coefficients `(B_s±p, C_s±(r+1))`, so their κ sum is
`2κ_s−p²/(2A)=2κ_s−R`; the supplied minus polynomial has exactly the supplier's
κ. For its u, the supplier lies d clocks before the source, accounting for
`u_j=u_s+d−R`. These formulas include suppliers across multiple periods.

Consequently for every real λ≤0, the finite-phase function `F=κ+λu` obeys

```text
F_a+F_j−2F_s = −R+λ(d−1) < 0.
```

Thus at least one of the actual or supplier phases has F strictly below the
source. This is `PROVED-PAPER` and is stronger than using just κ's minimum.
It gives a global finite-phase graph constraint, not an injection or a general
count theorem. It does not finish P2: a descent can reach a subtraction phase,
where no corresponding two-child inequality is available. No inequality
making those S phases pay for all incoming supplied A phases was obtained.

Even the entire class of minima with λ≤0 need not expose an A phase. For
`SSASAAA`, κ is uniquely smallest at phase 0 and u is uniquely largest there:

```text
κ=(-63,-15,-31,-7,-39,1,-7)/8,
u=(21,5,−11,1,−15,−3,9)/2.
```

That phase is S. It therefore minimizes `κ+λu` for every λ≤0. This explains
why the new necessary graph inequality cannot be completed merely by selecting
an exposed phase, rather than pretending it already gives the desired sink
contradiction.

## Tangent geometry and the remaining global inventory

Let H_n be the unweighted signed height, K_n the clock-weighted signed height,
and set `Z_n=K_n−nH_n`. Then

```text
Z_(n+1)−Z_n=−H_n,          Δ²Z_n=−ε_n.
```

A P2 supplier j for addition t satisfies

```text
H_(t−1)=H_j+1,
Z_t=Z_j−(t−j)H_j.
```

In this description, the down-curving A step meets the forward line with slope
−H_j issued at j, while its incoming slope is −H_j−1. S steps increase the
slope instead. This is an exact algebraic representation, not a new proof.
A contact-count potential would need to account for several old tangent lines
reactivated by a later S. The macro worker independently found that a single
S can increase the number of contacts in a future all-A continuation by two;
this pass does not assume a one-per-S inventory rule.

## Falsifier / auditor decision

- G1: `REFUTED` by the exact period-5 word.
- G2: `REFUTED` by the all-r paper family; selector route `STOPPED`.
- Phase graph descent identity: `PROVED-PAPER`, with the S-sink obstruction
  explicitly retained; no claimed all-period proof of P2 or Hall.
- Tangent geometry: exact reformulation only, not frontier-changing evidence.
- Canonical non-surjectivity and eventual sign nonperiodicity remain unproved
  by this pass. A counterword to P2 would still require a separate freshness
  audit before it could model an actual greedy orbit.

The remaining useful question for geometry is a global contact inventory that
survives simultaneous activation of several historical tangent lines, or a
proof that supplied-A descent sinks can be charged to S phases. None was
established here. Stop the escape selector; do not extend the period census
or add further preferred-phase selectors as substitutes for that obligation.

## Reproduction and files

```sh
python3 experiments/issue73_20260907/geometry_escape_selector.py > docs/data/issue73_20260907/geometry_escape_selector.txt
python3 experiments/issue73_20260907/geometry_escape_family.py > docs/data/issue73_20260907/geometry_escape_family.txt
```

Both exact logs print base/current revisions and script SHA-256. The selector
run was discovery of new G1/G2 statements, not another P2 holdout. The family
run is fixed-counterexample regression after the algebraic derivation.
No Lean, shared maps, old hashed bundle, Git/GitHub state, or user visualizer
was edited. Owned artifacts are this note, the two uniquely named scripts,
and their two output logs.

A short primary-source literature check did not supply the needed combinatorial
lemma. [Three Cousins of Recamán's Sequence](https://members.loria.fr/PZimmermann/papers/GOR3.8.pdf)
was inspected, but its additive/multiplicative/concatenation variants are not
used as premises for P2. No originality or exhaustive-literature claim is made.
