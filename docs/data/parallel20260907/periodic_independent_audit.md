# Independent audit: periodic-sign positive-drift reduction

- Audit owner: `joint_generation`, independent second pass of pattern 4.
- Source base revision: `612fcfaf74bfb49f3ae05a268057c82f70dcca26`.
- Audited source: `docs/HYPOTHESIS_CARD_2026-09-07_MACRO_INDUCTION.md`.
- Result: the reduction to the all-period finite-word lemma is sound, after
  making two harmless bookkeeping points explicit below. The finite-word
  lemma itself remains `CONJECTURED`; this pass has neither proved it nor
  constructed a counterexample to P2. A separate κ-selection rule was refuted
  by the exact algebraic example below; this was not a new exhaustive P2 census.

## 1. Finite lag does follow from positive quadratic drift

Assume signs become p-periodic and have period sum S>0. Absorb both the
original finite seed and the finite preperiod into one effective seed.
For sufficiently late n, each residue class has

```text
x_n = A n² + b_(n mod p) n + c_(n mod p),   A=S/(2p)>0.
```

The finite collection of coefficients permits constants B,C≥0 with
`|b_r|≤B` and `|c_r|≤C`. The subtraction candidate
`x_(t−1)−t` tends to +∞ and hence eventually exceeds every value in the
effective seed. Any supplier then has a clock j in the periodic region.
Writing `n=t−1` and `d=n−j`, the supplier equation implies

```text
n+1 = x_n−x_j
    ≥ A(n²−j²)−B(n+j)−2C
    = (Ad−B)(n+j)−2C.
```

For `n≥max(1,2C+1)` and `j≥0`, this gives

```text
Ad−B ≤ (n+1+2C)/(n+j) ≤ 2,
d ≤ (B+2)/A.
```

The original card's phrase “sufficiently large n with n≥2C” should explicitly
use `n≥2C+1` if the constant 2 is quoted. This is an off-by-one clarification,
not a missing global reachability assumption. It does not affect finiteness.
Also, “seed” must include the finite preperiod when removing early suppliers.
The candidate cannot equal x_n itself because t>0, so d≥1.

## 2. Every addition phase needs an identity lag

For fixed phase t mod p and fixed lag d, define

```text
U_d = Σ_(i=1)^d ε_(t−i),
V_d = Σ_(i=1)^d i ε_(t−i).
```

The supplier equation becomes `t U_d−V_d=t`. If `(U_d,V_d)≠(1,0)`,
that equation holds at most once as t ranges through the phase; if U_d=1
and V_d≠0 it holds never. There are finitely many allowed d by section 1,
so a phase with additions at arbitrarily late clocks requires at least one
lag with `(U_d,V_d)=(1,0)`. The supplier lag need not initially be selected
uniformly: finiteness and the affine equation force the identity case.

This proves necessity only. A word satisfying these addition identities can
still fail subtraction freshness, chronological first-birth conditions, or
nonnegative values. A counterexample to the word lemma would refute this
particular sufficient obstruction, not establish a periodic greedy orbit.

## 3. The word-only lag bound is valid

Write `d=q p+r`, `0≤r<p`. Periodicity gives `U_d=qS+U_r`.
If U_d=1, then

```text
qS=1−U_r≤1+r≤p.
```

Since S≥1, q≤p, hence `d≤p²+p−1`. Thus testing lags through
`p(p+1)` safely includes every possible identity lag. No information about
the actual sequence, initial value, or seed size enters this second bound.
There is no unbounded-lag loophole in the finite-word reformulation.

## 4. Exact height-area interpretation

Let H be the two-sided integer walk with `H_k−H_(k−1)=ε_k`.
For j=t−1−d and n=t−1, the first identity says `H_n−H_j=1`.
Summation by parts yields

```text
Σ_(k=j+1)^n k ε_k
 = n−Σ_(k=j)^(n−1) (H_k−H_j).
```

Therefore P2 is equivalently a past walk from height 0 to height 1 whose
relative discrete area is −1. This may be useful for a cycle-lemma proof,
but this reformulation alone gives no obstruction. The short forward path
`−++` has area −1 and is precisely the familiar local supply behind the
third addition in `SAAA`.

## 5. Extremum attempts did not close the lemma

Writing `x_(pq+r)=A_block q²+B_r q+C_r` with `A_block=pS/2`, define
`κ_r=C_r−B_r²/(4A_block)`. At an addition phase, its actual output parabola
and its hypothetical subtraction candidate parabola satisfy

```text
κ_actual + κ_candidate = 2κ_previous − p/S.
```

A supplied candidate must share κ with a supplier phase. Consequently an
addition immediately after a globally minimum κ phase is impossible.
However, a global minimum κ need not precede an addition. A separate
exploratory search of this choice rule first finds the word `SSASAAA` at p=7,
S=1. Its exact κ values, indexed by the phase of the next step, are

```text
−63/8, −15/8, −31/8, −7/8, −39/8, 1/8, −7/8.
```

Its unique minimum is phase 0, immediately before S. Thus selecting a minimum
κ phase does not complete the argument. This is an exact algebraic negative
control, not a counterexample to P2's all-period obstruction. An initial
hand calculation for AAS used the wrong denominator; corrected values are
`−3/8,5/8,−3/8` and do not refute this rule. No conclusion uses that discarded
calculation. The period-7 counterexample is independently recomputed with
exact rational arithmetic by `periodic_audit_kappa.py`; this fixed regression
is COMPUTED and makes no holdout claim.

The macro owner independently explored the same κ extreme and also reported
that a maximum one-period backward weighted sum is not a valid universal
choice of obstructed phase. No such choice rule is assumed by this audit.

## 6. Other sign sums are already excluded

S<0 forces negative quadratic growth, contradicting nonnegative values.
For S=0, one-period drift in a fixed phase is constant `D_r`. The sum of
these p phase drifts is zero, and adjacent drifts differ by `p ε_r`, so not
all are zero. A negative D_r exists and forces that phase's values to become
negative. No candidate-floor or coverage assumption is needed.

## Decision

The only genuinely open edge in this proposed periodic no-go proof is the
all-period combinatorial assertion:

```text
For every periodic ±1 word with S>0, some + phase has no lag with P2.
```

It is a concrete, smaller question than non-surjectivity and uses finite seed
history in an essential way. The current reductions justify investigating it.
They do not prove it, nor does exhaustive checking of any fixed maximum period.
An independent proof of the word assertion would finish the positive-drift
case. Without it, report a precise conjecture and a bounded next gate.

Only this audit, `experiments/parallel20260907/periodic_audit_kappa.py` and
`docs/data/parallel20260907/periodic_audit_kappa.txt` were created for the
independent audit. No Lean proof, source card, registry, Git state, or issue
state was changed. Reproduce the fixed counterexample with:

```sh
python3 experiments/parallel20260907/periodic_audit_kappa.py
```

The exact output records the source base, current revision, script SHA and
rational κ values. The finite exploratory selector search was not a protocol
for the full P2 lemma and was not promoted to an all-period claim.
