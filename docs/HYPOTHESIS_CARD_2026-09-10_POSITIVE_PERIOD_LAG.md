# Hypothesis card: positive-period collision lag bound

- ID: `H-20260910-16`
- Status: `PROVED-LEAN` (E-115)
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`
- Four roles: proposer, falsifier, formalizer, auditor, performed sequentially.

## Bounded question and quantifiers

Let b be a nonempty newest-first Boolean word of length p, mass(b)≥1.
Let v be ANY word of length r<p (it need not be a prefix of b), q≥0, and
w=b repeated q times followed by v. For an integer clock n>length(w),
does `moment(w)=n*(mass(w)−1)` imply `q<4p+4`, hence
`length(w)<(4p+4)p`? The constant is deliberately coarse and is not a
sharpness conjecture. The arbitrary v is a weakened-history stress test.

Acceptance: prove this complete word theorem and its periodic-window
specialization in Lean, then combine it with E-114 to obtain an explicit
clock threshold beyond which periodic-history collisions are P2.
Stop if any quantifier fails; do not assume bounded lag as an input.
This is a bounded input to E-065. Exclusion of pre-period seed blockers
and existence of a historical blocker at every late A remain separate
obligations before the full eventual-periodic reduction can be promoted.

## Informal dependencies before Lean

For S=mass(b), B=moment(b), s=mass(v), C=moment(v),
`mass(w)=qS+s` and `2moment(w)=2qB+pSq(q−1)+2qps+2C`.
Use S≥1, s≥−r, 2B≤p(p+1), 2C≤r(r+1), and n≥qp+r+1.
If q≥4p+4, the expression `2[n(mass(w)−1)−moment(w)]` is strictly
positive. This contradicts collision. A periodic past decomposes into
these repeated full blocks plus an old partial block. E-114 then applies
once `4n>D(D+4)`, D=(4p+4)p.

## Frozen falsifier

All binary b of positive mass, p1..7 discovery,p8..10 holdout; all binary
v with length r<p independently of b; q0..4p+5. Evaluate the exact formula
and every admissible integer collision clock n>length(w). For mass1,
moment0 permits all clocks, and the lag conclusion is checked directly.
Independently expand the words for p≤5 and compare the formula.
Negative control: b=AAASSS (mass0), v empty, q1,10,100 gives collision
n=9q>6q, with arbitrarily many blocks. Positivity cannot be omitted.

## Evidence

- `COMPUTED`: `python3 experiments/issue73_20260910/positive_period_lag.py > docs/data/issue73_20260910/positive_period_lag.txt` passed the frozen exhaustive ranges. The expanded small words independently match the block formulas. The mass0 family realizes unbounded lag.
- `PROVED-LEAN`: `Recaman/PositivePeriodLag.lean` proves the arbitrary-residual word bound, periodic decomposition, lag bound, explicit late-clock P2 implication, and the all-q balanced counterfamily.
- Full `./scripts/check.sh`: PASS,1,463 audited declarations; `check16_positive_period_lag.txt`.
- Auditor: no fixed lag, finite supply or recurrence hypothesis is hidden in the arithmetic core. Periodic specialization assumes positive mass for the current period. E-065 remains paper-only until finite initial history and the reason for each late A are handled.
