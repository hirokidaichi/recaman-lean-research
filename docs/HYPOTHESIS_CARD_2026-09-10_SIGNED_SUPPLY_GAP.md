# Hypothesis card: a signed quadratic gap without nesting

- ID: `H-20260910-01`
- Owner: Codex; proposer, falsifier, formalizer, auditor sequentially
- Created: 2026-09-10 JST, three-hour research run
- Status: `PROVED-LEAN`
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`
- Dependencies: previous working-tree modules are frozen by
  `docs/data/issue73_20260909/SHA256SUMS`; they are not all in HEAD.

## Exact question

For every e:Z→{A,S}, t∈Z, k≥1 and natural d,d₂, suppose e(t+i)=A
for 0≤i<k and both P2(e,t,d) and P2(e,t+k,d₂) hold. With the signed
integer Δ=d₂−d, is

```text
Δ(Δ−4k) ≥ 4k(d−1), equivalently (d₂−d)² ≥ 4k(d₂−1),
```

always true **without d+k≤d₂**? The lag is not assumed minimal, the
initial A run need not be long, and no periodicity, freshness, or actual
Recamán provenance is assumed. Δ may be negative. The desired consequence
is a gap in the possible lags: d₂<d or d₂>d+4k, not monotone increase.

## Why this is a new frontier input

E-092 proves the quadratic bound only for nested windows; E-094 refutes
the strict increasing-lag conclusion without containment. The proposed
signed inequality can allow the E-094 reset while constraining its size.
It handles nested and non-nested windows in one local bound, rather than
extending a fixed-lag table or assuming a global matching.

## Dependency chain before formalization

P2 forces d,d₂≥3. If d₂≤k the new window is all A and impossible.
Otherwise its shared old prefix has length ℓ=d₂−k.
If d≤ℓ, E-092 applies. If ℓ<d, write the old window as U V with |U|=ℓ,
while the new one is A^k U. Their two P2 equations force

```text
mass(V)=k,
4 moment(V)=−4kℓ−2k²+6k.
```

The **minimum** moment of a length-b word of mass k puts all its A signs
first, giving `4 moment(V)≥−b²+2bk+k²+2k`. Substitution yields the same
signed quadratic bound. The weakest new lemma is this lower moment
extremum applied to the removed tail, complementary to E-092's upper bound.

## Frozen falsifier and stop

- Boundary k=0 is checked only for the non-strict inequality, not the dichotomy.
- Existing reset: 23→15 across k=1 must pass with positive slack, not be excluded.
- Drop the A-run condition: look for a same-lag P2 pair separated by a
  non-A continuation, to show the strengthened interpretation would fail.
- Weakened history: all binary windows, with no freshness or reachability.
- Discovery: all P2 old words of d=3,7,11,15; prepend k=1..4 A signs and
  inspect every P2 prefix of the visible new word.
- Holdout: d=19,23 with k=1..4, only if discovery passes. These are new
  overlap tests of sign words, not independent trajectory data.
- Existing general reset family: r=2..8 discovery, r=9..64 holdout.
- Acceptance: a complete argument and stream-faithful Lean theorem, or
  an exact counterexample. Finite agreement alone does not pass.
- No permitted repair. Stop if the signed claim fails or needs an
  unstated nesting, minimality, or actual-history assumption.

## Evidence and decision

`PROVED-LEAN`: `stream_signed_supply_gap`, `stream_supply_square_gap`, and
`stream_lag_dichotomy` in `Recaman/SignedSupplyGap.lean` preserve the actual
stream and both P2 equations, with no containment or minimality premise.
The formal quadratic theorem also allows k=0; strict dichotomy requires k≥1.

`COMPUTED`: all declared non-nested cases pass. At d=23 there are 30,554
old P2 words and 12,347 / 14,174 / 9 / 0 contacts for k=1/2/3/4.
Zero-contact cells are not positive support. Every replayed E-094 family
member has signed-gap slack exactly 8, so the reset is allowed, not hidden.
The non-A continuation control has slack −32 as predicted.

After this falsification, an analytic equality witness was checked:
old word ASAASAS has minimum lag7; prefix AA, this word, and tail
SSSSSSAAAA give minimum lag19 across k=2. Then (19−7)²=4·2·(19−1).
`square_gap_equality_certificate` proves both minimalities and equality
by the kernel. Thus the coefficient4 cannot be increased even for minimum lags.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260910/signed_supply_gap.py
lake env lean Recaman/SignedSupplyGap.lean
./scripts/check.sh
```

Exact outputs: [falsifier](data/issue73_20260910/signed_supply_gap.txt),
[full audit](data/issue73_20260910/check01_signed_gap.txt), 1,272 declarations.
Decision: retain the sharp signed inequality. It permits decreases and does
not reverse E-094. Next use: bound supplies whose excess above4m−1 is bounded.
