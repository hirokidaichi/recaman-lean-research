# Hypothesis card: full finite-seed eventual-periodic reduction

- ID: `H-20260910-21`
- Status: `PROVED-LEAN` (E-120; full E-065 scope)
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`
- Roles performed sequentially.

## Exact bounded question

For arbitrary finite `State s`, arbitrary starting clock b, and the existing
`SeededReplay.run b s`, suppose its actual greedy signs are eventually
p-periodic after an absolute N≥b, p>0. Prove that the period has positive
mass and every A phase has some 0<d<p(p+1) with P2.
No current-value-in-seen consistency assumption is added to s: finite
arbitrary seed states are deliberately allowed.

Acceptance: generalize the candidate-growth/history argument to an arbitrary
nonnegative weighted walk with an explicit finite list of seed blockers,
then derive all premises from `SeededReplay.run`. Final statement must use
only actual seeded eventual periodicity, not assumed bounded suppliers,
positive candidates, or finite P2. Stop if arbitrary pre-b values leak into
the legal post-b history, or if the relative clock is confused with absolute
step magnitude. This is E-065's remaining finite-state scope.

## Informal dependency chain before Lean

Use the whole window from b to t, instead of0 to t. Its value identity is
x(t)−x(b)=(t+1)*mass−moment. The H17 arbitrary-residual growth theorem still
applies since t+1>t−b and x(b)≥0. All seed values and preperiod trajectory
values are bounded by an explicit finite list sum. A late positive
candidate exceeds this bound, so its real blocker occurs after N.
H16/H15 force P2; H18 transports/cuts off lag. H20 supplies positivity
without using greedy history. Existing SeededReplay is reused.

## Frozen falsifier

Base clocks0,1,5,100; initial values0,1,7,100; finite seen lists [],[0],
[0,value],[1,3,9]. Simulate256 steps. Base0/1 discovery,5/100 holdout.
At each transition check actual signed recurrence, stored-history
membership decomposition into initial seed or generated post-base value,
and the exact reason-for-A dichotomy. Also verify every prefix/window
value identity on lags0..min(t,16). Empty seen and an unrecorded current
value are boundary cases, not silently excluded.
Infinite-history control on paper: if every nonnegative integer is already
seen, an all-A sign pattern can be enforced forever although it has no P2.
This does not define a finite State and cannot be used as a finite-seed
counterexample; it shows why finiteness is an essential premise.

## Evidence

- `COMPUTED`: all256-step seeded tests passed at every frozen initial state/clock, including empty history and unrecorded current values; `finite_seed_periodic_bridge.txt`.
- `PROVED-LEAN`: `FiniteSeedPeriodicSupply.seeded_eventual_supply` uses the existing `SeededReplay.run` and only eventual periodicity of its actual greedy signs. It derives positive mass and 0<d<p(p+1) P2 for every A phase.
- The generic proof uses an explicit list-sum bound for all seed and preperiod values. Actual seeded-history membership, the reason for each A, and the absolute/relative clock conversion are individually proved. No `s.value∈s.seen` assumption is introduced. Canonical run/sign equality is separately checked.
- Full `./scripts/check.sh > docs/data/issue73_20260910/check21_finite_seed_periodic_bridge.txt 2>&1`: PASS; the exact declaration count is in that log.
- E-065 can now be promoted from PROVED-PAPER to PROVED-LEAN across its original finite-state scope. This is a reduction to E-067, not a proof of E-067, E-070, nonperiodicity without that combinatorial input, or non-surjectivity.
- No failed mathematical cases in the declared falsifier. The unbounded external-history control remains outside finite State by design.
