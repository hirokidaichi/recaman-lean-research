# Hypothesis card: nonnegative walks cannot have nonpositive periodic drift

- ID: `H-20260910-20`
- Status: `PROVED-LEAN` (E-119)
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`
- Four roles sequential.

## Exact bounded question

For every x:Nat→Nat, global p-periodic Boolean e with p>0, and N,
assume the actual signed weighted recurrence
`x(n+1)=x(n)+(n+1)*sign(e(n))` in Int for all n≥N.
Must the period mass be strictly positive?
No greedy choice or finite-history premise is needed. This would close
E-065's nonpositive-drift exclusion for any nonnegative weighted walk.

Acceptance: prove the complete generic theorem, including sign sum0,
and specialize to the canonical natural eventual-periodic assumption.
Stop if candidate nonnegativity is substituted for value nonnegativity,
or if a negative candidate drift is mistaken for a negative value drift.

## Informal dependencies before Lean

For a fixed phase let S be period mass and B its backward moment.
Repeated-block arithmetic gives a quadratic in q for x(n+qp)−x(n).
S<0 forces a negative value at large q. S0 gives −qB, so nonnegativity
forces every phase B≤0. The sum of phase moments is
`S*p(p+1)/2=0`; hence every B0. But adjacent moments differ by
`S−p*sign(e(t))`, nonzero when S0. Contradiction.
This explicitly uses value drift, not the old candidate-drift −p² sum.

## Frozen falsifier

All balanced and negative-mass words p1..8 discovery,p9..12 holdout.
For each phase verify the repeated-block polynomial against direct
weighted recurrence for q0..4; verify the phase-moment sum identity and
adjacent-moment relation. For S<0 verify eventual negativity with an
explicit large q based on the absolute block moment and initial value.
For S0 identify a positive backward-moment phase and verify its negative
value at q=x0+1 for x0=0,7,100. No claim about actual eventual periodicity
is inferred from finite examples.

## Evidence

- `COMPUTED`: frozen negative/balanced word checks through period12 passed; `nonpositive_period_drift.txt`, including exact expanded value-polynomial checks and positive-moment zero-drift phases.
- `PROVED-LEAN`: `NonpositivePeriodDrift.period_mass_positive` covers every nonnegative natural-valued walk with the eventual signed weighted recurrence. Negative mass is excluded by a quantitative quadratic test; balanced mass by the zero phase-moment sum and nonzero adjacent-moment difference.
- `canonical_eventual_supply` now derives positive mass and all A-phase P2 supply from canonical natural eventual periodicity alone, with d<p(p+1). No candidate floor, greedy obstruction premise, or sign-sum assumption is needed in its input.
- Full `./scripts/check.sh`: PASS,1,499 audited declarations; `check20_nonpositive_period_drift.txt`.
- Semantic audit: the old −p² candidate-drift identity is not used as a value-drift argument. The balanced value moments have sum0; their variation supplies the required negative-value phase. Arbitrary finite seeded greedy orbits still require the separate positive-drift history bridge.
