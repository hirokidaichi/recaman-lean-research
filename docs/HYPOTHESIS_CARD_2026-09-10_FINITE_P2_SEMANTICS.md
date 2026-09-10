# Hypothesis card: finite P2 and actual blocker semantics

- ID: `H-20260910-12`
- Created: 2026-09-10 JST
- Owner: Codex, four roles sequentially
- Status: `PROVED-LEAN`
- Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`

## Exact bounded question

Let e(n) be the actual sign of transition n→n+1, and P(n) its cumulative
sign sum over0..n−1. For every0≤u≤t, is P2 at(t,t−u) equivalent to
`P(t)−P(u)=1` and `a(t)=a(u)+t+1`?
Consequently any finite-history P2 witness forces the actual next sign A.
Conversely an actual historical blocker need not have a P2 witness: the
cumulative sign difference1 is a real additional condition.

This is a semantic audit of the10^7-step diagnostics, not a new capacity
theorem. It prevents the reported70% of finite P2 supply from being mistaken
for70% of all forced additions or all historical blockers.

## Dependencies and acceptance

For arbitrary signs, W(n)=sum(i*e(i),i<n). Telescoping gives window mass
P(t)−P(u) and moment t*(P(t)−P(u))−(W(t)−W(u)). Actual recurrence gives
a(n)=P(n)+W(n), hence the equivalence. Historical membership then excludes
CanSubtract. No periodicity premise is involved in this finite statement.

Falsifier: directly compare all lags in the standard prefix through2,000
(discovery500, holdout501..2,000) with the height/value key. Check all current
signs, including S; no P2 witness may occur at a legal S. Explicit negative
control: t5, candidate a5−6=1=a1, yet no P2 lag≤5. Positive control: t6,d3.
Keep strict integer subtraction in the value identity; do not let truncated
Nat subtraction manufacture a zero blocker at a low value.

Acceptance: Lean equivalence, actual forced-addition implication and concrete
negative control. Stop if the proposed equivalence requires periodicity or
does not match the code's zero-based sign convention.

## Evidence and conclusion

`PROVED-LEAN`: `FiniteP2Semantics.P2_iff_prefix_key` proves the exact lookup
identity for arbitrary signs. `canonical_value_prefix` connects W+P to the
actual a(n), and `canonical_P2_iff_height_one_blocker` proves both directions
of the stated actual-blocker equivalence. `finite_P2_forces_A` derives the
next actual A from historical membership, without periodicity.

The negative t5 and positive t6,d3 controls are both Lean certificates.
Thus the census can restrict to A phases without losing any finite P2
witness, but cannot treat every historical blocker as a P2 witness.

`COMPUTED`: `python3 experiments/issue73_20260910/finite_p2_semantics.py`
checks2,003,001 (time,lag) pairs through sign time2,000, finding391 P2
witnesses and151 positive historical blockers with no finite P2. Exact
output: `docs/data/issue73_20260910/finite_p2_semantics.txt`.

Audit: `./scripts/check.sh` PASS,1,417 declarations; log
`docs/data/issue73_20260910/check12_finite_p2_semantics.txt`.
No semantic counterexample to the exact equivalence was found. The control
refutes the stronger interpretation that all actual blockers are P2.
This closes the diagnostic's meaning audit, not the all-lag capacity problem.

