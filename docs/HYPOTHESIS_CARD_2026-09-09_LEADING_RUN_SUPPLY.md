# Hypothesis card: sharp leading-addition run bound for P2 supply

- ID: `H-20260909-03`
- Owner: Codex, proposer/falsifier/formalizer/auditor sequentially
- Created: 2026-09-09, during the 07:46–08:46 UTC research hour
- Status: `PROVED-LEAN` (after frozen falsification, formalization, and repository audit)
- Branch: issue #73, uniform local inequality; not lag-by-lag charging
- Base revision: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`

## One bounded question and exact statement

For every integer m≥3, every d≥m, and every newest-first sign word
w∈{A,S}^d whose first m signs are A, does P2(w) imply **4m≤d+1**?
Here P2(w) means signed sum 1 and weighted sum 0, with weights 1,...,d.
The lag need not be minimal and the word need not come from an actual orbit.

Claim of sharpness: for every m≥3, the newest-first word

```text
W_m = A^m S^(m−1) A S^m A^(m−1)
```

has length 4m−1, initial A run exactly m, satisfies P2, and has no shorter
P2 prefix. Thus the bound cannot be strengthened to d≥4m or to a stronger
asymptotic slope. This is a parameterized family, not a new table by lag.

## Why it would matter

This gives a uniform obstruction linking a visible run to the required
historical supply depth. A supplied addition after m≥3 consecutive A steps
needs at least 2m additions and 2m−1 subtractions in its P2 history window.
It does not give an injection across different supplied steps or solve E-070.
It rules out deriving a stronger run-only obstruction while explaining a
resource requirement for long-lag reactivation.

The run-length-only potential tried in H-20260908-02 remains stopped. This
claim is an inequality about the exact P2 window, not that failed potential.
Repository search found the fixed-lag examples and that stopped potential,
but no existing all-m run bound or this sharp family theorem.

## Dependency chain before Lean

Let a be the total A count and q=a−m the remaining A count. P2 implies
d=2a−1 and that a is even. The largest possible sum of A positions, given
the first m A positions, is obtained by placing the other q A signs last:

```text
2 sum(A positions) ≤ m(m+1)+q(2d−q+1).
2 sum(A positions) = d(d+1)/2 = a(2a−1).
```

Substitution gives `0≤q²−m²+2m`. If q≤m−2 and m≥3 this is impossible.
The remaining q=m−1 gives odd a=2m−1, also impossible. Hence q≥m and d≥4m−1.
The **weakest new lemma** is the extremal-position inequality linked to the
unchanged P2 signed sums; no reachability, future hit, or capacity assumption.

The five runs in W_m have total sum 1 and weighted sum 0 by exact arithmetic.
Any shorter P2 prefix of length≥m contradicts the bound. A shorter prefix
of length<m is all-A and cannot have both signed sum 1 and weighted sum 0.

## Frozen falsifier and stop

- Boundary: m=2, word AAS, refutes dropping m≥3; m=0,1 are not part of the claim.
- Drop moment: AAASS has sum 1 but violates the m=3 bound.
- Drop sum: AAAASSSA has moment 0 but violates the m=3 bound.
- Weakened history: every binary word is admissible, with no actual-orbit constraint.
- Discovery: all P2 words of lengths 3,7,11,15; test their full leading A run.
- Conditional holdout: all P2 words of length 19, only if discovery passes.
  These previously used words are held out for this new property, not new trajectory data.
- Family discovery: m=3..16, all prefix sums and moments.
- Family holdout: m=17..128 after discovery; computations are not the all-m proof.
- One repair: none. Stop on any violation or if the proof assumes the desired global capacity.
- Acceptance: complete paper proof with exact scope and sharp family, followed
  by Lean when the semantic bridge is available; otherwise record the precise gap.

## Evidence and decision

`PROVED-LEAN`: `Recaman.LeadingRunSupply.stream_leading_run_bound` proves the
bound for the unchanged stream P2 predicate. `sharpFamily_certificate` proves
the arbitrary-m family, its length, leading A prefix, and absence of any
shorter P2 prefix. `past_p2_iff` audits the word/stream bridge in both directions.

`COMPUTED`: discovery P2 counts 1,4,29,263; holdout count 2,724. Among these,
3,30,325 words at d=11,15,19 have leading run≥3, with zero violations.
All family prefixes at m=3..128 pass. The three negative controls give
signatures (1,0), (1,−3), (2,0) exactly as predicted.

Commands (repository root; base revision above, working-tree source frozen in
the [bundle](data/issue73_20260909/README.md)):

```sh
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260909/leading_run_supply.py
lake env lean Recaman/LeadingRunSupply.lean
./scripts/check.sh
```

The full audit passed with 1,265 declarations and no prohibited dependency.
Exact output: [leading_run_supply.txt](data/issue73_20260909/leading_run_supply.txt).
Semantic audit: m≥3 is essential; both P2 moments are essential; no minimality,
periodicity, or reachability was silently assumed. The finite checks are not
the proof. **Decision: retain the uniform sharp theorem; no stronger bound
depending only on the leading A run is possible.**
