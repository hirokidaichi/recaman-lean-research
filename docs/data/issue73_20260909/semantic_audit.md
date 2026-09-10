# Meaning audit for the one-hour sharp-supply research

The current signatures were printed from the built modules in
[semantic_statements.txt](semantic_statements.txt), separately from the
axiom audit. This note records the auditor role's comparison with the
informal claims; it is not an additional mathematical theorem.

## Scope of the new capacity theorem

`Recaman.SharpPeriodicSupply.periodic_capacity_extension` assumes an
**old injection on U only** (`hUinj`) and its S image (`hUS`). U's sources
have an actual P2 window of length≤L. Their offsets are in 1..L and
equal 3 at lag-3 sources. These are precisely the inputs the existing
short maps can provide; the theorem does not prove or assume all-lag
capacity. Concrete substitution of those existing maps remains paper-only.

For Q, the only mathematical inputs are the actual leading A signs,
m≥max(3,L+1), and P2 at lag4m−1. `run` supplies these witnesses; it is
not a guessed rank or a fresh matching. The theorem constructs Q's
charge and proves that it is injective, lands in S, and avoids U's
image. There is no assumed cardinality bound, injection, or coverage
certificate for Q. U and Q are duplicate-free finite phase lists; no
disjointness of U and Q is assumed as a shortcut.

The final theorem has a slightly larger Q domain than the research
statement: it does not require e(t)=A at a Q source. Restricting to the
intended supplied A phases is valid. This is a stronger conclusion over
a larger domain, not a weakening that avoids the intended application.
All intended phase sets are finite subsets of 0..p−1 and can be listed
with a run witness for each member, so the finite-list formulation does
not impose a hidden cutoff in m or the supply lag.

## Comparison of the other statements

| Informal claim | Actual signature / counterfactual |
|---|---|
| Leading m≥3 A signs imply d≥4m−1 | Stream theorem preserves both P2 equations and the actual e(t−i). m≤d is explicit. AAS refutes m=2 |
| The lower bound is sharp for all m≥3 | Certificate proves P2, length, leading prefix, and **every** shorter prefix fails; not just a finite range |
| Nested supply gap is uniform | List statement uses arbitrary w,v,k. Stream theorem explicitly includes d+k≤d₂ and all intervening A signs |
| Sharp windows force an S block | Both list and actual-stream forms are proved. Full partition classification is not imported as an assumption |
| Short charges avoid the protected S | m≥L+1, current short A, radius≤L, and the lag-3 convention all appear in the signature |
| Modulo-p gluing is valid | Entire windows shift using periodicity before the integer injection/disjointness theorem is applied |
| Minimum lag can fall from23 to15 | Certificate excludes all d:Fin23 and d:Fin15 respectively. The prepended A represents the intervening step |

The scalar calculations were independently rederived from A-position sums:
P2 gives d=2a−1, a even, and 2Σ(A positions)=a(2a−1). Maximizing the
remaining A positions yields q²−m²+2m≥0, which forces q≥m. For the
nested theorem, the extremal tail moment gives
`(ℓ+k)(ℓ−3k)≥4k(d−1)`, exactly the printed inequality.

The partition inverse has deficits λ_i=3m+i−x_i, decreasing and
nonnegative with sum m. The counterfamily proof checks all possible
shorter prefixes: the run bound and lag parity reduce the old-window
case to a prefix of mass−3; extending into the added tail gives mass1
only at its first sign or final sign, and the first has positive moment.
Neither proof obtains a universal quantifier from its finite replay.

## Negative controls and limits

- The m=2, missing-moment, and missing-mass controls establish that the
  bound was not proved by silently changing P2.
- The m=4,5 short-charge collisions prohibit dropping the long-run
  condition merely because every tested large window worked.
- The arbitrary-r lag-drop family prohibits removing containment or
  repairing monotonicity by increasing a run-length threshold.
- The concrete positive-periodic lag-drop word has 5 supplied A phases
  and 11 S phases by two all-lag computations. It is not an E-070
  counterword. No all-r capacity result is inferred from this control.
- No theorem supplies freshness, canonical generation, or actual-orbit
  reachability. None asserts Recamán surjectivity or non-surjectivity.

## Reproducing the signature snapshot

Create a temporary Lean file containing `import Recaman` followed by
`#check` for these declarations, then run `lake env lean <temporary-file>`:

```text
Recaman.LeadingRunSupply.stream_leading_run_bound
Recaman.LeadingRunSupply.sharpFamily_certificate
Recaman.LeadingRunSupply.nested_supply_gap
Recaman.LeadingRunSupply.stream_nested_supply_strict_gap
Recaman.LeadingRunSupply.sharp_protected_charge
Recaman.LeadingRunSupply.nonnested_lag_drop_certificate
Recaman.SharpPeriodicSupply.periodic_capacity_extension
```

The complete Lean build, module boundary check, evidence registry check,
and axiom audit are retained separately. Passing those checks alone
would not have supplied this meaning audit.
