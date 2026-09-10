# Hypothesis card: two SS per repeated endpoint

- ID: `H-20260910-29`
- Created: 2026-09-10 09:50 UTC, final bounded unit of the one-hour continuation.
- Status: `PROVED-LEAN` (E-131); the statement was frozen before implementation.
- Base: `2ed8606` plus the audited H-28 changes.
- Roles: proposer, falsifier, formalizer, auditor performed sequentially.

## Exact question and acceptance

For every stream e and strictly increasing natural times
`f(0)<...<f(m)`, if every e(f(i)) is A and every backward word of length
f(i) at f(i) is P2 (all have the same endpoint0), must the largest window
contain at least `2*m` adjacent SS edges?

No minimum-lag, NoSAAS, or reachability assumption is made. Acceptance is
this all-m bound in Lean plus an all-m finite common-history family attaining
2m, with the source A signs and shared endpoint explicitly checked. This
is an endpoint multiplicity budget, not an S-capacity bound for all windows.

## Dependencies and proof plan

H-28's strict A-ended moment margin says a zero-mass intervening word
with moment minus its length contains at least two SS. Consecutive sources
with equal old endpoints force precisely those two equalities. The
intervening windows are disjoint; SS count is superadditive under append.
Sum the two-unit increments by induction on m.

Candidate sharp family: let V=AASASASASSSA (length12, mass0, moment−12,
two SS, final A), W0=AAS, and W(k+1)=V++Wk. All Wk should be P2 with 2k
SS and share the final endpoint as suffixes of WK. The current source
positions in A++WK are 12(K−k), all A.

## Falsification and stopping

Discovery K0..8; frozen holdout K9..32, direct integer sums and explicit
common-history indices. Check all intermediate sources and suffix equality.
Also record minimum P2 lags: this family has minimum lag3, so it must never
be called a counterexample for *minimum*-window endpoint multiplicity.
Check V's NoSAAS and the joins. Stop on any counterexample or if the proof
requires assuming the claimed SS increment. No repairs or new offset maps.

## Significance and limits

This is a quantitative consequence of the new common-history obstruction,
not an identity equivalent to E-070. Sharpness would rule out a constant
multiplicity cap for arbitrary P2 witnesses, while leaving minimum-witness
methods open. It is compatible with the canonical step115 A-ended example:
one supplier alone imposes no repetition cost, and the endpoint may be A.

## Evidence and decision

- `COMPUTED`: all K0..32 passed the frozen direct checker, including every
  intermediate source, suffix equality, SS count, NoSAAS and minimum lag3.
  Source/hash/command: `endpoint/repetition_falsifier.txt`.
- `PROVED-LEAN`: `EndpointRepetitionBudget.repeated_endpoint_budget` is the
  actual stream bound. `sharp_common_history`, `sources_distinct` and
  `common_endpoint_position` certify the sharp finite model; `family_nonminimum`
  explicitly certifies the limiting qualification at every k>0.
- `./scripts/check.sh` passed:1,635 audited declarations.
- Semantic audit corrected a helper name before audit: lag3 is strictly
  shorter only when k>0; W0 itself has lag3. No minimum-witness obstruction
  is asserted. No canonical reachability or infinite fixed-seed execution
  is asserted for the sharp family.
- Decision: unit complete. The shared-endpoint budget is sharp, so stronger
  multiplicity bounds using only the total SS count cannot hold for arbitrary
  witnesses. Continue only with allocation across different endpoints or an
  independently justified minimum-witness restriction. E-067/E-070 remain open.
