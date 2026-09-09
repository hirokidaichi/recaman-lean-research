# Hypothesis card: E-067/E-070 counterword search on unused periods

- ID: `H-20260908-03`
- Owner: root; counterword worker isolated under `docs/data/issue73_20260908/counterword/`
- Created: 2026-09-08
- Status: `CONJECTURED` (target statements E-067, E-070)
- Research branch: issue #73
- Base revision: `8b07f93fbbb17352c091cabaa333fc366a66c04f`

## One bounded question

Does there exist a positive-sum cyclic ±1 word with every addition phase
P2-supplied (U=A), using the exact finite-lag identity with
1 ≤ d ≤ p(p+1) and no lag cap L < p(p+1)?

This is a falsifier for E-067. Because S>0 implies |A|>|D|, such a word
also refutes E-070. Absence of a word in a new finite range is `COMPUTED`
and is not a proof.

## Why it would matter

- A single explicit word closes E-067/E-070 as `REFUTED` and stops the
  periodic-supply proof class as a route to excluding eventually-periodic
  exact finite-history continuations.
- It would not decide Recamán surjectivity. A counterword still needs a
  freshness/realizability audit before it models an actual greedy orbit.

## Provenance and dependencies

- E-066 already exhausted p=1..18 (229,045 positive words) and sampled
  p=19..64 with 90,640 shuffle/swap evaluations. Those ranges are not
  holdout for a repeated census of the same property.
- Frozen new discovery: exhaustive p=19 and p=20 (never exhausted).
- Frozen holdout: exhaustive p=21, then p=22 only if 19–21 are clean.
- Independent check: every reported counterword must be replayed with
  both the closed-form supplier formula in
  `experiments/parallel20260907/periodic_search.py` and naive summation.
- Negative control: the lag-11 control word `SSSSAAAASAAA` has an
  unsupplied A and must be reported as non-counterexample.
- Do not treat shuffle sampling of p>22 as a holdout.

## Falsification plan

- Small cases: p=1 all-A (U empty); SAAA (U=1, D=1, not U=A unless the
  two extra A are supplied — they are not).
- Discovery p=19,20 exhaustive with prefix-sum P2, early exit on the
  first unsupplied A.
- Holdout p=21,22 only if discovery is clean.
- For p>22, a complete search is not required in this unit. Optional
  heuristic search (hill-climb on missing-supply count) may be logged
  as `OBSERVED` and must not be labelled `COMPUTED` unless every word
  in a declared finite set is examined.
- Stop immediately on the first positive-sum U=A word. Record period,
  the ±1 word, S, every supplier lag, and both checker outputs.
- One repair is not applicable: a counterword is terminal for E-067.

## Acceptance

- `REFUTED`: explicit word, independently replayed.
- `COMPUTED`: exhaustive clean ranges as specified, with command,
  revision, exact counts, and source hashes.
- Do not promote a clean exhaustive range to `PROVED-LEAN` or
  `PROVED-PAPER`.

## Semantic audit checklist

- U=A uses unrestricted P2, not U_L.
- Positive sign sum is required.
- Period need not be minimal.
- No freshness.

## Decision

- Continue / formalize / refute / stop: p=19–20 discovery and p=21–22 holdout
  are clean (`E-081`, 3,487,066 positive words, U=A=0). This unit is `COMPUTED`
  and stops. Do not extend the period cutoff further as a substitute for
  H-20260908-01/02.
