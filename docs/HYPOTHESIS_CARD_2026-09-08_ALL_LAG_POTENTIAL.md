# Hypothesis card: closed-form / inductive all-lag capacity potential

- ID: `H-20260908-02`
- Owner: root; potential worker isolated under `docs/data/issue73_20260908/potential/`
- Created: 2026-09-08
- Status: this formula class `STOPPED`; E-070 still `CONJECTURED`
- Research branch: issue #73, continuation of E-071 / E-077
- Base revision: `8b07f93fbbb17352c091cabaa333fc366a66c04f`

## One bounded question

For each lag cap L ≡ 3 (mod 4), the L-bit shift graph with A-edge weight 1
on P2-supplied states (any lag ≤ L) and 0 otherwise, and S-edge weight −1,
has no positive-weight cycle (E-077, L∈{3,7,11,15,19}, `COMPUTED`).
Let P_L be the least nonnegative integer potential produced by the existing
relaxation. Conjecture P_formula:

```text
there is a closed-form or uniformly inductive rule F, independent of L,
such that F(window of length L) is a valid potential for every L ≡ 3 (mod 4):
  F(s) + charge_L(s,b) ≤ F(advance(s,b))  for both bits b.
```

A valid F for all L would prove |U_L| ≤ |D| for every cyclic word and every
L, hence E-070, because on a period-p word one may take L ≥ p(p+1).

This unit is *not* "run L=23 and stop". L=23 is only a falsifier and a
source of coefficients for guessing F. Horizon extension alone is not
acceptance.

## Why it would matter

- Frontier obligation discharged: E-070 / E-067 for all periods.
- Stronger than E-071 because the lag cap is removed.
- Smallest useful consequence: a human-readable potential inequality,
  then a Lean `decide` or structural proof on an unbounded window encoding.

## Provenance and dependencies

- Existing potentials: `docs/data/issue73_20260907/automaton_L*_potential.txt.gz`
  with uncompressed SHA-256 in the 2026-09-07 logs.
- L=7 potential is already in `Recaman/ShortPeriodicSupply.potential`.
- Max P_L observed: L3→1, L7→2, L11→3, L15→4, L19→4. The plateau at 4
  is a discovery observation, not a theorem; it is allowed as a hint
  for F, not as evidence that F exists.
- Unverified: existence of F; boundedness of max P_L; absence of a
  positive cycle at L=23.
- Do not reuse the refuted all-A future-debt potential (E-075).
- Do not claim E-070 from a new finite L certificate.

## Falsification plan

- Boundary: L=3 and L=7 must recover the known potentials up to an
  additive constant (or at least remain valid).
- Weakened model: dropping the moment equation must *fail* to give a
  bounded potential (the AA cycle of the parent card).
- Discovery: decode P_3, P_7, P_11, P_15, P_19 as functions of
  pending P2 contacts / suffix statistics; propose at most one F.
- Frozen L=23 run, started only after F is proposed *or* after recording
  that no formula was found from L≤19. A positive cycle at L=23 refutes
  |U_23| ≤ |D| and hence E-070. No cycle at L=23 is `COMPUTED` only.
- One permitted repair of F after seeing L=23. A second failure stops
  this formula class.
- Stop if L=23 has a positive cycle, or if two proposed formulae fail
  their edge inequalities, or if the only surviving object is another
  finite vector.

## Acceptance

1. `REFUTED`: explicit cyclic word with |U_L| > |D| for some L
   (replayed with exact P2 sums), or
2. `PROVED-PAPER` / then `PROVED-LEAN`: a closed-form F with a complete
   inequality proof, or
3. `STOPPED`: no formula, and L=23 is only another certificate.

## Semantic audit checklist

- F must be evaluated on the actual preceding L signs of an arbitrary
  periodic word, not on an assumed automaton path.
- Charge must use the same P2 identities as `ShortPeriodicSupply.P2`.
- A proof of all-L |U_L| ≤ |D| does prove E-070; do not hide a lag cap.

## Decision

- Continue / formalize / refute / stop: stop the short-window embedding of the
  Lean L=7 potential (fails every lag-11-only A-edge at L=11) and its one
  AAA-boost repair. C++ L=23 has no positive cycle and max P=5, so the L=19
  plateau at 4 is not a bound. Another larger L is not the next unit.
- Reopen only if a new structural statistic raises F on `SSAAAAAASSS`
  (lag-11 A) and drops by at most 1 on S from `AAASAASSSSS`, without encoding
  P_L itself.
