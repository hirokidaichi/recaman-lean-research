# Hypothesis card: lag-11 residual injection extending U7

- ID: `H-20260908-01`
- Owner: root (orchestrator); lag11 worker isolated under `experiments/issue73_20260908/`
- Created: 2026-09-08
- Status: original gap-class `H_inject11` `REFUTED`; repaired type-to-offset count `PROVED-LEAN` (E-080); finite kernel `PROVED-LEAN` (E-079)
- Research branch: issue #73 periodic supply, continuation of `H-20260907-09` / E-071 / E-078
- Base revision: `8b07f93fbbb17352c091cabaa333fc366a66c04f`

## One bounded question

Let ε: Z → {−1,+1} be any period-p cyclic sign word. Write A, D for its
addition and subtraction phases. Let U7 be the A-phases with some P2 lag d≤7,
and let φ7 be the audited U7 injection of `E-071` / Gate 3:

```text
min d=3, pattern AAS           → last S, following gap ≥ 4
min d=7, h=1, S-offsets 1,6,7  → S_{l-2}, following gap = 1
min d=7, h=2, S-offsets 2,5,7  → S_{l-1}, following gap = 3
```

Let U11min be the A-phases whose *least* P2 lag is exactly 11. For t in U11min
let N_t be the five S-phases in the length-11 backward window. Conjecture
H_inject11:

```text
there is a period-independent rule assigning each combinatorial
minimal lag-11 window type a unique (S-index shift, following-gap class)
pair disjoint from the three U7 classes, yielding an injection
φ11: U11min → D \ φ7(U7) with φ11(t) ∈ N_t.
```

This is stronger than the already-computed finite matching `E-078` (p≤18).
It is weaker than full Hall H and weaker than E-070.

## Why it would matter

- Frontier obligation: E-078 asked whether classified lag-11 residual domains
  have a uniform matching while the short map is fixed. A period-independent
  gap-type rule would be that uniform matching, and would force any
  positive-sum E-070 counterword to use a minimum lag ≥ 15.
- Stronger than E-078 because it is all-period, not a census.
- Continuation gate: the rule must be visibly extensible to all d ≡ 3 (mod 4),
  or must exhibit a common potential/charge that is not lag-by-lag.
- Smallest useful consequence: |U7 ∪ U11min| ≤ |D| for every cyclic word.

## Provenance and dependencies

- Definitions: P2 as in `Recaman/ShortPeriodicSupply.lean`.
- Lean theorems: `periodic_capacity`, `exists_phase_without_short_supply`.
- Paper: U7 injection in `docs/data/issue73_20260907/macro_proof_attempt.md`.
- Unverified: existence of a gap-type rule for the finitely many minimal
  lag-11 windows (at most the 29 five-subsets of {1..11} summing to 33;
  minimality will discard those with a P2 prefix of length 3 or 7).
- Do not reuse: oldest-S map (E-069), second-moment rank (E-074),
  all-A future debt (E-075), escape selector (E-072).
- Do not present LoopClosingSubtraction restatements as new input.

## Falsification plan

- Small/boundary: all-A, all-S, SAAA, SSSSAAAASAAA, AAASSASSSAA,
  and every minimal lag-11 window as a cyclic completion by a single S
  or by A-padding.
- Adversarial: pack many copies of one lag-11 type so that residual S
  after φ7 are over-subscribed; also wrap the length-11 window around
  periods p < 11.
- Discovery: exhaustive combinatorial assignment search on the finite
  list of minimal types (no period census). A collision of (shift, gap-class)
  with U7 or among lag-11 types kills that particular charge; try one
  repaired charge family only.
- Frozen holdout, executed only if a candidate rule is written down:
  exhaustive H_extend on periods 19 and 20 (never exhaustively checked).
  This is a new-property check on a new period range, not a completion.
- Stop immediately on an explicit cyclic word where every gap-type rule
  collides, or on a Hall-deficient residual after φ7. Record the word,
  N_t, φ7 images, and whether flexible full-U matching still exists.
- Stop the lag-by-lag class if the finite type list admits no
  period-independent (shift, gap-class) rule after one repair, even if
  matching still exists by Hall. That is a failure of this proof class,
  not a refutation of E-070.

## Acceptance and formalization gate

Accept either:

1. a complete all-period gap-type injection, written before Lean, or
2. an explicit cyclic counterword to H_inject11 / H_extend, with independent
   recomputation of P2 sums.

If (1), the Lean statement is the count `|U7 ∪ U11min| ≤ |D|` with a
semantic bridge from actual windows, not an opaque matching oracle.
Add major declarations to `Recaman/Audit.lean` and run `./scripts/check.sh`.

## Semantic audit checklist

- Informal all-period injection ⇒ formal count.
- Formal count ⇏ E-067 (lag ≥ 15 still allowed).
- Counterfactual: a word whose lag-11 phases all charge to a U7 image
  should make H_inject11 false even if some other matching exists.
- No Recamán freshness, reachability, or canonical-orbit hypothesis.

## Decision

- Continue / formalize / refute / stop: the finite kernel is Lean (E-079)
  and the all-period count `|U7 ∪ U11min| ≤ |D|` is Lean (E-080). Lag-15
  injective CSP remains `PROVED-PAPER` (E-086). The lag-by-lag extension
  class is `STOPPED` (E-088). Do not enumerate lag-19 types.
- Reopen lag-by-lag only if a d-independent local obstruction is injective
  on the 155 min-lag-15 types without a new per-lag table.
