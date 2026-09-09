# Hypothesis card: lag-15 type-to-offset injection extending φ7 ∪ φ11

- ID: `H-20260908-04`
- Owner: root; isolated under `experiments/issue73_20260908/lag15_csp.py`
- Created: 2026-09-08
- Status: `PROVED-PAPER` (E-086)
- Research branch: issue #73, continuation of `H-20260908-01` / E-080
- Base revision: `8b07f93fbbb17352c091cabaa333fc366a66c04f`

## One bounded question

Let ε: Z → {−1,+1} be any period-p cyclic sign word. Write U7, U11min, U15min
for addition phases whose least P2 lag is ≤7, exactly 11, and exactly 15.
φ7 and φ11 are the audited maps of E-071 and E-080. Conjecture H_inject15:

```text
there is a period-independent assignment of each of the finitely many
minimal lag-15 window types to an S-offset in that window, incompatible
with every U7 pattern and every φ11 charge by a forced-sign clash,
such that distinct types clash at collision distance δ = j−i, yielding
an injection φ15: U15min → D \ (φ7(U7) ∪ φ11(U11min)) with φ15(t) ∈ N_t.
```

Consequently |U7 ∪ U11min ∪ U15min| ≤ |D| for every cyclic word.

This is stronger than E-080. It is weaker than E-070. It is not a new
finite-period census and not another L-bit automaton vector.

## Why it would matter

- Frontier obligation: E-080 asked whether the same incompatibility method
  extends one more lag. Existence of a blocked S on all 155 types is already
  `COMPUTED` (lag15_probe, uncovered=0). Injectivity among those types is the
  remaining edge of that method.
- Smallest useful consequence: a positive-sum E-070 counterword must use a
  least supplier lag ≥ 19.
- Continuation: a 155-row lookup is still lag-by-lag. The class stops unless
  the same local-obstruction rule is visibly uniform in d ≡ 3 (mod 4).

## Provenance and dependencies

- P2 as in `Recaman/ShortPeriodicSupply.lean`.
- φ7: Gate 3 / E-071. φ11: CSP assignment in E-080 / `lag11_verify_independent.CHOSEN`.
- 263 raw 7-subsets of {1..15} summing to 60; 155 with no P2 prefix of length
  3, 7, or 11 (`COMPUTED`, finite list).
- Do not reuse oldest-S (E-069), escape (E-072), min-lag endpoint (E-073),
  second moment (E-074), all-A future debt (E-075), following-gap classes
  (E-085), or L-window potentials (E-084).
- Do not treat uncovered=0 as E-070 or as injectivity.

## Falsification plan

- Boundary: every min-lag-15 type has ≥1 blocked S (already 1..6, uncovered 0).
- Weakened: pairwise Z-merge at δ=j−i, not Hall matching.
- Discovery: complete CSP on the 155 types and their blocked offsets.
- Independent check: rebuild types, U7/φ11 blocks, and pairwise clashes
  without importing the searcher.
- Cyclic regression, if an assignment exists, is `COMPUTED` confirmation,
  not the proof (same role as E-080's p≤18 regression).
- One repair: none. The lag-11 gap-class repair was already consumed.
- Stop immediately if the complete CSP has no assignment.

## Acceptance

1. `PROVED-PAPER`: explicit assignment, every ordered distinct pair clashes
   at δ=j−i, wrap reduces to the opposite pair as in E-080.
2. `STOPPED`: exhaustive unsatisfiable CSP. Reopen lag-by-lag only if a
   common all-lag charge appears (not another lag-19 table).
3. Do not promote a successful table to `PROVED-LEAN` via `decide` on 155
   types this unit (that is another finite vector). Glue of E-079 remains a
   separate Lean edge.

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-09-08 | `COMPUTED` | `python3 lag15_csp.py` at `8b07f93` | 155 types, uncovered 0, OPEN_PAIRS=0 |
| 2026-09-08 | `COMPUTED` | `python3 lag15_verify.py lag15_csp.txt` | N_UNBLOCKED=0, OPEN_COLLISION_PAIRS=0, PASS |
| 2026-09-08 | `COMPUTED` | `python3 lag15_regression.py lag15_csp.txt 18` | 524,286 words, 20,621 lag-15 events, PASS |
| 2026-09-08 | `PROVED-PAPER` | `docs/data/issue73_20260908/lag11/lag15_injection_proof.md` | all-period \|U7∪U11min∪U15min\|≤\|D\| (E-086) |

## Semantic audit checklist

- Informal injection ⇒ |U7 ∪ U11min ∪ U15min| ≤ |D|.
- The count does not imply U≠A (lag ≥ 19 remains).
- An S is blocked only by forced signs of the length-15 window; unconstrained
  future/past signs are treated as possibly completing a U7 or φ11 pattern.
- No freshness or Recamán reachability.

## Decision

- Continue / formalize / refute / stop: E-086 stands as `PROVED-PAPER`.
  The lag-by-lag extension past d=15 is `STOPPED` (E-088): declared uniform
  blocked-set selectors have Z-open pairs at lag-15. Do not `decide` the
  155-row table. Do not run lag-19.
- Reopen only if a d-independent local obstruction is injective on the 155
  types without a new per-lag table.
