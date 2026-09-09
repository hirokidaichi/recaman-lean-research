# Handoff: issue #73 cycle 2, lag-15 injection

Conclusion first: `|U7 ∪ U11min ∪ U15min| ≤ |D|` holds for every cyclic
sign word, by the audited φ7, the E-080 φ11 table, and an explicit 155-row
min-lag-15 charge that is locally incompatible with both and pairwise
Z-clashing at δ=j−i. Evidence: `PROVED-PAPER` (E-086). This is strictly
stronger than E-071 and E-080. It is not E-067/E-070: a positive-sum
counterword may still use least lag ≥ 19.

## Hypothesis-card status

- H-20260908-01: lag-15 incompatibility existed (`COMPUTED`); this fire
  completed the injective assignment. Residual Lean glue of the 17 types
  remains.
- H-20260908-02: still `STOPPED`.
- H-20260908-03: still `COMPUTED` / stopped (do not extend p).
- H-20260908-04: `PROVED-PAPER`.

## Changed files

- `docs/HYPOTHESIS_CARD_2026-09-08_LAG15_INJECTION.md` (new)
- `experiments/issue73_20260908/lag15_csp.py`
- `experiments/issue73_20260908/lag15_verify.py`
- `experiments/issue73_20260908/lag15_regression.py`
- `docs/data/issue73_20260908/lag11/lag15_csp.txt`
- `docs/data/issue73_20260908/lag11/lag15_verify.txt`
- `docs/data/issue73_20260908/lag11/lag15_regression.txt`
- `docs/data/issue73_20260908/lag11/lag15_assignment.json`
- `docs/data/issue73_20260908/lag11/lag15_injection_proof.md`
- `docs/data/issue73_20260908/SESSION_STATE.md`
- `docs/EVIDENCE_REGISTRY.tsv`, `docs/CURRENT_FRONTIER.md`, `docs/ROADMAP.md`

No Lean changes this fire. `recaman-visualizer/` untouched.

## Commands

```text
cd experiments/issue73_20260908
python3 lag15_csp.py
python3 lag15_verify.py ../../docs/data/issue73_20260908/lag11/lag15_csp.txt
python3 lag15_regression.py ../../docs/data/issue73_20260908/lag11/lag15_csp.txt 18
```

Revision `8b07f93fbbb17352c091cabaa333fc366a66c04f`.
CSP: 155 types, uncovered 0, OPEN_PAIRS=0, SEARCH_NODES=155.
Verify: N_UNBLOCKED=0, OPEN_COLLISION_PAIRS=0, PASS.
Regression: 524,286 words, 20,621 lag-15 events, 36,915 lag-11 events, PASS.

## Strongest evidence

`PROVED-PAPER` all-period injection of U15min off φ7∪φ11, finite type list
plus local obstruction plus Z-clash of all 23,870 ordered distinct pairs.
Wrap cannot resurrect a Z-clash. Cyclic p≤18 is confirmation only.

## Failed attempts and counterexamples

None this fire. The lag-11 following-gap class remains `REFUTED` (E-085);
this unit never used gap classes. No U=A word was found or sought.

## Remaining uncertainty

- Periodic glue of the 17 lag-11 types is still not in Lean.
- Least lag ≥ 19 is untouched. E-067/E-070 remain `CONJECTURED`.
- The 155-row table is not a uniform-in-d charge.

## Next decision

Do not run a lag-19 CSP as a completion. Next unit is the Lean semantic
glue of E-079 onto actual periodic windows (E-080 as `PROVED-LEAN`), or a
new d-independent obstruction. Stop further lag-by-lag tables unless such
an obstruction appears.
