# Issue 73 session state, 2026-09-08

Orchestrator: 1-day research loop on the only active direct branch (#73).
Base: `8b07f93fbbb17352c091cabaa333fc366a66c04f`.
Do not edit `recaman-visualizer/` or old hashed 2026-09-07 bundles.

## Cycle 6 results (2026-09-09, this fire) — STOPPED

Bounded question H-20260908-06: a d-independent selector F on min-lag
windows that reproduces φ7 and injects at lag-11 and lag-15.

- `STOPPED` (E-088): named class **lag-by-lag type-to-offset charge**.
- `COMPUTED`: `python3 experiments/issue73_20260908/uniform_selector.py`.
  Raw-S selectors fail φ7. Unique blocked S: 0/17 and 1/155. Blocked
  selectors max/median have 0 open pairs at lag-11 and 8–12 at lag-15.
- E-080 `PROVED-LEAN` and E-086 `PROVED-PAPER` stand. E-067/E-070 open.
- Reopen in one sentence: a d-independent local obstruction injective on
  the 155 min-lag-15 types without a new per-lag table, or a closed-form
  F that raises on `SSAAAAAASSS` and drops by at most 1 on S from
  `AAASAASSSSS`.
- Do not run lag-19. Do not extend p. Do not `decide` the 155-row table.
  The 1-day loop should not invent further lag-by-lag work.

## Cycle 5 results (2026-09-09)

Bounded question H-20260908-05: Lean `|U7 ∪ U11min| ≤ |D|`.

- `PROVED-LEAN` (E-080): `phi7Phase_inj` on actual 7-windows (forced-bit
  clash of the three U7 types), `phi7_phi11_image_ne` via `u7Blocked` on
  the recovered 11-window, and
  `suppliedCount_add_u11Count_le_subtractionCount`.
- All-period, not a census. Strictly stronger than E-071.
- `./scripts/check.sh` PASS (1245 audit decls). Do not run lag-19.

## Cycle 4 results (2026-09-09)

Bounded question H-20260908-05 continued: Lean `|U7 ∪ U11min| ≤ |D|`.

- `PROVED-LEAN`: `phi11Phase` is injective on a period and lands in D, hence
  `u11Count ≤ subtractionCount` for every period `p>0`
  (`u11Count_le_subtractionCount`). This is all-period, not a census.
- `PROVED-LEAN`: `phi7Phase_is_sub`; U7 three types pairwise same-time clash
  (`u7_pairwise_timeClash7`).
- The **union** bound is still missing: need `phi7Phase` injective on the
  circle (glue `timeClash7` to actual 7-windows) and images disjoint from
  `phi11` via `u7Blocked`. E-080 remains `PROVED-PAPER`.
- `./scripts/check.sh` PASS. Do not run lag-19.

## Cycle 3 results (2026-09-08)

Bounded question H-20260908-05: Lean glue of E-079 onto actual periodic windows,
statement `|U7 ∪ U11min| ≤ |D|`.

- Kernel strengthened: `types_complete` (every min-lag-11 11-bit mask is one of
  the 17 types) and `pairwise_timeClash` (same-time overlap, the geometric
  injectivity obstruction). `PROVED-LEAN` fragments, not the count.
- Glue module `Recaman/LagElevenPeriodic.lean`: `maskAt` recovers the 11 signs,
  `typeOf_spec`, `phi11` lands on an S, `timeClash_same_time` kills Z-collisions
  of distinct types, `u7_not_u11` (U7 and U11min are disjoint as phase sets),
  periodicity of `e` and `maskAt`. `./scripts/check.sh` PASS.
- The capacity inequality itself is **not** Lean yet. E-080 remains
  `PROVED-PAPER`. This fire did not meet the count gate.
- Do not run lag-19. Next: finish `phi11Phase` injectivity on the circle and
  the List injection into D, then disjointness from φ7 images via `u7Blocked`.

## Cycle 2 results (2026-09-08)

Bounded question H-20260908-04: injective type-to-offset charge for all 155
min-lag-15 windows, incompatible with φ7∪φ11, pairwise Z-clash at δ=j−i.

- `PROVED-PAPER` (E-086): |U7 ∪ U11min ∪ U15min| ≤ |D| for every cyclic word.
- CSP: 155 types, SAFE_COUNTS 1..6, uncovered 0, OPEN_PAIRS=0, SEARCH_NODES=155.
- Independent verifier: N_UNBLOCKED=0, OPEN_COLLISION_PAIRS=0, PASS.
- Cyclic regression p=1..18, all 524,286 words, 20,621 lag-15 events: PASS
  (`COMPUTED` confirmation, not the proof).
- Commands: `python3 lag15_csp.py`; `python3 lag15_verify.py lag15_csp.txt`;
  `python3 lag15_regression.py lag15_csp.txt 18` under
  `experiments/issue73_20260908/`.
- Do not enumerate lag-19 types. Remaining Lean edge: periodic glue of E-079.

## Cycle 1 results (2026-09-08)

- H-20260908-01: 17 min-lag-11 types. First gap-2 assignment failed cyclic
  regression (`SSSASSAAAASSAAA`, p=15) because collision distance was `i-j`.
  CSP assignment with `δ=j−i` has Z-pairwise clash 0 open pairs, U7 blocked,
  and cyclic regression 229,045 words / 26,586 lag-11 events PASS.
  Finite kernel `PROVED-LEAN` (E-079). All-period count `PROVED-PAPER` (E-080).
  Remaining Lean edge: glue actual periodic windows onto the 17 types.
- H-20260908-02: L=7 potential matches Lean. P is not P2-hit count. C++ L=23:
  8,388,608 states, no positive cycle, maxP=5, 0 violations. The L=19 maxP=4
  plateau ended. No closed form. Do not run L=27 as a substitute.
- H-20260908-03: exhaustive p=19–22, 3,487,066 positive words, U=A=0 (E-081).
  This unit stops as COMPUTED. Do not extend p.

Geometry inventory (independent worker): I_inv REFUTED by ASSSAASAAASAA
(t=11 both P2 children A; independently replayed) and AASAAASS Hall on
phase 6. Repair I_win REFUTED by ASASASAAASS. Class STOPPED as E-082/E-083.
Do not retune λ or give κ-min capacity 2.

Lag-15 discovery: 263 raw P2 windows, 155 minimal. Every one has an S that
neither U7 nor the lag-11 CSP charge can occupy (SAFE_COUNTS 1..6, uncovered 0).
That existence is now completed by the injective CSP of Cycle 2 (E-086).
Do not treat the table as E-070.

## Frozen units

| ID | Question | Acceptance | Stop |
|---|---|---|---|
| H-20260908-01 | all-period lag-11 gap-type injection extending U7 | paper injection or explicit cyclic collision | no period-independent rule after one repair |
| H-20260908-02 | closed-form all-L potential | formula proof, or L-cycle refuting E-070 | another finite vector only |
| H-20260908-03 | U=A counterword, exhaustive p=19–22 | explicit word, or clean COMPUTED ranges | do not extend p further |
| H-20260908-04 | lag-15 type-to-offset injection extending φ7∪φ11 | paper injection or unsat CSP | no lag-19 table; reopen only for a d-independent charge |
| H-20260908-05 | Lean `|U7 ∪ U11min| ≤ |D|` | E-080 Lean | glue complete Cycle 5 |
| H-20260908-06 | d-independent selector extending φ7 through lag-15 | uniform F, or stop the class | declared family failed at lag-15 |

## Isolation

- lag11: `experiments/issue73_20260908/lag11_classify.py`, `docs/data/issue73_20260908/lag11/`
- potential: `experiments/issue73_20260908/potential_formula.py`, `docs/data/issue73_20260908/potential/`
- counterword: `experiments/issue73_20260908/counterword_search.cpp` (or `.py`), `docs/data/issue73_20260908/counterword/`
- lag15: `experiments/issue73_20260908/lag15_csp.py`, outputs under `docs/data/issue73_20260908/lag11/`
- No two workers edit the same file. Root merges cards, frontier, registry, Lean.

## Known no-go (do not repeat)

E-069 oldest-S, E-072 escape selector, E-073 min-lag endpoint, E-074
second moment, E-075 all-A future debt, E-068 hole-only, E-064 connected
support, period-only census as a completion, lag-19 type tables, L-window
embedding potentials (E-084), following-gap classes (E-085).

## Success for this day

Any one of: a new `PROVED-LEAN` or `PROVED-PAPER` lemma that strictly
strengthens E-071; a `REFUTED` E-067/E-070/H_inject11; or a documented
`STOPPED` of the lag-by-lag class with a precise reopen condition.

Cycle 2 achieved the first: E-086 `PROVED-PAPER`.
Cycle 5 achieved the Lean form of E-080, strictly stronger than E-071.
Cycle 6 achieved the third: lag-by-lag class `STOPPED` (E-088).

## Next decision

STOPPED. Do not invent work. Do not run lag-19, extend p, or `decide` the
155-row table. Reopen lag-by-lag only if a d-independent local obstruction
is injective on the 155 min-lag-15 types without a new per-lag table, or a
closed-form F raises on `SSAAAAAASSS` and drops by at most 1 on S from
`AAASAASSSSS`. E-067/E-070 remain `CONJECTURED`; #73 is OPEN as a
proposition, closed as this method.
