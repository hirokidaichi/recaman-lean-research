# Issue 73: September 10 three-hour research evidence

The [Japanese handoff](../../THREE_HOUR_RESEARCH_2026-09-10.md) gives conclusions,
limitations, and the next decision. This bundle records H-20260910-01..27,
E-096..E-127, and the promotion of the original finite-state reduction
E-065 from PROVED-PAPER to PROVED-LEAN. E-067/E-070 and both surjectivity
alternatives remain open.

Base HEAD: `8dfbfb8f15eb2ff3d84629385cde99cd9f2bc9aa`.
Sources were uncommitted working-tree files. The new [SHA256 manifest](SHA256SUMS)
identifies the final source closure and output files; each experiment log
also identifies its own source and imported generator hashes.
No commits, pushes, external messages, or delegated agents were used.
The pre-existing unrelated `recaman-visualizer/` was not modified.

## Reproduction and environment

Run from the repository root. Preserve these frozen logs and redirect new
outputs to `/tmp`. Elapsed times need not reproduce byte-for-byte.

- Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; standard library only.
- Python 3.14.3; standard-library implementations.
- Apple clang 17.0.0, arm64 macOS; C++20, exact integer arithmetic.
- [REPRODUCTION_COMMANDS.tsv](REPRODUCTION_COMMANDS.tsv) lists every current
  experiment source, its saved output, and a complete command. Each source
  has frozen default discovery/holdout parameters and no required CLI
  arguments. The provenance verifier additionally accepts `--manifest`.

```sh
./scripts/check.sh > /tmp/recaman_final_check.txt 2>&1
PYTHONDONTWRITEBYTECODE=1 python3 experiments/issue73_20260910/verify_evidence_bundle.py --manifest
shasum -a 256 -c docs/data/issue73_20260910/SHA256SUMS
```

The canonical B search stops at the first verified candidate,10^9 steps,
900 seconds at its checkpoints, or the declared value-cap failure. It
stopped at step96,911,838 in this run. Its fixed-witness Python verifier
replays exactly that many steps and checks every shorter lag at the hit.
The other orbit censuses replay through10^7. These are finite computations,
not Lean proofs of their entire traces.

## Main result-to-output index

| Unit / evidence | Saved output | Interpretation |
|---|---|---|
| H01 / E-096 | [signed_supply_gap](signed_supply_gap.txt) | Signed overlap inequality, minimum-lag sharp example and needed-A-run control |
| H02 / E-097 | [bounded_excess_multiplicity](bounded_excess_multiplicity.txt) | Optimal same-run excess threshold and all-R boundary family checks |
| H03 / E-098,E-099 | [bounded_excess_reservoir](bounded_excess_reservoir.txt) | Density bound, fixed-offset counterfamily; all-R density sharpness remains paper-only |
| H04 / E-100 | [reservoir_capacity](reservoir_capacity.txt) | Exact reservoir geometry and finite capacity tests |
| H05 / E-101 | [nested_reservoir_capacity](nested_reservoir_capacity.txt) | Nested rank assignment and removal of quadratic threshold |
| H06 / E-102 | [short_reservoir_specialization](short_reservoir_specialization.txt) | Complete short map and new minimum-lag71 witness |
| H07 / E-103 | [orbit_coverage_census](orbit_coverage_census.txt), [lookup verification](verify_prefix_lookup.txt) | Exact all-finite-history minimum P2; long-run extension has zero eligible phases |
| H08 / E-104 | [parity_supply_capacity](parity_supply_capacity.txt) | Global-odd-A model, never asserted globally canonical |
| H09 / E-105,E-106 | [local_parity_capacity](local_parity_capacity.txt) | Local clean all-lag capacity and union with U≤11 |
| H07b / E-107 | [orbit_local_parity_census](orbit_local_parity_census.txt) | 921,983/1,315,896 finite P2 A phases covered, charges S and collision-free |
| H10 / E-108 | [single_defect_matching](single_defect_matching.txt), [orbit_defect_census](orbit_defect_census.txt) | Finite Hall passage only; fixed-small-defect branch stopped |
| H11 / E-109,E-110 | [ss_free_supply](ss_free_supply.txt), [orbit_ss_census](orbit_ss_census.txt) | NoSAAS SS-free iff clean; residual SS counts are finite data |
| H12 / E-111 | [finite_p2_semantics](finite_p2_semantics.txt) | Exact meaning of finite lookup; arbitrary blockers need not be P2 |
| H13 / E-112 | [one_ss_charge](one_ss_charge.txt), [canonical control](one_ss_canonical_counterexample.txt) | Fixed centered charge refuted; actual small trace also Lean-certified |
| H14 / E-113 | [clean_period_bound](clean_period_bound.txt) | Sharp3d+7≤4p for current A, with current-S negative control |
| H15 / E-114 | [short_blocker_rigidity](short_blocker_rigidity.txt) | Strict short-collision criterion and sharp boundary |
| H16 / E-115 | [positive_period_lag](positive_period_lag.txt) | Uniform positive-period collision lag; balanced control |
| H17 / E-116 | [eventual_periodic_bridge](eventual_periodic_bridge.txt) | Arbitrary old residual and positive candidate growth |
| H18 / E-117 | [periodic_representation](periodic_representation.txt) | Natural/integer period bridge and complete P2 cutoff |
| H19 / E-118 | [phase_energy](phase_energy.txt) | Finite passage, but audit found an old κ rescaling; STOPPED |
| H20 / E-119 | [nonpositive_period_drift](nonpositive_period_drift.txt) | Nonpositive value drift controls, distinct from candidate drift |
| H21 / E-120 | [finite_seed_periodic_bridge](finite_seed_periodic_bridge.txt) | Arbitrary initial clocks/values/finite lists, including empty and unrecorded-current cases |
| H22 / E-121 | [one_ss_classification](one_ss_classification.txt) | Two-family classification check; full proof is recorded on paper |
| H23 / E-122 | [one_ss_multiplicity](one_ss_multiplicity.txt) | All-k shared-SS construction, with separate Lean proof of minimum and NoSAAS |
| H23b / E-123 | [orbit_one_ss_census](orbit_one_ss_census.txt) | 70,375 SS1 supplies; all 2,796 sources in the largest shared-SS case retained |
| H24 / E-124 | [family_b_seeded_control](family_b_seeded_control.txt) | Small exact seeded B, separately Lean-certified |
| H25 / E-125 | [canonical_family_b_search](canonical_family_b_search.txt), [independent replay](verify_canonical_family_b.txt) | Canonical B at step96,911,838, COMPUTED |
| H26 / E-126 | [ss_gap_budget](ss_gap_budget.txt) | All-SS mass budget, actual-word bridge and NoSAAS control |
| H27 / E-127 | [one_ss_run_capacity](one_ss_run_capacity.txt), [union control](one_ss_union_control.txt) | All-mass period1..17 falsifier; paper capacity; explicit p13 conflict with the clean map |

`check01` through `check26` files record successful full repository checks
at the declared stable checkpoints; absent numbers are cycles without new
Lean. `check25_documented_frontier.txt` is the registry/documentation checkpoint.
`check26_ss_gap_budget.txt` audits1,583 declarations,318 more than the
1,265-declaration starting snapshot. Only propext, Classical.choice and
Quot.sound are permitted. The final check is separately preserved.

## Semantic and provenance audits

- [Semantic audit](semantic_audit.md) compares the exact signatures with
  the prose, assumptions, clock conventions, and negative controls.
- [Signature input](semantic_statements_input.lean.txt) and
  [successful output](semantic_statements.txt) cover16 major interfaces.
  To replay, copy the input to a temporary `.lean` file and run
  `lake env lean /absolute/path/to/Statements.lean` from this repository.
- [Provenance audit](provenance_audit.txt) verifies47 logged source hashes
  and all29 entries of the previous bundle, using the five frozen starting
  snapshots for files subsequently changed in this session.
- [baseline](baseline/) preserves those files, the starting tracked diff,
  and the source of H17's failed negative-control harness. The earlier
  manifest was not rewritten to accommodate new work.

The H17 failed harness log
[eventual_periodic_bridge_control_clock_error.txt](eventual_periodic_bridge_control_clock_error.txt)
uses an erroneous balanced-control clock6q+1; its exact source is preserved
as a `.py.txt` snapshot with the logged hash. Correct clock9q passes in the
current source. This failure did not refute the positive-mass theorem.

The manifest freezes all current Recaman Lean sources, root/build/audit
configuration, new experiment sources, the imported old periodic solver,
new cards/current-state documentation, these logs, and the preserved older
bundle/source dependencies. Derived binaries and caches are excluded.
The manifest does not hash itself. A subsequent source or document edit
will intentionally make verification fail until a new evidence snapshot
is created; never silently rewrite this snapshot to match later research.
