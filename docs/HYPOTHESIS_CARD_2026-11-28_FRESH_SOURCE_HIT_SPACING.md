# Hypothesis Card: Fresh Common-Source Hit Spacing and Source-Clock Capacity (`E-804`)

- **ID / Registry**: `E-804`
- **Status**: `PROVED-LEAN` (upgrades `E-760` + `E-761` source-clock consumer from `PROVED-PAPER` to unconditional `PROVED-LEAN` on `SeededReplay.run` and `Recaman.Basic.a`)
- **Module**: [FreshSourceHitSpacing.lean](file:///Users/hirokidaichi/orca/workspaces/recaman-lean-research/nereid/Recaman/FreshSourceHitSpacing.lean)
- **Research Note**: [RESEARCH_NOTE_2026-11-28_FRESH_SOURCE_HIT_SPACING.md](file:///Users/hirokidaichi/orca/workspaces/recaman-lean-research/nereid/docs/RESEARCH_NOTE_2026-11-28_FRESH_SOURCE_HIT_SPACING.md)
- **Audit Script**: [fresh_source_hit_spacing_audit.py](file:///Users/hirokidaichi/orca/workspaces/recaman-lean-research/nereid/docs/data/depth_general_20261128/fresh_source_hit_spacing_audit.py)
- **Scope**: Arbitrary excursion depth, arbitrary finite-state greedy replay `SeededReplay.run b s` (no `s.value ∈ s.seen` coherence assumption needed), and canonical orbit `Recaman.Basic.a`.

## Exact Mathematical Statement

For every base `b : Nat`, finite state `s : State` (even incoherent), and common `Win` source `u : Nat`:

1. **Unique length-8 bridge (`gap_eight_bridge_unique_Z`)**: Any sign sequence `f : Nat → Bool` with `f p = true`, `Fw f (p + 8) = Fw f p`, and `Ar f p 8 = -8` must satisfy `seg f p 8 = Z := ASSSSAAA`.
2. **Dynamic `Z ++ Z` exclusion (`consecutive_gap_eight_forbidden_on_replay`)**: `seg (replaySign b s) p 8 = Z` and `seg (replaySign b s) (p + 8) 8 = Z` cannot both hold on any `SeededReplay.run b s`, because the `S`-landing at phase `p + 11` collides with the earlier output at phase `p + 3 ≥ 1`.
3. **Two-step spacing (`common_source_two_step_gap_ge_twenty`)**: Any three strictly increasing actual `A` hits `p < q < r` sharing `Win` source `u` satisfy `p + 20 ≤ r`.
4. **Arbitrary-length span (`fresh_common_source_hit_span`)**: Any strictly sorted list `p0 :: rest` of actual `A` hits sharing `Win` source `u` satisfies `p0 + 8 * rest.length + 4 * (rest.length / 2) ≤ last` (i.e., `10 * n - 2 * (n % 2)`).
5. **Unified source-clock capacity (`original_win_source_clock_capacity`)**: Any strictly sorted list `ps` of `M ≥ 2` actual `A` hits sharing `Win` source `u` satisfies
   `(b + u) + 11 + 8 * (M - 2) + 4 * ((M - 2) / 2) ≤ (run b s u).value` and
   `M ≤ 2 + ((run b s u).value - (b + u) - 9) / 10`.
6. **Negative control (`raw_nonfresh_counterexample_beats_fresh_span`)**: Without `S`-freshness, the raw sign word `SSAA ++ Z ++ Z ++ A` realizes three common-source `Win` hits (`4, 12, 20`) from `u = 1` with span `16 < 20`.
7. **Canonical specialization (`canonical_orbit_fresh_source_spacing`)**: Both the `8n + 4(n/2)` span law and the `u + 11 + 8(M-2) + 4((M-2)/2) ≤ a u` capacity law hold unconditionally on `Recaman.Basic.a`.

## Dependencies & Evidence

- **Lean dependencies**: `Recaman.NumericCandidateRankPotential` (`E-802`), `Recaman.CoherentGreedyFreshness` (`E-798`), `Recaman.SeededReplay`.
- **Lean verification**: `lake build Recaman Recaman.Audit` (0 errors, 0 warnings in module), `9/9` substantive theorems (`harness_gate.py --lint-module`), `0 flagged, 0 unknown, 7 theorems` (`harness_lean.py --vacuity-row E-804`), standard axioms only.
- **Computational audit**: `python3 docs/data/depth_general_20261128/fresh_source_hit_spacing_audit.py` — `ALL E-804 AUDITS PASSED` (exhaustive `2^7 = 128` mask check proving uniqueness of `Z`, `Z ++ Z` phase 3/11 collision, discovery `N = 2000` + holdout `N = 5000` canonical common-source hit lists).

## Non-Claims & Stopping Boundary

- Controls hit lists sharing a single common `Win` source `u`; does **not** prove global `Fw` boundedness, `C1`, `Q`, `H`, `SL`, surjectivity, or any protected claim (`E-001`, `E-067`, `E-070`, `E-179`).
