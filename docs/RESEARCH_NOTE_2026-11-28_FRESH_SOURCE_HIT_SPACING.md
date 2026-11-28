# Research Note: Fresh Common-Source Hit Spacing and Source-Clock Capacity (`E-804`)

- **Date**: 2026-11-28
- **Evidence ID**: `E-804` (`PROVED-LEAN`)
- **Lean module**: [FreshSourceHitSpacing.lean](file:///Users/hirokidaichi/orca/workspaces/recaman-lean-research/nereid/Recaman/FreshSourceHitSpacing.lean)
- **Statement audit**: [E-804.md](file:///Users/hirokidaichi/orca/workspaces/recaman-lean-research/nereid/docs/statement_audits/E-804.md)
- **Audit script**: [fresh_source_hit_spacing_audit.py](file:///Users/hirokidaichi/orca/workspaces/recaman-lean-research/nereid/docs/data/depth_general_20261128/fresh_source_hit_spacing_audit.py)

## Conclusion

`E-804` upgrades both `E-760` (fresh `S`-forced `8/20/10` common-source hit spacing) and `E-761`'s source-clock capacity consumer (`a_src + 11 + 8(M-2) + 4((M-2)/2) ≤ X(u)`) from `PROVED-PAPER` to unconditional `PROVED-LEAN` directly on every finite-state greedy replay `SeededReplay.run b s` (even without assuming `s.value ∈ s.seen`) and on the canonical orbit `Recaman.Basic.a`.

## Proof Architecture

1. **Mod-4 and bridge-area law (`win_length_mod_four`, `win_bridge_mass_area`)**: Any `Win` window `[u, p]` has `p - u ≡ 3 (mod 4)` and `3 ≤ p - u`, so any two common-source hits `p < q` have `q - p ≡ 0 (mod 4)`, balanced bridge `Fw q = Fw p`, and exact area `Ar f p (q - p) = -(q - p)`. For `q - p = 4` this is impossible with `f p = true` (`Ar ≥ -4` requires `S` at `p`), forcing `q - p ≥ 8`.
2. **Unique length-8 bridge `Z` (`gap_eight_bridge_unique_Z`)**: Encoding the 7 steps `p + 1 .. p + 7` as 0/1 indicators forces `b_1 = b_2 = b_3 = b_4 = 0` and `b_5 = b_6 = b_7 = 1`, uniquely identifying `seg f p 8 = Z := ASSSSAAA`.
3. **Replay exclusion of `Z ++ Z` (`consecutive_gap_eight_forbidden_on_replay`)**: Across two consecutive copies of `Z`, steps `p + 3 .. p + 10` form `SSAAAASS` with zero mass and zero area, so `replay_value_eq_abel_potential` yields `value b s (p + 11) = value b s (p + 3)`. Because `p + 3 ≥ 1` (`value b s (p + 3)` is already in `(run b s (p + 10)).seen`) while step `p + 10` is `S`, this contradicts `SeededReplay`'s freshness rule for `S` (without requiring `s.value ∈ s.seen`!).
4. **Two-step `≥ 20` and span `8n + 4(n/2)` (`common_source_two_step_gap_ge_twenty`, `fresh_common_source_hit_span`)**: Since consecutive gaps cannot both be `8`, any 2-step jump satisfies `r - p ≥ 8 + 12 = 20`, giving exact span `p0 + 8 * n + 4 * (n / 2) ≤ last`.
5. **Unified source-clock consumer (`original_win_source_clock_capacity`)**: Splitting `ps = ps.dropLast ++ [p_last]` (`M ≥ 2`), `p_pen < p_last` both share the common `Win` source `u`. Applying `E-802`'s `original_win_source_finite_capacity` directly forces `b + p_pen + 8 ≤ (run b s u).value` (since `value b s u ≤ (b + p_pen + 1) + 6` would forbid a second hit `p_last > p_pen`). Combined with `u + 3 ≤ p0` (from `(p0 - u) % 4 = 3`) and `fresh_common_source_hit_span` on `ps.dropLast` (`p0 + 8*(M-2) + 4*((M-2)/2) ≤ p_pen`), this yields `(b + u) + 11 + 8*(M-2) + 4*((M-2)/2) ≤ (run b s u).value` and `M ≤ 2 + ((run b s u).value - (b + u) - 9) / 10`.
6. **Negative control (`raw_nonfresh_counterexample_beats_fresh_span`)**: Explicit non-fresh sign sequence `SSAA ++ Z ++ Z ++ A` exhibits three common-source `Win` hits at `4, 12, 20` (`span = 16 < 20`), confirming that `S`-freshness is essential and not an artifact of pure walk/area arithmetic.

## Verification Summary

- `lake build Recaman Recaman.Audit`: exit `0`, 0 warnings in `FreshSourceHitSpacing.lean`, standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).
- `python3 scripts/harness_gate.py --lint-module Recaman/FreshSourceHitSpacing.lean`: `9/9 substantive theorems`.
- `python3 scripts/harness_lean.py --vacuity-row E-804`: `0 flagged, 0 unknown, 7 theorems`.
- `python3 docs/data/depth_general_20261128/fresh_source_hit_spacing_audit.py`: `ALL E-804 AUDITS PASSED`.

## Explicit Non-Claims

`E-804` establishes arbitrary-depth common-source hit spacing and source-clock capacity on `SeededReplay.run` and `Recaman.Basic.a`. It does **not** prove global `Fw` boundedness, `C1`, `Q`, `H`, `SL`, surjectivity, or any protected central claim (`E-001`, `E-067`, `E-070`, `E-179`).
