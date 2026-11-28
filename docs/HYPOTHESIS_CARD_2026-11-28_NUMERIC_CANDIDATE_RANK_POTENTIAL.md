# Hypothesis Card: Purely Numeric Candidate-Band Rank Potential & All-Time Fresh Wallet (E-802)

- **Date**: 2026-11-28
- **Status**: `PROVED-LEAN` (`E-802`, `Recaman/NumericCandidateRankPotential.lean`)
- **Branch / Frontier**: General-principle arbitrary-depth branch — genuinely different purely numeric mechanism (upgrading `E-761 PROVED-PAPER` to `PROVED-LEAN` directly on `Recaman.SeededReplay` and `Recaman.Basic.a`)

## 1. Precise Statement & Quantifiers

For arbitrary `b : Nat`, `s : State` (coherence `s.value ∈ s.seen` NOT assumed!), let `replayCand b s t := value b s t - (b + t + 1)` and `bandRank Y b s p := (Y / 3 + 1) * Fw (replaySign b s) p - replayCand b s p / 3`.

1. **Exact bridge identity (`candidate_area_bridge_identity`)**: For all `p, q : Nat`:
   `floorPotential (replaySign b s) 0 (Fw p - 2) q - floorPotential (replaySign b s) 0 (Fw p - 2) p = (b + q + 1) * (Fw q - Fw p) + replayCand b s p - replayCand b s q`.
2. **Sharp permanent future sign floor (`small_candidate_permanent_floor`, `small_candidate_floor_sharp`)**:
   - If `replaySign b s p = true` and `replayCand b s p ≤ (b + p + 1) + 6`, then `∀ t ≥ p, Fw p - 1 ≤ Fw t`.
   - Sharp for EVERY `n ≥ 2`: `(b = n - 1, val = 2n + 7, seen = [0, n + 7, 2n + 7])` has `replayCand = n + 7` and executes `ASSS`, reaching `Fw 4 = -2`.
3. **Bounded candidate-band monotone rank (`candidate_band_rank_strict_mono`, `candidate_band_fixed_height_sharp`)**:
   - For every `Y : Nat` and `p < q` with `replaySign b s p = true`, `Y ≤ b + p + 1`, and `replayCand p, replayCand q ∈ [0, Y]`: `Fw p ≤ Fw q`, `Fw q = Fw p → replayCand q + 3 ≤ replayCand p`, and `bandRank Y b s p + 1 ≤ bandRank Y b s q`.
   - Sharp fixed-height count `Y / 3 + 1` for EVERY `Y : Nat` via `(AS)^(Y/3) A`.
4. **Independent all-time fresh-value wallet (`same_candidate_same_height_fresh_wallet`)**:
   - Without ANY late-clock restriction or coherence hypothesis, any strictly sorted list `ps` of actual `A`-clocks sharing `(y : Nat, k : Int)` satisfies `ps.length ≤ max 1 (y - 2)`.
5. **Late-clock strict ascent & fixed original `Win` source finite capacity (`same_candidate_late_strict_ascent`, `original_win_source_finite_capacity`)**:
   - For fixed `y : Nat`, after `y ≤ (b + p + 1) + 6`, every later event `q > p` with `replayCand q = y` has `Fw p + 1 ≤ Fw q`.
   - Every fixed original `Win` source `u` supplies at most `max 1 ((run b s u).value - 2)` hits in all time and at most `1` hit after `value b s u ≤ (b + p + 1) + 6`.
6. **Running-minimum positivity lower bound & finite-horizon cardinality (`replay_fw_lower_bound`, `candidate_band_finite_horizon_count_le`, `canonical_orbit_candidate_band_bounds`)**:
   - `∀ b s t, -(s.value / (b + 1)) ≤ Fw t`.
   - Selected events in `[0, Q)` number at most `(Y / 3 + 1) * (Fw Q + s.value / (b + 1) + 2)`, specializing unconditionally on `Recaman.Basic.a` to `(Y / 3 + 1) * (Fw canonicalOrbitSign Q + 2)`.

## 2. Dependencies

- `Recaman.Basic`, `Recaman.SeededReplay`, `Recaman.CoherentGreedyFreshness` (`E-798`).

## 3. Falsifier / Discovery-Holdout Computation

- Script: `docs/data/depth_general_20261128/numeric_candidate_rank_audit.py`
- Command: `python3 docs/data/depth_general_20261128/numeric_candidate_rank_audit.py`
- Results:
  - `+6` permanent floor sharpness verified for `n = 2..30` (`ASSS` hits `Fw 4 = -2`).
  - Fixed-height count `Y / 3 + 1` sharpness verified for `Y = 0..40` (`(AS)^(Y/3) A`).
  - Non-vacuity control: canonical `a[0..2500]` attains same-`(y, k)` multiplicity `3 ≥ 2`.
  - Discovery (`a[0..1000]` + 50 arbitrary states including incoherent) and Holdout (`a[0..2500]` + 50 arbitrary states): `ALL E-802 AUDITS PASSED`.

## 4. Lean Verification & Independent Audit

- Module: `Recaman/NumericCandidateRankPotential.lean` (`11` public theorems in `Recaman/Audit.lean`, `0` warnings, `0` `sorry`/`admit`/`native_decide`/custom axioms).
- `python3 scripts/harness_gate.py --lint-module Recaman/NumericCandidateRankPotential.lean`: `22/23` substantive theorems (`11/11` public theorems `SUBSTANTIVE`).
- `python3 scripts/harness_lean.py --vacuity-row E-802`: `0 flagged, 0 unknown, 11 theorems`.
- Statement audit: `docs/statement_audits/E-802.md`.

## 5. Explicit Non-Claims & Next Decision

- As `E-762` proved, translating a finite word's initial stock can push all candidates above the clock, so a single candidate band `[0, Y]` does not cover all additions; does NOT prove `Fw` globally bounded, `C1`, `Q`, `H`, `SL`, surjectivity, or `E-001`/`E-067`/`E-070`/`E-179`.
- Next decision: formalize the second genuinely different purely numeric arbitrary-depth mechanism `Recaman/NumericStockStripPotential.lean` (`E-772` departure `A` upcrossing strip + `34/15` floor potential beating `3^j` from `j ≥ 7`) as `E-803`, then `Recaman/FreshSourceHitSpacing.lean` (`E-760` + `E-761` source-clock consumer) as `E-804`.
