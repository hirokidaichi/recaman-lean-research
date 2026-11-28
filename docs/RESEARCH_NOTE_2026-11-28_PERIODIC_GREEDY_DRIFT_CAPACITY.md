# Research Note: Periodic Drift Dichotomy, `TypeIIFresh` Residue-Order Obstruction, and Golden-Ratio Capacity (`E-806`, `PROVED-LEAN`)

- **Date**: `2026-11-28`
- **Evidence label**: `PROVED-LEAN` (`E-806`)
- **Lean module**: [`Recaman/PeriodicGreedyDriftCapacity.lean`](../Recaman/PeriodicGreedyDriftCapacity.lean)
- **Hypothesis card**: [`docs/HYPOTHESIS_CARD_2026-11-28_PERIODIC_GREEDY_DRIFT_CAPACITY.md`](HYPOTHESIS_CARD_2026-11-28_PERIODIC_GREEDY_DRIFT_CAPACITY.md)
- **Statement audit**: [`docs/statement_audits/E-806.md`](statement_audits/E-806.md)
- **Reproducible audit**: [`docs/data/depth_general_20261128/periodic_greedy_drift_audit.py`](data/depth_general_20261128/periodic_greedy_drift_audit.py)

## 1. Summary

Following `E-797` (exact raw-`EndN` base `5/3`), `E-798` (`TypeIFresh` zero-drift and unit-drift `|d| = 1` periodic obstructions), and `E-805` (unconditional `Δ = 2` coherent cascade base `√(7/3) ≈ 1.527525` on `SeededReplay.run`), the natural arbitrary-depth question was whether **non-unit drift** `|d| ≥ 2` (either positive `d ≥ 2` or negative `d ≤ -2`) could allow a `Δ = 1` periodic coherent tower to beat `√(7/3)` or approach `5/3`.

`E-806` (`Recaman/PeriodicGreedyDriftCapacity.lean`) resolves the **periodic** drift-sign dichotomy unconditionally at **arbitrary excursion depth `H`** on every coherent `SeededReplay.run b st` (`st.value ∈ st.seen`) and on the canonical Recamán orbit `Recaman.Basic.a`:

1. **Exact Balanced Word Duality** (`balanced_word_sLandings_eq_levelAdditions`, `balanced_word_area_potential_identity`):
   By two clean prefix telescoping invariants—crossing parity for `S`-landings vs `A`-starts, and the quadratic potential `2 * wordRelPot V r k + (wordHeight V k - r) * (wordHeight V k - r - 1)` (whose `S`-step increment vanishes identically)—every balanced word `V` (`mass V = 0`) and every relative height `r : Int` satisfy:
   - `wordSLandings V r = wordLevelAdditions V r`,
   - `wordLowWeights V r + wordPotDrift V r = A_r(V) + 3 * A_{r+1}(V) + wordUpperExcess V r`.

2. **Negative-Drift Exact Golden-Ratio Capacity (`d ≤ 0`)** (`seeded_replay_periodic_neg_drift_exact_capacity`, `canonical_periodic_neg_drift_exact_capacity`):
   Combining `E-798`'s `TypeIFresh` pigeonhole `R * A_r(V) ≤ span + (R - 1) * (-d) + 1` with balanced duality eliminates `d` directly. Once `R ≥ wordPotSpan V r + |d| + 2`, the additive error drops out completely as an exact integer inequality:
   ```
   3 * A_{r+1}(V) + 2 * A_r(V) + wordUpperExcess V r ≤ wordLowWeights V r.
   ```
   Its two-height recurrence `3 * λ + 2 = (λ + 1)/(λ - 1)^2` has exact characteristic root `φ = (1 + √5)/2 ≈ 1.618034 < 5/3`. Moreover, because `wordPotDrift V r = areaW V - |V| * r` decreases strictly linearly in `r`, every height `r ≥ r* + 1` above the unique sign-flip threshold `r*` obeys `wordUpperExcess` on the LHS, forbidding exponential growth above `r*`.

3. **`TypeIIFresh` Periodic Residue-Order Obstruction & Negative-Drift `(AS)^a S` Ceiling** (`typeIIFresh_periodic_residue_order`, `seeded_replay_periodic_neg_drift_as_run_bound`):
   Attempted negative-drift `Δ = 1` cascades (`V = (AS)^p + A^4(AS)^{a_4} AA(AS)^j S (AS)^{a_5} S^5`) empirically reached `92.2%` supplied `E_5` when ignoring `TypeIIFresh`, yet always crashed on `TypeIIFresh` at height `4`. We formalize the exact mechanism: for **any** `SeededReplay.run b st` (no coherence needed) and any balanced `V` with `d = wordPotDrift V r ≠ 0` repeating `R ≥ wordPotSpan V r + 1` times, any `S`-landing `t` at height `r` and `A`-step `u` at height `r + 1` satisfying `|d| ∣ (Φ_r(t + 1) - Φ_r(u))` must satisfy:
   - `d < 0 → Φ_r(t + 1) ≤ Φ_r(u)` (and `t < u` on equality),
   - `0 < d → Φ_r(u) ≤ Φ_r(t + 1)` (and `t < u` on equality).
   For negative drift (`d < 0`), any `(AS)^a S` top-arch run at height `r + 1` has `A`-candidates `X + 3 * i` (`0 ≤ i < a`) strictly below its terminal `S`-landing `X + 3 * a`, forcing `∀ k ∈ [1, a], ¬(|d| ∣ 3 * k)`, hence `a < |d|` and `(3 ∣ d) → 3 * a < |d|`.

4. **Positive-Drift Arbitrary-`d` Top-Level Collapse (`d ≥ 0`) & Sign-Free Golden-Ratio Law** (`seeded_replay_periodic_pos_drift_top_collapse`, `seeded_replay_periodic_top_golden_capacity`, `canonical_periodic_top_golden_capacity`):
   Lifting `E-797`'s `n = 0` (`BlockWord.nil`) budget to an arbitrary offset `s` with zero `BlockWord` assumption (`arbitrary_offset_two_height_budget`, `prefixBudgetSlack` vanishing identically at `s = 0`), combining `E-797` with `E-798` and balanced duality proves that for **every** nonnegative drift `0 ≤ wordPotDrift V (H - 1)` (not only `|d| = 1`):
   ```
   E_{H-1}(V^R) ≤ 3 * F_H(V^R) + 3 * AA_{H-2}(V^R) + wordPotSpan V (H - 1) + |d| + 1 + prefixBudgetSlack.
   ```
   Combining the `d ≥ 0` collapse and `d < 0` negative-drift bound yields the **sign-free** top-level golden-ratio capacity law on every coherent `SeededReplay.run` and on `Recaman.Basic.a`:
   ```
   3 * E_H(V^R) + 2 * E_{H-1}(V^R) ≤ W(H - 1)(V^R) + 6 * AA_{H-2}(V^R) + 3 * F_H(V^R) + span + |d| + 1 + 2 * prefixBudgetSlack.
   ```
   Raw non-fresh `E-786` (`d = 0`) violates both the negative-drift bound (`+61/copy`) and the sign-free bound (`+190` at `R = 10`, diverging linearly to `+∞`).

## 2. Verification Summary

- Audit script: `python3 docs/data/depth_general_20261128/periodic_greedy_drift_audit.py` (`ALL E-806 AUDITS PASSED`; `35,460` repeated balanced subwords checked on canonical `Recaman.Basic.a(0..15000)`).
- Build: `lake build Recaman.PeriodicGreedyDriftCapacity Recaman.Audit` (0 errors, 0 warnings, 0 sorry, standard axioms `[propext, Classical.choice, Quot.sound]` only).
- Harness lint: `38/45` substantive theorems (`python3 scripts/harness_gate.py --lint-module Recaman/PeriodicGreedyDriftCapacity.lean`).
- Vacuity lint: `0 flagged, 0 unknown, 9 theorems` (`python3 scripts/harness_lean.py --vacuity-row E-806`).

## 3. Open Frontier

- `E-806` completely characterizes the periodic drift-sign dichotomy (`d ≤ 0` golden-ratio + `TypeIIFresh` `(AS)^a` ceiling; `d ≥ 0` arbitrary-drift `E_{H-1}` collapse; sign-free `3 E_H + 2 E_{H-1}` law), ruling out both naive positive-drift and negative-drift `Δ = 1` periodic cascades.
- The main remaining open question for `ρ_greedy ∈ [√(7/3), 5/3]` is whether **non-periodic** `TypeIFresh ∧ TypeIIFresh` sign words obey an unconditional `< 5/3` global exponential upper bound, or whether a non-periodic fresh construction can strictly beat `√(7/3)`.
