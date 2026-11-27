# Hypothesis card: `cross-block-source-bank-reuse`

- ID: `H-20261127-01` (executes `H-20261126-01`)
- Owner: Antigravity (proposer / falsifier / formalizer / separate audit pass)
- Created: 2026-11-27
- Status: `REFUTED` (main candidate `H-20261126-01` & all linear cross-block capacities); `PROVED-LEAN` (`E-783`, arbitrary-`H`/arbitrary-`R`/arbitrary-`U` unbounded-ratio theorem + 2-block refutation); `PROVED-PAPER` (`E-784`, coherent-greedy-realizable unbounded-ratio family for all `k ≥ 3`)
- Research branch: `cross-block-charging`
- Work state: completed (`E-783` Lean checked; `E-784` paper proof + discovery/holdout verified)
- Parent card / allocation cycle: `R-20261127-01` (main depth-general track)

## Exact statement

We evaluate the exact candidate frozen in `H-20261126-01`:

For arbitrary `R ≥ 1`, stage heights `H_i ≥ 2`, positive counts `a_(i,h) ≥ 1`, let
$$V_i = \left(\prod_{h=0}^{H_i} (AS)^{a_{i,h}-1} A\right) S^{H_i+1}.$$
For EVERY finite original prehistory `U` of length `n`, `m = 2 + max_i H_i`, cut `c = n + m`, and full word `U ++ S^m ++ V_1 ++ ... ++ V_R ++ AA`, with origin fixed at `0`, `F` = original free `A` after `c`, `O_c` = originally supplied `A` after `c` with NO internal supplier `u ≥ c` (retaining co-supplied targets as internal):
$$\text{Candidate:}\quad 2 A_{\text{after cut}} \le 3 (F + O_c) - 3.$$

**Results**:

1. **Exact Refutation & Unbounded Raw-Sign Ratio (`E-783`, `PROVED-LEAN` in `Recaman/CrossBlockReuseUnbounded.lean`)**:
   - Exact partition (`additions_partition_after_cut`): `additions f c L = internalSuppliedCount f c L + (free f c L + exclusiveOldCount f c L)` for every `f, c, L`.
   - Exact 2-block minimal refutation (`h20261126_two_block_counter`): for `V_1 = stagedBlock [1,2,1,1]`, `V_2 = stagedBlock [1,1,1,2]` (`R = 2, H = 3`, 27 letters after any `U` of length `n`), `additions = 12`, `internalSuppliedCount ≥ 4`, and `3 * (F + O_c) - 3 < 2 * additions` (`21 < 24`), for EVERY `f : Nat → Bool` and EVERY `n : Nat`.
   - Arbitrary-depth / arbitrary-`R` bank-reuse family (`cross_block_reuse_counts`): for every `k ≥ 1` (`H = 3k`, `a = k(3k - 2)`, `bank = 3a + 2`, `lift = a + 1`), every `R : Nat`, every `f : Nat → Bool`, and every `n : Nat` matching `familyWord k R` after `n`,
     `additions = (4a + H + 4) + R(H + a)`, `R * a ≤ internalSuppliedCount`, and `F + O_c ≤ (4a + H + 4) + R * H`.
   - **No linear cross-block capacity (`no_linear_cross_block_capacity`)**: for EVERY slope `C : Nat` and additive constant `K : Nat`, there exist explicit staged-grammar parameters `k ≥ 1, R ≥ 1` such that for EVERY `f : Nat → Bool` and EVERY prehistory length `n : Nat` matching `familyWord k R`,
     $$C \cdot (F + O_c) + K < A_{\text{after cut}}.$$

2. **Coherent-Greedy-Realizable Unbounded Ratio (`E-784`, `PROVED-PAPER`)**:
   Even when restricting to words that satisfy E-759 (I)/(II) (`fI = 0, fII = 0`) — and hence by `E-782` execute greedily from a coherent finite `State` whose exact seen set passes all 8 canonical scalar+spatial filters — NO linear cross-block capacity `A_after_cut ≤ C * (F + O_c) + K` holds:
   - At `R = 2`, the 25-letter word `V_1 = [2,1,1]`, `V_2 = [1,1,1,2]` has `A = 11, L = 3, F = 8, O_c = 0`, `2A = 22 > 21 = 3(F+O_c)-3`, with `E-759 = (0, 0)` and verified literal 8-filter greedy replay.
   - For EVERY `k ≥ 3`, setting `u = 6k + 2`, `h = 2u`, `K = 3u`, `a = 36k^2 + 8k - 1`, `R = (3k+1)^2`, `lift = 9k + 4`, `bank = 117k^2 + 105k + 29`, `V_0 = [1]^(h-2) ++ [bank] ++ [1]^(u+1) ++ [lift]`, `V = [1]^h ++ [a] ++ [1]^u`, the staged word `S^(K+2) ++ V_0 ++ V^R ++ AA` obeys:
     - `ΔΦ_{h-1}(V) = +1` (coprime shift),
     - all `R * a` stage-`h` additions are internally supplied by `V_0`'s stage-`(h-2)` bank, yielding `A / (F + O_c) = 2k - O(1) → ∞`,
     - **zero E-759 (I) collisions and zero E-759 (II) collisions** across all heights `0 ≤ y ≤ K + 1` (proved algebraically via exact polynomial interval separation across 6 height regimes).

## Why it would matter

- Frontier obligation discharged: decisively resolves `H-20261126-01` within the 15-minute gate by refuting not only `2A ≤ 3(F + O_c) - 3` at `R = 2`, but EVERY constant-factor linear cross-block capacity `A ≤ C(F + O_c) + K`, both in raw sign histories (`PROVED-LEAN`, `E-783`) and under full coherent greedy S-freshness + 8 canonical spatial/scalar filters (`PROVED-PAPER`, `E-784`).
- Stronger than an existing identity or equivalent reformulation because: `E-776` proved `2A ≤ 3(F + O_c) - 3` for a single staged block `R = 1`; `E-783` and `E-784` show that as soon as `R ≥ 2` balanced blocks can return to height `0`, a single lower-stage source bank can be reused `Θ(R)` (raw) or `Θ(k^2)` (coherent greedy) times across distinct blocks, completely destroying linear `F + O_c` charging of total `A`.
- Smallest useful consequence: closes the `E-776 → multi-block linear A/(F+O_c)` charging branch and pinpoints the exact obstruction (unbounded cross-block reuse of a single source bank).

## Connection to arbitrary depth

- Assessment axis: `depth_general_progress` (Protocol §1.8 criterion 3: exact arbitrary-depth countermechanism/no-go proved in Lean 4 and extended to coherent greedy histories).
- Quantifiers and dependence on depth D, length, height and run count: `E-783` quantifies over arbitrary `C, K, f, n` with unbounded height `H = 3k` and block count `R`; `E-784` quantifies over all `k ≥ 3`.
- Original actual-supply/free assumptions and their producers: origin stays strictly at `0`; `additions_partition_after_cut` retains every old prehistory `U` and co-supplier without deleting or resetting `EndN f 0`.
- Repeated use of the same free position, maximum load and boundary correction: exhibits the exact failure mode — each peak in `V_0`'s bank supplies `R` distinct targets across copies `V_1..V_R` in `E-783`, and up to `min(R, a)/3 ~ 3k^2` targets in `E-784`, while legally avoiding S-collisions.
- Depth-dependent cost and its proved payment/cancellation: neither `E-783` nor `E-784` refutes C1 — extra depth below initial head `m` is `D_depth = 0`, and `F` grows as `Θ(R H)` (`E-783`) or `Θ(k^3)` (`E-784`), far exceeding `m = O(k)`.
- Concrete next inequality or history-preserving induction step consuming this result: any arbitrary-depth charging theorem over multiple balanced blocks must either charge `D_depth` / `LOW free` directly (not total `A`) or account for the height `H` (since at fixed height `H`, `A/(F+O_c)` in our reuse mechanism scales linearly in `H`).
- Existing generic input and the genuinely new edge beyond it: `E-776` (`R = 1` capacity) and `E-759`/`E-782` (greedy realizability) are inputs; the new edge is the cross-block zero-shift / unit-shift bank-reuse mechanism and its Lean 4 proof (`E-783`) and 6-regime greedy separation proof (`E-784`).
- Countermodel/no-go test for this mechanism, with reachability scope: `E-783` is a raw-sign no-go (holds for every `U`, does not require greedy realizability); `E-784` establishes coherent finite-State greedy realizability (passing all 8 filters of `E-782`), NOT canonical reachability from `a 0 = 0` and NOT a C1 counterexample.

## Allocation and decision value

- Mode: global exploration + falsification + Lean formalization.
- Competing units and shared bottlenecks: main depth-general track paired with Track 2 (`H-20261127-02`, spatial visited inventory).
- Why this unit now: designated first-15-minute gate from 2026-11-25 DAILY handoff (`H-20261126-01`).
- If successful, which dependency edge changes?: closes linear cross-block `A ≤ C(F + O_c) + K` charging unconditionally in Lean 4 (`E-783`) and under full greedy S-freshness on paper (`E-784`).

| Budget dimension | Cycle total | This unit planned | This unit actual | Cap / accounting rule |
|---|---|---|---|---|
| Agent work minutes | ~115 min | 35 min (falsification + Lean + all-`k` paper proof) | ~35 min (10:07–10:17 & 10:27–10:52 JST) | Tracked separately from Track 2 |
| Python CPU seconds | — | ≤15s | ~10.6s (`cross_block_discovery.py` 0.49s + `cross_block_holdout.py` 4.68s + diagnostics ~5.4s) | Single-process exact checks |

- Audit reservation and who performs the separate audit pass: independent semantic audit pass + `harness_gate.py` + `harness_lean.py --vacuity-module` + `./scripts/check.sh`.
- First checkpoint: 10:22 JST — met at 10:08 JST (`R = 2` counterexample + unbounded family found within 1 minute!).

## Provenance and dependencies

- Definitions used: `Recaman.SingleWindowEquality.{Fw, Ar, Win, EndN, cN}`, `Recaman.AdditionRankSlack.{additions, free}`, `Recaman.CrossBlockReuseUnbounded.{stagedBlock, MatchesAt, InternalSupplied, ExclusiveOldSupplied}`.
- Lean theorems used: `cN_split`, `cN_congr`, `cN_add`, `cN_sub`, `cN_succ_pos`, `cN_succ_neg`, `Fw_succ`, `Ar_succ`, `Ar3`.
- Unverified mathematical assumptions: none for `E-783`; `E-784` is `PROVED-PAPER` (human review pending, not yet Lean-checked).

## Falsification plan

- Small and boundary cases: exhaustive `R = 2, H_i ∈ {2,3}, a ∈ {1,2,3}` (1,241 cases), `R = 1` E-776 sharp ASAA repeats (`n = 1..4, R = 1..5`), `k = 1` (`H = 3, a = 1`), empty and 5 non-empty prehistories `U` (checking co-suppliers).
- Adversarial or weakened-history model: `E-783` `minCounterWord` (`[(1,2,1,1),(1,1,1,2)]`) was tested for E-759 and caught to have `fI = 1`, motivating the distinct coherent 2-block counter `[(2,1,1),(1,1,1,2)]` (`fI = 0, fII = 0`) and the full coherent `E-784` Family B (`k ≥ 3`).
- Discovery range: exhaustive `R = 2` (1,241 words) + 5,000 random multi-block words + Family B `k = 3, 4`.
- Frozen holdout range: Family B `k = 5, 6, 7` (up to `Q = 1,902,094` letters) + independent `O(Q^2)` checks on `minCounterWord` + 6 prehistories `U` + literal 8-filter greedy replay on `[(2,1,1),(1,1,1,2)]` and `u = 6, h = 13, R = 6`.
- Maximum one permitted repair: 0 repairs to `E-783`; 1 formula correction in `cross_block_holdout.py` section 4 (`a = 28` for `u = 6, h = 13`).
- Stop condition: stop linear cross-block `A/(F+O_c)` charging search (`STOPPED` as a general method).

## Evidence log

| Date | Label | Revision / command | Result |
|---|---|---|---|
| 2026-11-27 | `COMPUTED` | `python3 docs/data/depth_general_20261127/cross_block_discovery.py` | 6 counters in exhaustive `R=2`, best `[(1,2,1,1),(1,1,1,2)]` (`A=12, L=4, F=8, O_c=0, slack=-3`) |
| 2026-11-27 | `PROVED-LEAN` | `lake build Recaman.CrossBlockReuseUnbounded && harness_gate.py --lint-module && harness_lean.py --vacuity-module` | 26/28 substantive, 0 flagged, 0 unknown across 14 elaborated theorems (`E-783`) |
| 2026-11-27 | `COMPUTED` | `python3 docs/data/depth_general_20261127/cross_block_holdout.py` | Independent `O(Q^2)` check on `U` variants + coherent 2-block `[(2,1,1),(1,1,1,2)]` + Family B `k=3,4` (disc) & `k=5,6,7` (holdout): `fI=0, fII=0`, ratio up to `13.6604` |
| 2026-11-27 | `PROVED-PAPER` | `docs/RESEARCH_NOTE_2026-11-27_CROSS_BLOCK_REUSE.md` | Complete 6-regime polynomial proof of `E-759 = (0, 0)` and `A/(F+O_c) = 2k - O(1) → ∞` for all `k ≥ 3` (`E-784`) |

## Semantic audit

- Informal statement implies formal statement: Yes — `stagedBlock`, `familyWord`, `InternalSupplied`, `ExclusiveOldSupplied`, `additions`, and `free` match `H-20261126-01` verbatim with origin kept at `0`.
- Formal statement implies intended consequence: Yes — `no_linear_cross_block_capacity` quantifies over all `C, K, f, n`, proving no linear bound `A ≤ C(F + O_c) + K` can hold across repeated balanced blocks for ANY prehistory `U`.
- Counterfactual examples that should make the statement false: `R = 1` satisfies `2A ≤ 3(F + O_c) - 3` (`E-776`), confirming multiple blocks (`R ≥ 2`) are essential; `minCounterWord` fails E-759 (`fI = 1`), separating `E-783` from greedy-realizable `E-784`.
- Could the theorem be proved from weaker or vacuous assumptions?: No (`harness_lean.py --vacuity-module`: 0 flagged, 0 unknown).
- Are reachability, freshness, time order, or actual-orbit provenance accidentally omitted?: No — raw-sign (`E-783`) vs coherent finite-State greedy (`E-784`) vs canonical reachability (`a 0 = 0`) vs C1 (`D_depth = 0`) are kept strictly separate.

## Decision

- Continue / formalize / refute / stop: **`H-20261126-01` REFUTED** (`E-783` `PROVED-LEAN`, `E-784` `PROVED-PAPER`); linear multi-block `A/(F+O_c)` charging **STOPPED**.
- Depth-general assessment: **yes** (Protocol §1.8 criterion 3: arbitrary-depth Lean 4 no-go + coherent greedy all-`k` countermechanism).
- Reopen only if: a height-dependent cross-block bound `A ≤ f(H) · (F + O_c)` or direct `LOW free` / `D_depth` charging is formulated (not a constant-slope `A/(F+O_c)` inequality).
