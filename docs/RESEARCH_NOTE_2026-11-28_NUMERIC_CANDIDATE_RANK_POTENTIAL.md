# Research Note: Purely Numeric Candidate-Band Rank Potential & All-Time Fresh Wallet in Lean 4 (E-802)

- **Date**: 2026-11-28
- **Evidence**: `E-802 PROVED-LEAN` (`Recaman/NumericCandidateRankPotential.lean`)
- **Upgrades**: `E-761` (`PROVED-PAPER`, `docs/RESEARCH_NOTE_2026-11-20_CANDIDATE_HEIGHT_POTENTIAL.md`)
- **Audit script**: `docs/data/depth_general_20261128/numeric_candidate_rank_audit.py`
- **Statement audit**: `docs/statement_audits/E-802.md`

## 1. Overview (Genuinely Different Arbitrary-Depth Mechanism)

Unlike the sign-word spacing capacities (`E-785`, `E-788`, `E-794`, `E-797`, `E-800`) and chronological freshness filters (`E-798`, `E-801`), `Recaman/NumericCandidateRankPotential.lean` formalizes a **purely numeric positivity + fresh-value wallet mechanism** directly on arbitrary finite-state greedy continuations `SeededReplay.run b s` (without assuming `s.value ∈ s.seen`) and on the canonical Recamán orbit `Recaman.Basic.a`.

## 2. Formalized Theorem Chain (`11` Public Theorems, `0` Warnings, `0` Vacuity Flags)

1. **`candidate_area_bridge_identity`**: Using `replay_value_eq_abel_potential` (`E-798`), for every `b, s, p, q`:
   $$\Phi_{H_p - 2}(q) - \Phi_{H_p - 2}(p) = (b + q + 1)(H_q - H_p) + c_p - c_q,$$
   where $c_t = X_t - (b + t + 1)$ and $H_t = \mathrm{Fw}(\mathrm{replaySign}\,b\,s)\,t$.
2. **`small_candidate_permanent_floor` & `small_candidate_floor_sharp`**:
   - If step `p` is an addition (`A`) with $c_p \le (b + p + 1) + 6$, then EVERY future clock $t \ge p$ satisfies $H_t \ge H_p - 1$. The proof takes the least drop $d$ to $H_p - 2$, observes $d \ge 4$ and an intermediate crossing $u \in (p + 1, p + d - 1)$ with $H_u = H_p$ via discrete IVT, giving $\Phi_{H_p - 2}(p + d) - \Phi_{H_p - 2}(p) \ge 2 + 1 + 0 - 1 = 2$, which forces $X_{p + d} \le 0$, contradicting positivity $X_{p + d} \ge 1$.
   - Constant $+6$ is **exact for every $n \ge 2$**: starting from $b = n - 1$, $s = \{2n + 7, [0, n + 7, 2n + 7]\}$ gives $c_0 = n + 7$ and executes `ASSS` to $H_4 = -2$.
3. **`candidate_band_rank_strict_mono` & `candidate_band_fixed_height_sharp`**:
   - Fix any $Y \in \mathbb{N}$ and $K = \lfloor Y/3 \rfloor + 1$, and define $\Phi_Y(p) = K \cdot H_p - \lfloor c_p / 3 \rfloor$. For any $p < q$ with $A$ at $p$, $b + p + 1 \ge Y$, and $c_p, c_q \in [0, Y]$, we prove $H_p \le H_q$, $H_q = H_p \Rightarrow c_q + 3 \le c_p$, and $\Phi_Y(p) + 1 \le \Phi_Y(q)$ (note: no `A` hypothesis at `q` is required!).
   - The fixed-height bound $K = \lfloor Y/3 \rfloor + 1$ is **exact for every $Y \in \mathbb{N}$**: `sharpBandState Y` executes $(AS)^{\lfloor Y/3 \rfloor} A$, realizing $\lfloor Y/3 \rfloor + 1$ events at height $0$ with candidates $Y, Y - 3, \dots, Y - 3\lfloor Y/3 \rfloor$.
4. **`same_candidate_same_height_fresh_wallet`**:
   - For fixed $(y : \mathbb{N}, k : \mathbb{Z})$ with **no late-clock restriction** and **no coherence hypothesis**, any strictly increasing list `ps` of `A`-clocks sharing $c_p = y$ and $H_p = k$ has length $\le \max(1, y - 2)$. Between every consecutive pair $(p_i, p_{i+1})$, the bridge identity forces $\Phi_{k - 2}(p_{i+1}) = \Phi_{k - 2}(p_i)$ while $H_{p_i + 1} = k + 1$, forcing a first fresh `S`-landing $v_i \in (p_i, p_{i+1}]$ at height $k - 1$ with $1 \le X_{v_i} \le y - 3$. Freshness makes $\{X_{v_i}\}$ pairwise distinct in $\{1, \dots, y - 3\}$.
5. **`same_candidate_late_strict_ascent` & `original_win_source_finite_capacity`**:
   - After $y \le (b + p + 1) + 6$, any later clock $q > p$ with $c_q = y$ satisfies $H_q \ge H_p + 1$.
   - Every original `Win` source $u$ enforces $c_p = X_u$ and $H_p = H_u + 1$ at all its hits, so source $u$ supplies at most $\max(1, X_u - 2)$ hits in all time and at most $1$ hit after $X_u \le (b + p + 1) + 6$.
6. **`replay_fw_lower_bound`, `candidate_band_finite_horizon_count_le`, & `canonical_orbit_candidate_band_bounds`**:
   - Extracting the running minimum $r \le t$ of $H$ gives $-\lfloor s.\mathrm{value}/(b + 1)\rfloor \le H_t$ unconditionally.
   - Combining the running-minimum lower bound with `small_candidate_permanent_floor` (`H_p ≤ H_Q + 1`) and `candidate_band_rank_strict_mono` yields `|bandSelectedClocks Y b s Q| ≤ (Y / 3 + 1) * (H_Q + s.value / (b + 1) + 2)`, specializing unconditionally on `Recaman.Basic.a` to `(Y / 3 + 1) * (Fw canonicalOrbitSign Q + 2)`.

## 3. Verification & Audit

- `lake build Recaman Recaman.Audit`: exit `0`, `0` warnings in `NumericCandidateRankPotential.lean`, standard axioms only.
- `python3 scripts/harness_gate.py --lint-module Recaman/NumericCandidateRankPotential.lean`: `22/23` substantive theorems (`11/11` public `SUBSTANTIVE`).
- `python3 scripts/harness_lean.py --vacuity-row E-802`: `0 flagged, 0 unknown, 11 theorems`.
- `python3 docs/data/depth_general_20261128/numeric_candidate_rank_audit.py`: `ALL E-802 AUDITS PASSED`.
