# Chronological `S`-Freshness in Lean 4 (`E-798`) and the Optimal Unit-Drift `Δ = 2` Coherent Greedy Cascade (`E-799`)

- **Date**: 2026-11-28
- **Evidence rows**:
  - `E-798` (`PROVED-LEAN`, `Recaman/CoherentGreedyFreshness.lean`)
  - `E-799` (`PROVED-PAPER`, this note + `docs/data/depth_general_20261128/delta2_coherent_cascade_audit.py`)

## 1. Executive Summary

`E-797` (`PROVED-LEAN`) closed the exact arbitrary-depth exponential growth base of actual `EndN` supply to **`5/3`** (`(2/5)(5/3)^H ≤ A/F ≤ (9/5)(5/3)^H`). The immediate open question was whether chronological greedy `S`-freshness (`E-759 (I)/(II)`) separates coherent finite-state greedy continuations from raw actual `EndN` words, and what exponential base `ρ_greedy` coherent greedy words can achieve.

This note records two coupled results:
1. **`E-798` (`PROVED-LEAN`)**: We formalize the exact Abel-summation bridge from arbitrary finite-state greedy replays `SeededReplay.run b s` (and unconditionally the canonical clock-0 orbit `Recaman.Basic.a`) to `floorPotential`, prove both `TypeIFresh` and `TypeIIFresh` unconditionally, and establish the **arbitrary-depth periodic `S`-freshness pigeonhole law**:
   $$R \cdot \mathrm{wordSLandings}(V, r) \le \mathrm{wordPotSpan}(V, r) + (R - 1)\cdot |\mathrm{wordPotDrift}(V, r)| + 1$$
   for every balanced word $V$ ($\mathrm{mass}(V) = 0$) repeated $R \ge 1$ times. Two sharp structural obstructions follow directly on every coherent greedy replay and on `Recaman.Basic.a`:
   - **Zero-drift obstruction**: If $\mathrm{wordPotDrift}(V, r) = 0$ and $\mathrm{wordSLandings}(V, r) \ge 1$ (which holds for every `E-786` balanced cascade cycle $V_H$ at height $r = H - 1$), then $R \le \mathrm{wordPotSpan}(V, r) + 1$. Thus the `E-786` $5/3$ cascade mechanism is rigorously obstructed from arbitrary repetition in coherent greedy replays and in `Recaman.Basic.a`.
   - **Unit-drift `Δ ≥ 2` necessity**: If $|\mathrm{wordPotDrift}(V, r)| = 1$ and $R \ge \mathrm{wordPotSpan}(V, r) + 2$, then $\mathrm{wordSLandings}(V, r) \le 1$. Consequently, any unit-drift coherent recursive tower whose top height $h_k$ is supplied from height $h_k - 1$ cannot populate height $h_k - 1$ with an earlier cascade stage (which would contribute $\ge 2$ `S`-landings at height $h_k - 1$): successive cascade levels MUST satisfy **$h_k - h_{k-1} \ge 2$ (`Δ ≥ 2`)**.
2. **`E-799` (`PROVED-PAPER`)**: We construct an explicit **`Δ = 2`** unit-drift coherent greedy cascade on height ladder $h_k = 2k + 2$ (band $[-1, 2k + 3]$) that matches `E-798`'s `Δ ≥ 2` optimality threshold. By placing the mod-3 congruence prefix $(AS)^{q_k}$ ($q_k \in \{0, 1, 2\}$) **before** $(SA)^{p_k}$ in $V_k$, every height $r \in [-1, 2k + 3]$ remains strictly corridor-separated (`E-759 = (0, 0)`), yielding exact per-stage growth $\mu = 7/3$ and per-height exponential base
   $$\rho_{\Delta=2} = \sqrt{7/3} \approx 1.527525 > 3^{1/3} \approx 1.442250,$$
   strictly narrowing the coherent greedy exponential base interval from $[3^{1/3}, 5/3]$ (`E-789` / `E-797`) to **`[\sqrt{7/3}, 5/3] = [1.527525, 1.666667]`**.

## 2. Lean 4 Formalization Architecture (`E-798`)

In `Recaman/CoherentGreedyFreshness.lean`:
- `replaySign b s t := decide (¬ CanSubtract (b + t + 1) (run b s t))` and `canonicalOrbitSign t := replaySign 0 initial t`.
- `replay_value_eq_abel_potential`: by induction on `t`,
  $$\mathrm{value}(b, s, t) = s.\mathrm{value} + (b + 1)\cdot \mathrm{Fw}_t - \mathrm{floorPotential}(f, 0, \mathrm{Fw}_t - 1, t).$$
- `seeded_replay_typeIFresh` (requires only `hs : s.value ∈ s.seen`) and `seeded_replay_typeIIFresh` (requires NO `s.value ∈ s.seen` assumption: at any earlier `A`-step `u < t` with `Fw u = r + 1`, the equality `value(t+1) = value(u) - (b + u + 1)` forces `value(u) - (b + u + 1) > 0`, so the failure of `CanSubtract` at `u` forces membership in `(run b s u).seen ⊆ (run b s t).seen`, contradicting `CanSubtract` at `t`).
  - *Negative control* (`coherent_greedy_freshness_audit.py`): `b = 0, s.value = 3, s.seen = {1}` yields values `[3, 2, 4, 7, 3]` with `E-759 = (1, 0)` (`TypeIFresh` fails at `t = 3`, `TypeIIFresh` holds).
- `canonical_orbit_greedyFresh`: proves `run 0 initial t = stateAt t` and discharges `initial.value ∈ initial.seen`, giving `TypeIFresh`, `TypeIIFresh`, and `(a t : Int) = Fw t - floorPotential 0 (Fw t - 1) t` unconditionally on `Recaman.Basic.a`.
- `typeIFresh_periodic_s_count_le_drift`: for balanced $V$ repeated $R \ge 1$ times, each pair $(c, j) \in \{0,\dots,R-1\} \times \mathrm{wordSLandingIndices}(V, r)$ maps to a distinct integer value of $\Phi_{r_{\mathrm{abs}}}(s + c|V| + j + 1) = p_0 + c\cdot d + \mathrm{wordRelPot}(V, r, j + 1)$ inside an interval of width $\mathrm{wordPotSpan}(V, r) + (R - 1)|d| + 1$.
- `seeded_replay_zero_drift_repeat_bound`, `seeded_replay_unit_drift_at_most_one_s_landing`, and `canonical_zero_drift_forbids_long_repeat` follow immediately with zero unproven `Prop` hypotheses and `0 flagged / 0 unknown` under `harness_lean.py --vacuity-row E-798`.

## 3. Explicit `Δ = 2` Coherent Greedy Cascade (`E-799`, `PROVED-PAPER`)

### 3.1 Construction

Set $h_k = 2k + 2$ ($k \ge 1$) and $B_0 = (AS)^{K_0}$ ($K_0 \ge 6$), $\mathrm{bank}_0 = K_0$. For each level $k \ge 1$ with target source height $r_{\mathrm{top}} = h_k - 1 = 2k + 1$:
1. Define the `(SA)` buffer lower bound:
   $$p_{\mathrm{lo}}(1) = 0, \qquad p_{\mathrm{lo}}(k) = \left\lfloor \frac{3\,\mathrm{bank}_{k-1}}{2(2 h_{k-1} - 3)} \right\rfloor + 2 \quad (k \ge 2).$$
2. Since $\Delta\Phi_{r_{\mathrm{top}}}(SA) = -(2 h_k - 1)$ and $\Delta\Phi_{r_{\mathrm{top}}}(AS) = -(2 h_k - 3)$ are consecutive odd integers, $\gcd(2h_k - 1, 2h_k - 3) = 1$, and moreover $-(2h_k - 1) \not\equiv -(2h_k - 3) \pmod 3$. Indeed, as $p$ ranges over $\{p_{\mathrm{lo}}, p_{\mathrm{lo}} + 1, p_{\mathrm{lo}} + 2\}$ and $q \in \{0, 1, 2\}$, at least one of $2h_k - 1$ or $2h_k - 3$ is coprime to $3$, so there ALWAYS exists a pair $(q_k, p_k) \in \{0, 1, 2\} \times \{p_{\mathrm{lo}}, p_{\mathrm{lo}}+1, p_{\mathrm{lo}}+2\}$ such that
   $$\mathrm{rem}_k := 1 - p_k \Delta\Phi_{r_{\mathrm{top}}}(SA) - q_k \Delta\Phi_{r_{\mathrm{top}}}(AS) - \Delta\Phi_{r_{\mathrm{top}}}(B_{k-1}) - \Delta\Phi_{r_{\mathrm{top}}}(A^{h_k} S^{h_k}) \equiv 0 \pmod 3, \quad \mathrm{rem}_k \ge 3.$$
   Set $a_k = \mathrm{rem}_k / 3$.
3. **Critical ordering (resolving the `q > 0` height-0 collision)**: Define
   $$V_k := (AS)^{q_k} \mathbin{+\!\!+} (SA)^{p_k} \mathbin{+\!\!+} B_{k-1} \mathbin{+\!\!+} A^{h_k} (AS)^{a_k} S^{h_k}.$$
   Then $\mathrm{mass}(V_k) = 0$ and $\Delta\Phi_{h_k - 1}(V_k) = +1$ identically.
4. Let $[c_{\min}, c_{\max}]$ be the range of height-$(h_k - 1)$ rejected `A`-candidate potentials $\Phi_{h_k - 1}$ within one copy of $V_k$, let $P_{\mathrm{bank}} = -\frac{(h_k - 1)(h_k - 2)}{2}$ be the height-$(h_k - 1)$ entry potential of $A^{h_k - 1}$, and let $d_0 = \Delta\Phi_{h_k - 1}(A^{h_k - 1} A S^{h_k})$. Set
   $$\mathrm{lift}_k = \max\!\left(1, \left\lceil \frac{P_{\mathrm{bank}} - d_0 - c_{\min}}{3} \right\rceil + 1\right), \qquad \mathrm{bank}_k = d_0 + 3\,\mathrm{lift}_k - P_{\mathrm{bank}} + c_{\max},$$
   $$V_{0,k} := A^{h_k - 1} (SA)^{\mathrm{bank}_k} A (AS)^{\mathrm{lift}_k} S^{h_k}, \qquad B_k := V_{0,k} \mathbin{+\!\!+} V_k^{R_k} \quad (1 \le R_k \le \mathrm{bank}_k).$$

### 3.2 Proof of `E-759 (I)/(II) = (0, 0)` (Corridor Separation at Every Height $r \in [-1, 2k + 3]$)

By induction on $k$, assume $B_{k-1}$ lies in height band $[-1, h_{k-1} + 1] = [-1, 2k + 1]$ and satisfies `E-759 = (0, 0)`. Notice the exact height alignment at `Δ = 2`:
- $h_{k-1} + 1 = 2k + 1 = h_k - 1$! Thus the **maximum height** of $B_{k-1}$ touches $h_k - 1$, where $B_{k-1}$ only executes `(AS)` loops at $h_{k-1}$ (which visit height $h_k - 1$ ONLY via `A`-steps and NEVER via `S`-landings!). So $B_{k-1}$ has **zero `S`-landings** at height $h_k - 1$ (and zero visits to $h_k$ or $h_k + 1$), preserving `E-798`'s `wordSLandings ≤ 1` invariant!
- **Height $r = 0$ (why `(AS)^{q_k}` MUST precede `(SA)^{p_k}`)**:
  - Inside a single copy of $V_k$ starting at relative potential $\Phi_0 = \phi_0$, `(AS)^{q_k}` executes steps $0 \to 1 \to 0$ with $\Delta\Phi_0(AS) = +1$, placing its `S`-landings at $\Phi_0 \in \{\phi_0 + 1, \dots, \phi_0 + q_k\}$ (strictly positive offset!).
  - Next, `(SA)^{p_k}` executes steps $0 \to -1 \to 0$ with $\Delta\Phi_0(SA) = -1$, placing its height-$0$ `A`-outputs at $\phi_0 + q_k - 1, \dots, \phi_0 + q_k - p_k$ and height-$(-1)$ `S`-landings at $\phi_0 + q_k - 1, \dots, \phi_0 + q_k - p_k$ — all strictly decreasing **after** `(AS)^{q_k}` has already finished!
  - Conversely, if `(SA)^{p_k}` preceded `(AS)^{q_k}`, then `(AS)^{q_k}`'s `S`-landings would step back UP into the already-visited height-$0$ outputs of `(SA)^{p_k}`, causing immediate Type-I collisions (verified in our negative control: `q = 2` yields `8` Type-I collisions).
  - Across consecutive copies of $V_k$, $\Delta\Phi_0(V_k) = \Delta\Phi_{h_k - 1}(V_k) + (h_k - 1)|V_k| \gg \max \Phi_0(V_k) - \min \Phi_0(V_k)$, so each copy's height-$0$ window is shifted strictly above all prior copies' height-$0$ visits and rejected candidates!
- **Height $r = -1$**: Every copy of $V_k$ shifts $\Phi_{-1}$ upward by $\Delta\Phi_{-1}(V_k) = \Delta\Phi_{h_k - 1}(V_k) + h_k|V_k| > 0$, strictly exceeding the internal dip of $B_{k-1}$ plus `(SA)^{p_k}`, so height-$(-1)$ `S`-landings of copy $c$ strictly exceed all height-$(-1)$ outputs and rejected candidates of copies $< c$ and of $V_{0,k}$.
- **Heights $r \in [1, h_{k-1}]$**: Identical to `E-789`: within each copy of $V_k$, the buffer `(SA)^{p_k}` with $p_k \ge p_{\mathrm{lo}}(k)$ shifts $\Phi_{h_{k-1}-1}$ downward enough that $V_{0,k-1}$'s bank valley lies below the previous copy's terminal height, while for every $r \le h_{k-1}$, $\Delta\Phi_r(V_k) = 1 + (h_k - 1 - r)|V_k| \ge 1 + |V_k|$ strictly dominates the internal span of $B_{k-1}$ at height $r$, strictly separating successive copies of $B_{k-1}$ from each other and from $V_{0,k}$.
- **Heights $r = h_k - 1, h_k, h_k + 1$**:
  - At $r = h_k - 1$: $V_{0,k}$ builds the bank corridor $[P_{\mathrm{bank}} - \mathrm{bank}_k, P_{\mathrm{bank}}]$ via `(SA)^{\mathrm{bank}_k}` and lifts the end of $V_{0,k}$ to $\Phi_{h_k - 1}(V_{0,k}) = P_{\mathrm{bank}} - \mathrm{bank}_k + d_0 + 3\,\mathrm{lift}_k = P_{\mathrm{bank}} - c_{\max}$. Each copy $c \in \{0, \dots, R_k - 1\}$ of $V_k$ executes $A^{h_k}(AS)^{a_k}S^{h_k}$, whose `A`-candidates at height $h_k - 1$ lie in $[\Phi_{h_k - 1}(V_{0,k}) + c + c_{\min}, \Phi_{h_k - 1}(V_{0,k}) + c + c_{\max}] \subseteq [P_{\mathrm{bank}} - \mathrm{bank}_k, P_{\mathrm{bank}}]$ — EVERY candidate is supplied by $V_{0,k}$'s bank! The sole `S`-landing of $V_k$ at height $h_k - 1$ (on the first `S` of $S^{h_k}$) occurs strictly ABOVE $P_{\mathrm{bank}}$ (by choice of $\mathrm{lift}_k$) and increases by $+1$ per copy, so no Type-I or Type-II collision can occur. Note also that $B_{k-1}$'s top height $h_{k-1} + 1 = h_k - 1$ only visits $h_k - 1$ via `A`-steps (with $\Phi_{h_k - 1}$ strictly BELOW $P_{\mathrm{bank}} - \mathrm{bank}_k$ because $B_{k-1}$ sits before $A^{h_k}(AS)^{a_k}$), so $B_{k-1}$'s visits never collide with any height-$(h_k - 1)$ `S`-landing!
  - At $r = h_k$: $\Delta\Phi_{h_k}(V_k) = 1 - |V_k| < 0$, and every `S`-landing of `(AS)^{a_k}` strictly advances by $+3$ in $-\Phi_{h_k}$ inside each copy and jumps strictly further downward in $\Phi_{h_k}$ between copies, giving zero Type-I/Type-II collisions.
  - At $r = h_k + 1$: only visited by `A`-steps (zero `S`-landings).

### 3.3 Exact Asymptotic Growth Rate $\sqrt{7/3} \approx 1.527525$

Inside $V_k$, as $R_j \to \infty$ (so the bank/lift overhead $V_{0,j}$ is amortized to $O(1/R_j)$ of $B_j$, and $p_k / |B_{k-1}| = O(1/R_{k-1}) \to 0$), the dominant term of $3 a_k = \mathrm{rem}_k$ is $-\Delta\Phi_{h_k - 1}(B_{k-1})$. Every `(AS)` pair at height $h_{k - m} = h_k - 2m$ ($m \ge 1$) has length $2$ and area $2 h_{k-m} + 1$, so it contributes
$$-\Delta\Phi_{h_k - 1}(AS\text{ at }h_k - 2m) = 2(h_k - 1) - (2(h_k - 2m) + 1) = 4m - 3$$
to $3 a_k$. Denoting by $A_k$ the amortized per-free-addition density of `(AS)` pairs at height $h_k = 2k + 2$, we obtain the exact linear recurrence
$$3 A_k = \sum_{m=1}^{k} (4m - 3) A_{k - m} \qquad (k \ge 1).$$
Its characteristic equation in $x = \mu^{-1}$ is
$$3 = \sum_{m=1}^{\infty} (4m - 3) x^m = \frac{x}{1 - x} + \frac{4 x^2}{(1 - x)^2} = \frac{x + 3 x^2}{(1 - x)^2}.$$
Multiplying by $(1 - x)^2$ cancels $3 x^2$ identically:
$$3 - 6x + 3x^2 = x + 3x^2 \iff 7x = 3 \iff x = \frac{3}{7}, \qquad \mu = \frac{7}{3}.$$
Since each stage increases the strip height by $\Delta = 2$, the per-height exponential growth base is exactly
$$\rho_{\Delta = 2} = \sqrt{\frac{7}{3}} \approx 1.5275252316519468.$$
In particular, for every $k \ge 1$ and every $\varepsilon > 0$, choosing $R_1, \dots, R_k$ sufficiently large produces a coherent finite-state greedy word $B_k$ in height band $[-1, 2k + 3]$ (width $H = 2k + 4$) with `E-759 = (0, 0)` and $A(B_k) / F(B_k) = \Omega((7/3)^{H/2})$.

## 4. Exact Reproducible Audit Results

Command: `python3 docs/data/depth_general_20261128/delta2_coherent_cascade_audit.py`
- `K_0 = 6, k = 3` (`R = [6, 6, 6]`, band `[-1, 9]`): `len = 198,018`, `A/F = 3.0572`, `q_3 = 0`, `E-759 = (0, 0)`.
- `K_0 = 9, k = 3` (`R = [6, 6, 6]`, band `[-1, 9]`): `len = 257,738`, `A/F = 3.0668`, `q_3 = 1`, `E-759 = (0, 0)`.
- `K_0 = 12, k = 3` (`R = [6, 6, 6]`, band `[-1, 9]`): `len = 322,770`, `A/F = 3.0694`, `q_3 = 0`, `E-759 = (0, 0)`.
- All 3 mod-3 residue classes `q_3 ∈ {0, 1, 2}` verified `E-759 = (0, 0)`.
- Negative control `(SA)^p ++ (AS)^q` at `q = 2`: `8` Type-I collisions (confirms ordering necessity).
- Exact 8-filter coherent finite-State greedy replay (`E-782`) on `B_1` (`len = 394`): `True`.
- High-`R` `k = 3` (`R = [12, 12, 12]`, band `[-1, 9]`): `len = 880,822`, `A/F = 4.3679`, `q_3 = 1`, `E-759 = (0, 0)`.
- Depth `k = 4` (`R = [5, 5, 5, 5]`, `h_4 = 10`, band `[-1, 11]`): `len = 2,618,760`, `A/F = 2.9016`, `q_4 = 0`, `E-759 = (0, 0)`.

## 5. Limitations & Open Problem

- `E-798` + `E-799` show that `Δ = 2` (base $\sqrt{7/3} \approx 1.527525$) is optimal among unit-drift coherent recursive towers, narrowing $\rho_{\mathrm{greedy}} \in [\sqrt{7/3}, 5/3]$. Whether non-periodic or large-drift `E-759 = (0, 0)` words can exceed $\sqrt{7/3}$ or whether `E-759` forces $\rho_{\mathrm{greedy}} < 5/3$ remains open.
- Neither `E-798` nor `E-799` constructs a canonical clock-0 prehistory for $B_k$, nor proves `C1`, `Q`, `H`, `SL`, surjectivity, or `E-001`/`E-067`/`E-070`/`E-179`.
