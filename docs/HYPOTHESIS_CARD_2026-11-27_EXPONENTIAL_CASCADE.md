# Hypothesis Card — `H-20261127-04` (Exponential-in-`H` Recursive Cascade on Actual `EndN`)

- **ID**: `H-20261127-04`
- **Date**: 2026-11-27
- **Parent Cycle**: `R-20261127-01`
- **Track**: Depth-general actual-`EndN` height-growth lower bound (closing the polynomial-vs-exponential gap between `E-783` `Ω(H)` and `E-785` `O(2^H)` / `O(1.8067^H)`)
- **Status**: **`PROVED-LEAN`** (`E-786`, `Recaman/ExponentialHeightCascade.lean`, 0 vacuity flags, 0 unknowns; plus Python literal actual-`EndN` & schedule verification)

## 1. Exact Mathematical Claim

For every height $H \ge 2$, every $\varepsilon > 0$, and every arbitrary prehistory $U$ (origin kept at `0`, retaining all old and internal co-suppliers), there exists an explicit balanced word $B_H$ (`Fw(B_H) = 0`) confined to relative height strip $Fw \in [0, H + 1]$ such that on **actual `EndN`** (`Win` supply):
$$\frac{A(B_H)}{F(B_H) + O_c(B_H)} \;\ge\; \left(\frac{12}{25} - \varepsilon\right) \cdot \left(\frac{5}{3}\right)^H.$$
Equivalently, any unweighted fixed-height capacity $A \le \psi(H) \cdot (F + O_c)$ on actual `EndN` over $Fw \in [m, m + H + 1]$ must grow exponentially: $\psi(H) = \Omega((5/3)^H)$, refuting every polynomial-in-$H$ bound on actual `EndN`. Moreover, for every geometric weight $q > 3/5$, no uniform weighted capacity $\sum q^h A_h \le C \sum q^h F_h$ holds on actual `EndN`.

Together with `E-785` (`PROVED-LEAN`, $q = 1/2$ holds with $C = 3$ and 3-spacing cone $\rho \approx 1.8067 < 2$), this pins the exact exponential growth base of actual `EndN` inside **`[5/3, 1.8067]`** (`[1.6667, 1.8067]`) and the geometric weight threshold $\kappa_{\mathrm{actual}}$ inside **`[0.5535, 0.6000]`**.

## 2. Mechanism & Proof Chain

1. Start from $B_0 = \mathrm{AS}$ ($|B_0| = 2, A = 1, F = 1, S = 1$, $Fw \in [0, 1]$).
2. Given balanced $B_{H-1}$ confined to $[0, H]$ with $D_H := (H - 1)|B_{H-1}| - S(B_{H-1}) > 0$, set $c_H := 2$ if $H \equiv 1 \pmod 3$ else $0$, choose $M = 3m$, and set
   $$a_H := \frac{3m \cdot D_H + c_H (2H - 3) + H^2 - 2H}{3} \in \mathbb{N}$$
   (exact divisibility by $3$ holds for every $H \ge 2$ and every $D_H \in \mathbb{Z}$).
3. Define the zero-shift block $V_H := (\mathrm{AS})^{c_H} B_{H-1}^{3m} A^H (\mathrm{AS})^{a_H} S^H$. Then $Fw(V_H) = 0$, $Fw \in [0, H+1]$, $\Delta\Phi_{H-1}(V_H) = 0$ (so $S(V_H) = (H-1)|V_H|$), and therefore **identically**:
   $$D_{H+1}(V_H) := H |V_H| - S(V_H) = |V_H| = 2 A(V_H).$$
4. Prepend the explicit height-$(H-1)$ bank $V_0^{(H)} := A^{H-1} (\mathrm{SA})^{\mathrm{bank}} A (\mathrm{AS})^{\mathrm{lift}} S^H$ (confined to $[0, H+1]$), whose visits to $Fw = H-1$ cover every integer in the $\Phi_{H-1}$-span of all $a_H$ targets in $V_H$. Set $B_H := V_0^{(H)} V_H^R$.
5. All $R a_H$ additions at height $H$ in $V_H^R$ are internally supplied by $V_0^{(H)}$, and every internal `Win` inside each copy of $B_{H-1}$ remains valid under prepending arbitrary history, so $F(B_H) + O_c(B_H) \le A(V_0^{(H)}) + R(3m F_{\mathrm{ub}}(B_{H-1}) + c_H + H)$. Letting $m \to \infty$ then $R \to \infty$ multiplies $A / F_{\mathrm{ub}}$ by $(3m + 2m)/(3m) = 5/3$ at every step $H \ge 3$ (and from $1$ to $4/3$ at $H = 2$), giving $(12/25)(5/3)^H$.

## 3. Evidence & Non-Claims

- **Verification (`COMPUTED`)**: [`docs/data/depth_general_20261127/exponential_cascade_audit.py`](data/depth_general_20261127/exponential_cascade_audit.py) (0.12s CPU) verifies literal actual-`EndN` execution for $B_0 \to B_2 \to B_3 \to B_4$ (including $c_4 = 2$ and 100% internal `Win` supply `8115/8115` at $H = 4$), prehistory invariance across 6 arbitrary $U$, and exact integer $(m, R)$ schedules for $H = 2..12$ hitting $\ge 99.9\%$ of $(12/25)(5/3)^H$ (`220.30` at $H = 12$).
- **Non-claims**: Raw sign word construction (`E-759` greedy coherence and canonical clock-0 reachability are NOT claimed for the literal $B_H$ since $V_H$ has integer mean height $H - 1$). Not a `C1`, `E-001`, `E-067`, or `E-070` counterexample ($D_{\mathrm{depth}} = 0$, $F$ grows with $R$).
