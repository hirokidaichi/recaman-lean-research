# Research Note — Exponential-in-`H` Recursive Cascade on Actual `EndN` (`E-786`)

- **Date**: 2026-11-27
- **Hypothesis Card**: [`docs/HYPOTHESIS_CARD_2026-11-27_EXPONENTIAL_CASCADE.md`](HYPOTHESIS_CARD_2026-11-27_EXPONENTIAL_CASCADE.md)
- **Status**: **`E-786 PROVED-PAPER`** (human review pending; Lean formalization deferred)
- **Reproducible Verification Script**: [`docs/data/depth_general_20261127/exponential_cascade_audit.py`](data/depth_general_20261127/exponential_cascade_audit.py)

## 1. Main Theorem

**Theorem (`E-786 PROVED-PAPER`)**: For every integer $H \ge 2$ and every $\varepsilon > 0$, there exists an explicit balanced word $B_H$ (`Fw(B_H) = 0`) confined to relative height strip $[0, H + 1]$ such that for **every** arbitrary prehistory $U$ (origin kept at `0`, retaining all old and internal co-suppliers), on actual `EndN`:
$$\frac{A(B_H)}{F_{\mathrm{orig}}(B_H) + O_c(B_H)} \;\ge\; \left(\frac{12}{25} - \varepsilon\right) \cdot \left(\frac{5}{3}\right)^H.$$

**Corollary 1 (Refutation of polynomial-in-$H$ actual-`EndN` bounds)**: No function $\psi(H) = o((5/3)^H)$ — in particular no polynomial in $H$ — bounds $A / (F + O_c)$ on actual `EndN` over bounded height strip $[0, H + 1]$.

**Corollary 2 (Narrowing the actual-`EndN` exponential window with `E-785`)**: Combining `E-785` (`PROVED-LEAN`, $q = 1/2$ holds with $C = 3$, 3-spacing cone $\kappa_{\mathrm{new}} \approx 0.5535, \rho_{\mathrm{new}} \approx 1.8067$) and `E-786` (`PROVED-PAPER`, $q > 3/5$ fails, growth $\ge (5/3)^H$), the true exponential base $\rho_{\mathrm{actual}} := \limsup_{H \to \infty} (\sup_{Fw \in [0, H]} A/F)^{1/H}$ on actual `EndN` satisfies
$$\frac{5}{3} \approx 1.66667 \;\le\; \rho_{\mathrm{actual}} \;\le\; 1.80669 < 2 < 2.20557 = \rho_{\text{E-674/E-775}},$$
and the critical geometric weight $\kappa_{\mathrm{actual}}$ lies in $[0.5535, 0.6000]$.

## 2. Exact Proof

Recall $\Phi_r(t) := S(t) - r t$, where $S(t) = \sum_{j=1}^{t} Fw(j)$. For any balanced word $W$ ($Fw(W) = 0$) placed at cut $c$ (with $Fw(c) = h_0$), relative quantities $|W|, A(W) = |W|/2, S_{\mathrm{rel}}(W)$, and relative $\Delta\Phi_r(W) = S_{\mathrm{rel}}(W) - r |W|$ depend only on $W$. Moreover, every internal `Win` supply (`u ≥ c` inside $W$) remains an internal `Win` supply regardless of what precedes $W$ (`InternalSupplied` is invariant under arbitrary prepending, so $F_{\mathrm{orig}}(W) + O_c(W) = A(W) - L_{\mathrm{int}}(W)$ depends only on $W$ and never increases when $W$ is embedded inside a larger word!).

### Inductive Construction of $B_H$ ($H \ge 2$)

Set $B_0 := \mathrm{AS}$ ($|B_0| = 2, A(B_0) = 1, F_{\mathrm{ub}}(B_0) = 1, S(B_0) = 1, Fw \in [0, 1]$). For $H = 2, 3, 4, \dots$, suppose we have a balanced word $B_{H-1}$ confined to $[0, H]$ with $D_H := (H - 1)|B_{H-1}| - S(B_{H-1}) > 0$ and internal-free upper bound $F_{\mathrm{ub}}(B_{H-1}) := A(B_{H-1}) - L_{\mathrm{int}}(B_{H-1}) \ge 1$.

1. **Mod-3 parity adjuster**: Set $c_H := 2$ if $H \equiv 1 \pmod 3$, and $c_H := 0$ otherwise. Then
   $$c_H (2H - 3) + H^2 - 2H \equiv 0 \pmod 3$$
   for every integer $H \ge 2$:
   - $H \equiv 0 \pmod 3$: $0 + 0 \equiv 0 \pmod 3$.
   - $H \equiv 2 \pmod 3$: $0 + 4 - 4 \equiv 0 \pmod 3$.
   - $H \equiv 1 \pmod 3$: $2(2 - 3) + 1 - 2 = -3 \equiv 0 \pmod 3$.
2. **Zero-shift block $V_H$**: For any integer $m \ge 1$, set $M := 3m$ and
   $$a_H := \frac{3m \cdot D_H + c_H(2H - 3) + H^2 - 2H}{3} \in \mathbb{N}_{> 0}.$$
   Define
   $$V_H := (\mathrm{AS})^{c_H} \cdot B_{H-1}^{3m} \cdot A^H \cdot (\mathrm{AS})^{a_H} \cdot S^H.$$
   Then:
   - $Fw(V_H) = 0$ and $Fw \in [0, H + 1]$ throughout $V_H$ (since $B_{H-1}$ stays in $[0, H]$ and $A^H (\mathrm{AS})^{a_H} S^H$ stays in $[0, H + 1]$).
   - $\Delta\Phi_{H-1}(V_H) = -c_H(2H - 3) - 3m D_H - (H^2 - 2H) + 3 a_H = 0$.
   - **Exact next-level drop identity**: Because $\Delta\Phi_{H-1}(V_H) = S(V_H) - (H - 1)|V_H| = 0$, we have $S(V_H) = (H - 1)|V_H|$, and therefore **identically**:
     $$D_{H+1}(V_H) := H |V_H| - S(V_H) = |V_H| = 2 A(V_H).$$
3. **Explicit bank block $V_0^{(H)}$**: Inside $V_H$ (starting from relative $\Phi_{H-1} = 0$), the $a_H$ targets of $(\mathrm{AS})^{a_H}$ at height $H$ take $\Phi_{H-1}$ values in the arithmetic progression $\phi_{\mathrm{start}} + 3j$ ($0 \le j < a_H$), where
   $$\phi_{\mathrm{start}} = -c_H(2H - 3) - 3m D_H + \frac{H(H+1)}{2} - H(H-1), \qquad \phi_{\mathrm{end}} = \phi_{\mathrm{start}} + 3(a_H - 1).$$
   Define
   $$V_0^{(H)} := A^{H-1} \cdot (\mathrm{SA})^{\mathrm{bank}} \cdot A \cdot (\mathrm{AS})^{\mathrm{lift}} \cdot S^H.$$
   Because $H \ge 2$, $(\mathrm{SA})^{\mathrm{bank}}$ oscillates between $H - 1$ and $H - 2 \ge 0$, so $V_0^{(H)}$ stays strictly inside $[0, H + 1]$ and ends at $0$. Each $(\mathrm{SA})$ drops $\Phi_{H-1}$ by $-1$, so the peaks at $Fw = H - 1$ cover every integer in $[\phi_{\mathrm{end}}(V_0^{(H)}) + \ell_0, \phi_{\mathrm{end}}(V_0^{(H)}) + \ell_0 + \mathrm{bank}]$, where $\ell_0 := \frac{H(H-1)}{2} - 1 - 3\,\mathrm{lift}$. Choosing
   $$\mathrm{lift} := \max\!\left(0, \left\lceil \frac{\frac{H(H-1)}{2} - 1 - \phi_{\mathrm{start}}}{3} \right\rceil\right), \qquad \mathrm{bank} := \max\!\left(0, \phi_{\mathrm{end}} - \left(\frac{H(H-1)}{2} - 1 - 3\,\mathrm{lift}\right)\right)$$
   guarantees that **every** target $\phi_{\mathrm{start}} + 3j$ ($0 \le j < a_H$) across **all** $R$ copies of $V_H$ in $B_H := V_0^{(H)} V_H^R$ has an explicit internal `Win` supplier inside $V_0^{(H)}$ (since $\Delta\Phi_{H-1}(V_H) = 0$).
4. **Inductive lower bound on $(A/F_{\mathrm{ub}}, D_{H+1}/F_{\mathrm{ub}})$**:
   For $B_H = V_0^{(H)} V_H^R$:
   $$A(B_H) = A(V_0^{(H)}) + R \big(c_H + 3m A(B_{H-1}) + H + a_H\big),$$
   $$F_{\mathrm{ub}}(B_H) \le A(V_0^{(H)}) + R \big(c_H + 3m F_{\mathrm{ub}}(B_{H-1}) + H\big),$$
   $$D_{H+1}(B_H) = D_{H+1}(V_0^{(H)}) + R \cdot 2 A(V_H).$$
   Letting $R \to \infty$ kills the fixed $V_0^{(H)}$ terms, and letting $m \to \infty$ kills the fixed $c_H, H$ terms:
   $$\lim_{m \to \infty} \lim_{R \to \infty} \frac{A(B_H)}{F_{\mathrm{ub}}(B_H)} = \frac{3 A(B_{H-1}) + D_H}{3 F_{\mathrm{ub}}(B_{H-1})} = \frac{A(B_{H-1})}{F_{\mathrm{ub}}(B_{H-1})} + \frac{D_H}{3 F_{\mathrm{ub}}(B_{H-1})},$$
   $$\lim_{m \to \infty} \lim_{R \to \infty} \frac{D_{H+1}(B_H)}{A(B_H)} = 2.$$
   - At $H = 2$ (from $B_0 = \mathrm{AS}$, where $A = 1, F_{\mathrm{ub}} = 1, D_2 = 1 \cdot 2 - 1 = 1$):
     $A(B_2)/F_{\mathrm{ub}}(B_2) \to 1 + 1/3 = 4/3 = \frac{12}{25} \cdot (5/3)^2$, and $D_3(B_2)/A(B_2) \to 2$.
   - For every $H \ge 3$, since $D_H / A(B_{H-1}) \to 2$, the multiplier is
     $$\frac{3 A(B_{H-1}) + 2 A(B_{H-1})}{3 A(B_{H-1})} = \frac{5}{3},$$
     yielding $A(B_H)/F_{\mathrm{ub}}(B_H) \to \frac{12}{25} \cdot (5/3)^H$ for every $H \ge 2$. Choosing $(m_k, R_k)$ sufficiently large at each level $k = 2..H$ achieves $(12/25 - \varepsilon)(5/3)^H$. $\square$

## 3. Reproducible Computational Verification (`COMPUTED`)

Running `python3 docs/data/depth_general_20261127/exponential_cascade_audit.py` (`0.12s` CPU) confirms:
- Literal actual-`EndN` execution of $B_0 \to B_2 \to B_3 \to B_4$, including $c_4 = 2$ at $H = 4$ with `8115 / 8115` (`100%`) internal `Win` supply of all height-$4$ targets in $V_4^3$.
- Prehistory invariance across 6 arbitrary prehistories $U \in \{\varepsilon, A, S^3, SAAA, SSAAASASAA, ASASSSAAA\}$ on $B_3$ ($L_{\mathrm{int}} \ge 2887$, $F + O_c \le 3202$).
- Exact integer $(m, R)$ schedules for $H = 2..12$ hitting $\ge 99.91\%$ of $(12/25)(5/3)^H$ (`A/F_ub = 220.3022` vs target `220.5090` at $H = 12$).

## 4. Boundaries & Non-Claims

- $V_H$ has integer mean height $S(V_H)/|V_H| = H - 1$, so literal repeated $V_H^R$ fails `E-759 (I)` greedy coherence (lifting `E-786` to coherent greedy `E-759 = (0,0)` via unit-shift blocks as in `E-784` is left open).
- Because $D_{\mathrm{depth}} = 0$ and $F$ grows with $R$, `E-786` is **not** a counterexample to `C1`, `E-001`, `E-067`, or `E-070`.
