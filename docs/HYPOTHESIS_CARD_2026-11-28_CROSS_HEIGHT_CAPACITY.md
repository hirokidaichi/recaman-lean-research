# Hypothesis Card — `H-20261128-01` (Exact Actual-`EndN` Exponential Base in `[5/3, 1.8067]` and Coherent Greedy Exponential Cascade)

- **ID**: `H-20261128-01`
- **Date**: 2026-11-28 (drafted at end of `R-20261127-01`; unexecuted)
- **Track**: Depth-general actual-`EndN` height capacity & greedy S-novelty separation (next frontier question after `E-785` and `E-786`)
- **Status**: **`CONJECTURED`** (unexecuted; card creation is not research progress)

## 1. Current Narrowed Window After `R-20261127-01`

On actual `EndN` confined to a height strip $Fw \in [m, m + H + 1]$ after any `BlockWord ++ A^a` prefix:
- **Upper bound (`E-785 PROVED-LEAN`)**: Uniform dyadic capacity at $q = 1/2$ (`dyadicAdditions ≤ 3 * dyadicFree`, $A_{m+h} \le 3 \cdot 2^h \cdot F$), with 3-spacing cone threshold $\kappa_{\mathrm{new}} \approx 0.55350$, spectral base $\rho_{\mathrm{new}} \approx 1.80669 < 2 < 2.20557$ (breaking `E-775`).
- **Lower bound (`E-786 PROVED-PAPER`)**: Recursive zero-shift cascade $B_H$ achieves $A(B_H)/(F + O_c) \ge (12/25 - \varepsilon)(5/3)^H$ for all $H \ge 2$ and all arbitrary prehistories $U$, refuting every polynomial-in-$H$ bound and every geometric capacity with $q > 3/5 = 0.6$.

Thus the true raw actual-`EndN` exponential base $\rho_{\mathrm{actual}}$ is already pinned to **`[5/3, 1.8067]`** (`[1.6667, 1.8067]`), and $\kappa_{\mathrm{actual}} \in [0.5535, 0.6000]$.

## 2. Two Concrete Bounded Research Questions

1. **Coherent greedy exponential test (Track A)**: Because `E-786`'s $V_H$ has integer mean height $H - 1$, literal $V_H^R$ fails `E-759 (I)` S-novelty. Does replacing $\Delta\Phi_{H-1}(V_H) = 0$ by a unit-shift block $\Delta\Phi_{H-1}(V_H) = +1$ (as in `E-784`) lift `E-786` to a **coherent finite-State greedy** (`E-759 = (0,0)`, passing all 8 filters of `E-782`) exponential family $\Omega(c^H)$, OR does S-freshness obstruct multi-level bank reuse and force sub-exponential growth?
2. **Exact raw actual-`EndN` base & Lean formalization (Track B)**:
   - Formalize `E-786` (`Ω((5/3)^H)` exponential lower bound on actual `EndN`) in Lean 4;
   - Determine whether combining `E-786`'s `D_{H+1} = 2 A` recursion with self-supplied short cycles (like `AAAASASSSS` achieving $E_3 = F_0 + F_1$, capturing the $+2 A_{r-1}$ term of `E-785`) pushes the actual-`EndN` lower bound strictly above $5/3$ toward $1.8067$, or whether a coupled 2-height slot injection lowers the upper bound strictly below $1.8067$.

## 3. Acceptance Test & Stopping Condition

- **Track A acceptance**: Either an explicit all-$H$ coherent (`E-759 = (0,0)`) family with $A/(F + O_c) \ge c^H$ ($c > 1$), OR a proved S-novelty obstruction separating coherent greedy height growth from raw actual `EndN`.
- **Track B acceptance**: Clean Lean 4 proof of `E-786` (0 vacuity flags), or strict narrowing of `[5/3, 1.8067]` from either side.
- **Non-claims**: Unexecuted card (`CONJECTURED`). Neither track alone proves `C1`, `E-001`, `E-067`, or `E-070`.
