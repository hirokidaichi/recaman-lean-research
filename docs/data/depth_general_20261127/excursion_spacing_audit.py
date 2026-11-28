#!/usr/bin/env python3
"""
Reproducible discovery, holdout, sharpness, and cone-separation audit for
H-20261127-03 / E-785 (Recaman/SupplyExcursionSpacing.lean).

Verifies:
  1. Discovery: exhaustive check over all binary words of length 1..14 (32,766 words)
     with n = 0.
  2. Holdout: 10,000 random BlockWord ++ A^a ++ tail instances (exact Lean BlockWord
     grammar), plus E-783 multi-block reuse words at H = 3k (k = 1..6).
  3. Sharpness witnesses at h = 1, 2, 3, and arbitrary H = 3k (3*E_H / (W + 2*A) -> 1).
  4. Exact spectral separation between the E-674/E-775 relaxed cone (rho ~ 2.2056,
     fails at q = 1/2) and the new E-785 3-spacing cone (rho ~ 1.8068 < 2, passes at
     q = 1/2 with exact factor C = 3).
  5. Negative controls: dropping +2*A_{r-1} fails on SAAASS; dropping BlockWord fails
     on non-BlockWord prefixes.
"""

from __future__ import annotations
import math
import random
import time


def eval_endN(w: str):
    L = len(w)
    fw = [0] * (L + 1)
    S = [0] * (L + 1)
    for i, ch in enumerate(w):
        fw[i + 1] = fw[i] + (1 if ch == "A" else -1)
        S[i + 1] = S[i] + fw[i + 1]
    seen = {(0, 0)}
    endN = [False] * L
    for t in range(L):
        if w[t] == "A":
            h = fw[t]
            if (h - 1, S[t] - (h - 1) * t) in seen:
                endN[t] = True
        seen.add((fw[t + 1], S[t + 1] - fw[t + 1] * (t + 1)))
    return fw, S, endN


def check_interval(bw: str, a_run: int, tail: str):
    full = bw + "A" * a_run + tail
    n = len(bw) + a_run
    L = len(full)
    fw, _, endN = eval_endN(full)
    lo = min(fw[n:])
    hi = max(fw[n:])
    v_budget = 0
    v_dyadic = 0
    v_e4 = 0
    v_exp2 = 0
    for r in range(lo - 1, hi + 1):
        E = sum(1 for t in range(n, L) if fw[t] == r + 1 and endN[t])
        W = sum(2 * (r - fw[t]) - 1 for t in range(n, L) if full[t] == "A" and fw[t] < r)
        Arm1 = sum(1 for t in range(n, L) if full[t] == "A" and fw[t] == r - 1)
        if 3 * E > W + 2 * Arm1:
            v_budget += 1
    m = lo
    H = hi - m
    A_by = [0] * (H + 1)
    F_by = [0] * (H + 1)
    E_by = [0] * (H + 1)
    for t in range(n, L):
        if full[t] == "A":
            idx = fw[t] - m
            A_by[idx] += 1
            if endN[t]:
                E_by[idx] += 1
            else:
                F_by[idx] += 1
    F_tot = sum(F_by)
    if H >= 4 and 3 * E_by[4] > 8 * F_tot:
        v_e4 += 1
    dy_A = 0
    dy_F = 0
    for h in range(H + 1):
        dy_A = 2 * dy_A + A_by[h]
        dy_F = 2 * dy_F + F_by[h]
        if dy_A > 3 * dy_F:
            v_dyadic += 1
        if A_by[h] > 3 * (1 << h) * F_tot:
            v_exp2 += 1
    return v_budget, v_dyadic, v_e4, v_exp2


def staged_block(stages):
    out = []
    for a in stages:
        out.append("AS" * (a - 1) + "A")
    out.append("S" * len(stages))
    return "".join(out)


def solve_root(fn, lo, hi):
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if fn(mid) * fn(lo) <= 0:
            hi = mid
        else:
            lo = mid
    return 0.5 * (lo + hi)


def main():
    t0 = time.process_time()

    # 1. Discovery: exhaustive over all 32,766 words of length 1..14 (n = 0)
    disc_words = 0
    disc_v = [0, 0, 0, 0]
    for L in range(1, 15):
        for mask in range(1 << L):
            w = "".join("A" if (mask >> i) & 1 else "S" for i in range(L))
            vb, vd, ve4, vx = check_interval("", 0, w)
            disc_words += 1
            disc_v[0] += vb
            disc_v[1] += vd
            disc_v[2] += ve4
            disc_v[3] += vx
    assert sum(disc_v) == 0, f"Discovery violation: {disc_v}"
    print(f"[DISCOVERY] Exhaustive L=1..14 ({disc_words} words, n=0): violations={disc_v}")

    # 2. Holdout: 10,000 random BlockWord ++ A^a ++ tail instances (frozen seed 2026112703)
    rng = random.Random(2026112703)
    hold_v = [0, 0, 0, 0]
    hold_trials = 10000
    for _ in range(hold_trials):
        steps = rng.randint(0, 6)
        bw = "".join(rng.choice(["A", "SAAA", "SSAAAASAAA"]) for _ in range(steps))
        a_run = rng.randint(0, 6)
        tlen = rng.randint(1, 140)
        p = rng.choice([0.2, 0.35, 0.5, 0.65, 0.8])
        tail = "".join("A" if rng.random() < p else "S" for _ in range(tlen))
        vb, vd, ve4, vx = check_interval(bw, a_run, tail)
        hold_v[0] += vb
        hold_v[1] += vd
        hold_v[2] += ve4
        hold_v[3] += vx
    assert sum(hold_v) == 0, f"Holdout violation: {hold_v}"
    print(f"[HOLDOUT-1] Random BlockWord+A^a+tail ({hold_trials} trials, len<=140): violations={hold_v}")

    # 3. Sharpness witnesses at h = 1, 2, 3, and E-783 arbitrary H = 3k (k = 1..6)
    print("[SHARPNESS] Exact & asymptotic tightness checks:")
    for label, w, r in [
        ("h=1 (r=0): (SAAASS)^10", "SAAASS" * 10, 0),
        ("h=2 (r=1): (AAASSS)^10", "AAASSS" * 10, 1),
        ("h=3 (r=2): (AAAASASSSS)^20", "AAAASASSSS" * 20, 2),
    ]:
        fw, _, endN = eval_endN(w)
        E = sum(1 for t in range(len(w)) if fw[t] == r + 1 and endN[t])
        W = sum(2 * (r - fw[t]) - 1 for t in range(len(w)) if w[t] == "A" and fw[t] < r)
        Arm1 = sum(1 for t in range(len(w)) if w[t] == "A" and fw[t] == r - 1)
        assert 3 * E <= W + 2 * Arm1
        print(f"  {label:30s}: 3*E={3*E:4d}, W+2*A_{{r-1}}={W+2*Arm1:4d}, ratio={3*E/(W+2*Arm1):.6f}")

    # E-783 family at H = 3k (k = 1..6), R = 30 copies (evaluating marginal ratio on V^R after V0)
    print("[HOLDOUT-2] E-783 arbitrary-height family (H = 3k, k=1..6, R=30):")
    for k in range(1, 7):
        H = 3 * k
        a = k * (3 * k - 2)
        bank = 3 * a + 2
        lift = a + 1
        V0 = staged_block([1] * (H - 2) + [bank, 1, lift])
        V = staged_block([1] * H + [a])
        m = H + 2
        w = "S" * m + V0 + V * 30 + "AA"
        vb, vd, ve4, vx = check_interval("", 0, w)
        assert vb == vd == ve4 == vx == 0
        # Target height relative to cut height -m is H -> Fw = -m + H = -2, so r = -3
        fw, _, endN = eval_endN(w)
        r = -m + H - 1
        # Marginal per copy of V in copies 1..30:
        start_V = m + len(V0)
        end_V = start_V + 30 * len(V)
        E_V = sum(1 for t in range(start_V, end_V) if fw[t] == r + 1 and endN[t])
        W_V = sum(2 * (r - fw[t]) - 1 for t in range(start_V, end_V) if w[t] == "A" and fw[t] < r)
        Arm1_V = sum(1 for t in range(start_V, end_V) if w[t] == "A" and fw[t] == r - 1)
        assert E_V == 30 * a
        # Single copy of V has W = (H-1)^2 + 1? Check exact W_V/30 and Arm1_V/30:
        print(
            f"  k={k} (H={H:2d}, a={a:3d}): per-V 3*E={3*a:4d}, W={W_V//30:4d}, A_{{r-1}}={Arm1_V//30}, "
            f"W+2*A={W_V//30 + 2*(Arm1_V//30):4d}, ratio={3*E_V/(W_V+2*Arm1_V):.6f}"
        )

    # 4. Exact spectral separation between E-674/E-775 cone and E-785 3-spacing cone
    kappa_old = solve_root(lambda q: q**3 + 2 * q - 1, 0.4, 0.5)
    rho_old = 1.0 / kappa_old
    kappa_new = solve_root(lambda q: 2 * q**4 - 3 * q**3 + 6 * q - 3, 0.5, 0.6)
    rho_new = 1.0 / kappa_new
    gain_old_half = (0.5**3 + 2 * 0.5)
    gain_new_half = (3 * 0.5**2 - 3 * 0.5**3 + 2 * 0.5**4) / (3 * (1 - 0.5) ** 2)
    assert abs(gain_old_half - 9 / 8) < 1e-12
    assert abs(gain_new_half - 2 / 3) < 1e-12
    print(f"[SPECTRAL] E-674/E-775 cone: kappa={kappa_old:.10f}, rho={rho_old:.10f}, q=1/2 gain={gain_old_half:.6f} (>1 FAILS)")
    print(f"[SPECTRAL] E-785 3-spacing:  kappa={kappa_new:.10f}, rho={rho_new:.10f}, q=1/2 gain={gain_new_half:.6f} (<1 PASSES, C=3)")

    # Primal upper bounds for F_0 = 1, F_{h>=1} = 0 (h = 0..12)
    A_old = [1, 0]
    A_new = [1, 0]
    for h in range(2, 13):
        A_old.append(sum((2 * (h - t) - 3) * A_old[t] for t in range(h - 1)))
        num = 3 * A_new[h - 2] + sum((2 * (h - t) - 3) * A_new[t] for t in range(h - 2))
        A_new.append(num // 3)
    print("[PRIMAL F0=1] h | E-674 cone | E-785 3-spacing | 3*2^h")
    for h in range(13):
        print(f"  h={h:2d}:  old={A_old[h]:6d}  |  new={A_new[h]:5d}  |  3*2^h={3*(1<<h):6d}")

    # 5. Negative controls
    # (a) Dropping +2*A_{r-1} fails on SAAASS at r=0: 3*E=3 > W=1
    fw, _, endN = eval_endN("SAAASS")
    E0 = sum(1 for t in range(6) if fw[t] == 1 and endN[t])
    W0 = sum(2 * (0 - fw[t]) - 1 for t in range(6) if "SAAASS"[t] == "A" and fw[t] < 0)
    assert E0 == 1 and W0 == 1 and 3 * E0 > W0
    # (b) Dropping BlockWord prefix fails on non-BlockWord prefix
    vb_neg, _, _, _ = check_interval("SASASASSSSAAAASASASA", 1, "SASSAAAAAAAAASSAAAAASAAAASASAAAAASSSAAAAAASAA")
    assert vb_neg >= 1
    print(f"[NEG-CTRL] Naive 3*E<=W fails on SAAASS (3*{E0}>{W0}); non-BlockWord prefix fails (v_budget={vb_neg})")

    elapsed = time.process_time() - t0
    print(f"ALL CHECKS PASSED in {elapsed:.2f}s CPU.")


if __name__ == "__main__":
    main()
