#!/usr/bin/env python3
"""Reproducible audit script for E-799 (Delta = 2 coherent greedy exponential cascade).

Constructs the Delta = 2 coherent greedy cascade on h_k = 2k + 2 (band [-1, 2k + 3])
with (AS)^q placed BEFORE (SA)^p inside V_k:
  V_k  = (AS)^{q_k} ++ (SA)^{p_k} ++ B_{k-1} ++ A^{h_k} (AS)^{a_k} S^{h_k}
  V0_k = A^{h_k - 1} (SA)^{bank_k} A (AS)^{lift_k} S^{h_k}
  B_k  = V0_k ++ V_k^{R_k}

Verifies:
1. Discovery (K0 = 6) and holdout (K0 = 9, 12) for k = 1, 2, 3: E-759 = (0, 0).
2. All 3 mod-3 residue classes q_3 in {0, 1, 2} at k = 3: E-759 = (0, 0).
3. Depth k = 4 (h_4 = 10, band [-1, 11], length > 7.2M): E-759 = (0, 0).
4. Exact 8-filter coherent finite-State greedy replay on B_1 (using E-782's spatial bridge).
5. Negative control: reversing (AS)^q and (SA)^p to (SA)^p ++ (AS)^q causes Type-I
   collisions at height 0 whenever q > 0.
6. Asymptotic growth rate verification: exact recurrence
     3 * A_k = sum_{m >= 1} (4m - 3) * A_{k - m}
   has exact ratio mu = 7/3 per Delta = 2 step, i.e., per-height base sqrt(7/3) ~= 1.527525.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "docs/data/depth_general_20261127"))
from spatial_inventory_holdout import verify_eight_filter_step_d  # noqa: E402


def dphi(w: str, r: int) -> int:
    H = 0
    B = 0
    for ch in w:
        H += 1 if ch == "A" else -1
        B += H
    assert H == 0
    return B - r * len(w)


def check_e759_and_af(w: str) -> tuple[int, int, int, int, int, int]:
    """Return (c1, c2, A, F, hmin, hmax) in one linear pass."""
    H = 0
    B = 0
    out_set = {(0, 0)}
    cand_set = set()
    fI = fII = A = F = 0
    hmin = hmax = 0
    for i, ch in enumerate(w):
        if ch == "A":
            A += 1
            key_c = (H - 1, B - i * (H - 1))
            if key_c not in out_set:
                F += 1
            cand_set.add(key_c)
            H += 1
            if H > hmax:
                hmax = H
        else:
            H -= 1
            if H < hmin:
                hmin = H
        B += H
        v = i + 1
        key = (H, B - v * H)
        if ch == "S":
            if key in out_set:
                fI += 1
            if key in cand_set:
                fII += 1
        out_set.add(key)
    return fI, fII, A, F, hmin, hmax


def build_delta2_level(
    B_prev: str,
    bank_prev: int,
    k: int,
    R: int,
    *,
    reverse_as_sa: bool = False,
) -> tuple[str, int, dict[str, int]]:
    h = 2 * k + 2
    h_prev = 2 * k
    p_lo = 0 if k == 1 else (3 * bank_prev) // (2 * (2 * h_prev - 3)) + 2
    dp_prev = dphi(B_prev, h - 1)
    dp_base = dphi("A" * h + "S" * h, h - 1)
    dp_SA = dphi("SA", h - 1)  # -(2*h - 1)
    dp_AS = dphi("AS", h - 1)  # -(2*h - 3)
    assert dp_SA == -(2 * h - 1) and dp_AS == -(2 * h - 3)

    found = None
    for q in range(3):
        for dp in range(3):
            p = p_lo + dp
            rem = 1 - p * dp_SA - q * dp_AS - dp_prev - dp_base
            if rem % 3 == 0 and rem >= 3:
                found = (q, p, rem // 3)
                break
        if found is not None:
            break
    assert found is not None
    q_k, p_k, a_k = found

    prefix = ("SA" * p_k + "AS" * q_k) if reverse_as_sa else ("AS" * q_k + "SA" * p_k)
    V = prefix + B_prev + ("A" * h) + ("AS" * a_k) + ("S" * h)
    assert dphi(V, h - 1) == 1

    H = 0
    B = 0
    cands = []
    for i, ch in enumerate(V):
        if ch == "A" and H == h:
            cands.append(B - i * (h - 1))
        H += 1 if ch == "A" else -1
        B += H
    c_min, c_max = min(cands), max(cands)
    P_bank_top = -((h - 1) * (h - 2)) // 2
    dp_v0_0 = dphi("A" * (h - 1) + "A" + "S" * h, h - 1)
    lift = max(1, (P_bank_top - dp_v0_0 - c_min + 2) // 3 + 1)
    bank = dp_v0_0 + 3 * lift - P_bank_top + c_max
    assert R <= bank, f"R={R} must be <= bank={bank}"
    V0 = "A" * (h - 1) + "SA" * bank + "A" + "AS" * lift + "S" * h
    B_new = V0 + V * R
    info = {
        "k": k,
        "h": h,
        "q": q_k,
        "p": p_k,
        "a": a_k,
        "bank": bank,
        "lift": lift,
        "R": R,
        "len": len(B_new),
    }
    return B_new, bank, info


def build_tower(
    K0: int,
    Rs: list[int],
    *,
    reverse_last: bool = False,
) -> tuple[str, list[dict[str, int]]]:
    B = "AS" * K0
    bank = K0
    infos: list[dict[str, int]] = []
    for idx, R_k in enumerate(Rs, 1):
        rev = reverse_last and (idx == len(Rs))
        B, bank, info = build_delta2_level(B, bank, idx, R_k, reverse_as_sa=rev)
        infos.append(info)
    return B, infos


def main() -> None:
    # 1. Discovery (K0 = 6) and holdout (K0 = 9, 12) through k = 3
    for K0 in [6, 9, 12]:
        B3, infos = build_tower(K0, [6, 6, 6])
        c1, c2, A, F, hmin, hmax = check_e759_and_af(B3)
        assert (c1, c2) == (0, 0), f"K0={K0} failed: {(c1, c2)}"
        assert hmin == -1 and hmax == 9
        print(
            f"[PASS] K0={K0:2d} k=3 (h=8, band [{hmin},{hmax}]): "
            f"len={len(B3):,}, A/F={A/F:.4f}, q={infos[-1]['q']}, E-759={(c1, c2)}"
        )

    # 2. All 3 mod-3 residue classes q_3 in {0, 1, 2}
    seen_q = set()
    for R2 in [5, 6, 7, 8, 9, 10]:
        B3, infos = build_tower(6, [6, R2, 4])
        q3 = infos[-1]["q"]
        c1, c2, A, F, _, _ = check_e759_and_af(B3)
        assert (c1, c2) == (0, 0), f"R2={R2}, q3={q3} failed: {(c1, c2)}"
        seen_q.add(q3)
    assert seen_q == {0, 1, 2}, f"Did not cover all q3 residues: {seen_q}"
    print(f"[PASS] All three mod-3 residue classes q_3 in {sorted(seen_q)} verified E-759=(0, 0)")

    # 3. Negative control: reversing (AS)^q ++ (SA)^p -> (SA)^p ++ (AS)^q fails when q > 0
    B_neg, infos_neg = None, None
    for R2 in [5, 6, 7, 8]:
        B_try, infos_try = build_tower(6, [6, R2, 4], reverse_last=True)
        if infos_try[-1]["q"] > 0:
            B_neg, infos_neg = B_try, infos_try
            break
    assert B_neg is not None and infos_neg is not None
    nc1, nc2, _, _, _, _ = check_e759_and_af(B_neg)
    assert nc1 > 0, "Expected Type-I collision when (SA)^p precedes (AS)^q with q > 0"
    print(
        f"[PASS] Negative control (SA)^p ++ (AS)^q at q={infos_neg[-1]['q']}: "
        f"Type-I collisions={nc1} > 0 (confirms ordering necessity)"
    )

    # 4. Exact 8-filter coherent finite-State greedy replay on B_1 (K0 = 6, R1 = 6)
    B1, _ = build_tower(6, [6])
    signs_b1 = [+1 if ch == "A" else -1 for ch in B1]
    res8 = verify_eight_filter_step_d(signs_b1)
    assert res8 is True or (isinstance(res8, dict) and res8.get("ok") is True), f"8-filter failed: {res8}"
    print(f"[PASS] 8-filter coherent greedy replay on B_1 (len={len(B1)}): result={res8}")

    # 5. High-R k=3 amplification check & depth k=4 verification (h_4 = 10, band [-1, 11])
    B3_hi, infos3_hi = build_tower(6, [12, 12, 12])
    c1h, c2h, A3h, F3h, hmin3h, hmax3h = check_e759_and_af(B3_hi)
    assert (c1h, c2h) == (0, 0) and hmin3h == -1 and hmax3h == 9
    print(
        f"[PASS] High-R k=3 (R=[12,12,12], band [{hmin3h},{hmax3h}]): "
        f"len={len(B3_hi):,}, A/F={A3h/F3h:.4f}, q_3={infos3_hi[-1]['q']}, E-759={(c1h, c2h)}"
    )

    B4, infos4 = build_tower(6, [5, 5, 5, 5])
    c1, c2, A4, F4, hmin4, hmax4 = check_e759_and_af(B4)
    assert (c1, c2) == (0, 0), f"k=4 failed: {(c1, c2)}"
    assert hmin4 == -1 and hmax4 == 11
    print(
        f"[PASS] Depth k=4 (R=[5,5,5,5], h=10, band [{hmin4},{hmax4}]): "
        f"len={len(B4):,}, A/F={A4/F4:.4f}, q_4={infos4[-1]['q']}, E-759={(c1, c2)}"
    )

    # 6. Asymptotic growth recurrence check: 3*A_k = sum_{m=1}^k (4m - 3) A_{k - m}
    # Generating function: 3 = (x + 3x^2)/(1-x)^2 => 3 - 6x + 3x^2 = x + 3x^2 => 7x = 3 => x = 3/7.
    As = [1.0]
    for k in range(1, 30):
        val = sum((4 * m - 3) * As[k - m] for m in range(1, k + 1)) / 3.0
        As.append(val)
    ratios = [As[k] / As[k - 1] for k in range(1, len(As))]
    assert abs(ratios[-1] - 7.0 / 3.0) < 1e-12
    base_per_h = math.sqrt(7.0 / 3.0)
    print(
        f"[PASS] Exact Delta=2 recurrence 3*A_k = sum_{{m>=1}} (4m-3) A_{{k-m}}: "
        f"A_k/A_{{k-1}} -> {ratios[-1]:.12f} == 7/3, per-height base = sqrt(7/3) = {base_per_h:.6f}"
    )
    print("ALL E-799 AUDITS PASSED.")


if __name__ == "__main__":
    main()
