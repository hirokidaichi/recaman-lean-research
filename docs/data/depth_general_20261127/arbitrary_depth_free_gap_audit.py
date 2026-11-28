#!/usr/bin/env python3
"""
Reproducible discovery, holdout, boundary, and negative-control audit for
H-20261127-05 / E-787 (`Recaman/ArbitraryDepthFreeGap.lean`).

Tests all 7 candidate theorems:
  1. low_weights_le_two_dyadic_free:
       lowAdditionWeights f n (m + d + 1) K <= 2 * dyadicFree f n K m d
  2. low_weights_le_pow_two_free:
       r <= m + d -> lowAdditionWeights f n r K <= 2^d * free f n K
  3. low_weights_five_three_spacing:
       r <= m + 5 -> 3 * lowAdditionWeights f n r K <= 59 * free f n K
  4. arbitrary_target_height_free_gap_square (NO hpos, NO ceiling):
       Fw(b + j) <= m + d + 1 -> (j + 1)^2 <= 2^d * free f n (b - n)
  5. arbitrary_target_height_free_gap (NO hpos, NO ceiling):
       Fw(b + j) <= m + d + 1 & 2^d <= j + 2 -> j + 1 <= free f n (b - n)
  6. positive_arbitrary_depth_free_gap_profile (arbitrary D >= 2):
       hfloor(Fw(n) - D), hpos, free <= j ->
         4 <= free & j + 3 <= 2^(D - 2) & Fw(b + j) <= Fw(n) - 1 &
         (j + 1)^2 <= 2^(D - 2) * free
  7. positive_depth_seven_counter_profile (D = 7):
       hfloor(Fw(n) - 7), hpos, free <= j ->
         4 <= free & j <= 17 & Fw(b + j) <= Fw(n) - 1 &
         3 * (j + 1)^2 <= 59 * free
"""

from __future__ import annotations
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


def make_block_word(rng: random.Random, max_blocks: int = 5) -> str:
    """Exact Lean BlockWord grammar: concat of A (free), SAAA (aas), SSAAAASAAA (triple)."""
    nb = rng.randint(0, max_blocks)
    return "".join(rng.choice(["A", "SAAA", "SSAAAASAAA"]) for _ in range(nb))


def audit_instance(bw: str, a_run: int, tail: str, stats: dict):
    full = bw + "A" * a_run + tail
    n = len(bw) + a_run
    L = len(full)
    fw, _, endN = eval_endN(full)

    # Check (1), (2), (3) on the full suffix [n, L)
    K = L - n
    if K >= 1:
        m = min(fw[n : L + 1])
        hi = max(fw[n : L + 1])
        free = sum(1 for t in range(n, L) if full[t] == "A" and not endN[t])
        # dyadicFree(m, d) = sum_{j=0}^d 2^{d-j} F_{m+j}
        df = 0
        for d in range(0, hi - m + 2):
            f_d = sum(1 for t in range(n, L) if full[t] == "A" and not endN[t] and fw[t] == m + d)
            df = 2 * df + f_d
            r = m + d + 1
            W = sum(2 * (r - fw[t]) - 1 for t in range(n, L) if full[t] == "A" and fw[t] < r)
            stats["checks_1"] += 1
            if W > 2 * df:
                stats["viol_1"] += 1
            # Also check (2) at r = m + d
            r2 = m + d
            W2 = sum(2 * (r2 - fw[t]) - 1 for t in range(n, L) if full[t] == "A" and fw[t] < r2)
            stats["checks_2"] += 1
            if W2 > (1 << d) * free:
                stats["viol_2"] += 1
            if d == 5:
                stats["checks_3"] += 1
                if 3 * W2 > 59 * free:
                    stats["viol_3"] += 1
                if free > 0:
                    ratio = W2 / free
                    if ratio > stats["max_W5_over_free"]:
                        stats["max_W5_over_free"] = ratio

    # Check (4), (5), (6), (7) at every supplied endable clock t0 = b + j in [n + 1, L)
    # where full[b..b+j) is all S (maximizing j and also testing every valid b < t0)
    for t0 in range(n + 1, L):
        if not endN[t0]:
            continue
        # Walk backwards through S's
        b = t0
        while b > n + 1 and full[b - 1] == "S":
            b -= 1
            j = t0 - b
            m = min(fw[n : b + 1])
            free = sum(1 for t in range(n, b) if full[t] == "A" and not endN[t])
            # Pick smallest d >= 0 with fw[t0] <= m + d + 1
            d = max(0, fw[t0] - m - 1)
            stats["checks_4"] += 1
            if (j + 1) ** 2 > (1 << d) * free:
                stats["viol_4"] += 1
            if (1 << d) <= j + 2:
                stats["checks_5"] += 1
                if j + 1 > free:
                    stats["viol_5"] += 1
            # Check hpos on [n, b]
            hpos = True
            e_cnt = 0
            s_cnt = 0
            for k in range(1, b - n + 1):
                idx = n + k - 1
                if endN[idx]:
                    e_cnt += 1
                if full[idx] == "S":
                    s_cnt += 1
                if e_cnt + 1 > s_cnt:
                    hpos = False
                    break
            if hpos:
                D = max(2, fw[n] - m)
                stats["hpos_hits"] += 1
                if free <= j:
                    stats["hpos_counter_hits"] += 1
                    stats["checks_6"] += 1
                    ok6 = (
                        4 <= free
                        and j + 3 <= (1 << (D - 2))
                        and fw[t0] <= fw[n] - 1
                        and (j + 1) ** 2 <= (1 << (D - 2)) * free
                    )
                    if not ok6:
                        stats["viol_6"] += 1
                    if D <= 7:
                        stats["checks_7"] += 1
                        ok7 = (
                            4 <= free
                            and j <= 17
                            and fw[t0] <= fw[n] - 1
                            and 3 * (j + 1) ** 2 <= 59 * free
                        )
                        if not ok7:
                            stats["viol_7"] += 1


def build_e786_word(H: int, a: int = 2, m: int = 3, R: int = 3) -> str:
    """Reproduce E-786 recursive balanced cascade word."""
    def bank(h):
        return "A" * (h - 1) + "SA" * a + "A" + "AS" * a + "S" * h
    def cyc(h):
        if h == 1:
            return "A" + "AS" * a + "S"
        B = 1
        inner = bank(h - 1) + cyc(h - 1) * B
        return inner * m + "A" * h + "AS" * a + "S" * h
    return bank(H) + cyc(H) * R


def main():
    t_start = time.time()
    stats = {
        "checks_1": 0, "viol_1": 0,
        "checks_2": 0, "viol_2": 0,
        "checks_3": 0, "viol_3": 0,
        "checks_4": 0, "viol_4": 0,
        "checks_5": 0, "viol_5": 0,
        "checks_6": 0, "viol_6": 0,
        "checks_7": 0, "viol_7": 0,
        "hpos_hits": 0,
        "hpos_counter_hits": 0,
        "max_W5_over_free": 0.0,
    }

    # 1. Discovery: exhaustive binary words length 1..13 (n=0, a=0)
    disc_words = 0
    for L in range(1, 14):
        for mask in range(1 << L):
            w = "".join("A" if (mask >> i) & 1 else "S" for i in range(L))
            audit_instance("", 0, w, stats)
            disc_words += 1
    print(f"[Discovery] exhaustive L=1..13 ({disc_words} words): "
          f"viols = {[stats[f'viol_{i}'] for i in range(1, 8)]}")

    # 2. Holdout: 4000 random BlockWord ++ A^a ++ deep tail (seed 2026112702)
    rng = random.Random(2026112702)
    for _ in range(4000):
        bw = make_block_word(rng, max_blocks=3)
        a_run = rng.randint(0, 4)
        pA = rng.choice([0.35, 0.45, 0.5, 0.55, 0.6])
        tail_len = rng.randint(5, 80)
        tail = "".join("A" if rng.random() < pA else "S" for _ in range(tail_len))
        audit_instance(bw, a_run, tail, stats)

    # 3. Adversarial E-786 exponential cascade words (H = 2, 3, 4)
    for H in (2, 3, 4):
        w = build_e786_word(H, a=2, m=2, R=3)
        audit_instance("", 0, w, stats)
        audit_instance("SAAA", 1, w, stats)
        # Also append descending S^j A probes
        for j in range(1, H + 4):
            audit_instance("", 0, w + "S" * j + "A", stats)

    # 4. Boundary cases (d=0, D=2, j=0, a=0, free=0, negative m)
    boundary_cases = [
        ("", 0, "S" * 10),
        ("", 0, "A" * 6),
        ("A", 0, "S" * 6 + "A"),
        ("SAAA", 2, "S" * 5 + "AA"),
        ("SSAAAASAAA", 0, "SSAAASSAA"),
    ]
    for bw, a_run, tail in boundary_cases:
        audit_instance(bw, a_run, tail, stats)

    # 5. Negative control: non-BlockWord prefix ("SAA") + tail ("A") breaks Theorems 1 & 2
    neg_pre, neg_tail = "SAA", "A"
    neg_full = neg_pre + neg_tail
    fw_n, _, end_n = eval_endN(neg_full)
    n_neg = len(neg_pre)
    m_neg = min(fw_n[n_neg:])
    free_neg = sum(1 for t in range(n_neg, len(neg_full)) if neg_full[t] == "A" and not end_n[t])
    W1_neg = sum(
        2 * (m_neg + 1 - fw_n[t]) - 1
        for t in range(n_neg, len(neg_full))
        if neg_full[t] == "A" and fw_n[t] < m_neg + 1
    )
    neg_found = (neg_pre, neg_tail, m_neg, free_neg, W1_neg) if W1_neg > 2 * free_neg else None

    elapsed = time.time() - t_start
    print(f"[Total] elapsed={elapsed:.2f}s")
    for i in range(1, 8):
        print(f"  Theorem {i}: checks={stats[f'checks_{i}']}, violations={stats[f'viol_{i}']}")
    print(f"  hpos_hits={stats['hpos_hits']}, hpos_counter_hits={stats['hpos_counter_hits']}")
    print(f"  max observed W(m+5)/free = {stats['max_W5_over_free']:.4f} (bound 59/3 = {59/3:.4f})")
    print(f"  [Negative control] non-BlockWord prefix breaking (2) at d=1: {neg_found}")
    assert all(stats[f"viol_{i}"] == 0 for i in range(1, 8)), "VIOLATION DETECTED!"
    assert neg_found is not None, "Negative control failed to find non-BlockWord violation!"
    print("ALL CHECKS PASSED WITH 0 VIOLATIONS.")


if __name__ == "__main__":
    main()
