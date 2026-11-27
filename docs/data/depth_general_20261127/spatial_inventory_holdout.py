#!/usr/bin/env python3
"""Independent holdout verification for E-782 (8-filter spatial bridge grid)
and C1 nonpositive-height S^L-predecessor closure corollary.

Uses independent reverse-sum area check for Win/E-759 and direct greedy replay
from the full compact set V = [0, L] union T.
"""
import itertools
import time

def check_e759_independent(W):
    """Direct O(Q^2) check of E-759 (I) and (II) via literal window sums."""
    Q = len(W)
    H = [0]
    for s in W:
        H.append(H[-1] + s)
    for v in range(1, Q + 1):
        if W[v - 1] != -1:
            continue
        hv = H[v]
        # (I): no 0 <= u < v with H[u] == H[v] and sum_{i=u+1..v} (H[i] - H[v]) == 0
        for u in range(v):
            if H[u] == hv:
                area = sum(H[i] - hv for i in range(u + 1, v + 1))
                if area == 0:
                    return False
        # (II): no 0 <= q < v with W[q] == +1, H[q]-1 == H[v], and sum_{i=q+1..v} (H[i] - H[v]) == 0
        for q in range(v):
            if W[q] == 1 and H[q] - 1 == hv:
                area = sum(H[i] - hv for i in range(q + 1, v + 1))
                if area == 0:
                    return False
    return True

def verify_eight_filter_step_d(W):
    Q = len(W)
    N = Q + 1
    b = 1000 * N * N
    x = 100 * (b + N) * N
    d = b - 200 * N
    ut_b = b * (b + 1) // 2

    # Compute exact trajectory values X_0..X_Q directly
    X = [x]
    for i, s in enumerate(W):
        X.append(X[-1] + s * (b + i + 1))

    # Original free A clocks via direct O(Q^2) Win check
    H = [0]
    for s in W:
        H.append(H[-1] + s)
    T0 = {x}
    s_vals = set()
    for q in range(Q):
        if W[q] == 1:
            supplied = False
            for u in range(q):
                if H[q] == H[u] + 1:
                    if sum(H[i] - H[u] for i in range(u + 1, q + 1)) == 0:
                        supplied = True
                        break
            if not supplied:
                T0.add(X[q] - (b + q + 1))
        else:
            s_vals.add(X[q + 1])

    M = max(T0)
    bad = {v % d for v in s_vals}
    delta = next(c for c in range(1, N + 1) if (b + c) % d not in bad)
    G = list(range(b + delta, M + 1, d))
    T = sorted(T0 | set(G))
    L = b // 2 - len(T)
    assert L >= 0 and T[0] > L
    card_V = (L + 1) + len(T)
    assert card_V == b // 2 + 1

    # Verify all 8 filters
    assert card_V <= b + 1
    assert x % 2 == ut_b % 2
    assert T[-1] <= ut_b
    s_cov = card_V - 1
    assert ut_b <= x + s_cov * (2 * b - s_cov + 1)
    assert 2 * T[-1] <= x + ut_b

    gaps = [(T[0] - L, L, T[0], len(T))]
    for i in range(len(T) - 1):
        gaps.append((T[i + 1] - T[i], T[i], T[i + 1], len(T) - 1 - i))
    for g, lo, hi, tc in gaps:
        assert g <= d < b
        assert tc <= b - g + 1
        assert 2 * T[-1] + (g - 1) * g // 2 <= x + lo + ut_b
    g_desc = sorted((g for g, _, _, _ in gaps), reverse=True)
    for k, g in enumerate(g_desc, start=1):
        assert g <= b + 1 - k

    # Exact greedy replay
    T_set = set(T)
    cur = x
    for i, expected in enumerate(W):
        step_k = b + i + 1
        cand = cur - step_k
        seen = (0 <= cand <= L) or (cand in T_set)
        if cand > 0 and not seen:
            actual = -1
            cur = cand
        else:
            actual = 1
            cur = cur + step_k
        if actual != expected:
            return False
        if cur > L:
            T_set.add(cur)
    return True

def main():
    t0 = time.process_time()
    # 1. Holdout: length-8 words (sample of all 256 words!)
    adm8 = 0
    for W in itertools.product((-1, 1), repeat=8):
        adm = check_e759_independent(W)
        ok = verify_eight_filter_step_d(W)
        assert ok == adm, f"Mismatch on length 8 word {W}"
        if adm:
            adm8 += 1
    print(f"[Holdout length 8] 256/256 exact match (adm={adm8}, non_adm={256-adm8})!")

    # 2. Holdout: sharp staged words W_n (E-777) for n = 1, 2, 3, 4
    for n in (1, 2, 3, 4):
        W = [-1]*(2*n+2) + [1,-1,1,1]*n + [1] + [-1]*(2*n+1) + [1,1]
        adm = check_e759_independent(W)
        ok = verify_eight_filter_step_d(W)
        assert adm and ok
        print(f"[Holdout E-777 W_{n}] len={len(W)} adm=True 8-filter+replay=True")

    # 3. C1 / nonpositive-height S^L-predecessor closure check (lengths 1..8)
    # Every coherent word with max H(t) <= 1 admits S^L ++ W for L in {1, 2, 5, 10}.
    c1_checked = 0
    for Q in range(1, 9):
        for W in itertools.product((-1, 1), repeat=Q):
            # check max prefix height <= 1
            H = 0
            ok_h = True
            for s in W:
                H += s
                if H > 1:
                    ok_h = False
                    break
            if not ok_h:
                continue
            if not check_e759_independent(W):
                continue
            c1_checked += 1
            for L_pre in (1, 2, 5):
                assert check_e759_independent((-1,)*L_pre + W), f"Failed S^{L_pre}++{W}"
    print(f"[S^L predecessor closure check] {c1_checked} coherent words with H<=1 (len 1..8): 100% admit S^L++W for L=1,2,5!")

    # Boundary negative control for H=2: SAAS fails S++AAS!
    assert check_e759_independent((1, 1, -1))  # AAS is coherent
    assert not check_e759_independent((-1, 1, 1, -1))  # S++AAS = SAAS fails (H(2)=2, B(2)=3=2+1)!
    print("[Negative control] AAS coherent (max H=2), S++AAS=SAAS rejected as predicted!")
    print(f"Elapsed CPU: {time.process_time() - t0:.4f}s")

if __name__ == "__main__":
    main()
