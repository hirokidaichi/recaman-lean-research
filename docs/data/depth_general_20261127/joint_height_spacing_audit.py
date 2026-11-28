#!/usr/bin/env python3
"""
Reproducible falsifier and exact audit for E-794 (Recaman/JointHeightSpacingCapacity.lean):
  - Joint two-height AA excursion 3+1 slot injection:
      3 * E_{r+1} + E_r <= (descentSlots f n r K).length + 3 * doubleAscent f n K (r - 1)
  - Arbitrary-height joint weight budget:
      3 * E_{r+1} + E_r <= lowAdditionWeights f n r K + 3 * doubleAscent f n K (r - 1)
  - Zero-slack rational polynomial telescoping across the entire joint cone [1/2, kappa_joint),
    where kappa_joint ≈ 0.563708 (1 / kappa_joint ≈ 1.773969), breaking the E-785/E-788
    3-spacing cone barrier (1 / kappa_3 ≈ 1.806686):
      L(P, Q) = (3*Q + P) * Q * (Q - P)^2
      M(P, Q) = P^2 * (4*Q^2 + 3*P^2 - 5*P*Q)
      (L - M) * ratAdditions(P, Q) <= L * ratFree(P, Q)
      (L - M) * P^h * A_{m+h} <= L * Q^h * free
      P^(d+1) * Q^2 * (Q - P) * lowAdditionWeights(r) <= M * Q^(d+1) * free  (r <= m + d + 1, no 1/(L-M) blowup)
      Concrete witnesses: P/Q = 5/9 (base 9/5 = 1.8000, strictly below E-788's 1.8067 cone barrier!),
                          P/Q = 9/16 (base 16/9 ≈ 1.7778),
                          P/Q = 107/190 (base 190/107 ≈ 1.7757, within 0.10% of 1.77397).
  - Exact negative controls:
      (a) non-BlockWord prefix "AASASSAAAA" violates joint slot/weight bound,
      (b) rational weight P/Q = 564/1000 (base 1.77305 < 1.77397) lies outside joint cone (L < M).
"""

import random


def joint_L(P: int, Q: int) -> int:
    return (3 * Q + P) * Q * (Q - P) * (Q - P)


def joint_M(P: int, Q: int) -> int:
    return P * P * (4 * Q * Q + 3 * P * P - 5 * P * Q)


def rat_sum(P: int, Q: int, arr):
    acc = 0
    for val in arr:
        acc = Q * acc + val
    # Actually ratSum P Q g H = sum_{j=0}^H Q^(H-j) P^j g(j)
    H = len(arr) - 1
    tot = 0
    for j, g in enumerate(arr):
        tot += (Q ** (H - j)) * (P ** j) * g
    return tot


def analyze_word(pref: str, tail: str):
    s = pref + tail
    N = len(s)
    n = len(pref)
    K = len(tail)
    Fw = [0] * (N + 1)
    for i, c in enumerate(s):
        Fw[i + 1] = Fw[i] + (1 if c == "A" else -1)
    P_sum = [0] * (N + 1)
    for i in range(N):
        P_sum[i + 1] = P_sum[i] + Fw[i + 1]
    End = [False] * N
    seen = set()
    for t in range(N):
        if s[t] == "A":
            h = Fw[t] - 1
            if (h, P_sum[t] - t * h) in seen:
                End[t] = True
        seen.add((Fw[t], P_sum[t] - t * Fw[t]))

    A, E, F, AA = {}, {}, {}, {}
    free_total = 0
    for t in range(n, n + K):
        h = Fw[t]
        if s[t] == "A":
            A[h] = A.get(h, 0) + 1
            if End[t]:
                E[h] = E.get(h, 0) + 1
            else:
                F[h] = F.get(h, 0) + 1
                free_total += 1
            if t + 1 < n + K and s[t + 1] == "A":
                AA[h] = AA.get(h, 0) + 1

    m = min(Fw[n : n + K + 1])
    M_h = max(Fw[n : n + K + 1])

    def W(r: int) -> int:
        return sum((2 * (r - h) - 1) * cnt for h, cnt in A.items() if h < r)

    def tri(r: int, x: int) -> int:
        d = max(0, r - x)
        return d * d

    def slots(r: int) -> int:
        return W(r) - tri(r, Fw[n]) + tri(r, Fw[n + K])

    return Fw, A, E, F, AA, free_total, m, M_h, W, slots


def check_all_theorems(pref: str, tail: str, pairs):
    Fw, A, E, F, AA, free_total, m, M_h, W, slots = analyze_word(pref, tail)
    h_checks = 0
    cone_checks = 0
    for r in range(m, M_h + 2):
        ep1 = E.get(r + 1, 0)
        er = E.get(r, 0)
        wr = W(r)
        sl = slots(r)
        aa = AA.get(r - 1, 0)
        h_checks += 1
        assert 3 * ep1 + er <= sl + 3 * aa, f"joint slots failed: {pref}|{tail} r={r}"
        assert 3 * ep1 + er <= wr + 3 * aa, f"joint W failed: {pref}|{tail} r={r}"

    H_max = max(1, M_h - m)
    A_vec = [A.get(m + j, 0) for j in range(H_max + 1)]
    F_vec = [F.get(m + j, 0) for j in range(H_max + 1)]
    for P, Q in pairs:
        L = joint_L(P, Q)
        M = joint_M(P, Q)
        assert M < L
        rA = rat_sum(P, Q, A_vec)
        rF = rat_sum(P, Q, F_vec)
        assert (L - M) * rA <= L * rF, f"joint rat cap failed: P/Q={P}/{Q} {pref}|{tail}"
        for h in range(H_max + 1):
            assert (L - M) * (P ** h) * A_vec[h] <= L * (Q ** h) * free_total
            # Low weights bound at r = m + d (d = h + 1):
            # P^(d+1) * Q^2 * (Q - P) * W(m + d) <= M * Q^d * free_total  (2.753 * (190/107)^d * free!)
            wd = W(m + h + 1)
            assert (P ** (h + 2)) * (Q * Q) * (Q - P) * wd <= M * (Q ** (h + 1)) * free_total, (
                f"joint low weights failed at d={h+1}, P/Q={P}/{Q}: lhs={(P**(h+2))*Q*Q*(Q-P)*wd}, rhs={M*(Q**(h+1))*free_total}"
            )
            cone_checks += 1
    return h_checks, cone_checks


def main():
    pairs = [(1, 2), (5, 9), (9, 16), (107, 190)]
    for P, Q in pairs:
        L, M = joint_L(P, Q), joint_M(P, Q)
        print(f"Cone witness P/Q={P}/{Q} (base={Q/P:.6f}): L={L}, M={M}, L-M={L-M}")
        assert M < L

    # 1. Exhaustive L = 1..15 (pref = "")
    exh_h = 0
    exh_c = 0
    for L_len in range(1, 16):
        for mask in range(1 << L_len):
            tail = "".join("A" if (mask >> i) & 1 else "S" for i in range(L_len))
            hc, cc = check_all_theorems("", tail, [(5, 9), (9, 16)])
            exh_h += hc
            exh_c += cc
    print(f"[1] Exhaustive L=1..15: 65534 words, {exh_h} joint-spacing checks, {exh_c} rational-cone checks, 0 violations.")

    # 2. Holdout BlockWord + A^a random tails (all 4 rational pairs including 107/190)
    rng = random.Random(20261127)
    atoms = ["", "A", "SAAA", "SSAAAASAAA", "ASAAA", "SAAASAAA"]
    prefs = [w + "A" * a for w in atoms for a in range(5)]
    rand_h = 0
    rand_c = 0
    for _ in range(3500):
        pref = rng.choice(prefs)
        tail = "".join("A" if rng.random() < rng.choice([0.35, 0.5, 0.65]) else "S" for _ in range(rng.randint(5, 65)))
        hc, cc = check_all_theorems(pref, tail, pairs)
        rand_h += hc
        rand_c += cc
    print(f"[2] Holdout BlockWord+A^a (3500 tails, all 4 pairs incl. 107/190): {rand_h} spacing + {rand_c} cone checks, 0 violations.")

    # 3. Sharpness witness (0 slack in 3*E_{r+1} + E_r <= W(r) + 3*AA_{r-1})
    _, A, E, _, AA, _, _, _, W, slots = analyze_word("SAAA", "SASSASASASASSSAAAASAASAAASSSAAAS")
    r = 0
    lhs = 3 * E.get(r + 1, 0) + E.get(r, 0)
    rhs = W(r) + 3 * AA.get(r - 1, 0)
    assert lhs == 7 and rhs == 7 and slots(r) == 4
    print(f"[3] Exact zero-slack sharpness ('SAAA' | tail, r=0): 3*E_1 + E_0 = {lhs} == W(0) + 3*AA_{'{-1}'} = {rhs} (slots={slots(r)}).")

    # 4. Negative controls
    _, _, E_neg, _, AA_neg, _, _, _, W_neg, _ = analyze_word("AASASSAAAA", "SAASAASSASSSSAAASAAA")
    neg_gap = 3 * E_neg.get(3, 0) + E_neg.get(2, 0) - (W_neg(2) + 3 * AA_neg.get(1, 0))
    assert neg_gap > 0
    assert joint_M(564, 1000) > joint_L(564, 1000)
    print(
        f"[4] Negative controls: (a) non-BlockWord prefix gap = +{neg_gap}; "
        f"(b) P/Q=564/1000 outside joint cone (M={joint_M(564, 1000)} > L={joint_L(564, 1000)})."
    )
    print("ALL CHECKS PASSED.")


if __name__ == "__main__":
    main()
