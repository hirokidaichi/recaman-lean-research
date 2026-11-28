#!/usr/bin/env python3
"""
Reproducible falsifier and exact audit for:
  - E-792 (Recaman/ExcursionClimbSpacing.lean):
      3 * E_{r+1} <= descentSlots(r) + 2 * AA_{r-1}
      3 * E_{r+1} <= W(r) + 2 * AA_{r-1}
      3 * E_{r+1} <= W(r) + 2 * min(A_{r-1}, A_r)
      AA_{r-1} = 0 -> 3 * E_{r+1} <= W(r)
      3 * E_{m+2} <= F_m + 2 * AA_m
      3 * E_{m+4} <= 6 * free + 2 * AA_{m+2}
  - E-793 (REFUTED): C2 conjecture 3 * E_{r+1} <= W(r) + 2 * F_{r-1}
      Refuted with zero-prefix unbounded family (3 * E_4 - W(3) = 2*k - 9, F_2 = 1)
      and minimal BlockWord+A^3 counterexample (3 * 7 = 21 > 19 + 2 * 0) where
      E-792 holds with exact equality 21 = 19 + 2 * 1.
"""

import random
import sys


def compute_stats(pref: str, tail: str):
    s = pref + tail
    N = len(s)
    n = len(pref)
    K = len(tail)
    Fw = [0] * (N + 1)
    for i, c in enumerate(s):
        Fw[i + 1] = Fw[i] + (1 if c == "A" else -1)
    P = [0] * (N + 1)
    for i in range(N):
        P[i + 1] = P[i] + Fw[i + 1]

    # Exact EndN f 0 t: f t = 'A' and exists u < t, Fw[u] = Fw[t]-1, Ar(u, t-u) = 0
    End = [False] * N
    seen = set()
    for t in range(N):
        if s[t] == "A":
            h = Fw[t] - 1
            if (h, P[t] - t * h) in seen:
                End[t] = True
        seen.add((Fw[t], P[t] - t * Fw[t]))

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
    M = max(Fw[n : n + K + 1])

    def W(r: int) -> int:
        return sum((2 * (r - h) - 1) * cnt for h, cnt in A.items() if h < r)

    def tri(r: int, x: int) -> int:
        d = max(0, r - x)
        return d * d

    def slots(r: int) -> int:
        return W(r) - tri(r, Fw[n]) + tri(r, Fw[n + K])

    return {
        "Fw": Fw,
        "A": A,
        "E": E,
        "F": F,
        "AA": AA,
        "free": free_total,
        "m": m,
        "M": M,
        "W": W,
        "slots": slots,
    }


def check_e792_on(pref: str, tail: str):
    st = compute_stats(pref, tail)
    m, M = st["m"], st["M"]
    A, E, F, AA = st["A"], st["E"], st["F"], st["AA"]
    checks = 0
    for r in range(m, M + 2):
        e = E.get(r + 1, 0)
        wr = st["W"](r)
        sl = st["slots"](r)
        aa = AA.get(r - 1, 0)
        arm1 = A.get(r - 1, 0)
        ar = A.get(r, 0)
        checks += 1
        assert aa <= arm1 and aa <= ar, f"AA bound failed: {pref}|{tail} r={r}"
        assert 3 * e <= sl + 2 * aa, f"slots AA bound failed: {pref}|{tail} r={r}"
        assert 3 * e <= wr + 2 * aa, f"W AA bound failed: {pref}|{tail} r={r}"
        assert 3 * e <= wr + 2 * min(arm1, ar), f"min bound failed: {pref}|{tail} r={r}"
        if aa == 0:
            assert 3 * e <= wr, f"plateau bound failed: {pref}|{tail} r={r}"
    # Floor-specialized checks
    assert 3 * E.get(m + 2, 0) <= F.get(m, 0) + 2 * AA.get(m, 0), (
        f"floor+2 AA failed: {pref}|{tail}"
    )
    assert 3 * E.get(m + 4, 0) <= 6 * st["free"] + 2 * AA.get(m + 2, 0), (
        f"floor+4 AA failed: {pref}|{tail}"
    )
    return checks


def main():
    # 1. Exhaustive audit over all words of length 1..15 (pref = "")
    exh_words = 0
    exh_checks = 0
    for L in range(1, 16):
        for mask in range(1 << L):
            tail = "".join("A" if (mask >> i) & 1 else "S" for i in range(L))
            exh_checks += check_e792_on("", tail)
            exh_words += 1
    print(f"[1] Exhaustive L=1..15 (pref=''): {exh_words} words, {exh_checks} height-checks, 0 violations.")

    # 2. Holdout audit over true BlockWord ++ A^a prefixes + random tails
    rng = random.Random(20261127)
    bw_atoms = ["", "A", "SAAA", "SSAAAASAAA"]
    bw_prefs = []
    for a1 in bw_atoms:
        for a2 in bw_atoms[:3]:
            for extra_a in range(4):
                bw_prefs.append(a1 + a2 + "A" * extra_a)
    bw_prefs = sorted(set(bw_prefs))

    rand_checks = 0
    strict_aa_gains = 0
    strict_min_gains = 0
    strict_f2_gains = 0
    for i in range(4000):
        pref = rng.choice(bw_prefs)
        L = rng.randint(5, 60)
        pA = rng.choice([0.35, 0.5, 0.65])
        tail = "".join("A" if rng.random() < pA else "S" for _ in range(L))
        rand_checks += check_e792_on(pref, tail)
        st = compute_stats(pref, tail)
        m = st["m"]
        if st["E"].get(m + 2, 0) > 0 and st["F"].get(m, 0) + 2 * st["AA"].get(m, 0) < 3 * st["F"].get(m, 0):
            strict_f2_gains += 1
        for r in range(m, st["M"] + 1):
            if st["E"].get(r + 1, 0) > 0:
                if st["AA"].get(r - 1, 0) < st["A"].get(r - 1, 0):
                    strict_aa_gains += 1
                if min(st["A"].get(r - 1, 0), st["A"].get(r, 0)) < st["A"].get(r - 1, 0):
                    strict_min_gains += 1
    print(
        f"[2] Holdout BlockWord+A^a random tails (4000 words): {rand_checks} height-checks, 0 violations "
        f"(strict AA<A instances={strict_aa_gains}, min<A_{'{r-1}'}={strict_min_gains}, floor+2 gains={strict_f2_gains})."
    )

    # 3. Negative control: non-BlockWord prefix "AASASSAAAA" violates E-792 by +3
    neg_st = compute_stats("AASASSAAAA", "SAASAASSASSSSAAASAAA")
    neg_gap = 3 * neg_st["E"].get(3, 0) - (neg_st["W"](2) + 2 * neg_st["AA"].get(1, 0))
    assert neg_gap == 3, f"Expected negative control gap +3, got {neg_gap}"
    print(
        f"[3] Negative control (non-BlockWord prefix 'AASASSAAAA', r=2): "
        f"3*E_3 - (W(2) + 2*AA_1) = +{neg_gap} (proves BlockWord prehistory is essential)."
    )

    # 4. E-793 REFUTED: Minimal BlockWord+A^3 counterexample to C2 (3*E_{r+1} <= W(r) + 2*F_{r-1})
    pref_c2 = "AAA"
    # Gadget G: 19 (AS) oscillations at height 3 -> dip S S (S A)^2 S A A (drop=19, d at h=2 supplied!)
    # -> A A (AS)^6 A (7 supplied additions at h=4, p = 1,4,7,10,13,16,19)
    gadget = "AS" * 19 + "SS" + "SA" * 2 + "SAA" + "AA" + "AS" * 6 + "A"
    st_c2 = compute_stats(pref_c2, gadget)
    e4 = st_c2["E"].get(4, 0)
    w3 = st_c2["W"](3)
    f2 = st_c2["F"].get(2, 0)
    e2 = st_c2["E"].get(2, 0)
    aa2 = st_c2["AA"].get(2, 0)
    assert e4 == 7 and w3 == 19 and f2 == 0 and e2 == 1 and aa2 == 1
    assert 3 * e4 - (w3 + 2 * f2) == 2
    assert 3 * e4 == w3 + 2 * aa2
    print(
        f"[4] E-793 REFUTED (minimal pref='AAA', len(tail)={len(gadget)}, r=3): "
        f"E_4={e4}, 3*E_4={3*e4}, W(3)={w3}, F_2={f2}, E_2={e2}, AA_2={aa2}; "
        f"C2 violation = +{3*e4 - w3 - 2*f2}; E-792 exact equality 21 = 19 + 2*1."
    )

    # 5. E-793 REFUTED: Unbounded empty-prefix (n=0, pref='') counterexample family!
    # Start with AAA (gets to h=3, contributes W(3)=9, F_2=1 once),
    # then repeat (return to h=3 via S + gadget) k times!
    # Wait: gadget ends at h=4 after final 'A' (so Fw = 5). To reset to h=3 cleanly, append "SS"!
    # Check: each copy of (gadget + "SS") starts and ends at h=3, never goes below h=0,
    # has F_2 = 0, AA_2 = 1, W(3) = 19, E_4 = 7 -> net +2 to 3*E_4 - W(3) per repeat!
    unit = gadget + "SS"
    print("[5] E-793 REFUTED (unbounded empty-prefix n=0 family, r=3):")
    for k in [1, 5, 6, 10, 20]:
        tail_k = "AAA" + unit * k
        st_k = compute_stats("", tail_k)
        ek = st_k["E"].get(4, 0)
        wk = st_k["W"](3)
        fk = st_k["F"].get(2, 0)
        aak = st_k["AA"].get(2, 0)
        gap_c2 = 3 * ek - (wk + 2 * fk)
        gap_e792 = 3 * ek - (wk + 2 * aak)
        assert fk == 1, f"Expected F_2=1, got {fk}"
        assert ek == 7 * k, f"Expected E_4={7*k}, got {ek}"
        assert wk == 9 + 19 * k, f"Expected W(3)={9+19*k}, got {wk}"
        assert aak == 1 + k, f"Expected AA_2={1+k}, got {aak}"
        assert gap_c2 == 2 * k - 11
        assert gap_e792 == -11
        print(
            f"    k={k:2d} (len={len(tail_k):4d}): E_4={ek:3d}, W(3)={wk:3d}, F_2={fk}, AA_2={aak:2d}, "
            f"3*E_4 - (W(3)+2*F_2) = {gap_c2:+3d}, 3*E_4 - (W(3)+2*AA_2) = {gap_e792:+3d}"
        )
    # Note: for k >= 6, 3*E_4 > W(3) + 2*F_2 on empty prefix n=0, and grows as +2*k -> +infinity!
    print("ALL CHECKS PASSED.")


if __name__ == "__main__":
    main()
