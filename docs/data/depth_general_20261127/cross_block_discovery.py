#!/usr/bin/env python3
"""Discovery falsifier for H-20261127-01 (cross-block charging after E-776).

Checks exact Win(u, q-u) for u >= c on post-cut words V_1 ... V_R AA,
and verifies against full word U S^m V_1 ... V_R AA from origin 0.
"""
import itertools
import time

def build_block(a_list):
    """Build V_i = prod_{h=0..H} ((AS)^(a_h - 1) A) S^(H+1). 'A'=+1, 'S'=-1."""
    H = len(a_list) - 1
    out = []
    for a in a_list:
        for _ in range(a - 1):
            out.append(1)   # A
            out.append(-1)  # S
        out.append(1)       # A
    out.extend([-1] * (H + 1))
    return out

def analyze_full_word(U_signs, blocks):
    """Compute exact origin-0 Fw, Ar, Win, EndN, F, O_c, L, A_after_cut."""
    max_H = max(len(b) - 1 for b in blocks)
    m = max_H + 2
    c = len(U_signs) + m
    W = list(U_signs) + [-1] * m
    for blk in blocks:
        W.extend(build_block(blk))
    W.extend([1, 1])  # trailing AA

    Q = len(W)
    H = [0] * (Q + 1)
    B = [0] * (Q + 1)
    for i, s in enumerate(W):
        H[i + 1] = H[i] + s
        B[i + 1] = B[i] + H[i + 1]

    # Pre-index clocks by height h and invariant Phi_h(t) = B[t] - t * h
    # Win(u, q-u) <=> u < q, H[q] = H[u] + 1, and B[q] - B[u] = (q - u) * H[u]
    # i.e. Phi_{H[u]}(q) == Phi_{H[u]}(u).
    # We track earliest and latest source clocks per (h, phi).
    seen_all = {}       # (h, phi) -> list of u
    seen_internal = {}  # (h, phi) -> list of u >= c

    A_after = 0
    L = 0
    O_c = 0
    F = 0
    cross_hits = 0

    # Also track block boundaries for diagnostics
    block_starts = []
    pos = c
    for blk in blocks:
        block_starts.append(pos)
        pos += sum(2 * a - 1 for a in blk) + len(blk)
    tail_aa_start = pos

    def blk_of(idx):
        if idx < c:
            return -1
        if idx >= tail_aa_start:
            return len(blocks)
        for bi in range(len(blocks) - 1, -1, -1):
            if idx >= block_starts[bi]:
                return bi
        return -1

    for t in range(Q):
        if t >= c and W[t] == 1:
            A_after += 1
            h_src = H[t] - 1
            phi = B[t] - t * h_src
            int_srcs = seen_internal.get((h_src, phi))
            all_srcs = seen_all.get((h_src, phi))
            if int_srcs:
                L += 1
                bi = blk_of(t)
                if any(blk_of(u) < bi for u in int_srcs):
                    cross_hits += 1
            elif all_srcs:
                O_c += 1
            else:
                F += 1
        # Record clock t as a potential future source at height H[t]
        h_t = H[t]
        phi_t = B[t] - t * h_t
        seen_all.setdefault((h_t, phi_t), []).append(t)
        if t >= c:
            seen_internal.setdefault((h_t, phi_t), []).append(t)

    # Slack of candidate 2A <= 3(F + O_c) - 3, i.e. A - 3L - 3 >= 0
    slack = 3 * (F + O_c) - 3 - 2 * A_after
    assert slack == A_after - 3 * L - 3
    return {
        "A": A_after, "L": L, "O_c": O_c, "F": F,
        "slack": slack, "cross_hits": cross_hits,
    }

def main():
    t0 = time.process_time()
    best_slack = 10**9
    best_case = None
    counters = []

    # 1. Exhaustive R=2, H1, H2 in {2, 3}, a in {1, 2, 3}
    tested = 0
    for H1 in (2, 3):
        for H2 in (2, 3):
            vals = (1, 2, 3) if (H1 == 2 and H2 == 2) else (1, 2)
            for b1 in itertools.product(vals, repeat=H1 + 1):
                for b2 in itertools.product(vals, repeat=H2 + 1):
                    res = analyze_full_word([], [b1, b2])
                    tested += 1
                    if res["slack"] < best_slack:
                        best_slack = res["slack"]
                        best_case = ([b1, b2], res)
                    if res["slack"] < 0 and len(counters) < 10:
                        counters.append(([b1, b2], res))
    print(f"[Exhaustive R=2] tested={tested}, best_slack={best_slack}, counters={len(counters)}")
    print(f"  best={best_case}")
    for c in counters[:5]:
        print(f"  COUNTER: {c}")

    # 2. Targeted sharp ASAA repeats: V = (2,1)^n ++ [1] repeated R times
    print("\n[Sharp ASAA repeats]")
    for n in (1, 2, 3, 4):
        blk = [2, 1] * n + [1]
        for R in (1, 2, 3, 4, 5):
            res = analyze_full_word([], [blk] * R)
            print(f"  n={n}, R={R}: A={res['A']}, L={res['L']}, F={res['F']}, O_c={res['O_c']}, slack={res['slack']}, cross={res['cross_hits']}")

    # 3. Targeted large-bank V1 followed by small/tailored V2..VR
    print("\n[Large V1 bank + small V2..VR]")
    for H1 in (2, 3, 4):
        for a10 in (2, 4, 6, 8, 12):
            b1 = [a10] + [1] * H1
            for b2 in ([1, 1, 1], [1, 1, 2], [2, 1, 1], [1, 2, 1], [2, 1, 2], [1, 1, 1, 1], [2, 1, 2, 1]):
                for R2 in (1, 2, 3, 5):
                    blocks = [b1] + [b2] * R2
                    res = analyze_full_word([], blocks)
                    if res["slack"] <= 0:
                        print(f"  HIT blocks=[{b1}]+[{b2}]*{R2}: {res}")

    # 4. Random / structured search over R=2..6, H=2..5, a in 1..8
    import random
    rng = random.Random(20261127)
    min_ratio = 10.0
    min_r_case = None
    neg_found = []
    for _ in range(5000):
        R = rng.choice([2, 3, 4, 5, 6])
        blocks = []
        for _ in range(R):
            H = rng.choice([2, 3, 4, 5])
            blk = [rng.choice([1, 1, 2, 2, 3, 4, 6, 8]) for _ in range(H + 1)]
            blocks.append(blk)
        res = analyze_full_word([], blocks)
        ratio = res["A"] / (res["F"] + res["O_c"])
        if res["slack"] < 0:
            neg_found.append((blocks, res))
        if ratio > 0 and (res["F"] + res["O_c"]) / res["A"] < min_ratio:
            min_ratio = (res["F"] + res["O_c"]) / res["A"]
            min_r_case = (blocks, res)
    print(f"\n[Random 5000] neg_found={len(neg_found)}, min (F+O_c)/A = {min_ratio:.6f} (max A/(F+O_c) = {1/min_ratio:.6f})")
    print(f"  worst_ratio_case={min_r_case}")
    for c in neg_found[:5]:
        print(f"  NEG: {c}")

    print(f"\nElapsed CPU: {time.process_time() - t0:.4f}s")

if __name__ == "__main__":
    main()
