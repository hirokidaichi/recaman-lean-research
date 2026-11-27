#!/usr/bin/env python3
"""Audit of spatial visited-inventory canonical invariants (Track 2 / H-20261127-02).

1. Verifies the 4 new canonical spatial invariants on actual Recaman a(0..5000),
   splitting discovery [0..1000] and holdout [1001..5000].
2. Demonstrates that H-20261126-02's literal step-b bridge grid FAILS the
   tail-cardinality-above-gap and descending gap-rank canonical invariants.
3. Verifies our margin-buffered step-d bridge grid (d = b - 200*N) passes ALL 8
   canonical necessary filters + exact greedy replay on discovery (lengths 0..5)
   and holdout (lengths 6..7 + sharp staged words).
"""
import itertools
import time

def recaman_prefix(B):
    a = [0]
    seen = {0}
    for n in range(1, B + 1):
        cand = a[-1] - n
        if cand > 0 and cand not in seen:
            nxt = cand
        else:
            nxt = a[-1] + n
        a.append(nxt)
        seen.add(nxt)
    return a

def upper_tri(n):
    return n * (n + 1) // 2

def audit_canonical_invariants(B_lo, B_hi, a):
    """Check all 4 new canonical spatial invariants on b in [B_lo, B_hi]."""
    sharp_peak = []
    sharp_tail_cnt = []
    sharp_gap_rank = []
    for b in range(B_lo, B_hi + 1):
        xb = a[b]
        ut_b = upper_tri(b)
        V = sorted(set(a[:b + 1]))
        M = V[-1]
        # 1. Walk-length peak bound: 2*M <= xb + upperTri(b)
        assert 2 * M <= xb + ut_b, f"Peak bound failed at b={b}"
        if 2 * M == xb + ut_b and b >= 1:
            sharp_peak.append(b)
        # Adjacent gaps (lo, hi) with g = hi - lo >= 2 (strictly empty open interval)
        gaps = []
        for idx in range(len(V) - 1):
            lo, hi = V[idx], V[idx + 1]
            g = hi - lo
            gaps.append((g, lo, hi, len(V) - 1 - idx))  # tail_cnt = #{v in V : v >= hi}
            # 2. Adjacent gap <= b (for b >= 1; for b=0 no gaps)
            assert g <= b, f"Gap > b at b={b}: ({lo}, {hi})"
            # 3. Tail cardinality above gap: #{v in V : v >= hi} <= b - g + 1
            tail_cnt = len(V) - 1 - idx
            assert tail_cnt <= b - g + 1, f"Tail count failed at b={b}, g={g}: {tail_cnt} > {b-g+1}"
            if g >= 2 and tail_cnt == b - g + 1:
                sharp_tail_cnt.append((b, g, lo, hi, tail_cnt))
            # 4. Tail peak bound above gap: 2*M <= xb + lo + upperTri(b) - upperTri(g - 1)
            rhs = xb + lo + ut_b - upper_tri(g - 1)
            assert 2 * M <= rhs, f"Tail peak failed at b={b}, g={g}: 2*{M} > {rhs}"
        # 5. Descending gap-rank: k-th largest gap (1-indexed) <= b + 1 - k
        g_sorted = sorted((g for g, _, _, _ in gaps), reverse=True)
        for k, g in enumerate(g_sorted, start=1):
            assert g <= b + 1 - k, f"Gap rank failed at b={b}, k={k}: g={g} > {b+1-k}"
            if g >= 2 and g == b + 1 - k:
                sharp_gap_rank.append((b, k, g))
    return sharp_peak, sharp_tail_cnt, sharp_gap_rank

def check_e759_word(W):
    Q = len(W)
    H = [0] * (Q + 1)
    B = [0] * (Q + 1)
    for i, s in enumerate(W):
        H[i + 1] = H[i] + s
        B[i + 1] = B[i] + H[i + 1]
    out_pairs = {(0, 0)}
    cand_pairs = set()
    for i in range(Q):
        v = i + 1
        if W[i] == -1:
            hv = H[v]
            key = (hv, B[v] - v * hv)
            if key in out_pairs or key in cand_pairs:
                return False
        else:
            hc = H[i] - 1
            cand_pairs.add((hc, B[i] - i * hc))
        out_pairs.add((H[v], B[v] - v * H[v]))
    return True

def original_free_candidates(W):
    """Return list of affine pairs (h, k) for original free A clocks in W.
    Candidate at clock q (W[q]==1) is C_q = x + b*(H[q]-1) + ((q+1)*(H[q]-1) - B[q]).
    """
    Q = len(W)
    H = [0] * (Q + 1)
    B = [0] * (Q + 1)
    for i, s in enumerate(W):
        H[i + 1] = H[i] + s
        B[i + 1] = B[i] + H[i + 1]
    seen_src = {}
    free_pairs = set()
    s_landings = []
    for q in range(Q):
        if W[q] == 1:
            h_src = H[q] - 1
            phi = B[q] - q * h_src
            if (h_src, phi) not in seen_src:
                # C_q = x + (b + q + 1)*(H[q] - 1) - B[q] = x + b*h_src + ((q+1)*h_src - B[q])
                free_pairs.add((h_src, (q + 1) * h_src - B[q]))
        else:
            v = q + 1
            s_landings.append((H[v], (v) * H[v] - B[v]))  # wait: X_v = x + (b + v + 1)*H[v] - B[v]?
        seen_src.setdefault((H[q], B[q] - q * H[q]), []).append(q)
    return H, B, free_pairs

def build_and_verify_bridge(W, step_mode="step_d"):
    """Construct compact representation of V = [0, L] union T (where T is sorted list > L)
    and verify ALL 8 canonical filters AND exact greedy replay of W!
    """
    Q = len(W)
    N = Q + 1
    b = 1000 * N * N
    x = 100 * (b + N) * N

    # Exact values X_i (0..Q) and C_q (0..Q-1 for W[q]==1)
    X = [x]
    for i, s in enumerate(W):
        X.append(X[-1] + s * (b + i + 1))

    # Original free A clocks
    H = [0] * (Q + 1)
    B = [0] * (Q + 1)
    for i, s in enumerate(W):
        H[i + 1] = H[i] + s
        B[i + 1] = B[i] + H[i + 1]
    seen_src = set()
    T0_set = {x}
    s_vals = set()
    for q in range(Q):
        if W[q] == 1:
            h_src = H[q] - 1
            phi = B[q] - q * h_src
            if (h_src, phi) not in seen_src:
                T0_set.add(X[q] - (b + q + 1))
        else:
            s_vals.add(X[q + 1])
        seen_src.add((H[q], B[q] - q * H[q]))

    M = max(T0_set)
    if step_mode == "step_b":
        d = b
    elif step_mode == "step_d":
        d = b - 200 * N
    else:
        raise ValueError(step_mode)

    # Pick delta in {1..N} avoiding residues of s_vals modulo d
    bad_res = {v % d for v in s_vals}
    delta = None
    for cand in range(1, N + 1):
        if (b + cand) % d not in bad_res:
            delta = cand
            break
    assert delta is not None, "No residue-avoiding delta found!"

    # Bridge grid G = {b + delta + j*d : j >= 0, <= M}
    G = []
    val = b + delta
    while val <= M:
        G.append(val)
        val += d

    T = sorted(T0_set | set(G))
    assert T[0] > b // 2, f"T[0] too small: {T[0]} vs {b//2}"
    L = b // 2 - len(T)
    assert L >= 0, f"L < 0: {L}"
    assert T[0] > L, f"Overlap between [0,L] and T: L={L}, T[0]={T[0]}"

    # Exact cardinality |V| = (L + 1) + |T| = b/2 + 1
    card_V = (L + 1) + len(T)
    assert card_V == b // 2 + 1
    ut_b = upper_tri(b)

    # Check ALL 8 filters!
    f1_card = (card_V <= b + 1)
    f2_parity = (x % 2 == ut_b % 2)
    f3_range = (0 <= T[0] and T[-1] <= ut_b)
    s_cov = card_V - 1
    f4_sorted_cover = (ut_b <= x + s_cov * (2 * b - s_cov + 1))
    f5_peak = (2 * T[-1] <= x + ut_b)

    # All non-unit adjacent gaps in V = [0..L] union T:
    # Gap 0: (L, T[0]), followed by (T[i], T[i+1]) for i = 0..len(T)-2
    gaps = [(T[0] - L, L, T[0], len(T))]
    for i in range(len(T) - 1):
        gaps.append((T[i + 1] - T[i], T[i], T[i + 1], len(T) - 1 - i))

    f6_adj_le_b = all(g <= b for g, _, _, _ in gaps)
    # Filter 7: descending gap-rank g_(k) <= b + 1 - k
    g_desc = sorted((g for g, _, _, _ in gaps), reverse=True)
    f7_gap_rank = all(g <= b + 1 - k for k, g in enumerate(g_desc, start=1))
    # Filter 8: tail-count and tail-peak above EVERY gap
    f8_tail_cnt = all(tc <= b - g + 1 for g, lo, hi, tc in gaps)
    f8_tail_peak = all(2 * T[-1] <= x + lo + ut_b - upper_tri(g - 1) for g, lo, hi, tc in gaps)

    # Exact greedy replay using compact membership: v in V <=> (0 <= v <= L) or (v in T_set)
    T_set = set(T)
    cur = x
    replay_ok = True
    for i, expected_s in enumerate(W):
        step_k = b + i + 1
        cand = cur - step_k
        in_seen = (0 <= cand <= L) or (cand in T_set)
        if cand > 0 and not in_seen:
            actual_s = -1
            cur = cand
        else:
            actual_s = 1
            cur = cur + step_k
        if actual_s != expected_s:
            replay_ok = False
            break
        if cur > L:
            T_set.add(cur)

    return {
        "N": N, "b": b, "d": d, "L": L, "len_T": len(T), "delta": delta,
        "f1": f1_card, "f2": f2_parity, "f3": f3_range, "f4": f4_sorted_cover,
        "f5_peak": f5_peak, "f6_adj_b": f6_adj_le_b,
        "f7_gap_rank": f7_gap_rank, "f8_tail_cnt": f8_tail_cnt, "f8_tail_peak": f8_tail_peak,
        "replay_ok": replay_ok,
    }

def main():
    t0 = time.process_time()
    a = recaman_prefix(5000)
    sp_d, st_d, sg_d = audit_canonical_invariants(0, 1000, a)
    sp_h, st_h, sg_h = audit_canonical_invariants(1001, 5000, a)
    print(f"[Canonical invariants discovery 0..1000] PASS! sharp_peak={sp_d[:10]} (total {len(sp_d)}), sharp_tail_cnt={len(st_d)}, sharp_gap_rank={len(sg_d)}")
    print(f"  sample sharp tail_cnt (b,g,lo,hi,tc): {st_d[:6]}")
    print(f"  sample sharp gap_rank (b,k,g): {sg_d[:6]}")
    print(f"[Canonical invariants holdout 1001..5000] PASS! sharp_peak={len(sp_h)}, sharp_tail_cnt={len(st_h)}, sharp_gap_rank={len(sg_h)}")

    # Compare step_b (H-20261126-02 literal) vs step_d (our strengthened grid)
    print("\n[Comparing literal step_b vs strengthened step_d on sample coherent words]")
    for name, W in [("empty", []), ("A", [1]), ("S", [-1]), ("SSAAA", [-1,-1,1,1,1]), ("E777_n2", [-1]*6 + [1,-1,1,1,1,-1,1,1,1] + [-1]*5 + [1,1])]:
        rb = build_and_verify_bridge(W, "step_b")
        rd = build_and_verify_bridge(W, "step_d")
        print(f"  {name:8s} step_b: f6={rb['f6_adj_b']} f7_rank={rb['f7_gap_rank']} f8_tc={rb['f8_tail_cnt']} f8_tp={rb['f8_tail_peak']} replay={rb['replay_ok']}")
        print(f"  {name:8s} step_d: f1..4={all([rd['f1'],rd['f2'],rd['f3'],rd['f4']])} f5={rd['f5_peak']} f6={rd['f6_adj_b']} f7={rd['f7_gap_rank']} f8_tc={rd['f8_tail_cnt']} f8_tp={rd['f8_tail_peak']} replay={rd['replay_ok']}")

    # Exhaustive discovery lengths 0..5 (63 words)
    disc_adm = 0
    disc_bad = 0
    for Q in range(0, 6):
        for W in itertools.product((-1, 1), repeat=Q):
            adm = check_e759_word(W)
            rd = build_and_verify_bridge(W, "step_d")
            assert all([rd['f1'], rd['f2'], rd['f3'], rd['f4'], rd['f5_peak'], rd['f6_adj_b'], rd['f7_gap_rank'], rd['f8_tail_cnt'], rd['f8_tail_peak']]), f"Filter failed on {W}: {rd}"
            assert rd['replay_ok'] == adm, f"Replay mismatch on {W}: adm={adm}, rd={rd}"
            if adm: disc_adm += 1
            else: disc_bad += 1
    print(f"\n[Discovery lengths 0..5] 63 words: adm={disc_adm}, non_adm={disc_bad}, ALL 8 filters & exact replay match!")

    # Exhaustive holdout lengths 6..7 (192 words)
    hold_adm = 0
    hold_bad = 0
    for Q in (6, 7):
        for W in itertools.product((-1, 1), repeat=Q):
            adm = check_e759_word(W)
            rd = build_and_verify_bridge(W, "step_d")
            assert all([rd['f1'], rd['f2'], rd['f3'], rd['f4'], rd['f5_peak'], rd['f6_adj_b'], rd['f7_gap_rank'], rd['f8_tail_cnt'], rd['f8_tail_peak']]), f"Holdout filter failed on {W}: {rd}"
            assert rd['replay_ok'] == adm, f"Holdout replay mismatch on {W}"
            if adm: hold_adm += 1
            else: hold_bad += 1
    print(f"[Holdout lengths 6..7] 192 words: adm={hold_adm}, non_adm={hold_bad}, ALL 8 filters & exact replay match!")
    print(f"Elapsed CPU: {time.process_time() - t0:.4f}s")

if __name__ == "__main__":
    main()
