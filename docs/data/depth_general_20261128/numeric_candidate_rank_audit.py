#!/usr/bin/env python3
"""
Falsifier & verification audit for E-802 (Recaman/NumericCandidateRankPotential.lean):
Purely numeric arbitrary-depth candidate-band rank potential (upgrading E-761 to PROVED-LEAN).

Verifies:
  1. Permanent future sign floor: cand_p <= (b + p + 1) + 6 => Fw(t) >= Fw(p) - 1 for all t >= p.
  2. Exact sharpness of +6: for every n >= 2, (b = n-1, val = 2n+7, seen = {0, n+7, 2n+7})
     executes ASSS with cand_0 = n + 7 and Fw(4) = -2.
  3. Exact candidate/area bridge identity at all pairs p <= q.
  4. Bounded candidate-band monotone rank Phi_Y(p) = (Y//3 + 1)*Fw(p) - cand_p//3:
     for all selected A events p < q with b+p+1 >= max(1, Y) and 0 <= cand <= Y:
     Fw(q) >= Fw(p), (Fw(q) == Fw(p) => cand_q + 3 <= cand_p), and Phi_Y(p) + 1 <= Phi_Y(q).
  5. Sharpness of fixed-height count Y//3 + 1 for every Y = 0..40 via (AS)^m A.
  6. Independent all-time fresh-value wallet for fixed (y, k):
     number of A events with cand_p = y and Fw(p) = k is <= max(1, y - 2),
     and <= 1 for y in {0, 1, 2, 3}.
  7. Late-clock same-candidate strict height ascent for b+p+1 >= max(1, y - 6),
     and finite-horizon band cardinality <= (Y//3 + 1) * (Fw(Q) + s.value//(b+1) + 2).
  8. Discovery (canonical a[0..1000] + 50 random states) and Holdout (canonical a[1000..2500]
     + 50 random states) checks.
"""
import random


def run_replay(b: int, val: int, seen_init, steps: int):
    seen = set(seen_init)
    vals = [val]
    signs = []
    fw = [0]
    ar = [0]
    cands = []
    cur = val
    for t in range(steps):
        k = b + t + 1
        c = cur - k
        cands.append(c)
        if c > 0 and c not in seen:
            nxt = c
            sg = False  # S
        else:
            nxt = cur + k
            sg = True   # A
        seen.add(nxt)
        signs.append(sg)
        h = fw[-1] + (1 if sg else -1)
        fw.append(h)
        ar.append(ar[-1] + h)
        vals.append(nxt)
        cur = nxt
    return vals, signs, fw, ar, cands


def check_trace(b: int, val: int, seen_init, steps: int, Y_list):
    vals, signs, fw, ar, cands = run_replay(b, val, seen_init, steps)
    # 0. Positive values for t >= 1
    for t in range(1, steps + 1):
        assert vals[t] >= 1

    # 1. Running minimum positivity bound: Fw(t) >= -(val // (b + 1))
    min_lb = -(val // (b + 1))
    for t in range(steps + 1):
        assert fw[t] >= min_lb, f"min_lb failed at t={t}: {fw[t]} < {min_lb}"

    # 2. Permanent future sign floor & bridge identity
    for p in range(steps):
        if signs[p] and cands[p] <= (b + p + 1) + 6:
            for t in range(p, steps + 1):
                assert fw[t] >= fw[p] - 1, f"floor failed at p={p}, t={t}"
    for p in range(0, steps, max(1, steps // 20)):
        for q in range(p, steps, max(1, steps // 20)):
            lhs = (ar[q] - q * (fw[p] - 1)) - (ar[p] - p * (fw[p] - 1))
            rhs = (b + q + 1) * (fw[q] - fw[p]) + cands[p] - cands[q]
            assert lhs == rhs, f"bridge mismatch at p={p}, q={q}: {lhs} != {rhs}"

    # 3. Monotone rank Phi_Y and finite-horizon cardinality
    for Y in Y_list:
        K = Y // 3 + 1
        sel = [p for p in range(steps) if signs[p] and b + p + 1 >= max(1, Y) and 0 <= cands[p] <= Y]
        for idx in range(len(sel) - 1):
            p, q = sel[idx], sel[idx + 1]
            assert fw[q] >= fw[p]
            if fw[q] == fw[p]:
                assert cands[q] + 3 <= cands[p]
            phi_p = K * fw[p] - (cands[p] // 3)
            phi_q = K * fw[q] - (cands[q] // 3)
            assert phi_p + 1 <= phi_q
        cap = K * (fw[steps] + (val // (b + 1)) + 2)
        assert len(sel) <= cap, f"horizon cap failed: {len(sel)} > {cap}"

    # 4. All-time fresh-value wallet for fixed (y, k) & late-clock strict ascent
    groups = {}
    for p in range(steps):
        if signs[p] and cands[p] >= 0:
            groups.setdefault((cands[p], fw[p]), []).append(p)
    for (y, k), ps in groups.items():
        bound = max(1, y - 2)
        assert len(ps) <= bound, f"wallet failed at y={y}, k={k}: {len(ps)} > {bound}"
        # Late-clock strict ascent: at most 1 event with b+p+1 >= max(1, y - 6)
        late = [p for p in ps if b + p + 1 >= max(1, y - 6)]
        assert len(late) <= 1, f"late same-cand failed at y={y}, k={k}: {late}"

    return len(groups)


def test_sharpness():
    # Sharpness of +6 floor threshold for n = 2..30
    for n in range(2, 31):
        b = n - 1
        val = 2 * n + 7
        seen = [0, n + 7, 2 * n + 7]
        vals, signs, fw, ar, cands = run_replay(b, val, seen, 4)
        assert signs == [True, False, False, False], f"ASSS failed at n={n}: {signs}"
        assert cands[0] == n + 7
        assert vals == [2 * n + 7, 3 * n + 7, 2 * n + 6, n + 4, 1]
        assert fw[4] == -2
    print("[PASS] Permanent floor +6 sharpness verified for n = 2..30 (ASSS hits Fw = -2).")

    # Sharpness of fixed-height count Y//3 + 1 for Y = 0..40
    for Y in range(41):
        m = Y // 3
        n = Y + 2
        b = n - 1
        val = 2 * Y + 2
        seen = [0, val] + [Y - 3 * j for j in range(m + 1)]
        steps = 2 * m + 1
        vals, signs, fw, ar, cands = run_replay(b, val, seen, steps)
        expected_signs = [True, False] * m + [True]
        assert signs == expected_signs, f"(AS)^m A failed at Y={Y}: {signs}"
        sel = [p for p in range(steps) if signs[p] and b + p + 1 >= max(1, Y) and 0 <= cands[p] <= Y]
        assert len(sel) == m + 1
        assert all(fw[p] == 0 for p in sel)
        assert [cands[p] for p in sel] == [Y - 3 * j for j in range(m + 1)]
    print("[PASS] Fixed-height count sharpness (Y//3 + 1 events at H = 0) verified for Y = 0..40.")

    # Negative control: without late-clock restriction, same y can repeat at same height (y >= 4)
    # Example: y = 4, b = 0, val = 5, seen = {0, 4, 5}:
    # t=0 (k=1): cand=4 in seen -> A, val=6 (H=1)
    # Check small search for y=4 repeating twice at H=0:
    # A(H:0->1) S(1->0) S(0->-1) S(-1->-2)? Wait: for M=2 at y=4, X_v in {1} => X_v=1!
    # Try (b, val, seen) with ASSA? H: 0,1,0,-1,0 -> Ar(4) = 1+0-1+0 = 0, mean = 0 != -1!
    # For bridge of mean -1 starting at H=0: A(1), S(0), S(-1), S(-2), S(-3), A(-2), A(-1), A(0) -> Ar = 1+0-1-2-3-2-1+0 = -8 = 8*(-1)!
    # At v=3 (H=-1): sum_{1..3}(H_i - (-1)) = 2 + 1 + 0 = 3 => X_3 = y - 3 = 1!
    # Check: b=0, val=5 (c_0 = 4), seen={0, 4, 5}, steps=9? Wait: X_4 = 1 - 4 = -3 (negative!).
    # So to stay positive at H=-3, need b large enough? No: X_3 = 1 => X_4 = 1 - (b+4) < 0!
    # Ah! At H=-1 we need X_v = 1 and next step to go to -2, which needs X_v > b + v + 1 >= 4!
    # Wait: that means for y <= 6, wallet is EVEN tighter? Let's test y = 10:
    # ASSSAA -> H: 0,1,0,-1,-2,-1,0? Ar = 1+0-1-2-1+0 = -3 != -6.
    # A S S S S A A A (len 8, H: 1,0,-1,-2,-3,-2,-1,0, Ar = -8) needs X_3 = y - 3, X_4 = y - 3 - (b+4), X_5 = y - 3 - (b+4) - (b+5) >= 1 => y >= 2b + 13!
    # At b=0, y=13: val = 14, seen = {0, 13, 14}! Let's test!
    vals, signs, fw, ar, cands = run_replay(0, 14, [0, 13, 14], 9)
    # Wait: step 0 (k=1): 14-1=13 in seen -> A (15), step 1 (k=2): 13 in seen -> A (17)! Oh, step 1 cand is 15-2=13!
    # Need b=1 or custom blockers to hit exact ASSSSAAAA:
    vals2, signs2, fw2, ar2, cands2 = run_replay(0, 20, [0, 19, 20], 10)
    # Just confirm canonical orbit has repeated same-(y, k) events (proving bound M >= 2 is non-vacuous!)
    vals_c, signs_c, fw_c, ar_c, cands_c = run_replay(0, 0, [0], 2500)
    groups = {}
    for p in range(2500):
        if signs_c[p] and cands_c[p] >= 0:
            groups.setdefault((cands_c[p], fw_c[p]), []).append(p)
    max_mult = max((len(v) for v in groups.values()), default=0)
    assert max_mult >= 2, "Expected canonical orbit to have repeated (y, k) A events"
    print(f"[PASS] Non-vacuity control: canonical a[0..2500] has max same-(y,k) multiplicity = {max_mult} (>= 2).")


def main():
    test_sharpness()

    # Discovery: canonical a[0..1000] + 50 random states
    check_trace(0, 0, [0], 1000, [0, 1, 2, 3, 5, 10, 25, 100])
    rng = random.Random(20261128)
    for idx in range(50):
        b = rng.randint(0, 80)
        val = rng.randint(0, 300)
        seen = [rng.randint(0, 400) for _ in range(rng.randint(0, 25))]
        check_trace(b, val, seen, 120, [0, 3, 12, 40])
    print("[PASS] Discovery: canonical a[0..1000] + 50 arbitrary (including incoherent) states passed.")

    # Holdout: canonical a[0..2500] + 50 random states with different seed
    check_trace(0, 0, [0], 2500, [0, 4, 9, 20, 60, 200])
    rng2 = random.Random(20261129)
    for idx in range(50):
        b = rng2.randint(0, 150)
        val = rng2.randint(0, 500)
        seen = [rng2.randint(0, 600) for _ in range(rng2.randint(0, 30))]
        check_trace(b, val, seen, 120, [0, 2, 7, 30, 80])
    print("[PASS] Holdout: canonical a[0..2500] + 50 arbitrary states passed.")
    print("ALL E-802 AUDITS PASSED.")


if __name__ == "__main__":
    main()
