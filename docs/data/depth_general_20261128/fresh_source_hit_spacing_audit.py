#!/usr/bin/env python3
"""
Falsifier & verification audit for E-804 (Recaman/FreshSourceHitSpacing.lean):
Fresh same-source hit spacing (upgrading E-760 + E-761's source-clock consumer to PROVED-LEAN).

Verifies:
  1. Exhaustive classification of all 35 balanced length-8 words starting with A:
     unique area -8 word is Z = ASSSSAAA.
  2. Z ++ Z fails TypeIFresh at (phase 3, phase 11) for every b, s (even incoherent!).
  3. On any actual greedy replay (including canonical a[0..3000]), any ordered list of M >= 1
     A hits sharing one unchanged original Win source s obeys:
       last_hit - first_hit >= 8*(M - 1) + 4*((M - 1) // 2) = 10*(M - 1) - 2*((M - 1) % 2),
     and if M >= 2, with a = b + s and y = value(b, s, s):
       10*(M - 2) - 2*((M - 2) % 2) <= y - a - 11
     (so y < a + 11 => M <= 1, otherwise M <= 2 + (y - a - 9) // 10).
  4. Raw non-fresh negative control: SSAA Z^M A (M = 2..6) has positive supplied deficit on
     every nonempty prefix, all boundary hits 4 + 8j sharing original Win source s = 1,
     yet span = 8*M < 10*M - 2*(M % 2) (at M = 2: 3 hits at 4, 12, 20 with span 16 < 20),
     confirming that S-freshness is strictly necessary!
"""
import itertools
import random


def word_mass_area(w):
    h = 0
    ar = 0
    for c in w:
        h += 1 if c == "A" else -1
        ar += h
    return h, ar


def run_replay(b: int, val: int, seen_init, steps: int):
    seen = set(seen_init)
    vals = [val]
    signs = []
    fw = [0]
    ar = [0]
    cur = val
    for t in range(steps):
        k = b + t + 1
        c = cur - k
        if c > 0 and c not in seen:
            nxt = c
            sg = False
        else:
            nxt = cur + k
            sg = True
        seen.add(nxt)
        signs.append(sg)
        h = fw[-1] + (1 if sg else -1)
        fw.append(h)
        ar.append(ar[-1] + h)
        vals.append(nxt)
        cur = nxt
    return vals, signs, fw, ar


def check_win(fw, ar, s, p):
    if p <= s:
        return False
    # Win f s (p - s): fw[p] = fw[s] + 1 and ar[p] - ar[s] = (p - s) * fw[s]
    return fw[p] == fw[s] + 1 and (ar[p] - ar[s]) == (p - s) * fw[s]


def test_unique_gap8_and_negative_control():
    # 1. Exhaustive 35 balanced length-8 words starting with A
    bal = []
    min_area_words = []
    for rest in itertools.combinations(range(1, 8), 3):
        w = ["S"] * 8
        w[0] = "A"
        for idx in rest:
            w[idx] = "A"
        ws = "".join(w)
        h, area = word_mass_area(ws)
        assert h == 0
        bal.append((ws, area))
        if area <= -8:
            min_area_words.append((ws, area))
    assert len(bal) == 35
    assert min_area_words == [("ASSSSAAA", -8)], f"Unexpected min-area words: {min_area_words}"
    print("[PASS] Exhaustive 35 balanced len-8 first-A words: unique area -8 word is Z = ASSSSAAA.")

    # 2. Raw non-fresh negative control: SSAA Z^M A for M = 2..6
    Z = "ASSSSAAA"
    for M in range(2, 7):
        w = "SSAA" + Z * M + "A"
        fw = [0]
        ar = [0]
        for c in w:
            h = fw[-1] + (1 if c == "A" else -1)
            fw.append(h)
            ar.append(ar[-1] + h)
        # All heights <= 1 (and positive supplied deficit on every nonempty prefix)
        assert max(fw) <= 1
        hits = [4 + 8 * j for j in range(M + 1)]
        for p in hits:
            assert w[p] == "A"
            assert check_win(fw, ar, 1, p), f"Win(1, {p}-1) failed for M={M}"
        span = hits[-1] - hits[0]
        fresh_lb = 8 * M + 4 * (M // 2)
        assert span == 8 * M < fresh_lb
        # Check exact Type-I collision at phase 3 vs phase 11 (indices 7 vs 15, both S landings at H=-1)
        assert w[6] == "S" and w[14] == "S"
        assert fw[7] == -1 and fw[15] == -1
        # floorPotential at m = -2 is ar[t] - t * (-1) = ar[t] + t
        assert ar[7] + 7 == ar[15] + 15
    print("[PASS] Negative control SSAA Z^M A (M=2..6): raw Win(1) hits beat 10n-2(n%2) via Type-I collision at 7 vs 15.")


def check_replay_sources(b: int, val: int, seen_init, steps: int):
    vals, signs, fw, ar = run_replay(b, val, seen_init, steps)
    # Group hits by (fw[s], pot_s) where pot_s = ar[s] - s * fw[s]
    # Note Win(s, p - s) iff fw[p] == fw[s] + 1 and ar[p] - p * fw[s] == ar[s] - s * fw[s]
    # Wait: ar[p] - ar[s] = (p - s) * fw[s] <=> ar[p] - p * fw[s] = ar[s] - s * fw[s]!
    by_key = {}
    for p in range(steps):
        if signs[p]:
            h_src = fw[p] - 1
            key = (h_src, ar[p] - p * h_src)
            by_key.setdefault(key, []).append(p)
    checked_sources = 0
    multi_sources = 0
    for s in range(steps):
        key = (fw[s], ar[s] - s * fw[s])
        hits = [p for p in by_key.get(key, []) if p > s]
        if not hits:
            continue
        checked_sources += 1
        M = len(hits)
        n = M - 1
        span = hits[-1] - hits[0]
        lb = 8 * n + 4 * (n // 2)
        assert span >= lb, f"Spacing failed at s={s}: {span} < {lb}"
        if M >= 2:
            multi_sources += 1
            a_src = b + s
            y_src = vals[s]
            k = M - 2
            # Note: every nonfinal hit has b + p + 1 <= y_src - 7, and first hit has p >= s + 3 (n_1 >= a + 4)
            assert hits[0] >= s + 3
            assert b + hits[-2] + 1 <= y_src - 7
            assert 8 * k + 4 * (k // 2) <= y_src - a_src - 11
            assert y_src >= a_src + 11
            assert M <= 2 + (y_src - a_src - 9) // 10
    return checked_sources, multi_sources


def main():
    test_unique_gap8_and_negative_control()

    # Discovery: canonical a[0..1500] + 40 random states
    cs, ms = check_replay_sources(0, 0, [0], 1500)
    rng = random.Random(20261128)
    for _ in range(40):
        b = rng.randint(0, 40)
        val = rng.randint(0, 300)
        seen = [rng.randint(0, 400) for _ in range(rng.randint(0, 20))]
        c2, m2 = check_replay_sources(b, val, seen, 150)
        cs += c2; ms += m2
    print(f"[PASS] Discovery: {cs} active Win sources ({ms} with M >= 2 hits) passed spacing + clock capacity.")

    # Holdout: canonical a[0..3000] + 40 random states
    cs2, ms2 = check_replay_sources(0, 0, [0], 3000)
    rng2 = random.Random(20261129)
    for _ in range(40):
        b = rng2.randint(0, 80)
        val = rng2.randint(0, 500)
        seen = [rng2.randint(0, 600) for _ in range(rng2.randint(0, 25))]
        c2, m2 = check_replay_sources(b, val, seen, 150)
        cs2 += c2; ms2 += m2
    print(f"[PASS] Holdout: {cs2} active Win sources ({ms2} with M >= 2 hits) passed spacing + clock capacity.")
    print("ALL E-804 AUDITS PASSED.")


if __name__ == "__main__":
    main()
