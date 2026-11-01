#!/usr/bin/env python3
"""H-20260917-01 baseline regression/discovery probe v2, 2026-09-20.

The first p=1..15 attempt used 1 <= d < p(p+1) and timed out; its empty log is not
evidence.  This corrected recovery probe uses 1 <= d <= p(p+1); the recorded run
exhausts p=1..11.  It retains full U, checks Hall over every subset, enumerates tight
B for Q and local W, and replays fixed controls.  It is diagnostic: violation counters
do not change exit status.  This is not the p=32,33 holdout and finite output is not a
proof or an automated acceptance gate.
"""

import sys
from itertools import product

DONORS = [
    "AAASSSASASA", "ASAAASSSASA", "ASASAAASSSA", "ASSAAAASSAS",
    "ASSAAASAASS", "SAAASAASSSA", "SAAASSAAASS",
]
W1 = "SAAAASS"


def past(word, u, d):
    p = len(word)
    return "".join(word[(u - k) % p] for k in range(1, d + 1))


def p2(window):
    vals = [1 if c == "A" else -1 for c in window]
    return sum(vals) == 1 and sum((k + 1) * v for k, v in enumerate(vals)) == 0


def ss_count(window):
    return sum(window[k] == window[k + 1] == "S" for k in range(len(window) - 1))


def least_supply(word, u):
    p = len(word)
    for d in range(1, p * (p + 1) + 1):
        w = past(word, u, d)
        if p2(w):
            cover = {(u - k) % p for k, c in enumerate(w, 1) if c == "S"}
            oldest_offset = max(k for k, c in enumerate(w, 1) if c == "S")
            return d, w, cover, (u - oldest_offset) % p, oldest_offset
    return None


def full_u(word):
    out = {}
    for u, c in enumerate(word):
        if c == "A":
            supply = least_supply(word, u)
            if supply:
                out[u] = supply
    return out


def masks(items):
    items = list(items)
    for mask in range(1 << len(items)):
        yield [items[i] for i in range(len(items)) if mask >> i & 1]


def neighborhood(U, subset):
    return set().union(*(U[u][2] for u in subset)) if subset else set()


def hall(U):
    return all(len(B) <= len(neighborhood(U, B)) for B in masks(U))


def analyze(word):
    U = full_u(word)
    if not hall(U):
        return {"hall": False}
    q_donors = q_tight = q_nonempty = q_violations = 0
    w_tight = w_occurrences = w_violations = 0
    phases = list(U)
    for u0 in phases:
        d, w, _cover, sstar, _off = U[u0]
        if d != 11 or ss_count(w) != 2:
            continue
        q_donors += 1
        for B in masks([u for u in phases if u != u0]):
            if any(U[u][0] not in (3, 7, 11) for u in B):
                continue
            if len(neighborhood(U, B)) != len(B):
                continue
            q_tight += 1
            if B:
                q_nonempty += 1
            if sstar in neighborhood(U, B):
                q_violations += 1
    for B in masks(phases):
        if not B or any(U[u][0] not in (3, 7) for u in B):
            continue
        if len(neighborhood(U, B)) != len(B):
            continue
        w_tight += 1
        for u in B:
            if U[u][0] == 7 and U[u][1] == W1:
                w_occurrences += 1
                if word[(u + 1) % len(word)] != "A":
                    w_violations += 1
    return dict(hall=True, q_donors=q_donors, q_tight=q_tight, q_nonempty=q_nonempty,
                q_violations=q_violations, w_tight=w_tight,
                w_occurrences=w_occurrences, w_violations=w_violations)


def check_e240():
    word = "AAAASSAAAASAAASASS"
    U = full_u(word)
    B = [2, 8, 11, 13]
    u0 = 7
    N = neighborhood(U, B)
    d, w, _cover, sstar, off = U[u0]
    print("E240", dict(word=word, U=sorted(U), hall=hall(U), donor=u0, lag=d,
          donor_word=w, ss=ss_count(w), true_oldest=sstar, oldest_offset=off, B=B,
          B_lags=[U[u][0] for u in B], B_words=[U[u][1] for u in B], N=sorted(N),
          tight=len(N) == len(B), non_AAS=any(U[u][0] != 3 for u in B),
          true_oldest_covered=sstar in N,
          w_next=[(u, word[(u + 1) % len(word)]) for u in B if U[u][1] == W1]))


def check_p15_offset_control():
    word = "AAAASAAASASASSS"
    U = full_u(word)
    u0 = 3
    d, w, _cover, sstar, off = U[u0]
    fixed = (u0 - 11) % len(word)
    q_nonempty = q_covered = 0
    for B in masks([u for u in U if u != u0]):
        N = neighborhood(U, B)
        if B and all(U[u][0] in (3, 7, 11) for u in B) and len(N) == len(B):
            q_nonempty += 1
            q_covered += sstar in N
    print("P15_OFFSET_CONTROL", dict(word=word, U=sorted(U), hall=hall(U), donor=u0,
          lag=d, donor_word=w, true_oldest=sstar, oldest_offset=off,
          fixed_offset11_phase=fixed, fixed_offset11_bit=word[fixed],
          q_nonempty=q_nonempty, q_violations=q_covered))


def check_small_nonempty_controls():
    for label, word in (("Q_P8_CONTROL", "SSAASAAA"), ("W_P10_CONTROL", "SSAAAASAAA")):
        U = full_u(word)
        print(label, dict(word=word, hall=hall(U),
              U=[(u, U[u][0], U[u][1], sorted(U[u][2]), U[u][3], U[u][4]) for u in U],
              aggregate=analyze(word)))


def donor_orientation():
    rows = []
    for i, w in enumerate(DONORS, 1):
        offsets = [k for k, c in enumerate(w, 1) if c == "S"]
        off = max(offsets)
        rows.append((f"d{i}", off, w[10], "REJECT" if off != 11 else "ACCEPT"))
    print("DONOR_ORIENTATION name true_oldest_offset offset11_bit naive_offset11")
    for row in rows:
        print(*row)


def main():
    phi = int(sys.argv[1]) if len(sys.argv) > 1 else 15
    print(f"PROTOCOL periods=1..{phi} words=all positive-sign-sum bit words lag_range=1..p(p+1)_inclusive full_U=yes Hall=all_subsets B=all_subsets holdout=no", flush=True)
    donor_orientation()
    check_e240()
    check_p15_offset_control()
    check_small_nonempty_controls()
    totals = {k: 0 for k in ("words", "hall_words", "q_donors", "q_tight", "q_nonempty", "q_violations", "w_tight", "w_occurrences", "w_violations")}
    first_q = first_w = None
    for p in range(1, phi + 1):
        row = {k: 0 for k in totals}
        for bits in product("SA", repeat=p):
            word = "".join(bits)
            if 2 * word.count("A") - p <= 0:
                continue
            row["words"] += 1
            a = analyze(word)
            if not a["hall"]:
                continue
            row["hall_words"] += 1
            for k in row:
                if k not in ("words", "hall_words"):
                    row[k] += a[k]
            if first_q is None and a["q_nonempty"]:
                first_q = (p, word, a)
            if first_w is None and a["w_occurrences"]:
                first_w = (p, word, a)
        for k in totals:
            totals[k] += row[k]
        print("PERIOD", p, row, flush=True)
    print("TOTAL", totals)
    print("FIRST_Q_NONEMPTY", first_q)
    print("FIRST_W_APPLICABLE", first_w)


if __name__ == "__main__":
    main()
