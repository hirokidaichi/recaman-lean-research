#!/usr/bin/env python3
"""Reproducible checks for the nearest initial-S source budget.

1. Sharp family S^h AAA (SSSSAAAA)^(N-1): D_near, free, U, V, positivity.
2. Exhaustive source-relative words of length <= MAXN: no word with F < 2 D_near.

Source-relative clock 0 is the last initial S. A is +1. This F ignores
padding sources before clock 0, so it can only overestimate F.
"""
import argparse

def heights(word):
    h = 0
    hs = [0]
    for ch in word:
        h += 1 if ch == "A" else -1
        hs.append(h)
    return hs

def is_end(word, hs, b, start):
    if b >= len(word) or word[b] != "A":
        return False
    for t in range(start, b):
        if hs[b] != hs[t] + 1:
            continue
        area = 0
        for k in range(t, b):
            area += hs[k + 1] - hs[t]
        if area == 0:
            return True
    return False

def family(h, n):
    return "S" * h + "AAA" + ("SSSSAAAA" * (n - 1))

def audit_family(h, n):
    word = family(h, n)
    hs = heights(word)
    floor = hs[h]
    e = s = f = u = v = d = 0
    for k in range(1, len(word) - h + 1):
        i = h + k - 1
        if word[i] == "S":
            s += 1
        sup = is_end(word, hs, i, 0)
        loc = is_end(word, hs, i, h)
        if sup:
            e += 1
        if word[i] == "A" and not sup:
            f += 1
        u = max(u, e + 1 - s)
        if sup and not loc:
            depth = (hs[i] - floor) - 1
            v = max(v, depth)
            if hs[i] - floor == 2:
                d += 1
    gap = 10**9
    fp = 0
    for k in range(1, len(word) + 1):
        i = k - 1
        if word[i] == "A" and not is_end(word, hs, i, 0):
            fp += 1
        gap = min(gap, fp - (hs[k] + 1))
    return d, f, u, v, gap

def scan(maxn):
    neg = 0
    best = None
    for n in range(1, maxn + 1):
        lim = 1 << (n - 1)
        for mask in range(lim):
            hs = [0]
            bs = [0]
            h = b = d = f = zeros = 0
            zeros = 1
            for i in range(n):
                is_a = i > 0 and ((mask >> (i - 1)) & 1)
                if is_a:
                    src_h = h - 1
                    supplied = False
                    for j in range(i):
                        if hs[j] == src_h and b - bs[j] == (i - j) * src_h:
                            supplied = True
                            break
                    if not supplied:
                        f += 1
                    if h == 1 and b == 0 and zeros == 1:
                        d += 1
                h += 1 if is_a else -1
                b += h
                if h == 0 and b == 0:
                    zeros += 1
                hs.append(h)
                bs.append(b)
            if d >= 1 and (best is None or f - 2 * d < best[0]):
                best = (f - 2 * d, d, f, n)
            if d >= 1 and f < 2 * d:
                neg += 1
    return neg, best

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--maxn", type=int, default=14)
    args = parser.parse_args()
    print("FAMILY")
    for h in (2, 5):
        for n in (1, 2, 3, 5):
            d, f, u, v, gap = audit_family(h, n)
            print(f"h={h} N={n} D={d} F={f} U={u} V={v} posGap={gap}")
    neg, best = scan(args.maxn)
    print(f"SCAN maxn={args.maxn} negSlack={neg} bestSlack={best}")

if __name__ == "__main__":
    main()
