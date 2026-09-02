#!/usr/bin/env python3
"""Unlimited-band closure of the hole-hopping game on a hole list.

Rule (DescendingChain / HoleHopping): landing at hole v makes the next small
candidates v-1, v-4, ... (class (v-1) mod 3); the chain lands the largest
hole of that class below v, then rotates again.  An arc enters the list at
the largest hole of some class.  With unlimited band survival an arc removes
one deterministic downward path.  This script repeatedly applies arcs with
entry classes chosen by a given order and reports what remains.

Usage: hole_hopping_closure.py HOLES_FILE
HOLES_FILE lines are single values or "a - b" ranges (Chaffin's format).
The output is an upper bound on what the hole-hopping combinatorics alone
can fill; it says nothing about band survival.
"""
import bisect
import collections
import random
import sys


def load(path):
    holes = []
    with open(path) as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            if "-" in line:
                lo, hi = (int(x) for x in line.split("-"))
                holes.extend(range(lo, hi + 1))
            else:
                holes.append(int(line))
    holes.sort()
    return holes


def closure(holes, order, label, watch=852655):
    cls = [[h for h in holes if h % 3 == c] for c in range(3)]
    alive = [[True] * len(cls[c]) for c in range(3)]
    parent = [list(range(len(cls[c]))) for c in range(3)]

    def find(c, i):
        root = i
        while root >= 0 and not alive[c][root]:
            root = parent[c][root]
        j = i
        while j >= 0 and j != root and not alive[c][j]:
            nj = parent[c][j]
            parent[c][j] = root
            j = nj
        return root

    def largest_below(c, pos):
        i = bisect.bisect_left(cls[c], pos) - 1
        return find(c, i) if i >= 0 else -1

    removed = 0
    arcs = 0
    stalled = 0
    watched = False
    while stalled < 3 and arcs < 10**6:
        c = order(arcs)
        top = largest_below(c, 1 << 62)
        this = 0
        if top >= 0:
            pos = cls[c][top]
            alive[c][top] = False
            parent[c][top] = top - 1
            this += 1
            cur = c
            while True:
                nc = (cur - 1) % 3
                j = largest_below(nc, pos)
                if j < 0:
                    break
                pos = cls[nc][j]
                alive[nc][j] = False
                parent[nc][j] = j - 1
                this += 1
                cur = nc
                if pos == watch:
                    watched = True
        removed += this
        arcs += 1
        stalled = stalled + 1 if this == 0 else 0
    remaining = sorted(cls[c][i] for c in range(3)
                       for i in range(len(cls[c])) if alive[c][i])
    print(f"[{label}] arcs={arcs} removed={removed} remaining={len(remaining)} "
          f"{watch}removed={watched}")
    print(f"  lowest remaining: {remaining[:12]}")
    print(f"  remaining by class: {dict(collections.Counter(h % 3 for h in remaining))}")


def main():
    holes = load(sys.argv[1])
    print(f"holes={len(holes)} min={holes[0]} max={holes[-1]} "
          f"classes={dict(collections.Counter(h % 3 for h in holes))}")
    closure(holes, lambda k: k % 3, "round-robin 0,1,2")
    closure(holes, lambda k: (2 - k) % 3, "round-robin 2,1,0")
    random.seed(1)
    closure(holes, lambda k: random.randrange(3), "random")
    for c in range(3):
        closure(holes, lambda k, c=c: c, f"always class {c}")


if __name__ == "__main__":
    main()
