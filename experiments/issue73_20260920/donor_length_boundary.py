#!/usr/bin/env python3
"""H-04: exact length15 donor enumeration and periodic motif embedding."""
import hashlib
import itertools
import json
import subprocess


def p2(w):
    signs = [1 if b == "A" else -1 for b in w]
    return sum(signs) == 1 and sum(k*b for k, b in enumerate(signs, 1)) == 0


def minimal(w):
    return not any(p2(w[:d]) for d in range(1, len(w)))


def placed(w, t):
    return {t: "A", **{t-k: b for k, b in enumerate(w, 1)}}


def compatible(a, b):
    return all(a[t] == b[t] for t in a.keys() & b.keys())


def motif(root, mode):
    members = {root: "AAS"} if mode == "AAS" else {
        root-3: "AAS", root: "SAAAASS", root+2: "AAS"}
    bits = {}
    for t, w in members.items():
        assert compatible(bits, placed(w, t))
        bits.update(placed(w, t))
    return members, bits


def embed(w, members, mbits):
    combined = {**placed(w, 0), **mbits}
    lo, hi = min(combined), max(combined)
    cycle = "".join(combined.get(t, "A") for t in range(lo, hi+1))
    B = {t-lo: len(v) for t, v in members.items()}
    u0 = -lo
    p = len(cycle)
    def past(t, d):
        return "".join(cycle[(t-k) % p] for k in range(1, d+1))
    assert past(u0, 15) == w and cycle[u0] == "A"
    N = set()
    for u, d in B.items():
        v = past(u, d)
        assert cycle[u] == "A" and p2(v) and minimal(v)
        N |= {(u-k) % p for k, b in enumerate(v, 1) if b == "S"}
    sstar = (u0-max(k for k, b in enumerate(w, 1) if b == "S")) % p
    assert len(B) == len(N) and sstar in N and u0 not in B
    assert cycle.count("A") > cycle.count("S")
    return dict(period=p, cycle=cycle, donor=u0, donor_window=w,
                donor_minimal=minimal(w), B=B, N=sorted(N), oldest=sstar,
                deleted_N=sorted(N-{sstar}), period_mass=cycle.count("A")-cycle.count("S"))


def main():
    print(json.dumps(dict(kind="provenance", revision=subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip())), flush=True)
    totals = dict(words=0, p2_ss2=0, minimal_donors=0, aas_covers=0,
                  triple_covers=0, minimal_countermodels=0)
    examples = {}
    wordhash = hashlib.sha256()
    for w in map("".join, itertools.product("AS", repeat=15)):
        totals["words"] += 1
        if not p2(w) or sum(w[i:i+2] == "SS" for i in range(14)) != 2:
            continue
        wordhash.update((w+"\n").encode())
        totals["p2_ss2"] += 1
        totals["minimal_donors"] += minimal(w)
        off = max(k for k, b in enumerate(w, 1) if b == "S")
        for mode, ks in (("AAS", (3,)), ("w1_triple", (1, 6, 7))):
            for k in ks:
                members, mbits = motif(k-off, mode)
                if compatible(placed(w, 0), mbits):
                    totals["aas_covers" if mode == "AAS" else "triple_covers"] += 1
                    totals["minimal_countermodels"] += minimal(w)
                    ex = embed(w, members, mbits)
                    key = mode + ("_minimal" if minimal(w) else "_nonminimal")
                    examples.setdefault(key, ex)
    print(json.dumps(dict(kind="enumeration", totals=totals, donor_words_sha256=wordhash.hexdigest(), examples=examples), sort_keys=True), flush=True)
    print(json.dumps(dict(status="REFUTED" if examples else "NO_COUNTEREXAMPLE_IN_FROZEN_DOMAIN")), flush=True)


if __name__ == "__main__":
    main()
