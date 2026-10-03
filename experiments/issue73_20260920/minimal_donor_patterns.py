#!/usr/bin/env python3
"""H-05 exact SS2 mass1 run generator and shortest-P2 terminal-pattern probe."""
import argparse
from collections import Counter
import hashlib
import itertools
import json
import subprocess


def p2(w):
    h = q = 0
    for k, b in enumerate(w, 1):
        x = 1 if b == "A" else -1
        h += x
        q += k*x
    return h == 1 and q == 0


def prefixes(w):
    h = q = 0
    result = []
    for k, b in enumerate(w, 1):
        x = 1 if b == "A" else -1
        h += x
        q += k*x
        if k < len(w) and h == 1 and q == 0:
            result.append(k)
    return result


def generated(d):
    assert d % 4 == 3 and d >= 11
    r = (d-1)//2 - 2
    for extra_s in itertools.combinations_with_replacement(range(r), 2):
        runs = [1] * r
        for k in extra_s:
            runs[k] += 1
        for extra_a in itertools.combinations_with_replacement(range(r+1), 4):
            gaps = [0] + [1]*(r-1) + [0]
            for k in extra_a:
                gaps[k] += 1
            w = "A"*gaps[0] + "".join("S"*runs[k] + "A"*gaps[k+1] for k in range(r))
            assert len(w) == d and w.count("A") - w.count("S") == 1
            assert sum(w[k:k+2] == "SS" for k in range(d-1)) == 2
            yield w


def placed(w, t):
    return {t: "A", **{t-k:b for k,b in enumerate(w, 1)}}


def compatible(a, b):
    return all(a[k] == b[k] for k in a.keys() & b.keys())


def analyze(d, verify_brute):
    words = list(generated(d))
    assert len(words) == len(set(words))
    p2words = sorted(w for w in words if p2(w))
    if verify_brute:
        brute = sorted("".join(v) for v in itertools.product("AS", repeat=d)
                       if sum(v[k] == v[k+1] == "S" for k in range(d-1)) == 2 and p2(v))
        assert p2words == brute, (d, len(p2words), len(brute))
    count = Counter(generated=len(words), p2_ss2=len(p2words))
    trailing = Counter()
    leading = Counter()
    examples = {}
    collisions = []
    for w in p2words:
        earlier = prefixes(w)
        is_min = not earlier
        count["minimal"] += is_min
        v = len(w)-len(w.rstrip("A"))
        a = len(w)-len(w.lstrip("A"))
        trailing[("minimal" if is_min else "nonminimal") + ":" + str(v)] += 1
        leading[("minimal" if is_min else "nonminimal") + ":" + str(a)] += 1
        off = max(k for k,b in enumerate(w, 1) if b == "S")
        root = placed(w, 0)
        aas = compatible(root, placed("AAS", 3-off))
        if aas:
            count["aas_minimal" if is_min else "aas_nonminimal"] += 1
        raw = []
        complete = []
        for k in (1, 6, 7):
            t = k-off
            pos = placed("SAAAASS", t)
            if compatible(root, pos):
                raw.append(k)
                if compatible(root, {**pos, t+1:"A", t+2:"A"}):
                    complete.append(k)
        for k in raw:
            count[("w1_raw_minimal:" if is_min else "w1_raw_nonminimal:") + str(k)] += 1
        for k in complete:
            count[("w1_complete_minimal:" if is_min else "w1_complete_nonminimal:") + str(k)] += 1
        if is_min:
            examples.setdefault("trailing"+str(v), w)
        if aas or complete:
            if len(collisions) < 12 or is_min:
                collisions.append(dict(word=w, minimal=is_min, proper_prefixes=earlier,
                                       oldest=off, aas=aas, w1_offsets=complete))
        if is_min and (aas or complete):
            count["minimal_countermodels"] += 1
    digest = hashlib.sha256("".join(w+"\n" for w in p2words).encode()).hexdigest()
    return dict(length=d, counters=dict(count), trailing=dict(trailing), leading=dict(leading),
                examples=examples, collisions=collisions, p2_words_sha256=digest,
                brute_force_crosscheck=verify_brute)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["discovery", "holdout"], required=True)
    args = ap.parse_args()
    print(json.dumps(dict(kind="provenance", mode=args.mode,
                         revision=subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip())), flush=True)
    bad = 0
    for d in ((11, 15, 19) if args.mode == "discovery" else (23, 27, 31)):
        result = analyze(d, args.mode == "discovery")
        bad += result["counters"].get("minimal_countermodels", 0)
        if d == 15:
            assert result["counters"].get("aas_nonminimal", 0) > 0
        print(json.dumps(result, sort_keys=True), flush=True)
    print(json.dumps(dict(status="COUNTEREXAMPLE" if bad else "NO_MINIMAL_COUNTEREXAMPLE",
                         scope=args.mode, minimal_countermodels=bad)), flush=True)
