#!/usr/bin/env python3
"""For every minimal lag-11 type, list S offsets that no U7 rule can occupy.

Time: signs[k]=ε(t+k). Type offsets i mean ε(t-i)=-1. t is A.
A U7 image at time s=t-i is an addition t' whose φ7 target is s.
Conflicts against the forced window are exact local obstructions.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import subprocess

LAG3 = (3,)
LAG7H1 = (1, 6, 7)
LAG7H2 = (2, 5, 7)


def p2_offsets(d):
    k = (d - 1) // 2
    target = d * (d + 1) // 4
    return [s for s in itertools.combinations(range(1, d + 1), k) if sum(s) == target]


def minimal_lag11():
    out = []
    for s in p2_offsets(11):
        def pref(p):
            inside = tuple(x for x in s if x <= p)
            kk = (p - 1) // 2
            return len(inside) == kk and sum(inside) == p * (p + 1) // 4

        if not pref(3) and not pref(7):
            out.append(s)
    return out


def force_ok(window, rel, val):
    if rel not in window:
        return True
    return window[rel] == val


def u7_possible(window, s_time, kind):
    """window maps time-relative-to-t -> sign. s_time is t-i."""
    if kind == "lag3":
        tp = s_time + 3
        need = {tp: 1, tp - 1: 1, tp - 2: 1, tp - 3: -1}
    elif kind == "lag7h1":
        tp = s_time + 7
        need = {tp: 1}
        for off in range(1, 8):
            need[tp - off] = -1 if off in LAG7H1 else 1
    else:
        tp = s_time + 5
        need = {tp: 1}
        for off in range(1, 8):
            need[tp - off] = -1 if off in LAG7H2 else 1
    return all(force_ok(window, rel, val) for rel, val in need.items())


def analyze(offsets):
    window = {0: 1}
    for i in range(1, 12):
        window[-i] = -1 if i in offsets else 1
    rows = []
    safe = []
    for i in offsets:
        s_time = -i
        kinds = [k for k in ("lag3", "lag7h1", "lag7h2") if u7_possible(window, s_time, k)]
        # following gap inside window
        more_recent = [j for j in offsets if j < i]
        if more_recent:
            gap_kind, gap = "eq", i - max(more_recent)
        else:
            gap_kind, gap = "ge", i + 1
        rec = {
            "offset": i,
            "u7_kinds": kinds,
            "gap_kind": gap_kind,
            "gap": gap,
        }
        rows.append(rec)
        if not kinds:
            safe.append(rec)
    return {"offsets": offsets, "S": rows, "safe": safe}


def main():
    print("protocol=H-20260908-01 safe U7-incompatible charges for all min lag-11 types", flush=True)
    print(
        "source_revision="
        + subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        flush=True,
    )
    print(
        "script_sha256="
        + hashlib.sha256(__import__("pathlib").Path(__file__).read_bytes()).hexdigest(),
        flush=True,
    )
    types = minimal_lag11()
    print("minimal=" + str(len(types)), flush=True)
    uncovered = []
    assignment = []
    for offs in types:
        rec = analyze(offs)
        print("TYPE=" + json.dumps(rec), flush=True)
        if not rec["safe"]:
            uncovered.append(offs)
        else:
            # prefer exact gap 2 among safe, else smallest offset
            safe = rec["safe"]
            safe.sort(key=lambda r: (0 if r["gap_kind"] == "eq" and r["gap"] == 2 else 1, r["offset"]))
            assignment.append({"type": offs, "charge": safe[0]})
    print("UNCOVERED=" + json.dumps(uncovered), flush=True)
    print("ASSIGNMENT=" + json.dumps(assignment), flush=True)
    if uncovered:
        print("CONCLUSION=some minimal type has no U7-incompatible S; local obstruction is incomplete", flush=True)
    else:
        print("CONCLUSION=every minimal lag-11 type has an S that U7 cannot occupy; candidate uniform charge exists", flush=True)


if __name__ == "__main__":
    main()
