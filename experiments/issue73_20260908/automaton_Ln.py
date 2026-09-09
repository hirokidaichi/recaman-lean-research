#!/usr/bin/env python3
"""H-20260908-02: bounded-lag shift-graph capacity falsifier.

Same algorithm as experiments/issue73_20260907/automaton_falsifier.py, but
self-contained and allowed to run a newly frozen horizon (default 23).
A positive cycle refutes |U_L| <= |D|. No cycle is COMPUTED, not a proof.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from collections import Counter, deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def is_supplied(mask: int, horizon: int) -> bool:
    for d in range(3, horizon + 1, 4):
        bits = mask & ((1 << d) - 1)
        if bits.bit_count() != (d + 1) // 2:
            continue
        moment = 0
        b = bits
        while b:
            low = b & -b
            moment += low.bit_length()
            b -= low
        if moment == d * (d + 1) // 4:
            return True
    return False


def suppliers_naive(word: list[int]) -> dict[int, list[int]]:
    result = {}
    p = len(word)
    for t, step in enumerate(word):
        if step < 0:
            continue
        total = moment = 0
        hits = []
        for d in range(1, p * (p + 1) + 1):
            e = word[(t - d) % p]
            total += e
            moment += d * e
            if total == 1 and moment == 0:
                hits.append(d)
        result[t] = hits
    return result


def search(horizon: int, outdir: Path) -> bool:
    size = 1 << horizon
    bound = size - 1
    print(
        json.dumps({"phase": "building_supplied", "horizon": horizon, "states": size}),
        flush=True,
    )
    supported = bytearray(is_supplied(mask, horizon) for mask in range(size))
    potential = [0] * size
    parent = [-1] * size
    depth = [0] * size
    queue = deque(range(size))
    queued = bytearray([1]) * size
    relaxations = 0
    print(
        json.dumps(
            {
                "phase": "relax",
                "supplied_states": int(sum(supported)),
            }
        ),
        flush=True,
    )
    while queue:
        u = queue.popleft()
        queued[u] = 0
        for bit, weight in ((0, -1), (1, supported[u])):
            v = ((u << 1) | bit) & bound
            candidate = potential[u] + weight
            if candidate <= potential[v]:
                continue
            potential[v] = candidate
            parent[v] = u
            depth[v] = depth[u] + 1
            relaxations += 1
            if relaxations & 0xFFFFF == 0:
                print(
                    json.dumps(
                        {
                            "phase": "progress",
                            "relaxations": relaxations,
                            "q": len(queue),
                            "max_potential": max(potential) if relaxations else 0,
                        }
                    ),
                    flush=True,
                )
            if depth[v] >= size:
                z = v
                for _ in range(size):
                    z = parent[z]
                    assert z >= 0
                cycle = [z]
                nxt = parent[z]
                while nxt != z:
                    assert nxt >= 0 and nxt not in cycle
                    cycle.append(nxt)
                    nxt = parent[nxt]
                cycle.reverse()
                word = [1 if node & 1 else -1 for node in cycle]
                cycle_weight = 0
                for i, u0 in enumerate(cycle):
                    v0 = cycle[(i + 1) % len(cycle)]
                    bit = v0 & 1
                    assert (((u0 << 1) | bit) & bound) == v0
                    cycle_weight += supported[u0] if bit else -1
                assert cycle_weight > 0
                sig = suppliers_naive(word)
                minus = word.count(-1)
                used = sum(bool(ds) for ds in sig.values())
                witness = {
                    "horizon": horizon,
                    "period": len(word),
                    "word": "".join("A" if e > 0 else "S" for e in word),
                    "sign_sum": sum(word),
                    "short_cycle_weight": cycle_weight,
                    "A_count": len(word) - minus,
                    "D_count": minus,
                    "U_count": used,
                    "suppliers": sig,
                }
                target = outdir / f"automaton_L{horizon}_counterexample.json"
                target.write_text(json.dumps(witness, sort_keys=True, indent=2) + "\n")
                print("CAPACITY_COUNTEREXAMPLE=" + json.dumps(witness, sort_keys=True), flush=True)
                return True
    for u in range(size):
        assert potential[(u << 1) & bound] >= potential[u] - 1
        assert potential[((u << 1) | 1) & bound] >= potential[u] + supported[u]
    payload = "\n".join(map(str, potential)) + "\n"
    raw = outdir / f"automaton_L{horizon}_potential.txt"
    raw.write_text(payload)
    summary = {
        "horizon": horizon,
        "states": size,
        "edges": 2 * size,
        "supplied_states": int(sum(supported)),
        "relaxations": relaxations,
        "potential_counts": dict(sorted(Counter(potential).items())),
        "potential_max": max(potential),
        "potential_sha256": hashlib.sha256(payload.encode()).hexdigest(),
    }
    (outdir / f"automaton_L{horizon}_summary.json").write_text(
        json.dumps(summary, indent=2) + "\n"
    )
    print("NO_POSITIVE_CYCLE=" + json.dumps(summary, sort_keys=True), flush=True)
    return False


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--horizon", type=int, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    if args.horizon < 3 or args.horizon % 4 != 3:
        raise SystemExit("horizon must be 3 mod 4")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    print("protocol=H-20260908-02 bounded-lag automaton", flush=True)
    print(
        "source_revision="
        + subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        flush=True,
    )
    print(
        "script_sha256="
        + hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        flush=True,
    )
    if search(args.horizon, args.output_dir):
        print("STOP: |U_L|<=|D| refuted at this L; replay the cycle independently", flush=True)
        return
    print("COMPLETE: no positive cycle at this L; not an all-L proof", flush=True)


if __name__ == "__main__":
    main()
